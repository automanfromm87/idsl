(* Front-end driver: lex + parse, then resolve `include "..."` directives
   into a single flattened program. Cycles terminate via the visited set.

   Public API returns a {ast; tokens; tree} record so callers never need to
   reach into mutable parser state. *)

open Ast

(* The parser populates Cst's global trivia/token buffer as a side effect
   of lexing; we snapshot it into a `parse_result` immediately and never
   expose the buffer beyond this module. *)

type parse_result = {
  ast      : (Ast.program, Diagnostic.t list) result;
  tokens   : Cst.tok list;
  tree     : Cst.node;
  includes : string list;   (* absolute paths of included files (parse_file) *)
}

let empty_tree () : Cst.node =
  { Cst.nkind = NProgram;
    nspan = (Lexing.dummy_pos, Lexing.dummy_pos);
    nchildren = [] }

let parse_diag pos msg =
  Diagnostic.error ~stage:Diagnostic.Parse ~pos msg

(* Parse one buffer. Returns (result, tokens, tree). The tree is always
   populated — even on failure it is at least a flat `NError` over the
   tokens we managed to lex. *)
let parse_lexbuf lexbuf : (Ast.program, Diagnostic.t) result * Cst.tok list * Cst.node =
  let cst_or_err, tokens =
    Cst.with_state (fun () ->
      Lexer.reset ();
      try Ok (Parser.program Lexer.token lexbuf)
      with
      | Lexer.Lex_error msg ->
          Error (parse_diag (Lexing.lexeme_start_p lexbuf) msg)
      | Parser.Error ->
          let p = Lexing.lexeme_start_p lexbuf in
          Error (parse_diag p
                   (Printf.sprintf "parse error at token %S" (Lexing.lexeme lexbuf))))
  in
  match cst_or_err with
  | Ok (Cst.GNode root) ->
      let result =
        try Ok (Lower.lower_program root)
        with Lower.Lower_error m ->
          Error (parse_diag (fst root.nspan) m)
      in
      (result, tokens, root)
  | Ok _ ->
      let tree = Cst.flat_tree tokens in
      (Error (parse_diag Lexing.dummy_pos "parser did not return a program node"),
       tokens, tree)
  | Error d ->
      (Error d, tokens, Cst.flat_tree tokens)

(* On parse failure we want a complete token stream for fmt / completion;
   re-lex the source and recover from lexer errors by capturing the
   offending bytes as opaque whitespace-trivia so the CST keeps every
   byte of the original input.  Without this, fmt would silently
   truncate any source containing an un-lexable character — a
   regression caught by the property suite. *)
let cst_of_failed_source (s : string) : Cst.tok list * Cst.node =
  let lb = Lexing.from_string s in
  let (), tokens = Cst.with_state (fun () ->
    Lexer.reset ();
    let rec drain () =
      match Lexer.token lb with
      | EOF _ -> ()
      | _ -> drain ()
      | exception _ ->
          (* The lexer's catch-all `_` rule matched one byte and then
             raised; ocamllex has already advanced lex_curr_pos past it,
             so lex_start_pos points at the byte we want to preserve. *)
          if lb.lex_start_pos < lb.lex_buffer_len then begin
            let bad =
              Bytes.sub_string lb.lex_buffer lb.lex_start_pos 1 in
            Cst.push_trivia
              { Cst.trk_kind = Whitespace;
                trk_text = bad;
                trk_pos  = lb.lex_start_p; };
            drain ()
          end
    in
    drain ())
  in
  (tokens, Cst.flat_tree tokens)

let extract_includes (prog : Ast.program) : string list =
  List.filter_map (function
    | Ast.TInclude { inc_path; _ } -> Some inc_path
    | _ -> None) prog

let parse_string s : parse_result =
  let lb = Lexing.from_string s in
  let (r, tokens, tree) = parse_lexbuf lb in
  match r with
  | Ok p ->
      { ast = Ok p; tokens; tree; includes = extract_includes p }
  | Error d ->
      let tokens, tree = cst_of_failed_source s in
      { ast = Error [d]; tokens; tree; includes = [] }

let parse_channel ?(filename = "<stdin>") ic =
  let lb = Lexing.from_channel ic in
  Lexing.set_filename lb filename;
  parse_lexbuf lb

let parse_file_raw path =
  let ic = open_in path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () -> parse_channel ~filename:path ic)

(* Path canonicalization for include cycle detection. *)
let canon p =
  try
    let cwd = Sys.getcwd () in
    let abs = if Filename.is_relative p then Filename.concat cwd p else p in
    let parts = String.split_on_char '/' abs in
    let stack = List.fold_left (fun acc seg ->
      match seg, acc with
      | "" , [] -> [""]
      | "" , _  -> acc
      | ".", _  -> acc
      | "..", _ :: rest when rest <> [] -> rest
      | "..", _ -> acc
      | s, _ -> s :: acc) [] parts in
    String.concat "/" (List.rev stack)
  with _ -> p

(* Resolve includes recursively, optionally consulting a `~lookup`
   callback before reading from disk. The callback receives the
   canonicalized absolute path and may return `Some content` to short-
   circuit the read — the LSP layer wires this to the in-memory
   document store so unsaved edits are visible across includes.

   Errors accumulate; the returned tokens / tree always belong to the
   root file (consumers want `fmt` / cst dumps keyed off the entry
   point, not whichever include happened to be parsed last). *)
let parse_file ?(lookup : string -> string option = fun _ -> None)
               path : parse_result =
  let visited : (string, unit) Hashtbl.t = Hashtbl.create 8 in
  let errors : Diagnostic.t list ref = ref [] in
  let push d = errors := d :: !errors in
  let root : (Cst.tok list * Cst.node * Ast.program) option ref = ref None in
  let parse_at path =
    let key = canon path in
    match lookup key with
    | Some content ->
        let lb = Lexing.from_string content in
        Lexing.set_filename lb path;
        parse_lexbuf lb
    | None ->
        try parse_file_raw path
        with Sys_error msg ->
          (Error (parse_diag Lexing.dummy_pos
                    (Printf.sprintf "%s: %s" path msg)),
           [], empty_tree ())
  in
  let rec parse_one path =
    let key = canon path in
    if Hashtbl.mem visited key then []
    else begin
      Hashtbl.add visited key ();
      let result, tokens, tree = parse_at path in
      match result with
      | Error d ->
          if !root = None then root := Some (tokens, tree, []);
          push d; []
      | Ok prog ->
          if !root = None then root := Some (tokens, tree, prog);
          let dir = Filename.dirname path in
          List.concat_map (function
            | TInclude { inc_path; inc_pos = _ } ->
                let resolved =
                  if Filename.is_relative inc_path
                  then Filename.concat dir inc_path
                  else inc_path in
                parse_one resolved
            | other -> [other]) prog
    end
  in
  let prog = parse_one path in
  let tokens, tree, root_prog = match !root with
    | Some t -> t
    | None   -> [], empty_tree (), []
  in
  let dir = Filename.dirname path in
  let includes = List.filter_map (function
    | Ast.TInclude { inc_path; _ } ->
        Some (if Filename.is_relative inc_path
              then Filename.concat dir inc_path else inc_path)
    | _ -> None) root_prog in
  match List.rev !errors with
  | [] -> { ast = Ok prog;  tokens; tree; includes }
  | es -> { ast = Error es; tokens; tree; includes }

(* Error recovery: split source at lines beginning with a top-level
   keyword, parse each chunk independently, collect successes and errors. *)
let top_level_re = Str.regexp
  "^\\(schema\\|rule\\|test\\|instance\\|include\\|@\\)"

let split_top_chunks (s : string) : (int * string) list =
  let lines = String.split_on_char '\n' s in
  let chunks = ref [] in
  let cur = Buffer.create 256 in
  let cur_start = ref 0 in
  let line_no = ref 0 in
  List.iter (fun line ->
    let starts_top =
      try Str.string_match top_level_re line 0 with _ -> false in
    if starts_top && Buffer.length cur > 0 then begin
      chunks := (!cur_start, Buffer.contents cur) :: !chunks;
      Buffer.clear cur;
      cur_start := !line_no
    end;
    Buffer.add_string cur line;
    Buffer.add_char cur '\n';
    incr line_no
  ) lines;
  if Buffer.length cur > 0 then
    chunks := (!cur_start, Buffer.contents cur) :: !chunks;
  List.rev !chunks

let parse_with_recovery (s : string) :
    Ast.program * (int * Diagnostic.t) list =
  let chunks = split_top_chunks s in
  let progs = ref [] in
  let errs = ref [] in
  List.iter (fun (line_off, chunk) ->
    let lb = Lexing.from_string chunk in
    let dummy = Lexing.dummy_pos in
    lb.lex_curr_p <- { dummy with pos_lnum = line_off + 1; pos_bol = 0 };
    let (r, _, _) = parse_lexbuf lb in
    match r with
    | Ok p -> progs := p :: !progs
    | Error d -> errs := (line_off, d) :: !errs
  ) chunks;
  (List.concat (List.rev !progs), List.rev !errs)
