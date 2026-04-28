(* Concrete Syntax Tree.

   Trivia (whitespace, comments, suppressed newlines) is stored as
   leading/trailing lists on each significant token, Roslyn-style. The
   parser produces a `green` tree directly; `Lower` derives the AST from it. *)

type kind =
  | KW       of string         (* schema, rule, when, then, ... *)
  | Ident    of string         (* user identifier *)
  | Op       of string         (* ==, !=, <=, +, -, ... *)
  | Punct    of string         (* `:` `,` `.` `@` `(` `)` `[` `]` `{` `}` `=` *)
  | Str      of string
  | TStr     of string         (* triple-quoted *)
  | Int      of int
  | Flt      of float
  | Money    of string
  | Date     of string
  | Bool     of bool
  | EgIe     of string         (* "e.g." or "i.e." *)
  | Newline
  | Whitespace
  | Comment  of string
  | Eof

(* A "trivia" leaf: whitespace, line comment, or a continuation newline
   that the parser doesn't see as significant. *)
type trivia = {
  trk_kind : kind;             (* one of Whitespace / Newline / Comment _ *)
  trk_text : string;
  trk_pos  : Lexing.position;
}

type tok = {
  kind     : kind;
  start    : Lexing.position;
  stop     : Lexing.position;
  text     : string;
  leading  : trivia list;      (* in source order *)
  trailing : trivia list;      (* in source order *)
}

(* Per-parse mutable state. Owned by `with_state`, swapped in/out under
   `parse_mutex` so concurrent callers serialize at the parse boundary
   instead of trashing each other's token snapshot. *)

type state = {
  mutable pending_leading : trivia list;
  mutable buf             : tok list;
}

let make_state () : state = { pending_leading = []; buf = [] }

let current : state option ref = ref None
let parse_mutex : Mutex.t = Mutex.create ()

let with_state (f : unit -> 'a) : 'a * tok list =
  Mutex.lock parse_mutex;
  let prev = !current in
  let s = make_state () in
  current := Some s;
  Fun.protect
    ~finally:(fun () ->
      current := prev;
      Mutex.unlock parse_mutex)
    (fun () ->
       let r = f () in
       (r, List.rev s.buf))

let active_state () : state =
  match !current with
  | Some s -> s
  | None ->
      failwith "Cst: no active parse state — call sites must run \
                inside Cst.with_state"

(* Per-parse state replaces the old explicit reset; kept as a no-op so
   the lexer's call site doesn't need to change. *)
let reset () = ()

let add_trivia kind lexbuf =
  let s = active_state () in
  let text = Lexing.lexeme lexbuf in
  let pos  = Lexing.lexeme_start_p lexbuf in
  s.pending_leading <-
    { trk_kind = kind; trk_text = text; trk_pos = pos } :: s.pending_leading

let take_leading () =
  let s = active_state () in
  let xs = List.rev s.pending_leading in
  s.pending_leading <- [];
  xs

let make_token lexbuf kind =
  let s = active_state () in
  let start = Lexing.lexeme_start_p lexbuf in
  let stop  = Lexing.lexeme_end_p   lexbuf in
  let text  = Lexing.lexeme         lexbuf in
  let t = { kind; start; stop; text;
            leading = take_leading ();
            trailing = [] } in
  s.buf <- t :: s.buf;
  t

let push t =
  let s = active_state () in
  s.buf <- t :: s.buf

(* Push a pre-built trivia record onto the active state's pending list.
   Used by error recovery to preserve bytes that didn't match any
   lexer production. *)
let push_trivia (t : trivia) =
  let s = active_state () in
  s.pending_leading <- t :: s.pending_leading

type node_kind =
  | NProgram
  | NMetadata
  | NAction
  | NActionParam
  | NTyAnnot
  | NSchema
  | NRule
  | NRuleName
  | NRuleOn
  | NRulePriority
  | NDescription
  | NTest
  | NInstance
  | NInclude
  | NDomain
  | NPredicate
  | NPredicateSig
  | NField
  | NFieldBody
  | NExample
  | NLiteral
  | NWhenBlock
  | NThenBlock
  | NGivenBlock
  | NGivenAssign
  | NExpectBlock
  | NExpectation
  | NCasesBlock
  | NCase
  | NExpr
  | NAtom
  | NKv
  | NError

let pp_node_kind = function
  | NProgram      -> "Program"
  | NMetadata     -> "Metadata"
  | NAction       -> "Action"
  | NActionParam  -> "ActionParam"
  | NTyAnnot      -> "TyAnnot"
  | NSchema       -> "Schema"
  | NRule         -> "Rule"
  | NRuleName     -> "RuleName"
  | NRuleOn       -> "RuleOn"
  | NRulePriority -> "RulePriority"
  | NDescription  -> "Description"
  | NTest         -> "Test"
  | NInstance     -> "Instance"
  | NInclude      -> "Include"
  | NDomain       -> "Domain"
  | NPredicate    -> "Predicate"
  | NPredicateSig -> "PredicateSig"
  | NField        -> "Field"
  | NFieldBody    -> "FieldBody"
  | NExample      -> "Example"
  | NLiteral      -> "Literal"
  | NWhenBlock    -> "WhenBlock"
  | NThenBlock    -> "ThenBlock"
  | NGivenBlock   -> "GivenBlock"
  | NGivenAssign  -> "GivenAssign"
  | NExpectBlock  -> "ExpectBlock"
  | NExpectation  -> "Expectation"
  | NCasesBlock   -> "CasesBlock"
  | NCase         -> "Case"
  | NExpr         -> "Expr"
  | NAtom         -> "Atom"
  | NKv           -> "Kv"
  | NError        -> "Error"

let pp_token_kind = function
  | KW s        -> Printf.sprintf "KW %S" s
  | Ident s     -> Printf.sprintf "Ident %S" s
  | Op s        -> Printf.sprintf "Op %S" s
  | Punct s     -> Printf.sprintf "Punct %S" s
  | Str _       -> "Str"
  | TStr _      -> "TStr"
  | Int _       -> "Int"
  | Flt _       -> "Flt"
  | Money _     -> "Money"
  | Date _      -> "Date"
  | Bool _      -> "Bool"
  | EgIe s      -> Printf.sprintf "EgIe %S" s
  | Newline     -> "Newline"
  | Whitespace  -> "Whitespace"
  | Comment _   -> "Comment"
  | Eof         -> "Eof"

type green =
  | GTok  of tok            (* leaf — a token (includes trivia) *)
  | GNode of node           (* internal — span + children *)
and node = {
  nkind    : node_kind;
  nspan    : Lexing.position * Lexing.position;
  nchildren : green list;
}

(* Reconstruct the byte-exact source text from a tree. *)
let emit_trivia b (xs : trivia list) =
  List.iter (fun t -> Buffer.add_string b t.trk_text) xs

let rec emit_green b = function
  | GTok t ->
      emit_trivia b t.leading;
      Buffer.add_string b t.text;
      emit_trivia b t.trailing
  | GNode n -> List.iter (emit_green b) n.nchildren

let text_of_green g =
  let b = Buffer.create 256 in
  emit_green b g;
  Buffer.contents b

let text_of_node n =
  let b = Buffer.create 256 in
  List.iter (emit_green b) n.nchildren;
  Buffer.contents b

(* Wrap a token list as a flat NError tree. Recovery fallback when no
   structural tree was produced. *)
let flat_tree (toks : tok list) : node =
  let prog_start, prog_end = match toks with
    | [] -> Lexing.dummy_pos, Lexing.dummy_pos
    | first :: _ ->
        let last = List.fold_left (fun _ t -> t) first toks in
        first.start, last.stop
  in
  { nkind = NError;
    nspan = (prog_start, prog_end);
    nchildren = List.map (fun t -> GTok t) toks }

(* Find the deepest node containing a position (LSP coords). *)
let node_at_lsp (root : node) ~line ~col =
  let in_node n =
    let (s, e) = n.nspan in
    let s_ln = s.pos_lnum - 1 and s_co = s.pos_cnum - s.pos_bol in
    let e_ln = e.pos_lnum - 1 and e_co = e.pos_cnum - e.pos_bol in
    let after_start = line > s_ln || (line = s_ln && col >= s_co) in
    let before_end  = line < e_ln || (line = e_ln && col <= e_co) in
    after_start && before_end
  in
  let rec descend n =
    match List.find_map (function
      | GNode child when in_node child -> Some (descend child)
      | _ -> None) n.nchildren with
    | Some deeper -> deeper
    | None -> n
  in
  if in_node root then Some (descend root) else None

(* -------- queries used by LSP -------- *)

let pos_of_lsp ~(line:int) ~(col:int) (p : Lexing.position) =
  p.pos_lnum - 1 = line && p.pos_cnum - p.pos_bol = col

let lsp_lt (l1, c1) (l2, c2) =
  l1 < l2 || (l1 = l2 && c1 < c2)
let lsp_le a b = a = b || lsp_lt a b

let to_lsp (p : Lexing.position) =
  (p.pos_lnum - 1, p.pos_cnum - p.pos_bol)

(* All tokens up to and including those whose start is < (line, col).
   Trivia (Whitespace / Newline / Comment) is included. *)
let tokens_before (toks : tok list) ~line ~col =
  List.filter (fun t -> lsp_le (to_lsp t.start) (line, col - 1)) toks
  |> Array.of_list

(* skip Whitespace / Comment / Newline backward; return Some idx of the
   first significant token at or before i, or None. *)
let prev_significant (arr : tok array) i =
  let r = ref i in
  while !r >= 0 &&
    (match arr.(!r).kind with
     | Whitespace | Newline | Comment _ -> true
     | _ -> false)
  do decr r done;
  if !r >= 0 then Some !r else None

let kind_at arr i = if i >= 0 && i < Array.length arr then Some arr.(i).kind else None

let is_op s arr i =
  match kind_at arr i with Some (Op x) -> x = s | _ -> false

let is_punct s arr i =
  match kind_at arr i with Some (Punct x) -> x = s | _ -> false

let is_kw s arr i =
  match kind_at arr i with Some (KW x) -> x = s | _ -> false

let ident_at arr i =
  match kind_at arr i with Some (Ident s) -> Some s | _ -> None

(* Read a path like `recv.field` (or just `field`) ending at the
   significant token at index i — going backwards. Returns the path in
   source order ("clause" :: "Kind" :: []) and the start index. *)
let read_path_back arr i =
  let rec loop acc cur =
    match prev_significant arr cur with
    | None -> acc, cur
    | Some k ->
        match arr.(k).kind with
        | Ident name ->
            (* check if there's a '.' before *)
            (match prev_significant arr (k - 1) with
             | Some j when is_punct "." arr j ->
                 loop (name :: acc) (j - 1)
             | _ -> (name :: acc), k)
        | _ -> acc, cur
  in
  let path, _ = loop [] i in
  path

