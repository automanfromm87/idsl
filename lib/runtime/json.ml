(* Minimal JSON parser + writer, no dependencies.
   Sufficient for loading test fixtures and emitting outcome reports. *)

type t =
  | JNull
  | JBool   of bool
  | JNum    of float
  | JStr    of string
  | JArr    of t list
  | JObj    of (string * t) list

exception Parse_error of string

(* ---------- writer ---------- *)

let buf_add_string b s = Buffer.add_string b s

let escape_string s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter (fun c ->
    match c with
    | '"'  -> Buffer.add_string b "\\\""
    | '\\' -> Buffer.add_string b "\\\\"
    | '\n' -> Buffer.add_string b "\\n"
    | '\r' -> Buffer.add_string b "\\r"
    | '\t' -> Buffer.add_string b "\\t"
    | c when Char.code c < 0x20 ->
        Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
    | c -> Buffer.add_char b c) s;
  Buffer.add_char b '"';
  Buffer.contents b

let rec to_buf b = function
  | JNull   -> buf_add_string b "null"
  | JBool true  -> buf_add_string b "true"
  | JBool false -> buf_add_string b "false"
  | JNum f ->
      if Float.is_integer f && Float.abs f < 1e16
      then buf_add_string b (Printf.sprintf "%d" (int_of_float f))
      else buf_add_string b (Printf.sprintf "%g" f)
  | JStr s -> buf_add_string b (escape_string s)
  | JArr xs ->
      Buffer.add_char b '[';
      List.iteri (fun i x ->
        if i > 0 then Buffer.add_string b ", ";
        to_buf b x) xs;
      Buffer.add_char b ']'
  | JObj kvs ->
      Buffer.add_char b '{';
      List.iteri (fun i (k, v) ->
        if i > 0 then Buffer.add_string b ", ";
        buf_add_string b (escape_string k);
        Buffer.add_string b ": ";
        to_buf b v) kvs;
      Buffer.add_char b '}'

let to_string j =
  let b = Buffer.create 64 in
  to_buf b j;
  Buffer.contents b

let rec to_buf_pretty b indent = function
  | JArr [] -> buf_add_string b "[]"
  | JObj [] -> buf_add_string b "{}"
  | JArr xs ->
      Buffer.add_string b "[\n";
      List.iteri (fun i x ->
        if i > 0 then Buffer.add_string b ",\n";
        Buffer.add_string b (String.make (indent + 2) ' ');
        to_buf_pretty b (indent + 2) x) xs;
      Buffer.add_char b '\n';
      Buffer.add_string b (String.make indent ' ');
      Buffer.add_char b ']'
  | JObj kvs ->
      Buffer.add_string b "{\n";
      List.iteri (fun i (k, v) ->
        if i > 0 then Buffer.add_string b ",\n";
        Buffer.add_string b (String.make (indent + 2) ' ');
        Buffer.add_string b (escape_string k);
        Buffer.add_string b ": ";
        to_buf_pretty b (indent + 2) v) kvs;
      Buffer.add_char b '\n';
      Buffer.add_string b (String.make indent ' ');
      Buffer.add_char b '}'
  | x -> to_buf b x

let to_string_pretty j =
  let b = Buffer.create 128 in
  to_buf_pretty b 0 j;
  Buffer.contents b

(* ---------- parser ---------- *)

type lex = { src : string; mutable pos : int }

let lex_peek l =
  if l.pos >= String.length l.src then None
  else Some l.src.[l.pos]

let lex_skip_ws l =
  let len = String.length l.src in
  while l.pos < len &&
        (let c = l.src.[l.pos] in c = ' ' || c = '\t' || c = '\n' || c = '\r')
  do l.pos <- l.pos + 1 done

let lex_expect l c =
  lex_skip_ws l;
  if l.pos >= String.length l.src || l.src.[l.pos] <> c then
    raise (Parse_error (Printf.sprintf "expected %C at offset %d" c l.pos));
  l.pos <- l.pos + 1

let lex_match l s =
  let len = String.length s in
  if l.pos + len <= String.length l.src
     && String.sub l.src l.pos len = s
  then (l.pos <- l.pos + len; true)
  else false

let parse_string l =
  lex_expect l '"';
  let b = Buffer.create 16 in
  let len = String.length l.src in
  let rec go () =
    if l.pos >= len then raise (Parse_error "unterminated string");
    match l.src.[l.pos] with
    | '"' -> l.pos <- l.pos + 1; Buffer.contents b
    | '\\' ->
        if l.pos + 1 >= len then raise (Parse_error "bad escape");
        let c = l.src.[l.pos + 1] in
        l.pos <- l.pos + 2;
        (match c with
         | '"'  -> Buffer.add_char b '"'
         | '\\' -> Buffer.add_char b '\\'
         | '/'  -> Buffer.add_char b '/'
         | 'n'  -> Buffer.add_char b '\n'
         | 't'  -> Buffer.add_char b '\t'
         | 'r'  -> Buffer.add_char b '\r'
         | _    -> raise (Parse_error "unknown escape"));
        go ()
    | c -> Buffer.add_char b c; l.pos <- l.pos + 1; go ()
  in
  go ()

let parse_number l =
  let start = l.pos in
  let len = String.length l.src in
  if l.pos < len && l.src.[l.pos] = '-' then l.pos <- l.pos + 1;
  while l.pos < len &&
        (let c = l.src.[l.pos] in
         (c >= '0' && c <= '9') || c = '.' || c = 'e' || c = 'E'
         || c = '+' || c = '-')
  do l.pos <- l.pos + 1 done;
  let s = String.sub l.src start (l.pos - start) in
  try float_of_string s
  with _ -> raise (Parse_error ("bad number " ^ s))

let rec parse_value l =
  lex_skip_ws l;
  match lex_peek l with
  | None -> raise (Parse_error "unexpected eof")
  | Some 'n' ->
      if lex_match l "null" then JNull
      else raise (Parse_error "expected null")
  | Some 't' ->
      if lex_match l "true" then JBool true
      else raise (Parse_error "expected true")
  | Some 'f' ->
      if lex_match l "false" then JBool false
      else raise (Parse_error "expected false")
  | Some '"' -> JStr (parse_string l)
  | Some '[' -> parse_array l
  | Some '{' -> parse_object l
  | Some c when c = '-' || (c >= '0' && c <= '9') -> JNum (parse_number l)
  | Some c -> raise (Parse_error (Printf.sprintf "unexpected %C" c))

and parse_array l =
  lex_expect l '[';
  lex_skip_ws l;
  if lex_peek l = Some ']' then (l.pos <- l.pos + 1; JArr [])
  else begin
    let items = ref [] in
    let v = parse_value l in
    items := [v];
    let cont = ref true in
    while !cont do
      lex_skip_ws l;
      match lex_peek l with
      | Some ',' ->
          l.pos <- l.pos + 1;
          let v = parse_value l in
          items := v :: !items
      | Some ']' -> l.pos <- l.pos + 1; cont := false
      | _ -> raise (Parse_error "expected , or ] in array")
    done;
    JArr (List.rev !items)
  end

and parse_object l =
  lex_expect l '{';
  lex_skip_ws l;
  if lex_peek l = Some '}' then (l.pos <- l.pos + 1; JObj [])
  else begin
    let items = ref [] in
    let parse_kv () =
      lex_skip_ws l;
      let k = parse_string l in
      lex_skip_ws l;
      lex_expect l ':';
      let v = parse_value l in
      items := (k, v) :: !items
    in
    parse_kv ();
    let cont = ref true in
    while !cont do
      lex_skip_ws l;
      match lex_peek l with
      | Some ',' -> l.pos <- l.pos + 1; parse_kv ()
      | Some '}' -> l.pos <- l.pos + 1; cont := false
      | _ -> raise (Parse_error "expected , or } in object")
    done;
    JObj (List.rev !items)
  end

let of_string s =
  let l = { src = s; pos = 0 } in
  let v = parse_value l in
  lex_skip_ws l;
  if l.pos < String.length s then
    raise (Parse_error (Printf.sprintf "trailing input at offset %d" l.pos));
  v

(* Replace or insert a top-level field. Errors if the value is not an object. *)
let set_field obj k v =
  match obj with
  | JObj kvs ->
      let replaced = ref false in
      let kvs' = List.map (fun (k', v') ->
        if k' = k then (replaced := true; (k, v)) else (k', v')) kvs in
      JObj (if !replaced then kvs' else kvs @ [(k, v)])
  | _ -> raise (Parse_error "set_field: value is not an object")

let of_file path =
  let ic = open_in path in
  Fun.protect ~finally:(fun () -> close_in_noerr ic) (fun () ->
    let n = in_channel_length ic in
    let s = really_input_string ic n in
    of_string s)
