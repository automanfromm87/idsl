{
open Parser

exception Lex_error of string

(* Per-parse state, swapped on each `Lexer.reset` and serialized via
   `Cst.with_state`'s mutex so concurrent parses don't corrupt each
   other. *)
type state = {
  mutable paren_depth : int;
  mutable at_eof      : bool;
  mutable last_token  : token;
}

let dummy_tok () = {
  Cst.kind = Cst.Eof; start = Lexing.dummy_pos; stop = Lexing.dummy_pos;
  text = ""; leading = []; trailing = [];
}

let make_state () : state =
  { paren_depth = 0;
    at_eof      = false;
    last_token  = EOF (dummy_tok ()) }

let current : state ref = ref (make_state ())

let is_keyword = function
  | "schema" | "rule" | "when" | "then" | "if" | "else"
  | "and" | "or" | "not" | "any" | "every" | "count" | "sum"
  | "of" | "in" | "where" | "is" | "missing" | "present"
  | "true" | "false" | "min" | "max" | "for"
  | "test" | "given" | "expect" | "action" | "instance"
  | "on" | "priority" | "include" | "domain"
  | "predicate" | "self" | "cases" | "default" -> true
  | _ -> false

(* tokens after which a newline is treated as continuation *)
let is_continuation = function
  | AND _ | OR _ | PLUS _ | MINUS _ | STAR _ | SLASH _
  | EQEQ _ | NEQ _ | LT _ | GT _ | LEQ _ | GEQ _
  | COMMA _ | LPAREN _ | DOT _ | AT _
  | IF _ | THEN _ | ELSE _ | NOT _ | IS _ | IN _ | OF _ | WHERE _ | FOR _
  | DEFAULT _ | LBRACKET _ | COLON _ | LBRACE _ | EQ _
  | TEST _ | GIVEN _ | EXPECT _
  | ACTION _ | PIPE _ | INSTANCE _ | ON _ | PRIORITY _ | INCLUDE _
  | DOMAIN _ | PREDICATE _ | CASES _ | ARROW _
    -> true
  | _ -> false

let emit t = (!current).last_token <- t; t

(* Emit a significant token: build a Cst.tok with currently-pending
   leading trivia, then wrap it as the menhir terminal. *)
let emit_log lexbuf cst_kind wrap =
  let ct = Cst.make_token lexbuf cst_kind in
  emit (wrap ct)

let add_trivia kind lexbuf =
  Cst.add_trivia kind lexbuf

(* Install a fresh state at the start of each parse_lexbuf. *)
let reset () =
  current := make_state ();
  Cst.reset ()
}

let digit    = ['0'-'9']
let int      = digit+
let frac     = '.' digit+
let float    = digit+ frac
let alpha    = ['a'-'z' 'A'-'Z' '_']
let alphanum = alpha | digit
let ident    = alpha alphanum*
let date     = digit digit digit digit '-' digit digit '-' digit digit
(* `$1,000,000` — digits with thousands-separator commas. Each comma
   must be followed by at least one digit, so a trailing `,` (e.g. in
   a list of money literals) stays a separator and isn't eaten. *)
let money    = '$' digit+ (',' digit+)* (frac)?
let ws       = [' ' '\t' '\r']

rule token = parse
  | "#" [^ '\n']* as c          { add_trivia (Comment c) lexbuf; token lexbuf }
  | ws+                         { add_trivia Whitespace   lexbuf; token lexbuf }
  | '\n' {
      Lexing.new_line lexbuf;
      let st = !current in
      if st.paren_depth > 0 then begin
        add_trivia Newline lexbuf;     (* suppressed inside parens → trivia *)
        token lexbuf
      end else if is_continuation st.last_token then begin
        add_trivia Newline lexbuf;     (* continuation after binop → trivia *)
        token lexbuf
      end else
        emit_log lexbuf Newline (fun t -> NEWLINE t)
    }
  | date as d                   { emit_log lexbuf (Date d) (fun ct -> DATE ct) }
  | money as m                  { emit_log lexbuf (Money m) (fun ct -> MONEY ct) }
  | float as f                  { emit_log lexbuf (Flt (float_of_string f)) (fun ct -> FLOAT ct) }
  | int as i                    { emit_log lexbuf (Int (int_of_string i)) (fun ct -> INT ct) }
  | "\"\"\""                    { tstring (Lexing.lexeme_start_p lexbuf)
                                          (Buffer.create 64) lexbuf }
  | '"' ([^ '"']* as s) '"'     { emit_log lexbuf (Str s) (fun ct -> STRING ct) }
  | '_'                         { emit_log lexbuf (Punct "_") (fun ct -> UNDERSCORE ct) }
  | ident as id                 {
      if is_keyword id then
        let parser_tok_ctor : Cst.tok -> Parser.token = match id with
          | "schema"   -> (fun ct -> SCHEMA ct)
          | "rule"     -> (fun ct -> RULE ct)
          | "when"     -> (fun ct -> WHEN ct)
          | "then"     -> (fun ct -> THEN ct)
          | "if"       -> (fun ct -> IF ct)
          | "else"     -> (fun ct -> ELSE ct)
          | "and"      -> (fun ct -> AND ct)
          | "or"       -> (fun ct -> OR ct)
          | "not"      -> (fun ct -> NOT ct)
          | "any"      -> (fun ct -> ANY ct)
          | "every"    -> (fun ct -> EVERY ct)
          | "count"    -> (fun ct -> COUNT ct)
          | "sum"      -> (fun ct -> SUM ct)
          | "of"       -> (fun ct -> OF ct)
          | "in"       -> (fun ct -> IN ct)
          | "where"    -> (fun ct -> WHERE ct)
          | "is"       -> (fun ct -> IS ct)
          | "missing"  -> (fun ct -> MISSING ct)
          | "present"  -> (fun ct -> PRESENT ct)
          | "true"     -> (fun ct -> TRUE ct)
          | "false"    -> (fun ct -> FALSE ct)
          | "min"      -> (fun ct -> MIN ct)
          | "max"      -> (fun ct -> MAX ct)
          | "for"      -> (fun ct -> FOR ct)
          | "test"     -> (fun ct -> TEST ct)
          | "given"    -> (fun ct -> GIVEN ct)
          | "expect"   -> (fun ct -> EXPECT ct)
          | "action"   -> (fun ct -> ACTION ct)
          | "instance" -> (fun ct -> INSTANCE ct)
          | "on"       -> (fun ct -> ON ct)
          | "priority" -> (fun ct -> PRIORITY ct)
          | "include"  -> (fun ct -> INCLUDE ct)
          | "domain"   -> (fun ct -> DOMAIN ct)
          | "predicate" -> (fun ct -> PREDICATE ct)
          | "self"     -> (fun ct -> SELF ct)
          | "cases"    -> (fun ct -> CASES ct)
          | "default"  -> (fun ct -> DEFAULT ct)
          | _ -> assert false
        in
        emit_log lexbuf (KW id) parser_tok_ctor
      else emit_log lexbuf (Ident id) (fun ct -> IDENT ct) }
  | "=="                        { emit_log lexbuf (Op "==") (fun ct -> EQEQ ct) }
  | "="                         { emit_log lexbuf (Punct "=") (fun ct -> EQ ct) }
  | "!="                        { emit_log lexbuf (Op "!=") (fun ct -> NEQ ct) }
  | "<="                        { emit_log lexbuf (Op "<=") (fun ct -> LEQ ct) }
  | ">="                        { emit_log lexbuf (Op ">=") (fun ct -> GEQ ct) }
  | '<'                         { emit_log lexbuf (Op "<") (fun ct -> LT ct) }
  | '>'                         { emit_log lexbuf (Op ">") (fun ct -> GT ct) }
  | '+'                         { emit_log lexbuf (Op "+") (fun ct -> PLUS ct) }
  | "->"                        { emit_log lexbuf (Punct "->") (fun ct -> ARROW ct) }
  | '-'                         { emit_log lexbuf (Op "-") (fun ct -> MINUS ct) }
  | '*'                         { emit_log lexbuf (Op "*") (fun ct -> STAR ct) }
  | '/'                         { emit_log lexbuf (Op "/") (fun ct -> SLASH ct) }
  | ':'                         { emit_log lexbuf (Punct ":") (fun ct -> COLON ct) }
  | ','                         { emit_log lexbuf (Punct ",") (fun ct -> COMMA ct) }
  | '('                         { (!current).paren_depth <- (!current).paren_depth + 1; emit_log lexbuf (Punct "(") (fun ct -> LPAREN ct) }
  | ')'                         { (!current).paren_depth <- (!current).paren_depth - 1; emit_log lexbuf (Punct ")") (fun ct -> RPAREN ct) }
  | '['                         { (!current).paren_depth <- (!current).paren_depth + 1; emit_log lexbuf (Punct "[") (fun ct -> LBRACKET ct) }
  | ']'                         { (!current).paren_depth <- (!current).paren_depth - 1; emit_log lexbuf (Punct "]") (fun ct -> RBRACKET ct) }
  | '{'                         { (!current).paren_depth <- (!current).paren_depth + 1; emit_log lexbuf (Punct "{") (fun ct -> LBRACE ct) }
  | '}'                         { (!current).paren_depth <- (!current).paren_depth - 1; emit_log lexbuf (Punct "}") (fun ct -> RBRACE ct) }
  | '.'                         { emit_log lexbuf (Punct ".") (fun ct -> DOT ct) }
  | '@'                         { emit_log lexbuf (Punct "@") (fun ct -> AT ct) }
  | '|'                         { emit_log lexbuf (Punct "|") (fun ct -> PIPE ct) }
  | eof {
      let st = !current in
      if st.at_eof then emit_log lexbuf Eof (fun ct -> EOF ct)
      else begin
        st.at_eof <- true;
        let dummy = { Cst.kind = Newline; start = Lexing.lexeme_start_p lexbuf;
                      stop = Lexing.lexeme_end_p lexbuf; text = "";
                      leading = []; trailing = [] } in
        emit (NEWLINE dummy)
      end
    }
  | _ as c {
      raise (Lex_error
        (Printf.sprintf "lexer: unexpected character %C at line %d"
           c (Lexing.lexeme_start_p lexbuf).pos_lnum))
    }

and tstring start_p buf = parse
  | "\"\"\""        {
      let body = Buffer.contents buf in
      let stop_p = Lexing.lexeme_end_p lexbuf in
      let raw = "\"\"\"" ^ body ^ "\"\"\"" in
      let ct = { Cst.kind = TStr body; start = start_p; stop = stop_p;
                 text = raw; leading = Cst.take_leading (); trailing = [] } in
      Cst.push ct;
      emit (TSTRING ct) }
  | '\n'            { Lexing.new_line lexbuf;
                      Buffer.add_char buf '\n';
                      tstring start_p buf lexbuf }
  | eof             { raise (Lex_error "unterminated triple-quoted string") }
  | _ as c          { Buffer.add_char buf c; tstring start_p buf lexbuf }
