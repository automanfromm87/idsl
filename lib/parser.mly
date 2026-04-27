%{
(* CST-first parser. Every grammar production constructs a `Cst.green`
   node; the AST is reconstructed by `Lower.lower_program` after parsing.
   Each %token carries a `Cst.tok` payload so the leaf preserves trivia,
   text, and source positions. *)

let mk kind sp ep kids =
  Cst.GNode { Cst.nkind = kind; nspan = (sp, ep); nchildren = kids }

let g (t : Cst.tok) : Cst.green = Cst.GTok t
let gs (ts : Cst.tok list) : Cst.green list = List.map g ts
let opt = function Some x -> [x] | None -> []
%}

%token <Cst.tok> INT FLOAT STRING TSTRING IDENT DATE MONEY

%token <Cst.tok> SCHEMA RULE WHEN THEN
%token <Cst.tok> IF ELSE
%token <Cst.tok> AND OR NOT
%token <Cst.tok> ANY EVERY COUNT SUM OF IN WHERE FOR
%token <Cst.tok> IS MISSING PRESENT
%token <Cst.tok> TRUE FALSE
%token <Cst.tok> MIN MAX
%token <Cst.tok> EG IE
%token <Cst.tok> TEST GIVEN EXPECT
%token <Cst.tok> ACTION INSTANCE ON PRIORITY INCLUDE DOMAIN
%token <Cst.tok> COLON COMMA LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE
%token <Cst.tok> DOT AT PIPE
%token <Cst.tok> EQEQ NEQ LEQ GEQ LT GT EQ UNDERSCORE
%token <Cst.tok> PLUS MINUS STAR SLASH
%token <Cst.tok> NEWLINE EOF

%left OR
%left AND
%nonassoc NOT
%nonassoc EQEQ NEQ LT GT LEQ GEQ
%left PLUS MINUS
%left STAR SLASH
%nonassoc IS
%left DOT

%start <Cst.green> program
%%

(* `nls` returns the list of NEWLINE tokens it consumed so they appear
   as CST leaves of their containing node. *)
nls:
  | xs=list(NEWLINE) { xs }

(* Separator-preserving lists. menhir's built-in `separated_list` drops
   the separator tokens, which destroys byte-perfect roundtrip for the
   CST. These rules thread the separator into the result list as a
   `green` leaf alongside the elements. *)

comma_seq_green:
  | { [] }
  | x=expr { [x] }
  | x=expr c=COMMA rest=comma_seq_green { x :: g c :: rest }

comma_seq_kv:
  | { [] }
  | x=kv { [x] }
  | x=kv c=COMMA rest=comma_seq_kv { x :: g c :: rest }

comma_seq_param:
  | { [] }
  | x=action_param { [x] }
  | x=action_param c=COMMA rest=comma_seq_param { x :: g c :: rest }

comma_seq_ident:
  | x=IDENT { [g x] }
  | x=IDENT c=COMMA rest=comma_seq_ident { g x :: g c :: rest }

pipe_seq_ident:
  | x=IDENT { [g x] }
  | x=IDENT p=PIPE rest=pipe_seq_ident { g x :: g p :: rest }

dot_seq_ident:
  | x=IDENT { [g x] }
  | x=IDENT d=DOT rest=dot_seq_ident { g x :: g d :: rest }

program:
  | leading=nls items=program_seq eof=EOF
    { mk Cst.NProgram $startpos $endpos
        (gs leading @ items @ [g eof]) }

(* `program_seq` flattens program-level items + trailing newlines into a
   green list so we don't double-wrap.  The split between
   `program_item` and `top` exists so `domain X:` is only allowed at
   program level — preventing nested `top_seq` recursion that otherwise
   produces an unbounded shift/reduce conflict. *)
program_seq:
  | { [] }
  | it=program_item trail=nls rest=program_seq { (it :: gs trail) @ rest }

program_item:
  | t=top         { t }
  | d=domain_def  { d }

top_seq:
  | { [] }
  | t=top trail=nls rest=top_seq { (t :: gs trail) @ rest }

top:
  | m=metadata     { m }
  | a=action_sig   { a }
  | s=schema_def   { s }
  | r=rule_def     { r }
  | t=test_def     { t }
  | i=instance_def { i }
  | i=include_dir  { i }

include_dir:
  | inc=INCLUDE p=STRING
    { mk Cst.NInclude $startpos $endpos [g inc; g p] }

(* `domain X:` block: scopes every nested decl under the domain.
   Body is `top_seq`; nesting is grammatically disallowed because
   `domain_def` is only reachable from `program_item`. *)
domain_def:
  | dk=DOMAIN name=IDENT c=COLON n0=nls items=top_seq
    { mk Cst.NDomain $startpos $endpos
        ([g dk; g name; g c] @ gs n0 @ items) }

instance_def:
  | inst=INSTANCE sch=IDENT name=IDENT c=COLON n0=nls assigns=list(given_assign)
    { mk Cst.NInstance $startpos $endpos
        ([g inst; g sch; g name; g c] @ gs n0 @ assigns) }

metadata:
  | at=AT k=IDENT lp=LPAREN v=STRING rp=RPAREN
    { mk Cst.NMetadata $startpos $endpos [g at; g k; g lp; g v; g rp] }

action_sig:
  | at=AT act=ACTION name=IDENT lp=LPAREN ps=comma_seq_param rp=RPAREN
    { mk Cst.NAction $startpos $endpos
        ([g at; g act; g name; g lp] @ ps @ [g rp]) }

action_param:
  | name=IDENT c=COLON t=ty_annot
    { mk Cst.NActionParam $startpos $endpos [g name; g c; t] }

ty_annot:
  | id=IDENT
    { mk Cst.NTyAnnot $startpos $endpos [g id] }
  | lb=LBRACE xs=pipe_seq_ident rb=RBRACE
    { mk Cst.NTyAnnot $startpos $endpos ([g lb] @ xs @ [g rb]) }
  | lbk=LBRACKET t=ty_annot rbk=RBRACKET
    { mk Cst.NTyAnnot $startpos $endpos [g lbk; t; g rbk] }

(* ---------- schema ---------- *)

schema_def:
  | sk=SCHEMA name=IDENT c=COLON n0=nls fs=list(field)
    { mk Cst.NSchema $startpos $endpos
        ([g sk; g name; g c] @ gs n0 @ fs) }

field:
  | dash=MINUS name=IDENT c=COLON body=field_body nl=NEWLINE n0=nls
    { mk Cst.NField $startpos $endpos
        ([g dash; g name; g c; body; g nl] @ gs n0) }

field_body:
  | eg=EG ex=example
    { mk Cst.NFieldBody $startpos $endpos [g eg; ex] }
  | ie=IE e=expr
    { mk Cst.NFieldBody $startpos $endpos [g ie; e] }

example:
  | l=literal
    { mk Cst.NExample $startpos $endpos [l] }
  | xs=comma_seq_ident
    { mk Cst.NExample $startpos $endpos xs }
  | lb=LBRACKET es=comma_seq_green rb=RBRACKET
    { mk Cst.NExample $startpos $endpos ([g lb] @ es @ [g rb]) }

literal:
  | i=INT    { mk Cst.NLiteral $startpos $endpos [g i] }
  | f=FLOAT  { mk Cst.NLiteral $startpos $endpos [g f] }
  | s=STRING { mk Cst.NLiteral $startpos $endpos [g s] }
  | t=TRUE   { mk Cst.NLiteral $startpos $endpos [g t] }
  | f=FALSE  { mk Cst.NLiteral $startpos $endpos [g f] }
  | m=MONEY  { mk Cst.NLiteral $startpos $endpos [g m] }
  | d=DATE   { mk Cst.NLiteral $startpos $endpos [g d] }

(* ---------- rule ---------- *)

rule_def:
  | rk=RULE name=rule_name sch=rule_on? prio=rule_priority? c=COLON n0=nls
    desc=description?
    wk=WHEN wc=COLON n1=nls preds=expr_lines
    tk=THEN tc=COLON n2=nls acts=expr_lines
    { mk Cst.NRule $startpos $endpos
        ([g rk; name] @ opt sch @ opt prio @ [g c] @ gs n0
         @ opt desc
         @ [g wk; g wc] @ gs n1 @ preds
         @ [g tk; g tc] @ gs n2 @ acts) }

rule_on:
  | on=ON s=IDENT
    { mk Cst.NRuleOn $startpos $endpos [g on; g s] }

rule_priority:
  | pri=PRIORITY n=INT
    { mk Cst.NRulePriority $startpos $endpos [g pri; g n] }

rule_name:
  | xs=dot_seq_ident
    { mk Cst.NRuleName $startpos $endpos xs }

description:
  | s=TSTRING nl=NEWLINE n0=nls
    { mk Cst.NDescription $startpos $endpos ([g s; g nl] @ gs n0) }

expr_lines:
  | { [] }
  | e=expr nl=NEWLINE n0=nls rest=expr_lines
    { (e :: g nl :: gs n0) @ rest }

(* ---------- test ---------- *)

test_def:
  | tk=TEST name=STRING c=COLON n0=nls
    g0=given_block
    e0=expect_block
    { mk Cst.NTest $startpos $endpos
        ([g tk; g name; g c] @ gs n0 @ [g0; e0]) }

given_block:
  | gk=GIVEN sch=IDENT c=COLON n0=nls assigns=list(given_assign)
    { mk Cst.NGivenBlock $startpos $endpos
        ([g gk; g sch; g c] @ gs n0 @ assigns) }

given_assign:
  | name=IDENT eq=EQ value=expr nl=NEWLINE n0=nls
    { mk Cst.NGivenAssign $startpos $endpos
        ([g name; g eq; value; g nl] @ gs n0) }

expect_block:
  | ek=EXPECT c=COLON n0=nls xs=list(expectation)
    { mk Cst.NExpectBlock $startpos $endpos
        ([g ek; g c] @ gs n0 @ xs) }

expectation:
  | nk=NOT e=expr nl=NEWLINE n0=nls
    { mk Cst.NExpectation $startpos $endpos
        ([g nk; e; g nl] @ gs n0) }
  | e=expr nl=NEWLINE n0=nls
    { mk Cst.NExpectation $startpos $endpos
        ([e; g nl] @ gs n0) }

(* ---------- expressions ---------- *)

expr:
  | e1=expr op=AND   e2=expr   { mk Cst.NExpr $startpos $endpos [e1; g op; e2] }
  | e1=expr op=OR    e2=expr   { mk Cst.NExpr $startpos $endpos [e1; g op; e2] }
  | op=NOT e=expr              { mk Cst.NExpr $startpos $endpos [g op; e] }
  | e1=expr op=EQEQ  e2=expr   { mk Cst.NExpr $startpos $endpos [e1; g op; e2] }
  | e1=expr op=NEQ   e2=expr   { mk Cst.NExpr $startpos $endpos [e1; g op; e2] }
  | e1=expr op=LT    e2=expr   { mk Cst.NExpr $startpos $endpos [e1; g op; e2] }
  | e1=expr op=GT    e2=expr   { mk Cst.NExpr $startpos $endpos [e1; g op; e2] }
  | e1=expr op=LEQ   e2=expr   { mk Cst.NExpr $startpos $endpos [e1; g op; e2] }
  | e1=expr op=GEQ   e2=expr   { mk Cst.NExpr $startpos $endpos [e1; g op; e2] }
  | e1=expr op=PLUS  e2=expr   { mk Cst.NExpr $startpos $endpos [e1; g op; e2] }
  | e1=expr op=MINUS e2=expr   { mk Cst.NExpr $startpos $endpos [e1; g op; e2] }
  | e1=expr op=STAR  e2=expr   { mk Cst.NExpr $startpos $endpos [e1; g op; e2] }
  | e1=expr op=SLASH e2=expr   { mk Cst.NExpr $startpos $endpos [e1; g op; e2] }
  | ifk=IF c=expr tk=THEN t=expr ek=ELSE el=expr
    { mk Cst.NExpr $startpos $endpos [g ifk; c; g tk; t; g ek; el] }
  | ak=ANY   x=IDENT ink=IN y=IDENT sep=pred_sep p=expr
    { mk Cst.NExpr $startpos $endpos [g ak; g x; g ink; g y; sep; p] }
  | ak=EVERY x=IDENT ink=IN y=IDENT sep=pred_sep p=expr
    { mk Cst.NExpr $startpos $endpos [g ak; g x; g ink; g y; sep; p] }
  | ck=COUNT ofk=OF x=IDENT ink=IN y=IDENT wk=WHERE p=expr
    { mk Cst.NExpr $startpos $endpos [g ck; g ofk; g x; g ink; g y; g wk; p] }
  | sk=SUM ofk=OF f=expr fk=FOR x=IDENT ink=IN y=IDENT wk=WHERE p=expr
    { mk Cst.NExpr $startpos $endpos [g sk; g ofk; f; g fk; g x; g ink; g y; g wk; p] }
  | e=expr ik=IS mk1=MISSING
    { mk Cst.NExpr $startpos $endpos [e; g ik; g mk1] }
  | e=expr ik=IS pk=PRESENT
    { mk Cst.NExpr $startpos $endpos [e; g ik; g pk] }
  | a=atom { a }

%inline pred_sep:
  | c=COLON  { g c }
  | w=WHERE  { g w }

atom:
  | l=literal { l }
  | a=atom dot=DOT f=IDENT
    { mk Cst.NAtom $startpos $endpos [a; g dot; g f] }
  | id=IDENT lp=LPAREN args=comma_seq_green rp=RPAREN
    { mk Cst.NAtom $startpos $endpos ([g id; g lp] @ args @ [g rp]) }
  | mk1=MIN lp=LPAREN e1=expr c=COMMA e2=expr rp=RPAREN
    { mk Cst.NAtom $startpos $endpos [g mk1; g lp; e1; g c; e2; g rp] }
  | mk1=MAX lp=LPAREN e1=expr c=COMMA e2=expr rp=RPAREN
    { mk Cst.NAtom $startpos $endpos [g mk1; g lp; e1; g c; e2; g rp] }
  | id=IDENT
    { mk Cst.NAtom $startpos $endpos [g id] }
  | mi=MISSING
    { mk Cst.NAtom $startpos $endpos [g mi] }
  | u=UNDERSCORE
    { mk Cst.NAtom $startpos $endpos [g u] }
  | minus=MINUS a=atom
    { mk Cst.NAtom $startpos $endpos [g minus; a] }
  | lp=LPAREN e=expr rp=RPAREN
    { mk Cst.NAtom $startpos $endpos [g lp; e; g rp] }
  | lb=LBRACKET es=comma_seq_green rb=RBRACKET
    { mk Cst.NAtom $startpos $endpos ([g lb] @ es @ [g rb]) }
  | lb=LBRACE kvs=comma_seq_kv rb=RBRACE
    { mk Cst.NAtom $startpos $endpos ([g lb] @ kvs @ [g rb]) }

kv:
  | name=IDENT c=COLON v=expr
    { mk Cst.NKv $startpos $endpos [g name; g c; v] }
