(* CST → AST lowering. *)

open Cst
open Ast

exception Lower_error of string
let err fmt = Printf.ksprintf (fun s -> raise (Lower_error s)) fmt

let tok_text (t : Cst.tok) = t.text

let tok_string_payload (t : Cst.tok) =
  match t.kind with
  | Cst.Str s | Cst.TStr s -> s
  | _ -> err "expected string literal, got %S" t.text

let tok_int_payload (t : Cst.tok) =
  match t.kind with
  | Cst.Int i -> i
  | _ -> err "expected int literal, got %S" t.text

let is_trivia_kind = function
  | Newline | Whitespace | Comment _ -> true
  | _ -> false

let is_ident_kind = function Cst.Ident _ -> true | _ -> false

let significant (kids : green list) : green list =
  List.filter (function GTok t -> not (is_trivia_kind t.kind) | _ -> true) kids

(* ---------- expression lowering ----------

   An NExpr / NAtom / NLiteral node: dispatch on the children's structure. *)

let rec lower_expr (n : node) : Ast.expr =
  let pos = fst n.nspan in
  let endpos = snd n.nspan in
  let kids = significant n.nchildren in
  let nd = lower_expr_node n.nkind kids in
  Ast.mke pos endpos nd

and lower_expr_node nk kids : expr_node =
  match nk, kids with
  | NLiteral, [GTok t] ->
      ELit (lower_literal t)
  | NAtom, [g] when (match g with GNode n -> n.nkind = NLiteral | _ -> false) ->
      (match g with
       | GNode n -> (lower_expr n).e_node
       | _ -> err "literal in atom shape mismatch")
  | NAtom, [GTok id] when is_ident_kind id.kind ->
      EVar (tok_text id)
  | NAtom, [GTok t] when t.kind = Cst.KW "missing" -> EMissing
  | _ ->
      (* General atom / expr structure dispatch. We use the children's
         shape to figure out which expression form it is. *)
      lower_expr_general nk kids

and lower_expr_general _nk kids : expr_node =
  match kids with
  (* MISSING / wildcard / ident leaf via NAtom *)
  | [GTok t] -> lower_atom_leaf t
  (* IDENT . field — record the field token's pos for goto/refs/rename *)
  | [GNode recv; GTok dot; GTok field]
    when dot.kind = Cst.Punct "." ->
      let r = lower_expr recv in
      EField (r, field.start, tok_text field)
  (* IDENT (args) — call *)
  | GTok id :: GTok lp :: rest
    when is_ident_kind id.kind && lp.kind = Cst.Punct "(" ->
      let args = collect_call_args rest in
      ECall (tok_text id, args)
  (* MIN ( e , e ) / MAX ( e , e ) *)
  | GTok kw :: GTok _lp :: e1 :: GTok _comma :: e2 :: GTok _rp :: []
    when (match kw.kind with Cst.KW "min" | Cst.KW "max" -> true | _ -> false) ->
      let nm = match kw.kind with Cst.KW s -> s | _ -> "min" in
      ECall (nm, [lower_expr_g e1; lower_expr_g e2])
  (* Unary: NOT expr | - expr *)
  | [GTok op; e]
    when (match op.kind with Cst.KW "not" -> true | Cst.Op "-" -> true | _ -> false) ->
      let inner = lower_expr_g e in
      let u = match op.kind with
        | Cst.KW "not" -> Not
        | Cst.Op "-" -> Neg
        | _ -> err "unknown unary op" in
      EUnary (u, inner)
  (* Binary *)
  | [a; GTok op; b] when is_binop_kind op.kind ->
      let opv = binop_of_kind op.kind in
      EBin (opv, lower_expr_g a, lower_expr_g b)
  (* if c then t else e *)
  | [GTok ifk; c; GTok _tk; t; GTok _ek; e]
    when ifk.kind = Cst.KW "if" ->
      EIf (lower_expr_g c, lower_expr_g t, lower_expr_g e)
  (* any|every X in Y : pred *)
  | [GTok ak; GTok x; GTok _ink; GTok y; _sep; p]
    when (match ak.kind with Cst.KW "any" | Cst.KW "every" -> true | _ -> false) ->
      let xn = tok_text x and yn = tok_text y in
      let pe = lower_expr_g p in
      (match ak.kind with
       | Cst.KW "any"   -> EAny   (xn, yn, pe)
       | Cst.KW "every" -> EEvery (xn, yn, pe)
       | _ -> err "unreachable")
  (* count of X in Y where pred *)
  | [GTok ck; GTok _ofk; GTok x; GTok _ink; GTok y; GTok _wk; p]
    when ck.kind = Cst.KW "count" ->
      ECount (tok_text x, tok_text y, lower_expr_g p)
  (* sum of expr for X in Y where pred *)
  | [GTok sk; GTok _ofk; f; GTok _fk; GTok x; GTok _ink; GTok y; GTok _wk; p]
    when sk.kind = Cst.KW "sum" ->
      ESum (lower_expr_g f, tok_text x, tok_text y, lower_expr_g p)
  (* expr is missing | is present *)
  | [e; GTok ik; GTok mk] when ik.kind = Cst.KW "is" ->
      let inner = lower_expr_g e in
      (match mk.kind with
       | Cst.KW "missing" -> EIsMissing inner
       | Cst.KW "present" -> EIsPresent inner
       | _ -> err "unknown is-suffix")
  (* ( expr ) — passthrough atom *)
  | [GTok lp; e; GTok rp]
    when lp.kind = Cst.Punct "(" && rp.kind = Cst.Punct ")" ->
      (lower_expr_g e).e_node
  (* [ es ] — list literal *)
  | GTok lb :: rest when lb.kind = Cst.Punct "[" ->
      let es = collect_list_elements rest in
      EList es
  (* { kvs } — object literal *)
  | GTok lb :: rest when lb.kind = Cst.Punct "{" ->
      let kvs = collect_kvs rest in
      EObject kvs
  | _ -> err "lower_expr: unrecognised CST shape (%d children)" (List.length kids)

and lower_atom_leaf (t : Cst.tok) : expr_node =
  match t.kind with
  | Cst.Ident s -> EVar s
  | Cst.KW "missing" -> EMissing
  | Cst.Punct "_" -> EWildcard
  | _ -> err "atom leaf has unexpected kind %S" t.text

and lower_expr_g = function
  | GNode n -> lower_expr n
  | GTok t -> Ast.mke t.start t.stop (lower_atom_leaf t)

and is_binop_kind = function
  | Cst.Op ("==" | "!=" | "<" | ">" | "<=" | ">=" | "+" | "-" | "*" | "/")
  | Cst.KW ("and" | "or") -> true
  | _ -> false

and binop_of_kind = function
  | Cst.KW "and" -> And  | Cst.KW "or" -> Or
  | Cst.Op "==" -> Eq    | Cst.Op "!=" -> Neq
  | Cst.Op "<"  -> Lt    | Cst.Op ">"  -> Gt
  | Cst.Op "<=" -> Leq   | Cst.Op ">=" -> Geq
  | Cst.Op "+"  -> Add   | Cst.Op "-"  -> Sub
  | Cst.Op "*"  -> Mul   | Cst.Op "/"  -> Div
  | _ -> err "binop_of_kind: not a binop"

and collect_call_args (kids : green list) : expr list =
  (* between LPAREN and RPAREN, separated by COMMA *)
  let acc = ref [] in
  List.iter (function
    | GNode _ as g -> acc := lower_expr_g g :: !acc
    | GTok t when t.kind = Cst.Punct ")" -> ()
    | GTok t when t.kind = Cst.Punct "," -> ()
    | GTok _ -> ()) kids;
  List.rev !acc

and collect_list_elements (kids : green list) : expr list =
  let acc = ref [] in
  List.iter (function
    | GNode _ as g -> acc := lower_expr_g g :: !acc
    | GTok t when t.kind = Cst.Punct "]" || t.kind = Cst.Punct "," -> ()
    | GTok _ -> ()) kids;
  List.rev !acc

and collect_kvs (kids : green list) : (ident * expr) list =
  let acc = ref [] in
  List.iter (function
    | GNode n when n.nkind = NKv ->
        let kk = significant n.nchildren in
        (match kk with
         | GTok name :: GTok _colon :: v :: _ ->
             acc := (tok_text name, lower_expr_g v) :: !acc
         | _ -> err "bad kv shape")
    | GTok t when t.kind = Cst.Punct "}" || t.kind = Cst.Punct "," -> ()
    | _ -> ()) kids;
  List.rev !acc

and lower_literal (t : Cst.tok) : literal =
  match t.kind with
  | Cst.Int i    -> LInt i
  | Cst.Flt f    -> LFloat f
  | Cst.Str s    -> LString s
  | Cst.KW "true"  -> LBool true
  | Cst.KW "false" -> LBool false
  | Cst.Money m  -> LMoney m
  | Cst.Date d   -> LDate d
  | _ -> err "unknown literal token %S" t.text

(* ---------- field / schema lowering ---------- *)

and lower_field (n : node) : field =
  let kids = significant n.nchildren in
  match kids with
  | GTok _dash :: GTok name :: GTok _colon :: GNode body :: _ ->
      (* Use the name-token's position so error messages and the
         semantic index point exactly at the field identifier. *)
      let pos = name.start in
      let body_kids = significant body.nchildren in
      (match body_kids with
       | GTok eg :: rest when eg.kind = Cst.EgIe "e.g." ->
           let ex = lower_example rest in
           FRaw (pos, tok_text name, ex)
       | GTok ie :: [GNode e] when ie.kind = Cst.EgIe "i.e." ->
           FDerived (pos, tok_text name, lower_expr e)
       | _ -> err "field body shape unrecognised")
  | _ -> err "field shape unrecognised"

and lower_example (kids : green list) : example =
  (* The grammar wraps the whole example in a single NExample node
     (so kids may be `[GNode {nkind = NExample; ...}]`). Descend through
     that wrapper before pattern-matching on actual content. *)
  let kids =
    match kids with
    | [GNode n] when n.nkind = NExample -> significant n.nchildren
    | _ -> kids
  in
  match kids with
  | [GNode lit] when lit.nkind = NLiteral ->
      ExLit (match lit.nchildren with
        | [GTok t] -> lower_literal t
        | _ -> err "literal child")
  | _ ->
      let has_lbracket =
        List.exists (function GTok t -> t.kind = Cst.Punct "[" | _ -> false) kids in
      if has_lbracket then
        let es = collect_list_elements kids in
        ExList es
      else
        let names = List.filter_map (function
          | GTok t when is_ident_kind t.kind -> Some (tok_text t)
          | _ -> None) kids in
        ExEnum names

let lower_schema (n : node) : schema_def =
  let kids = significant n.nchildren in
  let name, name_pos = match kids with
    | _sk :: GTok n :: _ -> tok_text n, n.start
    | _ -> err "schema_def shape" in
  let fields =
    List.filter_map (function
      | GNode f when f.nkind = NField -> Some (lower_field f)
      | _ -> None) kids in
  (* spos points at the schema name (not the `schema` keyword) so that
     hover / goto / rename / refs all anchor on the identifier. *)
  { sname = name; spos = name_pos; sfields = fields }

(* ---------- include / metadata / action_sig / instance ---------- *)

let lower_include (n : node) : include_decl =
  match significant n.nchildren with
  | [GTok _kw; GTok p] ->
      { inc_path = tok_string_payload p; inc_pos = fst n.nspan }
  | _ -> err "include shape"

let lower_metadata (n : node) : metadata =
  match significant n.nchildren with
  | [GTok _at; GTok k; GTok _lp; GTok v; GTok _rp] ->
      { mkey = tok_text k; mvalue = tok_string_payload v }
  | _ -> err "metadata shape"

let rec lower_ty_annot (n : node) : ty_annot =
  match significant n.nchildren with
  | [GTok id] when is_ident_kind id.kind ->
      AnnScalar (tok_text id)
  | GTok lb :: _ when lb.kind = Cst.Punct "{" ->
      let names = List.filter_map (function
        | GTok t when is_ident_kind t.kind -> Some (tok_text t)
        | _ -> None) (significant n.nchildren) in
      AnnEnum names
  | [GTok lb; GNode inner; GTok _rb] when lb.kind = Cst.Punct "[" ->
      AnnList (lower_ty_annot inner)
  | _ -> err "ty_annot shape"

let lower_action_param (n : node) : action_param =
  match significant n.nchildren with
  | [GTok name; GTok _c; GNode ty] ->
      { pname = tok_text name; ptype = lower_ty_annot ty; ppos = fst n.nspan }
  | _ -> err "action_param shape"

let lower_action_sig (n : node) : action_sig =
  let kids = significant n.nchildren in
  match kids with
  | _at :: _act :: GTok name :: _lp :: rest ->
      let params = List.filter_map (function
        | GNode p when p.nkind = NActionParam -> Some (lower_action_param p)
        | _ -> None) rest in
      { asname = tok_text name; asparams = params; aspos = name.start }
  | _ -> err "action_sig shape"

(* Reuse field / given_assign / etc. for instance bodies. *)
let lower_given_assign (n : node) : field_assign =
  match significant n.nchildren with
  | GTok name :: GTok _eq :: GNode v :: _ ->
      { aname     = tok_text name;
        aname_pos = name.start;
        avalue    = lower_expr v;
        apos      = name.start }
  | _ -> err "given_assign shape"

let lower_instance (n : node) : instance_def =
  match significant n.nchildren with
  | _inst :: GTok sch :: GTok name :: _c :: rest ->
      let assigns = List.filter_map (function
        | GNode a when a.nkind = NGivenAssign -> Some (lower_given_assign a)
        | _ -> None) rest in
      { iname        = tok_text name;
        iname_pos    = name.start;
        ischema      = tok_text sch;
        ischema_pos  = sch.start;
        ipos         = fst n.nspan;
        ivalues      = assigns }
  | _ -> err "instance shape"

(* ---------- rule / test ---------- *)

(* Returns names paired with their token positions, in source order.
   Used so the binder can emit a Symbol for each path segment instead of
   one for the joined string. *)
let lower_rule_name (n : node) : (ident * Lexing.position) list =
  List.filter_map (function
    | GTok t when is_ident_kind t.kind -> Some (tok_text t, t.start)
    | _ -> None) (significant n.nchildren)

let lower_rule (n : node) : rule_def =
  (* Single pass over kids: pick named sub-nodes from the pre-when phase,
     and partition the remaining children into when/then buckets. *)
  let path = ref None in
  let rschema = ref None in
  let rschema_pos = ref None in
  let rpriority = ref None in
  let rdesc = ref None in
  let when_acc = ref [] in
  let then_acc = ref [] in
  let phase = ref `Pre in
  List.iter (fun g ->
    match g, !phase with
    | GTok t, _ when t.kind = Cst.KW "when" -> phase := `When
    | GTok t, _ when t.kind = Cst.KW "then" -> phase := `Then
    | GNode m, `Pre when m.nkind = NRuleName ->
        path := Some (lower_rule_name m)
    | GNode m, `Pre when m.nkind = NRuleOn ->
        (match significant m.nchildren with
         | [_; GTok name] ->
             rschema     := Some (tok_text name);
             rschema_pos := Some name.start
         | _ -> ())
    | GNode m, `Pre when m.nkind = NRulePriority ->
        (match significant m.nchildren with
         | [_; GTok num] -> rpriority := Some (tok_int_payload num)
         | _ -> ())
    | GNode m, `Pre when m.nkind = NDescription ->
        (match significant m.nchildren with
         | GTok t :: _ -> rdesc := Some (tok_string_payload t)
         | _ -> ())
    | _, `When -> when_acc := g :: !when_acc
    | _, `Then -> then_acc := g :: !then_acc
    | _, `Pre -> ()
  ) (significant n.nchildren);
  let path_with_locs = match !path with
    | Some p -> p | None -> err "rule missing name" in
  let exprs_in xs =
    List.filter_map (function
      | GNode e when e.nkind = NExpr || e.nkind = NAtom || e.nkind = NLiteral ->
          Some (fst e.nspan, lower_expr e)
      | _ -> None) xs
  in
  { rpath        = List.map fst path_with_locs;
    rpath_locs   = List.map snd path_with_locs;
    rpos         = (match path_with_locs with
                    | (_, p) :: _ -> p
                    | [] -> fst n.nspan);
    rdesc        = !rdesc;
    rschema      = !rschema;
    rschema_pos  = !rschema_pos;
    rpriority    = (match !rpriority with Some p -> p | None -> 0);
    rwhen        = exprs_in (List.rev !when_acc);
    rthen        = exprs_in (List.rev !then_acc) }

let lower_given_block (n : node) : given_block =
  match significant n.nchildren with
  | _gk :: GTok sch :: _c :: rest ->
      let assigns = List.filter_map (function
        | GNode a when a.nkind = NGivenAssign -> Some (lower_given_assign a)
        | _ -> None) rest in
      { gschema     = tok_text sch;
        gschema_pos = sch.start;
        gvalues     = assigns }
  | _ -> err "given_block shape"

let lower_expectation (n : node) : expectation =
  let kids = significant n.nchildren in
  let pos = fst n.nspan in
  let starts_not = match kids with GTok t :: _ -> t.kind = Cst.KW "not" | _ -> false in
  let expr_node = List.find_map (function
    | GNode e when e.nkind = NExpr || e.nkind = NAtom || e.nkind = NLiteral ->
        Some e
    | _ -> None) kids in
  let e = match expr_node with
    | Some n -> lower_expr n
    | None -> err "expectation has no expr" in
  if starts_not then MustNot (pos, e) else Must (pos, e)

let lower_expect_block (n : node) : expectation list =
  List.filter_map (function
    | GNode e when e.nkind = NExpectation -> Some (lower_expectation e)
    | _ -> None) (significant n.nchildren)

let lower_test (n : node) : test_def =
  let kids = significant n.nchildren in
  let tname_tok = List.find_map (function
    | GTok t when (match t.kind with Cst.Str _ -> true | _ -> false) -> Some t
    | _ -> None) kids in
  let g_block = List.find_map (function
    | GNode m when m.nkind = NGivenBlock -> Some (lower_given_block m)
    | _ -> None) kids in
  let e_block = List.find_map (function
    | GNode m when m.nkind = NExpectBlock -> Some (lower_expect_block m)
    | _ -> None) kids in
  match tname_tok, g_block, e_block with
  | Some t, Some g, Some e ->
      { tname  = tok_string_payload t;
        tpos   = t.start;          (* anchor at the test's name string *)
        tgiven = g;
        texpect = e }
  | _ -> err "test shape"

(* ---------- top-level ---------- *)

let lower_program (root : node) : Ast.program =
  if root.nkind <> NProgram then err "program root has wrong kind";
  List.filter_map (function
    | GNode n ->
        (match n.nkind with
         | NMetadata -> Some (TMeta     (lower_metadata    n))
         | NAction   -> Some (TAction   (lower_action_sig  n))
         | NSchema   -> Some (TSchema   (lower_schema      n))
         | NRule     -> Some (TRule     (lower_rule        n))
         | NTest     -> Some (TTest     (lower_test        n))
         | NInstance -> Some (TInstance (lower_instance    n))
         | NInclude  -> Some (TInclude  (lower_include     n))
         | _ -> None)
    | GTok _ -> None) root.nchildren
