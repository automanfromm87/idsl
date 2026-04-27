(* Typed (elaborated) AST.

   Differences from Ast:
   - Every expression carries its inferred type.
   - `EVar id` is resolved into one of three roles:
       VarLocal  — iteration-bound (e.g. `clause` in `any clause in Clauses:`)
       VarField  — a field of the current schema object
       VarTag    — a free or enum tag (yellow, NDA, ...)
   - Rules know which schema they apply to.
   - Action / expectation calls are pre-split into (name, args). *)

type ident = string

type var =
  | VarLocal    of ident
  | VarField    of ident
  | VarTag      of string
  | VarInstance of ident       (* references a top-level `instance Foo Bar:` *)

type texpr = { node : tnode; ty : Types.ty; pos : Ast.pos }
and tnode =
  | TLit       of Ast.literal
  | TVar       of var
  | TPath      of texpr * Ast.pos * ident   (* pos = the field name token *)
  | TList      of texpr list
  | TObject    of (ident * texpr) list
  | TWildcard
  | TMissing
  | TUnary     of Ast.unop  * texpr
  | TBin       of Ast.binop * texpr * texpr
  | TIf        of texpr * texpr * texpr
  | TAny       of ident * ident * texpr
  | TEvery     of ident * ident * texpr
  | TCount     of ident * ident * texpr
  | TSum       of texpr * ident * ident * texpr
  | TIsMissing of texpr
  | TIsPresent of texpr
  | TCall      of ident * texpr list

type tfield =
  | TFRaw     of ident * Types.ty
  | TFDerived of ident * texpr

type tschema = {
  ts_name   : ident;
  ts_fields : tfield list;
  ts_types  : (ident * Types.ty) list;
}

(* Position is the call name token; lets the index point goto/refs/rename
   at the function/action identifier rather than the whole call expr. *)
type tcall = Ast.pos * ident * texpr list

type trule = {
  tr_path     : ident list;
  tr_desc     : string option;
  tr_schema   : ident;
  tr_priority : int;
  tr_when     : texpr list;
  tr_then     : tcall list;
}

type tgiven = {
  tg_schema : ident;
  tg_values : (ident * texpr) list;
}

type texpectation =
  | TMust    of tcall
  | TMustNot of tcall

type ttest = {
  tt_name   : string;
  tt_given  : tgiven;
  tt_expect : texpectation list;
}

type tinstance = {
  ti_name   : ident;
  ti_schema : ident;
  ti_values : (ident * texpr) list;
}

type taction = {
  ta_name   : ident;
  ta_params : (ident * Types.ty) list;
  ta_pos    : Ast.pos;
}

type tprogram = {
  schemas   : tschema list;
  rules     : trule list;
  tests     : ttest list;
  instances : tinstance list;
  actions   : taction list;
  metas     : Ast.metadata list;
}

(* ---------- helpers ---------- *)

let raw_fields s =
  List.filter_map (function
    | TFRaw (n, t) -> Some (n, t)
    | TFDerived _  -> None) s.ts_fields

let derived_fields s =
  List.filter_map (function
    | TFDerived (n, te) -> Some (n, te)
    | TFRaw _           -> None) s.ts_fields

let schemas_table tp =
  let t = Hashtbl.create 16 in
  List.iter (fun s -> Hashtbl.replace t s.ts_name s) tp.schemas;
  t

let rec iter_expr f e =
  f e;
  match e.node with
  | TList tes              -> List.iter (iter_expr f) tes
  | TObject kvs            -> List.iter (fun (_, v) -> iter_expr f v) kvs
  | TPath (e, _, _)
  | TUnary (_, e)
  | TIsMissing e
  | TIsPresent e           -> iter_expr f e
  | TBin (_, a, b)         -> iter_expr f a; iter_expr f b
  | TIf  (a, b, c)         -> iter_expr f a; iter_expr f b; iter_expr f c
  | TAny   (_, _, p)
  | TEvery (_, _, p)
  | TCount (_, _, p)       -> iter_expr f p
  | TSum (g, _, _, p)      -> iter_expr f g; iter_expr f p
  | TCall (_, args)        -> List.iter (iter_expr f) args
  | TLit _ | TVar _
  | TWildcard | TMissing   -> ()

(* ---------- pretty-print ---------- *)

let pp_var = function
  | VarLocal id    -> id
  | VarField id    -> id
  | VarTag s       -> "`" ^ s
  | VarInstance id -> "@" ^ id

(* Drop the "`" / "@" markers that pp_var inserts for VarTag / VarInstance.
   Useful when rendering for end users (audit reports) instead of debug. *)
let strip_tags s =
  let b = Buffer.create (String.length s) in
  String.iter (fun c -> if c <> '`' && c <> '@' then Buffer.add_char b c) s;
  Buffer.contents b

let rec pp_expr (e : texpr) =
  match e.node with
  | TLit l       -> Printer.pp_lit l
  | TVar v       -> pp_var v
  | TPath (o, _, f) -> pp_expr o ^ "." ^ f
  | TList tes    -> "[" ^ String.concat ", " (List.map pp_expr tes) ^ "]"
  | TObject kvs  ->
      "{" ^ String.concat ", "
              (List.map (fun (k, v) -> k ^ ": " ^ pp_expr v) kvs) ^ "}"
  | TWildcard    -> "_"
  | TMissing     -> "missing"
  | TUnary (op, e) ->
      Printf.sprintf "(%s %s)" (Printer.pp_unop op) (pp_expr e)
  | TBin (op, a, b) ->
      Printf.sprintf "(%s %s %s)" (pp_expr a) (Printer.pp_binop op) (pp_expr b)
  | TIf (c, t, el) ->
      Printf.sprintf "(if %s then %s else %s)"
        (pp_expr c) (pp_expr t) (pp_expr el)
  | TAny   (x, y, p) -> Printf.sprintf "(any %s in %s: %s)"   x y (pp_expr p)
  | TEvery (x, y, p) -> Printf.sprintf "(every %s in %s: %s)" x y (pp_expr p)
  | TCount (x, y, p) -> Printf.sprintf "(count of %s in %s where %s)" x y (pp_expr p)
  | TSum (f, x, y, p) ->
      Printf.sprintf "(sum of %s for %s in %s where %s)"
        (pp_expr f) x y (pp_expr p)
  | TIsMissing e -> Printf.sprintf "(%s is missing)" (pp_expr e)
  | TIsPresent e -> Printf.sprintf "(%s is present)" (pp_expr e)
  | TCall (f, args) ->
      Printf.sprintf "%s(%s)" f (String.concat ", " (List.map pp_expr args))

let pp_call (_pos, n, args) =
  Printf.sprintf "%s(%s)" n (String.concat ", " (List.map pp_expr args))

let pp_field = function
  | TFRaw (n, t) ->
      Printf.sprintf "  - %s : %s" n (Types.pp_ty t)
  | TFDerived (n, te) ->
      Printf.sprintf "  - %s : %s = %s" n (Types.pp_ty te.ty) (pp_expr te)

let pp_schema s =
  Printf.sprintf "schema %s:\n%s"
    s.ts_name (String.concat "\n" (List.map pp_field s.ts_fields))

let indent_lines prefix xs =
  String.concat "\n" (List.map (fun s -> prefix ^ s) xs)

let pp_rule r =
  let name = String.concat "." r.tr_path in
  let preds = indent_lines "    " (List.map pp_expr r.tr_when) in
  let acts  = indent_lines "    " (List.map pp_call r.tr_then) in
  let desc  = match r.tr_desc with
    | None   -> ""
    | Some s -> Printf.sprintf "  \"\"\"%s\"\"\"\n" s in
  Printf.sprintf "rule %s on %s:\n%s  when:\n%s\n  then:\n%s"
    name r.tr_schema desc preds acts

let pp_test t =
  let givens = indent_lines "    "
    (List.map (fun (k, v) ->
       Printf.sprintf "%s = %s   :: %s" k (pp_expr v) (Types.pp_ty v.ty))
       t.tt_given.tg_values) in
  let expects = indent_lines "    "
    (List.map (function
       | TMust c    -> pp_call c
       | TMustNot c -> "not " ^ pp_call c) t.tt_expect) in
  Printf.sprintf "test %S on %s:\n  given:\n%s\n  expect:\n%s"
    t.tt_name t.tt_given.tg_schema givens expects

let pp_meta { Ast.mkey; mvalue } = Printf.sprintf "@%s(%S)" mkey mvalue

let pp_instance i =
  let body = String.concat "\n"
    (List.map (fun (k, v) ->
       Printf.sprintf "  %s = %s" k (pp_expr v)) i.ti_values) in
  Printf.sprintf "instance %s %s:\n%s" i.ti_schema i.ti_name body

let pp_program tp =
  let parts =
    List.map pp_meta tp.metas
    @ List.map pp_schema tp.schemas
    @ List.map pp_instance tp.instances
    @ List.map pp_rule tp.rules
    @ List.map pp_test tp.tests
  in
  String.concat "\n\n" parts
