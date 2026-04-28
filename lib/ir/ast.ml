(* iDSL AST — design.md v6 (e.g./i.e. + rule + test) *)

type ident = string

type pos = Lexing.position
let dummy_pos = Lexing.dummy_pos
let pp_pos (p : pos) =
  Printf.sprintf "line %d, col %d"
    p.pos_lnum (p.pos_cnum - p.pos_bol + 1)

type literal =
  | LInt    of int
  | LFloat  of float
  | LString of string
  | LBool   of bool
  | LMoney  of string  (* keep raw form, e.g. "$5,000,000" *)
  | LDate   of string  (* "YYYY-MM-DD" *)

type ty =
  | TName of ident
  | TList of ty

type binop =
  | And | Or
  | Eq  | Neq | Lt | Gt | Leq | Geq
  | Add | Sub | Mul | Div

type unop =
  | Not | Neg

type expr = { e_node : expr_node; e_pos : pos; e_endpos : pos }
and expr_node =
  | EVar       of ident
  | EField     of expr * pos * ident      (* pos = the field name token's pos *)
  | ELit       of literal
  | EList      of expr list
  | EObject    of (ident * expr) list
  | EWildcard
  | EMissing
  | EUnary     of unop  * expr
  | EBin       of binop * expr * expr
  | EIf        of expr  * expr * expr
  | EAny       of ident * ident * expr
  | EEvery     of ident * ident * expr
  | ECount     of ident * ident * expr
  | ESum       of expr  * ident * ident * expr
  | EIsMissing of expr
  | EIsPresent of expr
  | ECall      of ident * expr list        (* call name's pos = e.e_pos *)
  | ESelf                                  (* `self` keyword: the
                                              current schema's row;
                                              valid only inside a
                                              schema context *)

let mke pos endpos node = { e_node = node; e_pos = pos; e_endpos = endpos }

(* Standard initial size for the program-scoped Hashtbls scattered through
   the codebase. The exact value barely matters (Hashtbl auto-grows) — this
   is here so we stop sprinkling 8 / 16 / 0 magic numbers around. *)
let new_table () : ('a, 'b) Hashtbl.t = Hashtbl.create 16

(* A raw field declaration. At least one of `fd_ty` / `fd_sample` must
   be Some; the parser never emits both None. When `fd_ty` is missing
   the type is inferred from the sample; when `fd_sample` is missing
   the field is type-only with no displayed example. *)
type field_decl = {
  fd_ty     : ty_annot option;
  fd_sample : expr option;
}

and field =
  | FRaw     of pos * ident * field_decl
  | FDerived of pos * ident * expr

and ty_annot =
  | AnnScalar of string             (* Int / Money / Bool / String / Date / Float *)
  | AnnEnum   of string list        (* {NDA, MSA, DPA} *)
  | AnnList   of ty_annot           (* [T] *)
  | AnnSchema of string             (* user-defined schema name *)

(* `domain : ident option` on every decl: None = top-level (global),
   Some d = declared inside a `domain d:` block. The pipeline uses this
   to scope name lookups — same-domain references resolve first, then
   global. *)

type schema_def = {
  sname   : ident;
  spos    : pos;
  sfields : field list;
  sdomain : ident option;
}

type rule_def = {
  rpath        : ident list;
  rpath_locs   : pos list;            (* one per segment of rpath *)
  rpos         : pos;
  rdesc        : string option;
  rschema      : ident option;        (* explicit `on Schema:`; None → infer *)
  rschema_pos  : pos option;          (* set iff rschema is Some *)
  rpriority    : int;                 (* default 0; higher fires first *)
  rwhen        : (pos * expr) list;
  rthen        : (pos * expr) list;
  rdomain      : ident option;
}

type metadata = { mkey : string; mvalue : string }

type field_assign = {
  aname     : ident;
  aname_pos : pos;                    (* position of the LHS identifier *)
  avalue    : expr;
  apos      : pos;
}

type given_block = {
  gschema     : ident;
  gschema_pos : pos;
  gvalues     : field_assign list;
}

type expectation =
  | Must    of pos * expr
  | MustNot of pos * expr

type test_def = {
  tname    : string;
  tpos     : pos;
  tgiven   : given_block;
  texpect  : expectation list;
  tdomain  : ident option;
}

type action_param = { pname : ident; ptype : ty_annot; ppos : pos }

(* `predicate name on { F: T, ... }: body`. Pure-Bool named expression.
   The signature is structural: any object whose fields cover the
   declared (name, type) pairs satisfies the predicate. *)
type predicate_def = {
  pname     : ident;
  pname_pos : pos;
  ppos      : pos;
  pparams   : (ident * ty_annot * pos) list;
  pbody     : expr;
  pdomain   : ident option;
}

type action_sig = {
  asname    : ident;
  asparams  : action_param list;
  aspos     : pos;
  asdomain  : ident option;
}

type instance_def = {
  iname        : ident;
  iname_pos    : pos;
  ischema      : ident;
  ischema_pos  : pos;
  ipos         : pos;
  ivalues      : field_assign list;
  idomain      : ident option;
}

type include_decl = { inc_path : string; inc_pos : pos }

type top =
  | TSchema    of schema_def
  | TRule      of rule_def
  | TMeta      of metadata
  | TTest      of test_def
  | TAction    of action_sig
  | TInstance  of instance_def
  | TInclude   of include_decl
  | TPredicate of predicate_def

type program = top list

(* ---------- helpers ---------- *)

let field_name = function FRaw (_, n, _) | FDerived (_, n, _) -> n
let field_pos  = function FRaw (p, _, _) | FDerived (p, _, _) -> p
let field_names fs = List.map field_name fs

let schemas p    = List.filter_map (function TSchema s -> Some s | _ -> None) p
let rules   p    = List.filter_map (function TRule r   -> Some r | _ -> None) p
let tests   p    = List.filter_map (function TTest t   -> Some t | _ -> None) p
let actions   p  = List.filter_map (function TAction a   -> Some a | _ -> None) p
let instances p  = List.filter_map (function TInstance i -> Some i | _ -> None) p
let predicates p = List.filter_map (function TPredicate p' -> Some p' | _ -> None) p

(* Visit every sub-expression node, including the input. *)
let rec iter_expr f e =
  f e.e_node;
  match e.e_node with
  | EList es              -> List.iter (iter_expr f) es
  | EObject kvs           -> List.iter (fun (_, v) -> iter_expr f v) kvs
  | EField (e, _, _)
  | EUnary (_, e)
  | EIsMissing e
  | EIsPresent e          -> iter_expr f e
  | EBin (_, a, b)        -> iter_expr f a; iter_expr f b
  | EIf  (a, b, c)        -> iter_expr f a; iter_expr f b; iter_expr f c
  | EAny   (_, _, p)
  | EEvery (_, _, p)
  | ECount (_, _, p)      -> iter_expr f p
  | ESum (g, _, _, p)     -> iter_expr f g; iter_expr f p
  | ECall (_, args)       -> List.iter (iter_expr f) args
  | EVar _ | ELit _
  | ESelf
  | EWildcard | EMissing  -> ()

exception Cycle of ident

(* Field names referenced by this expr that belong to the same schema
   (i.e. dependencies in the derived-field DAG). *)
let derived_deps sch fname expr =
  let names = field_names sch.sfields in
  let in_schema id = List.mem id names in
  let out = ref [] in
  iter_expr (function
    | EVar id when in_schema id && id <> fname -> out := id :: !out
    | _ -> ()) expr;
  !out

(* Topologically order derived fields by their intra-schema dependencies. *)
let topo_derived sch =
  let derived = List.filter_map
    (function FDerived (_, n, e) -> Some (n, e) | FRaw _ -> None) sch.sfields in
  let visited = Hashtbl.create 16 in
  let temp    = Hashtbl.create 16 in
  let result  = ref [] in
  let rec visit (n, e) =
    if Hashtbl.mem visited n then ()
    else if Hashtbl.mem temp n then raise (Cycle n)
    else begin
      Hashtbl.add temp n ();
      List.iter (fun dep ->
        match List.assoc_opt dep derived with
        | Some de -> visit (dep, de)
        | None -> ())
        (derived_deps sch n e);
      Hashtbl.remove temp n;
      Hashtbl.add visited n ();
      result := (n, e) :: !result
    end
  in
  List.iter visit derived;
  List.rev !result
