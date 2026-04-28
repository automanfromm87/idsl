(* Bidirectional type inference + elaboration.
   Walks the surface AST and produces a Typed.tprogram in which every node
   carries its inferred type and every bare ident is resolved as
   VarLocal | VarField | VarTag. *)

open Ast
open Types
open Typed

type action_param_ty = { pty_name : ident; pty : ty }
type predicate_sig = { ps_params : (ident * ty) list }

type env = {
  schemas           : (ident, tschema) Hashtbl.t;
  actions           : (ident, action_param_ty list) Hashtbl.t;
  predicates        : (ident, predicate_sig) Hashtbl.t;
  instances         : (ident, ident) Hashtbl.t;
  domains           : (ident, unit) Hashtbl.t;
                      (* set of declared domain names; lets the
                         typechecker recognize `core.Money` etc. as a
                         qualified ref rather than a field access *)
  fields            : (ident * ty) list;
  vars              : (ident * ty) list;
  strict_calls      : bool;
  current_domain    : ident option;
  current_schema    : ident option;
  in_predicate_body : bool;
}

let make_env ?(strict_calls = false) ?(predicates = Hashtbl.create 0)
    ?(domains = Hashtbl.create 0)
    schemas actions instances =
  { schemas; actions; predicates; instances; domains;
    fields = []; vars = [];
    strict_calls; current_domain = None; current_schema = None;
    in_predicate_body = false }

let is_domain env name = Hashtbl.mem env.domains name

(* Domain-aware key derivation.  All decl tables (schemas / instances /
   actions) are keyed on the *qualified* name "domain.bare", with no
   prefix when the decl is global.  Scoped lookups try the current
   domain's qualified key first and fall back to the global one. *)
let qualify (dom : ident option) (name : ident) : ident =
  match dom with Some d -> d ^ "." ^ name | None -> name

(* `scoped_find_canon` returns both the canonical key the table is
   using and the value, in one pass — call sites that need both
   (most of them) avoid a redundant second lookup. *)
let scoped_find_canon (tbl : (ident, 'a) Hashtbl.t) (env : env) (name : ident)
    : (ident * 'a) option =
  match env.current_domain with
  | None ->
      (match Hashtbl.find_opt tbl name with
       | Some v -> Some (name, v) | None -> None)
  | Some d ->
      let q = d ^ "." ^ name in
      (match Hashtbl.find_opt tbl q with
       | Some v -> Some (q, v)
       | None ->
           match Hashtbl.find_opt tbl name with
           | Some v -> Some (name, v)
           | None -> None)

let scoped_find tbl env name =
  Option.map snd (scoped_find_canon tbl env name)

let scoped_mem tbl env name = scoped_find_canon tbl env name <> None

(* Canonical key the table actually uses.  Tries qualified-by-domain
   first, falls back to bare; on miss returns the qualified form so
   downstream lookups raise a clean "unknown" rather than aliasing
   into a foreign domain. *)
let resolve_key tbl ~domain name =
  let q = qualify domain name in
  if Hashtbl.mem tbl q then q
  else if Hashtbl.mem tbl name then name
  else q

let scoped_canon_key tbl env name =
  resolve_key tbl ~domain:env.current_domain name

let mkdiag ?related pos msg =
  Diagnostic.error ?related ~stage:Diagnostic.Typecheck ~pos msg

(* Carries a position with the failure message, for paths where the inner
   inferrer hits a known position deep inside. Catch sites convert these
   to Diagnostic.t. *)
exception Located of Lexing.position * string
let err_at pos fmt = Printf.ksprintf (fun s -> raise (Located (pos, s))) fmt

let rec resolve_ty_annot ?domain schemas = function
  | AnnScalar "Int"    -> TInt
  | AnnScalar "Float"  -> TFloat
  | AnnScalar "Bool"   -> TBool
  | AnnScalar "String" -> TString
  | AnnScalar "Money"  -> TMoney
  | AnnScalar "Date"   -> TDate
  | AnnScalar "Duration" -> TDuration
  | AnnScalar s ->
      let q = qualify domain s in
      if Hashtbl.mem schemas q then TSchema q
      else if Hashtbl.mem schemas s then TSchema s
      else err "unknown type %s" s
  | AnnEnum xs   -> TEnum xs
  | AnnList t    -> TList (resolve_ty_annot ?domain schemas t)
  | AnnSchema s  ->
      let q = qualify domain s in
      if Hashtbl.mem schemas q then TSchema q
      else TSchema s

let mk pos node ty = { node; ty; pos }

let infer_lit = function
  | LInt _    -> TInt
  | LFloat _  -> TFloat
  | LString _ -> TString
  | LBool _   -> TBool
  | LMoney _  -> TMoney
  | LDate _   -> TDate

let resolve_var env id =
  match List.assoc_opt id env.vars with
  | Some t -> Some (VarLocal id, t)
  | None ->
    match List.assoc_opt id env.fields with
    | Some t -> Some (VarField id, t)
    | None ->
      match scoped_find_canon env.instances env id with
      | Some (canon, sname) -> Some (VarInstance canon, TSchema sname)
      | None -> None

let rec infer env e : texpr =
  let mk = mk e.e_pos in
  match e.e_node with
  | ELit l    -> mk (TLit l) (infer_lit l)
  | EWildcard -> mk TWildcard TAny
  | EMissing  -> mk TMissing TMissing
  | ESelf ->
      (match env.current_schema with
       | None -> err "`self` used outside any schema context"
       | Some _ ->
           (* `self` is structural: any predicate that accepts a record
              type matching the current schema's fields can accept it.
              The TSelf node carries the field snapshot so eval can
              build a VObject without consulting the schemas table. *)
           mk (TSelf env.fields) (TObject env.fields))
  | EVar id ->
      (match resolve_var env id with
       | Some (v, t) -> mk (TVar v) t
       | None ->
         (* Bare predicate reference — `is_high_risk` with no
            explicit `(self)`.  Allowed only inside a schema context;
            implicitly applies the predicate to `self`. *)
         (match scoped_find_canon env.predicates env id with
          | Some (canon, ps) when env.current_schema <> None ->
              check_predicate_args ~env ~name:id ~canon ~ps
                ~self_fields:env.fields ~explicit_arg:None ~mk
          | _ ->
              let ty = match scoped_find_canon env.schemas env id with
                | Some (canon, _) -> TSchema canon
                | None            -> TTag id
              in
              mk (TVar (VarTag id)) ty))
  | EField ({ e_node = EVar dom_name; _ }, _, f)
    when is_domain env dom_name ->
      let qkey = dom_name ^ "." ^ f in
      (match Hashtbl.find_opt env.instances qkey with
       | Some sname -> mk (TVar (VarInstance qkey)) (TSchema sname)
       | None when Hashtbl.mem env.schemas qkey ->
           mk (TVar (VarTag qkey)) (TSchema qkey)
       | None when Hashtbl.mem env.predicates qkey
                && env.current_schema <> None ->
           (* `legal.is_high_risk` — qualified predicate ref with no
              parens.  Implicit-self call. *)
           let ps = Hashtbl.find env.predicates qkey in
           check_predicate_args ~env ~name:f ~canon:qkey ~ps
             ~self_fields:env.fields ~explicit_arg:None ~mk
       | _ ->
           err "%sunknown qualified reference `%s.%s`"
             (Printf.sprintf "%s: " (pp_pos e.e_pos)) dom_name f)
  | EField (obj, fpos, f) ->
      let to_ = infer env obj in
      let fty = field_type ~pos:e.e_pos env to_.ty f in
      mk (TPath (to_, fpos, f)) fty
  | EList es ->
      let tes = List.map (infer env) es in
      let elem = List.fold_left
        (fun acc te -> unify acc te.ty) TAny tes in
      mk (TList tes) (TList elem)
  | EObject kvs ->
      let tkvs = List.map (fun (k, v) -> (k, infer env v)) kvs in
      mk (TObject tkvs)
        (TObject (List.map (fun (k, te) -> (k, te.ty)) tkvs))
  | EUnary (Not, e) ->
      let te = check env e TBool in
      mk (TUnary (Not, te)) TBool
  | EUnary (Neg, e) ->
      let te = infer env e in
      if is_numeric te.ty || te.ty = TMissing then
        mk (TUnary (Neg, te)) te.ty
      else err "negation requires numeric, got %s" (pp_ty te.ty)
  | EBin (op, a, b) -> infer_bin env e.e_pos op a b
  | EIf (c, t, el) ->
      let tc = check env c TBool in
      let tt = infer env t and tel = infer env el in
      mk (TIf (tc, tt, tel)) (unify tt.ty tel.ty)
  | EAny (x, y, p) ->
      let elem = list_elem env y in
      let env' = { env with vars = (x, elem) :: env.vars } in
      let tp = check env' p TBool in
      mk (TAny (x, y, tp)) TBool
  | EEvery (x, y, p) ->
      let elem = list_elem env y in
      let env' = { env with vars = (x, elem) :: env.vars } in
      let tp = check env' p TBool in
      mk (TEvery (x, y, tp)) TBool
  | ECount (x, y, p) ->
      let elem = list_elem env y in
      let env' = { env with vars = (x, elem) :: env.vars } in
      let tp = check env' p TBool in
      mk (TCount (x, y, tp)) TInt
  | ESum (f, x, y, p) ->
      let elem = list_elem env y in
      let env' = { env with vars = (x, elem) :: env.vars } in
      let tp = check env' p TBool in
      let tf = infer env' f in
      if is_numeric tf.ty || tf.ty = TMissing then
        mk (TSum (tf, x, y, tp)) tf.ty
      else err "sum body must be numeric, got %s" (pp_ty tf.ty)
  | EIsMissing e -> mk (TIsMissing (infer env e)) TBool
  | EIsPresent e -> mk (TIsPresent (infer env e)) TBool
  | ECall (("min" | "max") as name, [a; b]) ->
      let ta = infer env a and tb = infer env b in
      if (is_numeric ta.ty || ta.ty = TMissing)
         && (is_numeric tb.ty || tb.ty = TMissing)
      then mk (TCall (name, [ta; tb])) (arith_result ta.ty tb.ty)
      else err "%s requires numeric operands" name
  | ECall (name, args) ->
      if env.in_predicate_body
         && (Hashtbl.mem env.predicates name
             || (match env.current_domain with
                 | Some d -> Hashtbl.mem env.predicates (d ^ "." ^ name)
                 | None   -> false))
      then err "predicate body cannot call other predicates";
      if env.in_predicate_body
         && (Hashtbl.mem env.actions name
             || (match env.current_domain with
                 | Some d -> Hashtbl.mem env.actions (d ^ "." ^ name)
                 | None   -> false))
      then err "predicate body cannot call actions (predicates are pure)";
      (match scoped_find_canon env.predicates env name with
       | None ->
           err "function `%s` not allowed in expression context" name
       | Some (canon, ps) ->
           let explicit_arg = match args with
             | [a]  -> Some a
             | []   -> None
             | _    -> err "predicate %s expects at most 1 argument, got %d"
                         name (List.length args)
           in
           check_predicate_args ~env ~name ~canon ~ps
             ~self_fields:env.fields ~explicit_arg ~mk)

(* Shared core for predicate-call typing.  Two entry points:
     - explicit:  `is_high_risk(self)` (or any other expr argument)
     - implicit:  `is_high_risk` (no parens) inside a schema context;
                  the predicate auto-applies to `self`.
   Both paths verify the argument structurally satisfies the
   predicate's signature, then emit `TCall(canon, [arg])` typed
   `Bool`. *)
and check_predicate_args ~env ~name ~canon ~ps ~self_fields
    ~explicit_arg ~mk =
  let arg_te = match explicit_arg with
    | Some arg -> infer env arg
    | None ->
        if self_fields = [] || env.current_schema = None then
          err "implicit predicate call `%s` requires a schema context" name;
        { node = TSelf self_fields;
          ty   = TObject self_fields;
          pos  = Lexing.dummy_pos }
  in
  let arg_fields = match arg_te.ty with
    | TObject kvs -> kvs
    | TSchema s ->
        (match scoped_find env.schemas env s with
         | Some ts -> ts.ts_types
         | None    -> err "predicate %s: unknown schema %s for argument" name s)
    | TAny -> []
    | _ -> err "predicate %s expects an object/schema argument, got %s"
             name (pp_ty arg_te.ty)
  in
  List.iter (fun (k, expected) ->
    match List.assoc_opt k arg_fields with
    | None ->
        err "predicate %s: argument missing field `%s : %s`"
          name k (pp_ty expected)
    | Some actual ->
        (try ignore (unify expected actual)
         with Type_error m ->
           err "predicate %s field `%s`: %s" name k m))
    ps.ps_params;
  mk (TCall (canon, [arg_te])) TBool

and field_type ?pos env ot f =
  let prefix = match pos with
    | Some p -> Printf.sprintf "%s: " (pp_pos p)
    | None   -> "" in
  let look_in fields =
    match List.assoc_opt f fields with
    | Some t -> t
    | None ->
      err "%sno field `%s` in %s (have: %s)" prefix f (pp_ty ot)
        (String.concat ", " (List.map fst fields))
  in
  match ot with
  | TSchema s ->
      (match scoped_find env.schemas env s with
       | Some ts -> look_in ts.ts_types
       | None    -> err "%sunknown schema %s" prefix s)
  | TObject kvs     -> look_in kvs
  | TDuration ->
      (match f with
       | "days"   -> TInt
       | "years"  -> TFloat
       | _ -> err "%sDuration has fields `days` and `years`, not `%s`" prefix f)
  | TMissing | TAny -> TAny
  | _ -> err "%sfield access on non-object: %s.%s" prefix (pp_ty ot) f

and infer_bin env pos op a b =
  let mk = mk pos in
  match op with
  | And | Or ->
      let ta = check env a TBool and tb = check env b TBool in
      mk (TBin (op, ta, tb)) TBool
  | Eq | Neq ->
      let ta = infer env a in
      let tb = check env b ta.ty in
      mk (TBin (op, ta, tb)) TBool
  | Lt | Gt | Leq | Geq ->
      let ta = infer env a and tb = infer env b in
      let _ = unify ta.ty tb.ty in
      if is_ordered ta.ty || ta.ty = TMissing then mk (TBin (op, ta, tb)) TBool
      else err "comparison on un-ordered type %s" (pp_ty ta.ty)
  | Add ->
      let ta = infer env a and tb = infer env b in
      let rty = match ta.ty, tb.ty with
        | TString, _ | _, TString -> TString
        | TDate, TDuration | TDuration, TDate -> TDate
        | TDuration, TDuration -> TDuration
        | x, y when (is_numeric x || x = TMissing)
                 && (is_numeric y || y = TMissing) -> arith_result x y
        | _ -> err "+ requires numeric or string operands, got %s and %s"
                 (pp_ty ta.ty) (pp_ty tb.ty)
      in
      mk (TBin (op, ta, tb)) rty
  | Sub ->
      let ta = infer env a and tb = infer env b in
      (match ta.ty, tb.ty with
       | TDate, TDate           -> mk (TBin (op, ta, tb)) TDuration
       | TDate, TDuration       -> mk (TBin (op, ta, tb)) TDate
       | TDuration, TDuration   -> mk (TBin (op, ta, tb)) TDuration
       | x, y when (is_numeric x || x = TMissing)
                && (is_numeric y || y = TMissing) ->
           mk (TBin (op, ta, tb)) (arith_result x y)
       | _ -> err "- requires numeric or Date operands, got %s and %s"
                (pp_ty ta.ty) (pp_ty tb.ty))
  | Mul ->
      let ta = infer env a and tb = infer env b in
      (match ta.ty, tb.ty with
       | TDuration, TInt | TInt, TDuration -> mk (TBin (op, ta, tb)) TDuration
       | x, y when (is_numeric x || x = TMissing)
                && (is_numeric y || y = TMissing) ->
           mk (TBin (op, ta, tb)) (arith_result x y)
       | _ -> err "* requires numeric operands, got %s and %s"
                (pp_ty ta.ty) (pp_ty tb.ty))
  | Div ->
      let ta = infer env a and tb = infer env b in
      if (is_numeric ta.ty || ta.ty = TMissing)
         && (is_numeric tb.ty || tb.ty = TMissing)
      then mk (TBin (op, ta, tb)) (arith_result ta.ty tb.ty)
      else err "/ requires numeric operands, got %s and %s"
             (pp_ty ta.ty) (pp_ty tb.ty)

and list_elem env y =
  match List.assoc_opt y env.vars with
  | Some (TList t) -> t
  | _ ->
    (match List.assoc_opt y env.fields with
     | Some (TList t)            -> t
     | Some TMissing | Some TAny -> TAny
     | Some t -> err "%s is not a list (got %s)" y (pp_ty t)
     | None   -> err "unknown name `%s`" y)

(* check: form-first specialization, then fall back to infer + unify. *)
and check env e expected : texpr =
  let mk = mk e.e_pos in
  match e.e_node, expected with
  | EList es, TList ea ->
      let tes = List.map (fun el -> check env el ea) es in
      mk (TList tes) (TList ea)
  | EObject kvs, TSchema s ->
      let tkvs = check_object_fits env s kvs in
      mk (TObject tkvs) (TSchema s)
  | EWildcard, _ ->
      mk TWildcard expected
  | _ ->
      let te = infer env e in
      let _ = unify expected te.ty in
      te

and check_object_fits env s kvs =
  match scoped_find env.schemas env s with
  | None -> err "unknown schema %s" s
  | Some ts ->
      List.map (fun (k, v) ->
        match List.assoc_opt k ts.ts_types with
        | None -> err "no field `%s` in schema %s" k s
        | Some expected -> (k, check env v expected)) kvs

(* ---------- schemas ---------- *)

(* Resolve a raw field's type from its declaration: explicit annotation
   wins; otherwise infer from the sample expression (which the parser
   guarantees is present whenever no annotation was supplied).  The
   sample may reference cross-domain instances or schemas, so the env
   it sees needs the workspace-wide domains / instances tables. *)
let infer_field_type ?domain ~instances ~domains
    schemas (decl : field_decl) : Types.ty =
  let env =
    let base = make_env ~domains schemas (Hashtbl.create 0) instances in
    { base with current_domain = domain }
  in
  match decl.fd_ty, decl.fd_sample with
  | None, None        -> err "field has neither type nor sample"
  | None, Some e      -> (infer env e).ty
  | Some ty, None     -> resolve_ty_annot ?domain schemas ty
  | Some ty, Some e   ->
      let resolved = resolve_ty_annot ?domain schemas ty in
      let _ = check env e resolved in
      resolved

let typecheck_schema schemas actions predicates instances domains sch =
  let errors = ref [] in
  let push d = errors := d :: !errors in
  let raw_pairs = List.filter_map (function
    | FRaw (pos, n, decl) ->
        (try Some (n,
          infer_field_type ?domain:sch.sdomain
            ~instances ~domains schemas decl)
         with Type_error m ->
           push (mkdiag pos
             (Printf.sprintf "schema %s.%s: %s" sch.sname n m));
           Some (n, TAny))
    | FDerived _ -> None) sch.sfields in
  let topo =
    try Ast.topo_derived sch
    with Ast.Cycle n ->
      push (mkdiag sch.spos
        (Printf.sprintf "schema %s: derived cycle through `%s`" sch.sname n));
      [] in
  let derived_pos = List.map (function
    | FDerived (p, n, _) -> (n, p) | FRaw (p, n, _) -> (n, p)) sch.sfields in
  let derived_typed_acc, all_types =
    List.fold_left (fun (dacc, tyacc) (n, e) ->
      let env =
        { schemas; actions; predicates; instances; domains;
          fields = tyacc; vars = []; strict_calls = false;
          current_domain = sch.sdomain;
          current_schema = Some (qualify sch.sdomain sch.sname);
          in_predicate_body = false } in
      match (try `Ok (infer env e) with Type_error m -> `Err m) with
      | `Ok te -> ((n, te) :: dacc, tyacc @ [(n, te.ty)])
      | `Err m ->
          let p = try List.assoc n derived_pos with Not_found -> sch.spos in
          push (mkdiag p (Printf.sprintf "schema %s.%s: %s" sch.sname n m));
          (dacc, tyacc @ [(n, TAny)]))
      ([], raw_pairs) topo in
  let derived_typed = List.rev derived_typed_acc in
  let tfields =
    List.map (function
      | FRaw (_, n, _) ->
          let t = List.assoc n raw_pairs in
          TFRaw (n, t)
      | FDerived (_, n, _) ->
          (match List.assoc_opt n derived_typed with
           | Some te -> TFDerived (n, te)
           | None    -> TFRaw (n, TAny))) sch.sfields
  in
  let tsch = {
    ts_name   = qualify sch.sdomain sch.sname;
    ts_bare   = sch.sname;
    ts_domain = sch.sdomain;
    ts_fields = tfields;
    ts_types  = all_types;
  } in
  (tsch, List.rev !errors)

(* ---------- rules ---------- *)

let pick_schema_for_rule env r =
  let referenced = ref [] in
  let collect (_, e) =
    Ast.iter_expr (function
      | EVar id when not (scoped_mem env.schemas env id) ->
          if not (List.mem id !referenced) then referenced := id :: !referenced
      | EVar _ | ELit _ | EList _ | EObject _ | EWildcard | EMissing
      | ESelf
      | EUnary _ | EBin _ | EIf _ | EAny _ | EEvery _ | ECount _ | ESum _
      | EIsMissing _ | EIsPresent _ | ECall _ | EField _ -> ()) e in
  List.iter collect r.rwhen;
  List.iter collect r.rthen;
  (* Restrict candidates to the rule's domain (or top-level when the
     rule has no domain) so two same-bare-name schemas in different
     domains can't masquerade as each other's home schema. *)
  let in_scope (ts : tschema) =
    match env.current_domain with
    | None        -> ts.ts_domain = None
    | Some d      -> ts.ts_domain = Some d || ts.ts_domain = None
  in
  let scored = Hashtbl.fold (fun name ts acc ->
    if not (in_scope ts) then acc
    else
      let names = List.map fst ts.ts_types in
      let overlap = List.fold_left (fun n id ->
        if List.mem id names then n + 1 else n) 0 !referenced in
      (name, overlap) :: acc) env.schemas [] in
  match List.sort (fun (_, a) (_, b) -> compare b a) scored with
  | (s, n) :: _ when n > 0 -> s
  | _ -> err "rule %s: no schema overlaps any referenced name"
           (String.concat "." r.rpath)

(* When an action signature is registered, validate name + arity + arg
   types. Otherwise, just infer arg types loosely. *)
let has_wildcard e =
  let found = ref false in
  Ast.iter_expr (function
    | EWildcard -> found := true
    | _ -> ()) e;
  !found

let typecheck_call env (e : expr) : tcall =
  match e.e_node with
  | ECall (name, args) ->
      let targs = List.map (infer env) args in
      (match scoped_find_canon env.actions env name with
       | None ->
           if env.strict_calls then
             err "action `%s` has no @action declaration (strict mode)" name;
           (e.e_pos, name, targs)
       | Some (canon, sig_params) ->
           if List.length sig_params <> List.length targs then
             err "action %s expects %d argument(s), got %d"
               name (List.length sig_params) (List.length targs);
           List.iter2 (fun sp ta ->
             let _ =
               try unify sp.pty ta.ty
               with Type_error m ->
                 err "argument `%s`: %s" sp.pty_name m
             in ()) sig_params targs;
           (e.e_pos, canon, targs))
  | EVar _ | EField _ | ELit _ | EList _ | EObject _ | EWildcard | EMissing
  | ESelf
  | EUnary _ | EBin _ | EIf _ | EAny _ | EEvery _ | ECount _ | ESum _
  | EIsMissing _ | EIsPresent _ -> err "expected a call expression"

let typecheck_rule env r =
  let env = { env with current_domain = r.rdomain } in
  let where = String.concat "." r.rpath in
  let sname, ts = match r.rschema with
    | Some s ->
        (match scoped_find_canon env.schemas env s with
         | Some r -> r
         | None ->
             err_at r.rpos "rule %s on %s: unknown schema" where s)
    | None ->
        let canon = pick_schema_for_rule env r in
        (match Hashtbl.find_opt env.schemas canon with
         | Some t -> canon, t
         | None ->
             err_at r.rpos "rule %s: schema %s not found" where canon)
  in
  let env' = { env with fields = ts.ts_types; current_schema = Some sname } in
  let twhen = List.map (fun (pos, p) ->
    if has_wildcard p then
      err_at pos "rule %s when: `_` only allowed in test expect calls" where;
    try check env' p TBool
    with Type_error m -> err_at pos "rule %s when: %s" where m) r.rwhen in
  let tthen = List.map (fun (pos, a) ->
    try typecheck_call env' a
    with Type_error m -> err_at pos "rule %s then: %s" where m) r.rthen in
  { tr_path = r.rpath; tr_desc = r.rdesc; tr_schema = sname;
    tr_priority = r.rpriority;
    tr_when = twhen; tr_then = tthen }

(* ---------- tests ---------- *)

let typecheck_test env t =
  let env = { env with current_domain = t.tdomain } in
  let bare_sname = t.tgiven.gschema in
  let canon_sname, ts =
    match scoped_find_canon env.schemas env bare_sname with
    | Some r -> r
    | None ->
        err_at t.tpos "test %S: unknown schema %s" t.tname bare_sname
  in
  let env_g = { env with fields = ts.ts_types;
                         current_schema = Some canon_sname } in
  let givens = List.map (fun a ->
    match List.assoc_opt a.aname ts.ts_types with
    | None -> err_at a.apos "test %S: no field `%s` in schema %s"
                t.tname a.aname bare_sname
    | Some expected ->
        let te =
          try check env_g a.avalue expected
          with Type_error m ->
            err_at a.apos "test %S: %s = ...: %s" t.tname a.aname m
        in (a.aname, te)) t.tgiven.gvalues in
  let expects = List.map (fun ex ->
    let pos, e, ctor =
      match ex with
      | Must (p, e)    -> p, e, (fun c -> TMust c)
      | MustNot (p, e) -> p, e, (fun c -> TMustNot c) in
    let call =
      try typecheck_call env_g e
      with Type_error m -> err_at pos "test %S expect: %s" t.tname m
    in ctor call) t.texpect
  in
  { tt_name = qualify t.tdomain t.tname;
    tt_bare = t.tname;
    tt_given = { tg_schema = canon_sname; tg_values = givens };
    tt_expect = expects }

let typecheck_instance env i =
  let env = { env with current_domain = i.idomain } in
  let canon_schema, ts =
    match scoped_find_canon env.schemas env i.ischema with
    | Some r -> r
    | None   ->
        err_at i.ipos "instance %s: unknown schema %s" i.iname i.ischema
  in
  let env_g = { env with fields = ts.ts_types;
                         current_schema = Some canon_schema } in
  let values = List.map (fun a ->
    match List.assoc_opt a.aname ts.ts_types with
    | None -> err_at a.apos "instance %s: no field `%s` in schema %s"
                i.iname a.aname i.ischema
    | Some expected ->
        let te =
          try check env_g a.avalue expected
          with Type_error m ->
            err_at a.apos "instance %s: %s = ...: %s" i.iname a.aname m
        in (a.aname, te)) i.ivalues in
  { ti_name   = qualify i.idomain i.iname;
    ti_bare   = i.iname;
    ti_schema = canon_schema;
    ti_values = values }

let typecheck_action schemas a =
  let params = List.map (fun p ->
    let ty =
      try resolve_ty_annot ?domain:a.asdomain schemas p.ptype
      with Type_error m ->
        err_at p.ppos "@action %s param `%s`: %s" a.asname p.pname m
    in { pty_name = p.pname; pty = ty }) a.asparams in
  (a.asname, params)

(* ---------- driver ---------- *)

(* Enum tags must be unique *within the schema's domain* — same tag
   name in two different domains is fine.  Bare tag references are
   resolved through the enum's TEnum set at the comparison site, which
   is already domain-local; this check is a clarity guard against
   confusing duplicates inside one domain. *)
let check_unique_enum_tags errors schema_pos tschemas =
  let seen : (string * string, string) Hashtbl.t = Hashtbl.create 32 in
  let domain_of canon =
    match String.index_opt canon '.' with
    | Some i -> String.sub canon 0 i
    | None   -> ""
  in
  List.iter (fun s ->
    let pos = try Hashtbl.find schema_pos s.ts_name
              with Not_found -> Lexing.dummy_pos in
    let dom = domain_of s.ts_name in
    List.iter (fun (fname, ty) ->
      match ty with
      | TEnum tags ->
          let where = Printf.sprintf "%s.%s" s.ts_name fname in
          List.iter (fun t ->
            match Hashtbl.find_opt seen (dom, t) with
            | Some other when other <> where ->
                errors := mkdiag pos (Printf.sprintf
                  "enum tag `%s` declared in both %s and %s — tags must be unique within a domain"
                  t other where) :: !errors
            | _ -> Hashtbl.replace seen (dom, t) where) tags
      | _ -> ()) s.ts_types) tschemas

(* Versions of the DSL surface this build accepts.
   Bump when a syntax/semantics change is breaking; older `.idsl` files
   declaring an unsupported version will be rejected.

   0.0.1–0.0.3 used `e.g.` / `i.e.` keywords and pipe-separated enums.
   0.0.4 introduced `default` / `=` for fields, `predicate`, table
   tests, three-valued logic, and cross-domain qualified refs. The
   surfaces are syntactically incompatible, so old version strings are
   no longer accepted. *)
let supported_versions = ["0.0.4"]

let check_metadata errors program =
  List.iter (function
    | Ast.TMeta { mkey = "version"; mvalue = v } ->
        if not (List.mem v supported_versions) then
          errors := mkdiag Lexing.dummy_pos (Printf.sprintf
            "@version(%S) not supported by this build (accept: %s)"
            v (String.concat ", " supported_versions)) :: !errors
    | _ -> ()) program

(* Catch helper: convert Located (pos, m) and Type_error m at a known
   fallback position into a typecheck Diagnostic. *)
let with_diag fallback_pos thunk =
  try `Ok (thunk ())
  with
  | Located (p, m)  -> `Err (mkdiag p m)
  | Type_error m    -> `Err (mkdiag fallback_pos m)

let run program =
  let schemas   = Hashtbl.create 16 in
  let actions   = Hashtbl.create 8 in
  let action_decls = ref [] in
  let instances = Hashtbl.create 8 in
  let domains   = Hashtbl.create 4 in
  (* Collect every declared domain name so the typechecker can spot
     `core.Money` as a qualified ref instead of a field access. *)
  List.iter (function
    | Ast.TSchema { sdomain = Some d; _ }
    | Ast.TRule   { rdomain = Some d; _ }
    | Ast.TTest   { tdomain = Some d; _ }
    | Ast.TInstance { idomain = Some d; _ }
    | Ast.TAction { asdomain = Some d; _ }
    | Ast.TPredicate { pdomain = Some d; _ } ->
        Hashtbl.replace domains d ()
    | _ -> ()) program;
  let errors : Diagnostic.t list ref = ref [] in
  let push d = errors := d :: !errors in
  check_metadata errors program;
  List.iter (fun a ->
    match with_diag a.aspos (fun () -> typecheck_action schemas a) with
    | `Err d -> push d
    | `Ok (n, params) ->
        let key = qualify a.asdomain n in
        if Hashtbl.mem actions key then
          push (mkdiag a.aspos (Printf.sprintf "duplicate @action %s" key))
        else begin
          Hashtbl.add actions key params;
          action_decls := { ta_name = key;
                            ta_bare = n;
                            ta_params = List.map (fun p -> (p.pty_name, p.pty)) params;
                            ta_pos = a.aspos } :: !action_decls
        end) (Ast.actions program);
  (* Predicates: resolve param signatures up front (bodies typecheck
     after env is fully populated). Doing this *before* schemas means
     a derived field body can call a predicate. *)
  let predicates : (ident, predicate_sig) Hashtbl.t = Hashtbl.create 8 in
  let predicate_param_meta = Hashtbl.create 8 in
  List.iter (fun (p : Ast.predicate_def) ->
    let key = qualify p.pdomain p.pname in
    if Hashtbl.mem predicates key then
      push (mkdiag p.pname_pos
              (Printf.sprintf "duplicate predicate %s" key))
    else
      let resolved =
        try
          List.map (fun (n, ty, pos) ->
            (n, resolve_ty_annot ?domain:p.pdomain schemas ty, pos))
            p.pparams
        with Type_error m ->
          push (mkdiag p.ppos
            (Printf.sprintf "predicate %s sig: %s" p.pname m));
          []
      in
      Hashtbl.add predicates key
        { ps_params = List.map (fun (n, t, _) -> (n, t)) resolved };
      Hashtbl.add predicate_param_meta key (resolved, p)
    ) (Ast.predicates program);
  (* Pre-register instance (key → schema_key) mappings before schema
     bodies typecheck, so a derived field can resolve a sample like
     `core.Alpha` to its TSchema type. The instance's *value* is type-
     checked later, when the env is fully populated. *)
  let inst_schema_key idomain ischema =
    if String.contains ischema '.' then ischema
    else qualify idomain ischema
  in
  List.iter (fun i ->
    let key = qualify i.idomain i.iname in
    if Hashtbl.mem instances key then
      push (mkdiag i.ipos (Printf.sprintf "duplicate instance %s" key))
    else
      Hashtbl.add instances key (inst_schema_key i.idomain i.ischema))
    (Ast.instances program);
  let schema_pos : (ident, Lexing.position) Hashtbl.t = Hashtbl.create 16 in
  let tschemas =
    List.filter_map (fun s ->
      let key = qualify s.sdomain s.sname in
      Hashtbl.replace schema_pos key s.spos;
      let tsch, errs =
        typecheck_schema schemas actions predicates instances domains s in
      Hashtbl.replace schemas key tsch;
      List.iter push errs;
      Some tsch) (Ast.schemas program) in
  check_unique_enum_tags errors schema_pos tschemas;
  let strict_calls =
    List.exists (function
      | Ast.TMeta { mkey = "strict_actions"; _ } -> true
      | _ -> false) program in
  let env = make_env ~strict_calls ~predicates ~domains
                     schemas actions instances in
  let tinstances =
    List.filter_map (fun i ->
      match with_diag i.ipos (fun () -> typecheck_instance env i) with
      | `Ok ti -> Some ti
      | `Err d -> push d; None) (Ast.instances program) in
  let trules =
    List.filter_map (fun r ->
      match with_diag r.rpos (fun () -> typecheck_rule env r) with
      | `Ok tr -> Some tr
      | `Err d -> push d; None) (Ast.rules program) in
  let ttests =
    List.filter_map (fun t ->
      match with_diag t.tpos (fun () -> typecheck_test env t) with
      | `Ok tt -> Some tt
      | `Err d -> push d; None) (Ast.tests program) in
  (* Predicate bodies — env is fully populated now, so the body sees
     other predicates and actions defined later. *)
  let tpredicates =
    Hashtbl.fold (fun key (resolved, (p : Ast.predicate_def)) acc ->
      let body_env =
        { env with
          fields = List.map (fun (n, t, _) -> (n, t)) resolved;
          current_domain = p.pdomain;
          current_schema = None;
          in_predicate_body = true } in
      let result = with_diag p.ppos (fun () ->
        let tbody = check body_env p.pbody TBool in
        { tp_name   = key;
          tp_bare   = p.pname;
          tp_params = List.map (fun (n, t, _) -> (n, t)) resolved;
          tp_body   = tbody;
          tp_pos    = p.pname_pos }) in
      match result with
      | `Ok tp -> tp :: acc
      | `Err d -> push d; acc
    ) predicate_param_meta [] in
  let metas =
    List.filter_map (function
      | TMeta m -> Some m
      | TSchema _ | TRule _ | TTest _ | TAction _ | TInstance _
      | TInclude _ | TPredicate _ -> None)
      program in
  (* Any unresolved TInclude here means parse_string was used (browser path);
     surface a clear error instead of silently dropping. *)
  List.iter (function
    | TInclude { inc_path; inc_pos } ->
        push (mkdiag inc_pos
          (Printf.sprintf "include %S not resolved (use parse_file path)" inc_path))
    | _ -> ()) program;
  match List.rev !errors with
  | [] -> Ok { schemas = tschemas; rules = trules; tests = ttests;
               instances = tinstances; actions = List.rev !action_decls;
               predicates = tpredicates;
               metas }
  | es -> Error es
