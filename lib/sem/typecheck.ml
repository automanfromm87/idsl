(* Bidirectional type inference + elaboration.
   Walks the surface AST and produces a Typed.tprogram in which every node
   carries its inferred type and every bare ident is resolved as
   VarLocal | VarField | VarTag. *)

open Ast
open Types
open Typed

type action_param_ty = { pty_name : ident; pty : ty }
type env = {
  schemas      : (ident, tschema) Hashtbl.t;
  actions      : (ident, action_param_ty list) Hashtbl.t;
  instances    : (ident, ident) Hashtbl.t;
  fields       : (ident * ty) list;
  vars         : (ident * ty) list;
  strict_calls : bool;
}

let make_env ?(strict_calls = false) schemas actions instances =
  { schemas; actions; instances; fields = []; vars = []; strict_calls }

let mkdiag ?related pos msg =
  Diagnostic.error ?related ~stage:Diagnostic.Typecheck ~pos msg

(* Carries a position with the failure message, for paths where the inner
   inferrer hits a known position deep inside. Catch sites convert these
   to Diagnostic.t. *)
exception Located of Lexing.position * string
let err_at pos fmt = Printf.ksprintf (fun s -> raise (Located (pos, s))) fmt

let resolve_ty_annot schemas = function
  | AnnScalar "Int"    -> TInt
  | AnnScalar "Float"  -> TFloat
  | AnnScalar "Bool"   -> TBool
  | AnnScalar "String" -> TString
  | AnnScalar "Money"  -> TMoney
  | AnnScalar "Date"   -> TDate
  | AnnScalar s ->
      if Hashtbl.mem schemas s then TSchema s
      else err "unknown type %s" s
  | AnnEnum xs   -> TEnum xs
  | AnnList _    -> err "list type annotations not yet supported in @action"
  | AnnSchema s  -> TSchema s

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
      match Hashtbl.find_opt env.instances id with
      | Some sname -> Some (VarInstance id, TSchema sname)
      | None -> None

let rec infer env e : texpr =
  let mk = mk e.e_pos in
  match e.e_node with
  | ELit l    -> mk (TLit l) (infer_lit l)
  | EWildcard -> mk TWildcard TAny
  | EMissing  -> mk TMissing TMissing
  | EVar id ->
      (match resolve_var env id with
       | Some (v, t) -> mk (TVar v) t
       | None ->
         let ty = if Hashtbl.mem env.schemas id then TSchema id else TTag id in
         mk (TVar (VarTag id)) ty)
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
  | ECall (name, _) ->
      err "function `%s` not allowed in expression context" name

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
      (match Hashtbl.find_opt env.schemas s with
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
  match Hashtbl.find_opt env.schemas s with
  | None -> err "unknown schema %s" s
  | Some ts ->
      List.map (fun (k, v) ->
        match List.assoc_opt k ts.ts_types with
        | None -> err "no field `%s` in schema %s" k s
        | Some expected -> (k, check env v expected)) kvs

(* ---------- schemas ---------- *)

let infer_example schemas = function
  | ExLit l     -> infer_lit l, `Lit l
  | ExEnum tags ->
      if tags = [] then err "empty enum"
      else TEnum tags, `Enum tags
  | ExList es ->
      let env = make_env schemas
        (Hashtbl.create 0) (Hashtbl.create 0) in
      let tes = List.map (infer env) es in
      let elem = List.fold_left (fun acc te -> unify acc te.ty) TAny tes in
      TList elem, `List tes

let typecheck_schema schemas actions sch =
  let errors = ref [] in
  let push d = errors := d :: !errors in
  let raw_pairs = List.filter_map (function
    | FRaw (pos, n, ex) ->
        (try Some (n, fst (infer_example schemas ex))
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
        { schemas; actions; instances = Hashtbl.create 0;
          fields = tyacc; vars = []; strict_calls = false } in
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
  let tsch = { ts_name = sch.sname; ts_fields = tfields; ts_types = all_types } in
  (tsch, List.rev !errors)

(* ---------- rules ---------- *)

let pick_schema_for_rule env r =
  let referenced = ref [] in
  let collect (_, e) =
    Ast.iter_expr (function
      | EVar id when not (Hashtbl.mem env.schemas id) ->
          if not (List.mem id !referenced) then referenced := id :: !referenced
      | EVar _ | ELit _ | EList _ | EObject _ | EWildcard | EMissing
      | EUnary _ | EBin _ | EIf _ | EAny _ | EEvery _ | ECount _ | ESum _
      | EIsMissing _ | EIsPresent _ | ECall _ | EField _ -> ()) e in
  List.iter collect r.rwhen;
  List.iter collect r.rthen;
  let scored = Hashtbl.fold (fun name ts acc ->
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
      (match Hashtbl.find_opt env.actions name with
       | None ->
           if env.strict_calls then
             err "action `%s` has no @action declaration (strict mode)" name;
           (e.e_pos, name, targs)
       | Some sig_params ->
           if List.length sig_params <> List.length targs then
             err "action %s expects %d argument(s), got %d"
               name (List.length sig_params) (List.length targs);
           List.iter2 (fun sp ta ->
             let _ =
               try unify sp.pty ta.ty
               with Type_error m ->
                 err "argument `%s`: %s" sp.pty_name m
             in ()) sig_params targs;
           (e.e_pos, name, targs))
  | EVar _ | EField _ | ELit _ | EList _ | EObject _ | EWildcard | EMissing
  | EUnary _ | EBin _ | EIf _ | EAny _ | EEvery _ | ECount _ | ESum _
  | EIsMissing _ | EIsPresent _ -> err "expected a call expression"

let typecheck_rule env r =
  let where = String.concat "." r.rpath in
  let sname = match r.rschema with
    | Some s ->
        if not (Hashtbl.mem env.schemas s) then
          err_at r.rpos "rule %s on %s: unknown schema" where s;
        s
    | None -> pick_schema_for_rule env r in
  let ts = Hashtbl.find env.schemas sname in
  let env' = { env with fields = ts.ts_types } in
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
  let sname = t.tgiven.gschema in
  let ts = match Hashtbl.find_opt env.schemas sname with
    | Some s -> s
    | None   -> err_at t.tpos "test %S: unknown schema %s" t.tname sname in
  let env_g = { env with fields = ts.ts_types } in
  let givens = List.map (fun a ->
    match List.assoc_opt a.aname ts.ts_types with
    | None -> err_at a.apos "test %S: no field `%s` in schema %s"
                t.tname a.aname sname
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
  { tt_name = t.tname;
    tt_given = { tg_schema = sname; tg_values = givens };
    tt_expect = expects }

let typecheck_instance env i =
  let ts = match Hashtbl.find_opt env.schemas i.ischema with
    | Some s -> s
    | None   -> err_at i.ipos "instance %s: unknown schema %s" i.iname i.ischema in
  let env_g = { env with fields = ts.ts_types } in
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
  { ti_name = i.iname; ti_schema = i.ischema; ti_values = values }

let typecheck_action schemas a =
  let params = List.map (fun p ->
    let ty =
      try resolve_ty_annot schemas p.ptype
      with Type_error m ->
        err_at p.ppos "@action %s param `%s`: %s" a.asname p.pname m
    in { pty_name = p.pname; pty = ty }) a.asparams in
  (a.asname, params)

(* ---------- driver ---------- *)

(* Walk all schema field types, collect every enum tag, error if any tag
   appears in more than one enum field. Forces unambiguous tag → enum
   resolution at compare-time. *)
let check_unique_enum_tags errors schema_pos tschemas =
  let seen : (string, string) Hashtbl.t = Hashtbl.create 32 in
  List.iter (fun s ->
    let pos = try Hashtbl.find schema_pos s.ts_name
              with Not_found -> Lexing.dummy_pos in
    List.iter (fun (fname, ty) ->
      match ty with
      | TEnum tags ->
          let where = Printf.sprintf "%s.%s" s.ts_name fname in
          List.iter (fun t ->
            match Hashtbl.find_opt seen t with
            | Some other when other <> where ->
                errors := mkdiag pos (Printf.sprintf
                  "enum tag `%s` declared in both %s and %s — tags must be unique across all enum fields"
                  t other where) :: !errors
            | _ -> Hashtbl.replace seen t where) tags
      | _ -> ()) s.ts_types) tschemas

(* Versions of the DSL surface this build accepts.
   Bump when a syntax/semantics change is breaking; older `.idsl` files
   declaring an unsupported version will be rejected. *)
let supported_versions = ["0.0.1"; "0.0.2"; "0.0.3"]

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
  let errors : Diagnostic.t list ref = ref [] in
  let push d = errors := d :: !errors in
  check_metadata errors program;
  List.iter (fun a ->
    match with_diag a.aspos (fun () -> typecheck_action schemas a) with
    | `Err d -> push d
    | `Ok (n, params) ->
        if Hashtbl.mem actions n then
          push (mkdiag a.aspos (Printf.sprintf "duplicate @action %s" n))
        else begin
          Hashtbl.add actions n params;
          action_decls := { ta_name = n;
                            ta_params = List.map (fun p -> (p.pty_name, p.pty)) params;
                            ta_pos = a.aspos } :: !action_decls
        end) (Ast.actions program);
  let schema_pos : (ident, Lexing.position) Hashtbl.t = Hashtbl.create 16 in
  let tschemas =
    List.filter_map (fun s ->
      Hashtbl.replace schema_pos s.sname s.spos;
      let tsch, errs = typecheck_schema schemas actions s in
      Hashtbl.replace schemas tsch.ts_name tsch;
      List.iter push errs;
      Some tsch) (Ast.schemas program) in
  check_unique_enum_tags errors schema_pos tschemas;
  List.iter (fun i ->
    if Hashtbl.mem instances i.iname then
      push (mkdiag i.ipos (Printf.sprintf "duplicate instance %s" i.iname))
    else Hashtbl.add instances i.iname i.ischema)
    (Ast.instances program);
  let strict_calls =
    List.exists (function
      | Ast.TMeta { mkey = "strict_actions"; _ } -> true
      | _ -> false) program in
  let env = make_env ~strict_calls schemas actions instances in
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
  let metas =
    List.filter_map (function
      | TMeta m -> Some m
      | TSchema _ | TRule _ | TTest _ | TAction _ | TInstance _
      | TInclude _ -> None)
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
               metas }
  | es -> Error es
