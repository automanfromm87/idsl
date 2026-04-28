(* Pass 1: collect schema names + each schema's field names.
   Pass 2: validate references — currently only `e.g. [Foo]` where Foo is a
           bare identifier expected to be a schema.

   Domain-aware: schemas are keyed on `(domain option, name)` so two
   schemas with the same bare name in different domains coexist.
   Lookup of a bare reference inside `domain D:` tries `(Some D, X)`
   first and falls back to global `(None, X)`. *)

open Ast

type qkey = ident option * ident

type env = {
  schema_names   : (qkey, ident list) Hashtbl.t;
  mutable errors : Diagnostic.t list;
}

let make_env () = { schema_names = Hashtbl.create 16; errors = [] }

let report env ~pos msg =
  env.errors <- Diagnostic.error ~stage:Resolve ~pos msg :: env.errors

(* Display a domain-qualified schema name as "shipping.Order" / "Order". *)
let pp_qname (dom, name) =
  match dom with
  | Some d -> d ^ "." ^ name
  | None   -> name

let collect_schemas env program =
  List.iter (fun s ->
    let k = (s.sdomain, s.sname) in
    if Hashtbl.mem env.schema_names k then
      report env ~pos:s.spos
        (Printf.sprintf "duplicate schema %S" (pp_qname k))
    else
      Hashtbl.add env.schema_names k (field_names s.sfields))
    (schemas program)

(* Resolve a schema reference. Qualified names (`other.X`) bypass the
   domain-scoped lookup and target an explicit (Some other, X) pair. *)
let resolve_schema env ~domain name =
  match String.index_opt name '.' with
  | Some i ->
      let dom = String.sub name 0 i in
      let bare = String.sub name (i + 1) (String.length name - i - 1) in
      Hashtbl.mem env.schema_names (Some dom, bare)
  | None ->
      Hashtbl.mem env.schema_names (domain, name)
      || Hashtbl.mem env.schema_names (None, name)

let check_list_element env ~domain where e =
  match e.e_node with
  | EVar id when not (resolve_schema env ~domain id) ->
      report env ~pos:e.e_pos
        (Printf.sprintf "%s: unknown schema reference %S" where id)
  | EVar _ | ELit _ | EList _ | EObject _ | EWildcard | EMissing
  | ESelf
  | EUnary _ | EBin _ | EIf _ | EAny _ | EEvery _ | ECount _ | ESum _
  | EIsMissing _ | EIsPresent _ | ECall _ | EField _ -> ()

let check_field env ~domain schema_name = function
  | FRaw (_pos, fname, decl) ->
      let where = Printf.sprintf "schema %s.%s" schema_name fname in
      (* Sample-side schema refs: `e.g. [Foo]` lowers to an EList of
         EVars; each one must resolve to a known schema in scope. *)
      (match decl.fd_sample with
       | Some { e_node = EList es; _ } ->
           List.iter (check_list_element env ~domain where) es
       | _ -> ());
      (* Annotation-side schema refs: `[Foo]` and `Foo` (when Foo is
         user-defined) need the same resolution. *)
      let rec check_ty = function
        | AnnList t -> check_ty t
        | AnnScalar s | AnnSchema s ->
            (* Skip built-ins; check user-defined schema names. *)
            (match s with
             | "Int" | "Float" | "Bool" | "String"
             | "Money" | "Date" | "Duration" -> ()
             | _ when not (resolve_schema env ~domain s) ->
                 report env ~pos:_pos
                   (Printf.sprintf "%s: unknown type %S" where s)
             | _ -> ())
        | AnnEnum _ -> ()
      in
      Option.iter check_ty decl.fd_ty
  | FDerived _ -> ()

let validate_program env program =
  List.iter (fun s ->
    List.iter (check_field env ~domain:s.sdomain s.sname) s.sfields)
    (schemas program)

let run program =
  let env = make_env () in
  collect_schemas env program;
  validate_program env program;
  match List.rev env.errors with
  | []   -> Ok ()
  | errs -> Error errs
