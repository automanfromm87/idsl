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

(* Bare reference `X` inside domain D: try (Some D, X) first, then
   global (None, X).  Cross-domain references aren't supported yet
   (Phase 1 limitation). *)
let resolve_schema env ~domain name =
  if Hashtbl.mem env.schema_names (domain, name) then true
  else if Hashtbl.mem env.schema_names (None, name) then true
  else false

let check_list_element env ~domain where e =
  match e.e_node with
  | EVar id when not (resolve_schema env ~domain id) ->
      report env ~pos:e.e_pos
        (Printf.sprintf "%s: unknown schema reference %S" where id)
  | EVar _ | ELit _ | EList _ | EObject _ | EWildcard | EMissing
  | EUnary _ | EBin _ | EIf _ | EAny _ | EEvery _ | ECount _ | ESum _
  | EIsMissing _ | EIsPresent _ | ECall _ | EField _ -> ()

let check_field env ~domain schema_name = function
  | FRaw (_pos, fname, ExList es) ->
      let where = Printf.sprintf "schema %s.%s" schema_name fname in
      List.iter (check_list_element env ~domain where) es
  | FRaw _ | FDerived _ -> ()

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
