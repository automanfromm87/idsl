(* Pass 1: collect schema names + each schema's field names.
   Pass 2: validate references — currently only `e.g. [Foo]` where Foo is a
           bare identifier expected to be a schema. Deeper checks (derived
           field DAG, type inference, enum-tag resolution) come later. *)

open Ast

type env = {
  schema_names   : (ident, ident list) Hashtbl.t;
  mutable errors : Diagnostic.t list;
}

let make_env () = { schema_names = Hashtbl.create 16; errors = [] }

let report env ~pos msg =
  env.errors <- Diagnostic.error ~stage:Resolve ~pos msg :: env.errors

let collect_schemas env program =
  List.iter (fun s ->
    if Hashtbl.mem env.schema_names s.sname then
      report env ~pos:s.spos
        (Printf.sprintf "duplicate schema %S" s.sname)
    else
      Hashtbl.add env.schema_names s.sname (field_names s.sfields))
    (schemas program)

let check_list_element env where e =
  match e.e_node with
  | EVar id when not (Hashtbl.mem env.schema_names id) ->
      report env ~pos:e.e_pos
        (Printf.sprintf "%s: unknown schema reference %S" where id)
  | EVar _ | ELit _ | EList _ | EObject _ | EWildcard | EMissing
  | EUnary _ | EBin _ | EIf _ | EAny _ | EEvery _ | ECount _ | ESum _
  | EIsMissing _ | EIsPresent _ | ECall _ | EField _ -> ()

let check_field env schema_name = function
  | FRaw (_pos, fname, ExList es) ->
      let where = Printf.sprintf "schema %s.%s" schema_name fname in
      List.iter (check_list_element env where) es
  | FRaw _ | FDerived _ -> ()

let validate_program env program =
  List.iter (fun s ->
    List.iter (check_field env s.sname) s.sfields)
    (schemas program)

let run program =
  let env = make_env () in
  collect_schemas env program;
  validate_program env program;
  match List.rev env.errors with
  | []   -> Ok ()
  | errs -> Error errs
