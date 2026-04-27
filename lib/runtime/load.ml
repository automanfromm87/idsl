(* Schema-aware JSON → Eval.value loader.

   Coercion rules: walk a typed schema's fields in parallel with the JSON
   object. Use the static type to decide how to interpret strings (Money /
   Date / String) and how to recurse into lists / objects. *)

open Typed
open Types
open Json

exception Load_error of string
let err fmt = Printf.ksprintf (fun s -> raise (Load_error s)) fmt

(* `instances` carries the runtime instance table — every recursive call
   threads it through so `{"$ref": "Alpha"}` resolutions don't depend on
   any process-level state. The caller usually passes
   `Eval.ctx.instances`; the empty-table default keeps single-shot uses
   (tests, simple CLIs) ergonomic. *)
let lookup_instance instances name =
  match Hashtbl.find_opt instances name with
  | Some v -> Some v
  | None   -> None

let rec load_value ~instances
                   (schemas : (Ast.ident, tschema) Hashtbl.t)
                   (ty : ty) (j : t) : Eval.value =
  match ty, j with
  | _, JNull -> VMissing
  | TInt,    JNum n when Float.is_integer n -> VInt (int_of_float n)
  | TInt,    JNum n -> err "expected Int, got non-integer %g" n
  | TFloat,  JNum n -> VFloat n
  | TBool,   JBool b -> VBool b
  | TString, JStr s -> VString s
  | TMoney,  JStr s -> VMoney (parse_money_str s)
  | TMoney,  JNum n -> VMoney n
  | TDate,   JStr s -> VDate s
  | TDuration, JNum n when Float.is_integer n -> VDuration (int_of_float n)
  | TEnum tags, JStr s ->
      if List.mem s tags then VTag s
      else err "value %S not in enum {%s}" s (String.concat "|" tags)
  | TTag _, JStr s -> VTag s
  | TList el, JArr xs ->
      VList (List.map (fun x -> load_value ~instances schemas el x) xs)
  | TSchema _, JObj [("$ref", JStr name)]
  | TSchema _, JStr name ->
      (* `{"$ref": "Alpha"}` and the bare-string shorthand both look up
         a pre-declared instance. *)
      (match lookup_instance instances name with
       | Some v -> v
       | None   -> err "unknown instance reference %S" name)
  | TSchema name, JObj kvs -> load_object ~instances schemas name kvs
  | TObject expected, JObj kvs ->
      VObject (List.map (fun (k, v) ->
        match List.assoc_opt k expected with
        | Some t -> (k, load_value ~instances schemas t v)
        | None   -> err "unexpected field `%s` in object" k) kvs)
  | TAny, _ -> load_any ~instances schemas j
  | TMissing, _ -> VMissing
  | _, _ ->
      err "type/JSON mismatch: expected %s, got %s"
        (pp_ty ty) (to_string j)

and parse_money_str s =
  let drop_dollar = if String.length s > 0 && s.[0] = '$'
                    then String.sub s 1 (String.length s - 1) else s in
  let cleaned = String.concat "" (String.split_on_char ',' drop_dollar) in
  try float_of_string cleaned
  with _ -> err "bad money literal %S" s

and load_object ~instances schemas name kvs =
  match Hashtbl.find_opt schemas name with
  | None -> err "unknown schema %s" name
  | Some sch ->
      let pairs = List.map (fun (k, v) ->
        match List.assoc_opt k sch.ts_types with
        | None -> err "no field `%s` in schema %s" k name
        | Some t -> (k, load_value ~instances schemas t v)) kvs in
      VObject pairs

and load_any ~instances schemas = function
  | JNull   -> VMissing
  | JBool b -> VBool b
  | JNum n  ->
      if Float.is_integer n then VInt (int_of_float n) else VFloat n
  | JStr s  -> VString s
  | JArr xs -> VList (List.map (fun x -> load_any ~instances schemas x) xs)
  | JObj kvs ->
      VObject (List.map (fun (k, v) -> (k, load_any ~instances schemas v)) kvs)

(* Build a runtime env directly from a top-level JSON object + a target
   schema, mimicking what `given Schema:` does in a test block. *)
let build_env ?(instances = Hashtbl.create 0) schemas schema_name (j : Json.t) =
  let sch =
    match Hashtbl.find_opt schemas schema_name with
    | Some s -> s
    | None   -> err "unknown schema %s" schema_name in
  let kvs = match j with
    | JObj kvs -> kvs
    | _ -> err "input must be a JSON object for schema %s" schema_name in
  let raw_pairs = List.map (fun (k, v) ->
    match List.assoc_opt k sch.ts_types with
    | None -> err "no field `%s` in schema %s" k schema_name
    | Some t -> (k, load_value ~instances schemas t v)) kvs in
  Eval.build_env_from_values ~instances sch raw_pairs
