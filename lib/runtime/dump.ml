(* Eval.value / outcome → JSON. *)

open Eval

let rec value_to_json (v : value) : Json.t =
  match v with
  | VInt i      -> JNum (float_of_int i)
  | VFloat f    -> JNum f
  | VBool b     -> JBool b
  | VString s   -> JStr s
  | VMoney f    -> JNum f
  | VDate d     -> JStr d
  | VDuration n -> JNum (float_of_int n)
  | VTag s      -> JStr s
  | VList vs    -> JArr (List.map value_to_json vs)
  | VObject kvs ->
      JObj (List.map (fun (k, v) -> (k, value_to_json v)) kvs)
  | VMissing    -> JNull
  | VWildcard   -> JNull

let outcome_to_json (name, args) : Json.t =
  JObj [
    ("call", JStr name);
    ("args", JArr (List.map value_to_json args));
  ]

let outcomes_to_json outs : Json.t =
  JArr (List.map outcome_to_json outs)
