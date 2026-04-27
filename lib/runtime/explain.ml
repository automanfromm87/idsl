(* Explain mode: given an input object, walk every rule, evaluate each
   `when` predicate, and produce a structured trace.

   For each predicate we record:
   - its pretty-printed text + truth value
   - the field bindings referenced by the predicate (transitively through
     derived fields), so the reader can see *why* the predicate is true /
     false at the level of the underlying raw inputs. *)

open Typed
open Eval

(* A binding shown alongside a predicate trace. Derived fields show both
   their formula and their current evaluated value. *)
type binding =
  | BRaw     of ident * value
  | BDerived of ident * string * value     (* name, formula, value *)

type pred_trace = {
  pt_text     : string;
  pt_value    : value;
  pt_bindings : binding list;
}

type rule_trace = {
  rt_path     : string;
  rt_schema   : string;
  rt_fired    : bool;
  rt_traces   : pred_trace list;
  rt_outcomes : outcome list;
}

(* ---------- collecting referenced fields, recursively through derived ---------- *)

let derived_body schemas schema_name fname =
  match Hashtbl.find_opt schemas schema_name with
  | None -> None
  | Some ts ->
      List.find_map (function
        | TFDerived (n, body) when n = fname -> Some body
        | TFDerived _ | TFRaw _ -> None) ts.ts_fields

(* Walk an expression (using Typed.iter_expr) and return the set of field
   names referenced, including names exposed by recursing into derived
   field bodies. Loop-bound (VarLocal) and tag (VarTag/VarInstance) names
   are excluded — only schema-level field references make it in. *)
let collect_refs schemas schema_name (root : texpr) : ident list =
  let acc = ref [] in
  let seen = Hashtbl.create 8 in
  let rec walk te =
    Typed.iter_expr (fun sub ->
      match sub.node with
      | TVar (VarField id) when not (Hashtbl.mem seen id) ->
          Hashtbl.add seen id ();
          acc := id :: !acc;
          (match derived_body schemas schema_name id with
           | Some body -> walk body
           | None -> ())
      | _ -> ()) te
  in
  walk root;
  List.rev !acc

let resolve_bindings schemas schema_name env refs =
  List.map (fun id ->
    let v = match Eval.lookup env id with
      | Some v -> v
      | None   -> VMissing in
    match derived_body schemas schema_name id with
    | Some body -> BDerived (id, Typed.pp_expr body, v)
    | None      -> BRaw (id, v)) refs

(* ---------- predicate / rule tracing ---------- *)

let trace_predicate ctx env schema_name pred =
  let v = Eval.eval env pred in
  let refs = collect_refs ctx.Eval.schemas schema_name pred in
  let bindings = resolve_bindings ctx.Eval.schemas schema_name env refs in
  { pt_text = Typed.pp_expr pred; pt_value = v; pt_bindings = bindings }

let trace_rule ctx env (r : trule) =
  let traces = List.map (trace_predicate ctx env r.tr_schema) r.tr_when in
  let fired = List.for_all (fun t ->
    match t.pt_value with VBool true -> true | _ -> false) traces in
  let outcomes =
    if fired then
      List.map (fun (_p, n, args) -> (n, List.map (Eval.eval env) args)) r.tr_then
    else [] in
  { rt_path = String.concat "." r.tr_path;
    rt_schema = r.tr_schema;
    rt_fired = fired;
    rt_traces = traces;
    rt_outcomes = outcomes }

let run ctx env =
  List.map (trace_rule ctx env) ctx.Eval.rules

(* ---------- pretty (human) ---------- *)

let pp_status fired = if fired then "FIRED" else "skipped"

let pp_binding = function
  | BRaw (n, v) ->
      Printf.sprintf "%s = %s" n (Eval.pp_value v)
  | BDerived (n, body, v) ->
      Printf.sprintf "%s = %s   →  %s" n (Typed.strip_tags body) (Eval.pp_value v)

let pp_pred_trace t =
  let mark = match t.pt_value with VBool true -> "✓" | _ -> "✗" in
  let head = Printf.sprintf "    [%s]  %s" mark (Typed.strip_tags t.pt_text) in
  match t.pt_bindings with
  | [] -> head
  | bs ->
      let lines = List.map (fun b -> "          • " ^ pp_binding b) bs in
      head ^ "\n" ^ String.concat "\n" lines

let pp_rule_trace rt =
  let header =
    Printf.sprintf "%s  [%s]  on %s"
      rt.rt_path (pp_status rt.rt_fired) rt.rt_schema in
  let preds =
    if rt.rt_traces = [] then "    (no when predicates)"
    else String.concat "\n" (List.map pp_pred_trace rt.rt_traces) in
  let acts =
    if rt.rt_fired && rt.rt_outcomes <> [] then
      "\n  produced:\n" ^ String.concat "\n"
        (List.map (fun o -> "    → " ^ Eval.pp_outcome o) rt.rt_outcomes)
    else "" in
  Printf.sprintf "%s\n  when:\n%s%s" header preds acts

let pp_report rts =
  let fired, skipped = List.partition (fun r -> r.rt_fired) rts in
  let section label xs =
    if xs = [] then Printf.sprintf "── %s ──\n\n  (none)" label
    else
      Printf.sprintf "── %s ──\n\n%s" label
        (String.concat "\n\n" (List.map pp_rule_trace xs)) in
  Printf.sprintf "%s\n\n%s"
    (section "FIRED"        fired)
    (section "DID NOT FIRE" skipped)

(* ---------- JSON variant for downstream tooling ---------- *)

let value_json = Dump.value_to_json

let binding_json = function
  | BRaw (n, v) ->
      Json.JObj [("kind", JStr "raw"); ("name", JStr n); ("value", value_json v)]
  | BDerived (n, body, v) ->
      Json.JObj [("kind", JStr "derived"); ("name", JStr n);
                 ("formula", JStr body); ("value", value_json v)]

let pred_trace_json t =
  Json.JObj [
    ("text", JStr t.pt_text);
    ("value", value_json t.pt_value);
    ("bindings", JArr (List.map binding_json t.pt_bindings));
  ]

let rule_trace_json rt =
  Json.JObj [
    ("rule",   JStr rt.rt_path);
    ("schema", JStr rt.rt_schema);
    ("fired",  JBool rt.rt_fired);
    ("when",   JArr (List.map pred_trace_json rt.rt_traces));
    ("outcomes", JArr (List.map Dump.outcome_to_json rt.rt_outcomes));
  ]

let to_json rts = Json.JArr (List.map rule_trace_json rts)
