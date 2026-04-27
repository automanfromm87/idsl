(* Counterfactual / diff analysis between two evaluator runs.
   Given two envs (and their explain traces) over the same program, report:
   - which raw fields differ
   - which rules flipped FIRED ↔ skipped (or had predicate values shift)
   - which outcomes appeared / disappeared *)

open Eval

type outcome_diff = {
  od_added   : outcome list;
  od_removed : outcome list;
}

type pred_change = {
  pc_text   : string;
  pc_before : value;
  pc_after  : value;
}

type rule_change = {
  rc_path         : string;
  rc_fired_before : bool;
  rc_fired_after  : bool;
  rc_pred_changes : pred_change list;
}

type field_change = {
  fc_name   : string;
  fc_before : value;
  fc_after  : value;
}

type diff = {
  fields    : field_change list;
  outcomes  : outcome_diff;
  rules     : rule_change list;
}

let outcome_eq (n1, a1) (n2, a2) =
  n1 = n2
  && List.length a1 = List.length a2
  && List.for_all2 value_eq a1 a2

let outcomes_of_traces (rts : Explain.rule_trace list) =
  List.concat_map (fun (rt : Explain.rule_trace) -> rt.rt_outcomes) rts

let diff_outcomes before after =
  let removed =
    List.filter (fun o -> not (List.exists (outcome_eq o) after)) before in
  let added =
    List.filter (fun o -> not (List.exists (outcome_eq o) before)) after in
  { od_added = added; od_removed = removed }

let diff_rules (before : Explain.rule_trace list)
               (after  : Explain.rule_trace list) =
  List.map2 (fun (rb : Explain.rule_trace) (ra : Explain.rule_trace) ->
    let pcs = List.map2 (fun (pb : Explain.pred_trace)
                              (pa : Explain.pred_trace) ->
      if value_eq pb.pt_value pa.pt_value then None
      else Some { pc_text = pb.pt_text;
                  pc_before = pb.pt_value; pc_after = pa.pt_value })
      rb.rt_traces ra.rt_traces
      |> List.filter_map (fun x -> x) in
    { rc_path = rb.rt_path;
      rc_fired_before = rb.rt_fired;
      rc_fired_after  = ra.rt_fired;
      rc_pred_changes = pcs })
    before after
  |> List.filter (fun rc ->
    rc.rc_fired_before <> rc.rc_fired_after
    || rc.rc_pred_changes <> [])

let diff_fields tsch env_before env_after =
  List.filter_map (fun (name, _ty) ->
    let vb = match Eval.lookup env_before name with
      | Some v -> v | None -> VMissing in
    let va = match Eval.lookup env_after name with
      | Some v -> v | None -> VMissing in
    if value_eq vb va then None
    else Some { fc_name = name; fc_before = vb; fc_after = va })
    (Typed.raw_fields tsch)

let compute tsch env_before env_after traces_before traces_after =
  let outs_before = outcomes_of_traces traces_before in
  let outs_after  = outcomes_of_traces traces_after  in
  { fields   = diff_fields tsch env_before env_after;
    outcomes = diff_outcomes outs_before outs_after;
    rules    = diff_rules traces_before traces_after }

(* ---------- pretty ---------- *)

let pp_field_change fc =
  Printf.sprintf "  %s:  %s  →  %s"
    fc.fc_name (Eval.pp_value fc.fc_before) (Eval.pp_value fc.fc_after)

let pp_pred_change pc =
  Printf.sprintf "      • %s   (%s → %s)"
    (Typed.strip_tags pc.pc_text)
    (Eval.pp_value pc.pc_before) (Eval.pp_value pc.pc_after)

let pp_rule_change rc =
  let head = Printf.sprintf "  %s:  %s  →  %s"
    rc.rc_path
    (Explain.pp_status rc.rc_fired_before)
    (Explain.pp_status rc.rc_fired_after) in
  if rc.rc_pred_changes = [] then head
  else head ^ "\n" ^ String.concat "\n" (List.map pp_pred_change rc.rc_pred_changes)

let pp_outcome_set marker xs =
  if xs = [] then "  (none)"
  else String.concat "\n"
         (List.map (fun o -> "  " ^ marker ^ " " ^ Eval.pp_outcome o) xs)

let pp_diff d =
  let section_fields =
    if d.fields = [] then "  (no field changes)"
    else String.concat "\n" (List.map pp_field_change d.fields) in
  let section_rules =
    if d.rules = [] then "  (no rule status changes)"
    else String.concat "\n" (List.map pp_rule_change d.rules) in
  Printf.sprintf
    "── Field changes ──\n%s\n\n── Rule status changes ──\n%s\n\n── Outcomes ──\nREMOVED:\n%s\nADDED:\n%s"
    section_fields section_rules
    (pp_outcome_set "-" d.outcomes.od_removed)
    (pp_outcome_set "+" d.outcomes.od_added)
