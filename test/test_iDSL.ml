let pp_diag (d : IDSL.Diagnostic.t) = IDSL.Diagnostic.to_string d
let pp_diags ds = String.concat "; " (List.map pp_diag ds)

let parse src = (IDSL.Driver.parse_string src).ast

let assert_ok label src =
  match parse src with
  | Ok _      -> Printf.printf "ok   %s\n" label
  | Error ds  -> Printf.printf "FAIL %s: %s\n" label (pp_diags ds); exit 1

let assert_resolve_ok label src =
  match parse src with
  | Error ds -> Printf.printf "FAIL %s: parse %s\n" label (pp_diags ds); exit 1
  | Ok p ->
      (match IDSL.Resolve.run p with
       | Ok ()    -> Printf.printf "ok   %s\n" label
       | Error ds ->
           Printf.printf "FAIL %s: %s\n" label (pp_diags ds); exit 1)

let assert_resolve_err label src =
  match parse src with
  | Error ds -> Printf.printf "FAIL %s: parse %s\n" label (pp_diags ds); exit 1
  | Ok p ->
      (match IDSL.Resolve.run p with
       | Ok ()    -> Printf.printf "FAIL %s: expected resolve error\n" label; exit 1
       | Error _  -> Printf.printf "ok   %s\n" label)

let assert_tc_ok label src =
  match parse src with
  | Error ds -> Printf.printf "FAIL %s: parse %s\n" label (pp_diags ds); exit 1
  | Ok p ->
      (match IDSL.Typecheck.run p with
       | Ok _      -> Printf.printf "ok   %s\n" label
       | Error ds  ->
           Printf.printf "FAIL %s: %s\n" label (pp_diags ds); exit 1)

let assert_tc_err label expected_substr src =
  match parse src with
  | Error ds -> Printf.printf "FAIL %s: parse %s\n" label (pp_diags ds); exit 1
  | Ok p ->
      (match IDSL.Typecheck.run p with
       | Ok _ -> Printf.printf "FAIL %s: expected typecheck error\n" label; exit 1
       | Error ds ->
           let msgs = String.concat "\n" (List.map (fun d -> d.IDSL.Diagnostic.message) ds) in
           let contains s =
             try let _ = Str.search_forward (Str.regexp_string s) msgs 0 in true
             with Not_found -> false
           in
           if contains expected_substr
           then Printf.printf "ok   %s\n" label
           else (Printf.printf "FAIL %s: msg %S did not contain %S\n"
                   label msgs expected_substr; exit 1))

let () =
  assert_ok "metadata"
    {|@version("0.0.1")
@status("Active")
|};

  assert_ok "raw schema fields"
    {|schema C:
  - ID: e.g. 123
  - Kind: {NDA, MSA, DPA}
  - V: e.g. $5,000,000
  - D: e.g. 2025-01-15
  - B: e.g. true
|};

  assert_tc_ok "type-only field annotation (no e.g.)"
    {|schema C:
  - Amount: Money
  - Kind:   {NDA, MSA}
  - Items:  [Int]
|};

  assert_tc_ok "type annotation + e.g. sample"
    {|schema C:
  - Amount: Money e.g. $50
  - Kind:   {NDA, MSA} e.g. NDA
|};

  assert_tc_err "type annot rejects mismatched sample"
    "type mismatch"
    {|schema C:
  - Amount: Money e.g. true
|};

  assert_tc_ok "predicate decl + self call from derived field"
    {|predicate is_high_risk on { Value: Money, IsRenewal: Bool }:
  Value > $1,000,000 and not IsRenewal

schema Contract:
  - Value: Money e.g. $500,000
  - IsRenewal: e.g. true
  - IsHighRisk: i.e. is_high_risk(self)
|};

  assert_tc_err "predicate rejects schema missing a required field"
    "missing field"
    {|predicate is_high_risk on { Value: Money, IsRenewal: Bool }:
  Value > $1,000,000

schema Amendment:
  - Value: Money e.g. $1
  - IsHighRisk: i.e. is_high_risk(self)
|};

  assert_tc_err "self inside predicate body errors"
    "outside any schema"
    {|predicate p on { X: Int }:
  self == self
|};

  (* End-to-end: predicate is callable from a derived field, runtime
     evaluates it against the schema's row, and the rule fires
     accordingly. *)
  (let src = {|@action notify(level: {Low, High})

predicate is_high_risk on { Value: Money, IsRenewal: Bool }:
  Value > $1,000,000 and not IsRenewal

schema Contract:
  - Value:      Money e.g. $1
  - IsRenewal:  e.g. true
  - IsHighRisk: i.e. is_high_risk(self)

rule r on Contract:
  when:
    IsHighRisk
  then:
    notify(High)

test "predicate fires on high-value non-renewal":
  given Contract:
    Value = $2,000,000
    IsRenewal = false
  expect:
    notify(High)

test "predicate stays off on renewal":
  given Contract:
    Value = $2,000,000
    IsRenewal = true
  expect:
    not notify(_)
|} in
   match parse src with
   | Error ds ->
       Printf.printf "FAIL predicate runtime: parse %s\n" (pp_diags ds);
       exit 1
   | Ok p ->
       (match IDSL.Typecheck.run p with
        | Error ds ->
            Printf.printf "FAIL predicate runtime: tc %s\n" (pp_diags ds);
            exit 1
        | Ok tp ->
            let results, _ = IDSL.Eval.run_all tp in
            let all_passed = List.for_all (fun r -> r.IDSL.Eval.passed) results in
            if all_passed then Printf.printf "ok   predicate runtime smoke\n"
            else begin
              Printf.printf "FAIL predicate runtime smoke: tests failed\n";
              List.iter (fun r ->
                if not r.IDSL.Eval.passed then
                  List.iter (fun f -> Printf.printf "       %s\n" f) r.failures)
                results;
              exit 1
            end));

  assert_resolve_ok "list literal of schema ref"
    {|schema Party:
  - Name: e.g. "Alpha"
schema Contract:
  - Parties: e.g. [Party]
|};

  assert_resolve_err "unknown schema ref"
    {|schema Contract:
  - Parties: e.g. [Party]
|};

  assert_ok "derived fields"
    {|schema C:
  - DurationDays: e.g. 365
  - IsLongTerm: i.e. DurationDays > 1825
  - Retention: i.e. (if Kind == Financial then 3650 else 1825)
|};

  assert_ok "rule with dotted path and multiple predicates"
    {|rule contract.financial.high_value:
  when:
    Kind == Financial
    IsHighValue
  then:
    flag(red, "high-value financial")
    notify("senior counsel")
|};

  assert_ok "rule with triple-quoted description"
    {|rule contract.nda.long_term:
  """
  Long-term NDAs warrant a yellow flag.
  Multiple lines are fine.
  """
  when:
    IsLongTerm
  then:
    flag(yellow, "long-term NDA")
|};

  assert_ok "any/where with field access"
    {|schema C:
  - Bad: i.e. any clause in Clauses where (clause.Kind == Indemnification
                                           and clause.Cap is missing)
|};

  assert_ok "example file"
    (let ic = open_in "../examples/order.idsl" in
     let n = in_channel_length ic in
     let s = really_input_string ic n in
     close_in ic; s);

  assert_tc_ok "tc: well-typed schema + rule"
    {|schema C:
  - Kind: {NDA, MSA}
  - IsLong: i.e. true
rule r.x:
  when:
    Kind == NDA
    IsLong
  then:
    flag(yellow, "x")
|};

  assert_tc_err "tc: enum tag not in declared set" "tag `FOO`"
    {|schema C:
  - Kind: {NDA, MSA}
rule r.x:
  when:
    Kind == FOO
  then:
    flag(red, "x")
|};

  assert_tc_err "tc: field access on non-object" "field access on non-object"
    {|schema C:
  - Inner: i.e. true
rule r.x:
  when:
    Inner.NoSuch
  then:
    flag(red, "x")
|};

  assert_tc_err "tc: unknown field on schema" "no field"
    {|schema Sub:
  - X: e.g. 1
schema C:
  - Inner: e.g. [Sub]
  - Bad: i.e. any s in Inner: s.NotThere == 1
|};

  assert_tc_err "tc: bool + int" "+ requires"
    {|schema C:
  - Flag: e.g. true
  - Bad: i.e. Flag + 1
|};

  assert_tc_err "tc: test assigns wrong-typed value" "type mismatch"
    {|schema C:
  - Kind: {NDA, MSA}
test "bad":
  given C:
    Kind = 42
  expect:
    flag(_, _)
|}
