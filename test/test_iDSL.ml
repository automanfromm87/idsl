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
    {|@version("0.0.4")
@status("Active")
|};

  assert_ok "raw schema fields"
    {|schema C:
  - ID: default 123
  - Kind: {NDA, MSA, DPA}
  - V: default $5,000,000
  - D: default 2025-01-15
  - B: default true
|};

  assert_tc_ok "type-only field annotation (no default)"
    {|schema C:
  - Amount: Money
  - Kind:   {NDA, MSA}
  - Items:  [Int]
|};

  assert_tc_ok "type annotation + default sample"
    {|schema C:
  - Amount: Money default $50
  - Kind:   {NDA, MSA} default NDA
|};

  assert_tc_err "type annot rejects mismatched sample"
    "type mismatch"
    {|schema C:
  - Amount: Money default true
|};

  assert_tc_ok "predicate decl + self call from derived field"
    {|predicate is_high_risk on { Value: Money, IsRenewal: Bool }:
  Value > $1,000,000 and not IsRenewal

schema Contract:
  - Value: Money default $500,000
  - IsRenewal: default true
  - IsHighRisk = is_high_risk(self)
|};

  assert_tc_ok "implicit self: predicate without parens"
    {|predicate is_high_risk on { Value: Money }: Value > $1,000,000

schema Contract:
  - Value: Money default $1
  - IsHighRisk = is_high_risk
|};

  assert_tc_ok "implicit self: qualified predicate without parens"
    {|domain core:
  predicate is_high_risk on { V: Int }: V > 100

domain shipping:
  schema Order:
    - V: Int default 1
    - IsHigh = core.is_high_risk
|};

  assert_tc_err "predicate rejects schema missing a required field"
    "missing field"
    {|predicate is_high_risk on { Value: Money, IsRenewal: Bool }:
  Value > $1,000,000

schema Amendment:
  - Value: Money default $1
  - IsHighRisk = is_high_risk(self)
|};

  assert_tc_err "self inside predicate body errors"
    "outside any schema"
    {|predicate p on { X: Int }:
  self == self
|};

  assert_tc_err "predicate body cannot call another predicate"
    "cannot call other predicates"
    {|predicate inner on { Y: Int }: Y > 0
predicate outer on { Y: Int }: inner(self)
|};

  assert_tc_err "predicate body cannot call an action"
    "cannot call actions"
    {|@action notify(team: String)
predicate p on { X: Int }: notify("ops")
|};

  (* Table-driven test: each `case -> action(...)` line lowers to a
     standalone test_def at runtime; all of them run + report. *)
  (let src = {|@action flag(severity: {info, warn, alert}, reason: String)

schema Order:
  - Total: Money default $1

rule big_order on Order:
  when:
    Total > $1,000
  then:
    flag(alert, "big")

test "thresholds" on Order:
  cases:
    Total = $999    -> not flag(_, _)
    Total = $1,000  -> not flag(_, _)
    Total = $1,001  -> flag(alert, "big")
|} in
   match parse src with
   | Error ds ->
       Printf.printf "FAIL table tests: parse %s\n" (pp_diags ds); exit 1
   | Ok p ->
       (match IDSL.Typecheck.run p with
        | Error ds ->
            Printf.printf "FAIL table tests: tc %s\n" (pp_diags ds); exit 1
        | Ok tp ->
            let n = List.length tp.IDSL.Typed.tests in
            if n <> 3 then
              (Printf.printf "FAIL table tests: expected 3 cases, got %d\n" n;
               exit 1);
            let results, _ = IDSL.Eval.run_all tp in
            if List.for_all (fun r -> r.IDSL.Eval.passed) results
            then Printf.printf "ok   table-driven test (3 cases)\n"
            else begin
              Printf.printf "FAIL table tests: ";
              List.iter (fun r ->
                if not r.IDSL.Eval.passed then
                  Printf.printf "%s " r.IDSL.Eval.rname) results;
              Printf.printf "\n"; exit 1
            end));

  (* Cross-domain qualified refs.  A `core` domain defines a shared
     `Money` schema; `shipping` consumes it via `core.Money` in
     type-annotation position. *)
  (let src = {|domain core:
  schema Money:
    - Amount: Int default 0
    - Currency: {USD, EUR} default USD

domain shipping:
  schema Order:
    - Total: core.Money default {Amount: 50, Currency: USD}
|} in
   match parse src with
   | Error ds ->
       Printf.printf "FAIL cross-domain ty: parse %s\n" (pp_diags ds); exit 1
   | Ok p ->
       (match IDSL.Typecheck.run p with
        | Error ds ->
            Printf.printf "FAIL cross-domain ty: %s\n" (pp_diags ds); exit 1
        | Ok _ ->
            Printf.printf "ok   cross-domain type annotation\n"));

  (* Cross-domain action call: `core.notify(...)` from inside another
     domain resolves to the action declared in `core`. *)
  (let src = {|domain core:
  @action notify(team: String)

domain shipping:
  schema Order:
    - V: Int default 1

  rule big on Order:
    when:
      V > 0
    then:
      core.notify("ops")

  test "qualified action call":
    given Order:
      V = 5
    expect:
      core.notify("ops")
|} in
   match parse src with
   | Error ds ->
       Printf.printf "FAIL cross-domain call: parse %s\n" (pp_diags ds); exit 1
   | Ok p ->
       (match IDSL.Typecheck.run p with
        | Error ds ->
            Printf.printf "FAIL cross-domain call: %s\n" (pp_diags ds); exit 1
        | Ok tp ->
            let results, _ = IDSL.Eval.run_all tp in
            if List.for_all (fun r -> r.IDSL.Eval.passed) results
            then Printf.printf "ok   cross-domain action call\n"
            else (Printf.printf "FAIL cross-domain call (runtime)\n"; exit 1)));

  (* Cross-domain instance reference: `core.Alpha` resolves to an
     instance declared in `core`, used inside a `shipping` schema. *)
  (let src = {|domain core:
  schema Party:
    - Name: default "x"
  instance Party Alpha:
    Name = "Alpha"

domain shipping:
  schema Order:
    - P: core.Party default core.Alpha
|} in
   match parse src with
   | Error ds ->
       Printf.printf "FAIL cross-domain instance: parse %s\n" (pp_diags ds);
       exit 1
   | Ok p ->
       (match IDSL.Typecheck.run p with
        | Error ds ->
            Printf.printf "FAIL cross-domain instance: %s\n" (pp_diags ds);
            exit 1
        | Ok _ -> Printf.printf "ok   cross-domain instance reference\n"));

  (* Cross-domain predicate call. *)
  (let src = {|domain core:
  predicate is_high on { V: Int }: V > 100

domain shipping:
  schema Order:
    - V: Int default 1
    - Risk = core.is_high(self)
|} in
   match parse src with
   | Error ds ->
       Printf.printf "FAIL cross-domain pred: parse %s\n" (pp_diags ds);
       exit 1
   | Ok p ->
       (match IDSL.Typecheck.run p with
        | Error ds ->
            Printf.printf "FAIL cross-domain pred: %s\n" (pp_diags ds);
            exit 1
        | Ok _ -> Printf.printf "ok   cross-domain predicate call\n"));

  (* Enum tags are domain-local: same tag name can appear in two
     domains without colliding.  Inside a single domain, dup tags
     across schemas are still rejected. *)
  assert_tc_ok "enum tag domain-local: same name in two domains"
    {|domain a:
  schema S:
    - K: {Active, Closed}
domain b:
  schema T:
    - K: {Active, Closed}
|};

  assert_tc_err "enum tag clash inside one domain"
    "tags must be unique within a domain"
    {|domain a:
  schema S:
    - K: {Active, Closed}
  schema T:
    - K2: {Active, Pending}
|};

  (let src = {|@action notify(payload: String)

schema Order:
  - V: Int default 1

rule big on Order:
  when:
    V > 0
  then:
    notify("ops")

test "exact string still works":
  given Order:
    V = 5
  expect:
    notify("ops")

@action emit(p: String)

rule emit_kvs on Order:
  when:
    V > 0
  then:
    emit("just-a-test")
|} in
   match parse src with
   | Error ds -> Printf.printf "FAIL partial: parse %s\n" (pp_diags ds); exit 1
   | Ok p ->
       (match IDSL.Typecheck.run p with
        | Error ds ->
            Printf.printf "FAIL partial: tc %s\n" (pp_diags ds); exit 1
        | Ok tp ->
            let results, _ = IDSL.Eval.run_all tp in
            if List.for_all (fun r -> r.IDSL.Eval.passed) results
            then Printf.printf "ok   expect: object partial match (smoke)\n"
            else (Printf.printf "FAIL partial smoke\n"; exit 1)));

  (let src = {|@action notify(team: String)

schema Order:
  - V: Int default 1

rule a on Order priority 10:
  when:
    V > 0
  then:
    notify("ops")

rule b on Order priority 5:
  when:
    V > 0
  then:
    notify("ops")

rule c on Order priority 1:
  when:
    V > 0
  then:
    notify("ops")

test "exact count":
  given Order:
    V = 5
  expect:
    notify("ops") times 3

test "at_least passes":
  given Order:
    V = 5
  expect:
    notify("ops") at_least 2

test "at_most passes":
  given Order:
    V = 5
  expect:
    notify("ops") at_most 5
|} in
   match parse src with
   | Error ds -> Printf.printf "FAIL count: parse %s\n" (pp_diags ds); exit 1
   | Ok p ->
       (match IDSL.Typecheck.run p with
        | Error ds ->
            Printf.printf "FAIL count: tc %s\n" (pp_diags ds); exit 1
        | Ok tp ->
            let results, _ = IDSL.Eval.run_all tp in
            if List.for_all (fun r -> r.IDSL.Eval.passed) results
            then Printf.printf "ok   expect: count assertions\n"
            else (Printf.printf "FAIL count\n";
                  List.iter (fun r ->
                    if not r.IDSL.Eval.passed then
                      List.iter (fun f -> Printf.printf "       %s\n" f) r.failures) results;
                  exit 1)));

  (let src = {|@action flag(s: String)
@action notify(t: String)

schema Order:
  - V: Int default 1

rule first on Order priority 10:
  when:
    V > 0
  then:
    flag("alert")

rule second on Order priority 1:
  when:
    V > 0
  then:
    notify("ops")

test "ordering":
  given Order:
    V = 1
  expect:
    flag("alert") before notify("ops")
    notify("ops") after flag("alert")
|} in
   match parse src with
   | Error ds -> Printf.printf "FAIL order: parse %s\n" (pp_diags ds); exit 1
   | Ok p ->
       (match IDSL.Typecheck.run p with
        | Error ds ->
            Printf.printf "FAIL order: tc %s\n" (pp_diags ds); exit 1
        | Ok tp ->
            let results, _ = IDSL.Eval.run_all tp in
            if List.for_all (fun r -> r.IDSL.Eval.passed) results
            then Printf.printf "ok   expect: before / after ordering\n"
            else (Printf.printf "FAIL order\n";
                  List.iter (fun r ->
                    if not r.IDSL.Eval.passed then
                      List.iter (fun f -> Printf.printf "       %s\n" f) r.failures) results;
                  exit 1)));

  (let src = {|@action flag(reason: String)

schema Order:
  - V: Int default 1

rule big on Order:
  when:
    V > 0
  then:
    flag("high-value contract: needs review")

test "regex matches reason text":
  given Order:
    V = 5
  expect:
    flag(r"high-value")
    flag(r"^high.*review$")

test "regex doesn't match unrelated text":
  given Order:
    V = 5
  expect:
    not flag(r"low-value")
|} in
   match parse src with
   | Error ds -> Printf.printf "FAIL regex: parse %s\n" (pp_diags ds); exit 1
   | Ok p ->
       (match IDSL.Typecheck.run p with
        | Error ds ->
            Printf.printf "FAIL regex: tc %s\n" (pp_diags ds); exit 1
        | Ok tp ->
            let results, _ = IDSL.Eval.run_all tp in
            if List.for_all (fun r -> r.IDSL.Eval.passed) results
            then Printf.printf "ok   expect: regex literal r\"...\"\n"
            else (Printf.printf "FAIL regex\n";
                  List.iter (fun r ->
                    if not r.IDSL.Eval.passed then
                      List.iter (fun f -> Printf.printf "       %s\n" f) r.failures) results;
                  exit 1)));

  (* Three-valued logic: a comparison whose operand is `missing`
     yields `missing`, which propagates through `not` / `and` / `or`
     / `if` / `==`. Rule when-blocks treat missing as false (rule
     does not fire). *)
  (let src = {|@action notify(team: String)

schema Order:
  - Cap: Money default $1
  - Required: Bool default true

rule no_cap_when_required on Order:
  when:
    Required
    Cap is missing
  then:
    notify("ops")

rule guarded_threshold on Order:
  when:
    Cap is missing or Cap > $1,000
  then:
    notify("review")

rule naive_threshold on Order:
  when:
    not (Cap > $1,000)
  then:
    notify("safe")

test "explicit missing probe fires":
  given Order:
    Required = true
  expect:
    notify("ops")

test "guarded threshold fires on missing":
  given Order:
    Required = true
  expect:
    notify("review")

test "naive threshold does NOT fire on missing (three-valued)":
  given Order:
    Required = true
  expect:
    not notify("safe")

test "naive threshold fires when value is well-defined and small":
  given Order:
    Required = true
    Cap = $500
  expect:
    notify("safe")
|} in
   match parse src with
   | Error ds ->
       Printf.printf "FAIL three-valued: parse %s\n" (pp_diags ds); exit 1
   | Ok p ->
       (match IDSL.Typecheck.run p with
        | Error ds ->
            Printf.printf "FAIL three-valued: tc %s\n" (pp_diags ds); exit 1
        | Ok tp ->
            let results, _ = IDSL.Eval.run_all tp in
            if List.for_all (fun r -> r.IDSL.Eval.passed) results
            then Printf.printf "ok   three-valued logic semantics\n"
            else begin
              Printf.printf "FAIL three-valued:\n";
              List.iter (fun r ->
                if not r.IDSL.Eval.passed then begin
                  Printf.printf "       %s\n" r.IDSL.Eval.rname;
                  List.iter (fun f ->
                    Printf.printf "         %s\n" f) r.failures
                end) results;
              exit 1
            end));

  (* End-to-end: predicate is callable from a derived field, runtime
     evaluates it against the schema's row, and the rule fires
     accordingly. *)
  (let src = {|@action notify(level: {Low, High})

predicate is_high_risk on { Value: Money, IsRenewal: Bool }:
  Value > $1,000,000 and not IsRenewal

schema Contract:
  - Value:      Money default $1
  - IsRenewal:  default true
  - IsHighRisk = is_high_risk(self)

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
  - Name: default "Alpha"
schema Contract:
  - Parties: default [Party]
|};

  assert_resolve_err "unknown schema ref"
    {|schema Contract:
  - Parties: default [Party]
|};

  assert_ok "derived fields"
    {|schema C:
  - DurationDays: default 365
  - IsLongTerm = DurationDays > 1825
  - Retention = (if Kind == Financial then 3650 else 1825)
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
  - Bad = any clause in Clauses where (clause.Kind == Indemnification
                                           and clause.Cap is missing)
|};

  assert_tc_ok "example file: contract_review"
    (let ic = open_in "../examples/contract_review.idsl" in
     let n = in_channel_length ic in
     let s = really_input_string ic n in
     close_in ic; s);

  assert_tc_ok "tc: well-typed schema + rule"
    {|schema C:
  - Kind: {NDA, MSA}
  - IsLong = true
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
  - Inner = true
rule r.x:
  when:
    Inner.NoSuch
  then:
    flag(red, "x")
|};

  assert_tc_err "tc: unknown field on schema" "no field"
    {|schema Sub:
  - X: default 1
schema C:
  - Inner: default [Sub]
  - Bad = any s in Inner: s.NotThere == 1
|};

  assert_tc_err "tc: bool + int" "+ requires"
    {|schema C:
  - Flag: default true
  - Bad = Flag + 1
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
