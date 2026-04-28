(* Identity-correctness regressions for `domain` blocks.

   Pin down the invariants that justify the canonical-qualified-key
   refactor:

   1. Two same-bare-name schemas in different domains keep distinct
      *runtime* identities — a `[Item]` reference inside `shipping.Order`
      must select the shipping schema, not be shadowed by `billing.Item`.

   2. Two same-bare-name instances in different domains do not collide in
      the runtime instance table.

   3. LSP `documentSymbol`'s selectionRange covers exactly the source
      token (`Item`), not the qualified label (`shipping.Item`). That is,
      the range length must equal `String.length "Item"`, not
      `String.length "shipping.Item"`.

   4. goto/rename on the bare token in source resolves to the right
      qualified symbol — clicking `Item` inside `shipping`'s body finds
      the `shipping.Item` decl, and rename emits an edit at the source
      token's actual span.

   These tests are deliberately written in a way that fails on the
   pre-refactor codebase. *)

open IDSL

let pass = ref 0
let fail = ref 0

let check label cond =
  if cond then begin
    incr pass;
    Printf.printf "ok   %s\n" label
  end else begin
    incr fail;
    Printf.printf "FAIL %s\n" label
  end

(* ---- 1+2: runtime identity isolation across domains ---- *)

let src_runtime = {|domain shipping:
  schema Item:
    - Weight: default 1
  schema Order:
    - Items: default [Item]

  @action ship(w: Int)

  rule r on Order:
    when:
      any it in Items: it.Weight > 0
    then:
      ship(1)

  test "shipping isolates Item from billing":
    given Order:
      Items = [{Weight: 5}]
    expect:
      ship(1)

domain billing:
  schema Item:
    - Price: default 1
|}

let test_runtime_identity_across_domains () =
  let s = Session.compile_string src_runtime in
  check "[id1] domain program compiles cleanly"
    (s.diagnostics = [] && s.typed <> None);
  match s.typed with
  | None -> ()
  | Some tp ->
      let results, _ = Eval.run_all tp in
      let r = List.hd results in
      List.iter (fun f -> Printf.printf "       failure: %s\n" f) r.failures;
      check "[id1] test passes — shipping.Item resolved correctly at runtime"
        r.passed

let test_instance_identity_across_domains () =
  let src = {|domain a:
  schema P:
    - K: default 1
  instance P I:
    K = 7

domain b:
  schema P:
    - K: default 1
  instance P I:
    K = 99
|} in
  let s = Session.compile_string src in
  check "[id2] dual-domain instances compile (no spurious dup)"
    (s.diagnostics = [] && s.typed <> None);
  match s.typed with
  | None -> ()
  | Some tp ->
      let ctx = Eval.make_ctx tp in
      let n = Hashtbl.length ctx.instances in
      check "[id2] runtime instance table has both instances (no overwrite)"
        (n = 2)

(* ---- 3: documentSymbol selectionRange uses bare token length ---- *)

let test_document_symbol_range_is_bare_token () =
  let src = {|domain shipping:
  schema Item:
    - K: default 1
|} in
  let s = Session.compile_string src in
  let idx = match Session.index s with
    | Some i -> i | None -> failwith "no index" in
  let syms = Lsp_query.document_symbols idx s.cst in
  let item =
    List.find_opt (fun (d : Lsp_query.doc_symbol) ->
      d.ds_name = "shipping.Item" || d.ds_name = "Item") syms in
  match item with
  | None -> check "[range] schema symbol present" false
  | Some d ->
      let span =
        d.ds_selection.sr_end.character - d.ds_selection.sr_start.character in
      check "[range] selectionRange covers exactly the bare token `Item`"
        (span = String.length "Item")

(* ---- 4: rename / goto resolve the qualified symbol via the bare token ---- *)

let test_rename_resolves_through_domain () =
  let src = "domain shipping:\n  schema Item:\n    - K: default 1\n" in
  let s = Session.compile_string src in
  let idx = match Session.index s with
    | Some i -> i | None -> failwith "no index" in
  (* Cursor on "Item" at line 1 (0-based), col 9 (after "  schema "). *)
  let edits =
    match Lsp_query.rename_at idx { line = 1; character = 9 }
            ~new_name:"Widget" with
    | Some es -> es
    | None -> [] in
  check "[rn] rename produces an edit on `Item`"
    (List.length edits >= 1);
  (* The first edit is the decl; its range must be exactly `Item`'s span. *)
  match edits with
  | [] -> ()
  | e :: _ ->
      let span =
        e.te_range.sr_end.character - e.te_range.sr_start.character in
      check "[rn] rename edit length = bare token (`Item`) length"
        (span = String.length "Item")

(* ---- 5: parser is reentrant (concurrent / nested parses don't collide) ---- *)

let test_parser_is_reentrant () =
  let s1 = "schema A:\n  - X: default 1\n" in
  let s2 = "schema B:\n  - Y: default true\n" in
  let r1 = Driver.parse_string s1 in
  let _r2 = Driver.parse_string s2 in
  (* After a second parse, r1's token list should still contain `A`,
     not be polluted by tokens from s2. *)
  let has_ident name (toks : Cst.tok list) =
    List.exists (fun (t : Cst.tok) ->
      match t.kind with Cst.Ident s -> s = name | _ -> false) toks
  in
  check "[reent] first parse retains its tokens after a second parse"
    (has_ident "A" r1.tokens && not (has_ident "B" r1.tokens))

(* Many threads parsing distinct programs concurrently; each thread's
   snapshot must contain only its own ident and its own decl name.
   This is the smoke test that the parse-state-via-mutex refactor
   actually serializes per call instead of sharing a process buffer. *)
let test_parser_concurrent_safety () =
  let n = 16 in
  let make i =
    Printf.sprintf "schema S%d:\n  - F%d: default %d\n" i i i
  in
  let outputs = Array.make n None in
  let threads = Array.init n (fun i ->
    Thread.create (fun () ->
      let r = Driver.parse_string (make i) in
      outputs.(i) <- Some r) ())
  in
  Array.iter Thread.join threads;
  let ok = ref true in
  for i = 0 to n - 1 do
    match outputs.(i) with
    | None -> ok := false
    | Some r ->
        let want = Printf.sprintf "S%d" i in
        let foreign = Printf.sprintf "S%d" ((i + 1) mod n) in
        let has name = List.exists (fun (t : Cst.tok) ->
          match t.kind with Cst.Ident s -> s = name | _ -> false) r.tokens in
        if not (has want) || has foreign then ok := false
  done;
  check "[reent] concurrent parses produce isolated snapshots" !ok

(* ---- driver ---- *)

let () =
  Printf.printf "\n--- domain identity regressions ---\n";
  test_runtime_identity_across_domains ();
  test_instance_identity_across_domains ();
  test_document_symbol_range_is_bare_token ();
  test_rename_resolves_through_domain ();
  test_parser_is_reentrant ();
  test_parser_concurrent_safety ();
  Printf.printf "%d passed, %d failed\n" !pass !fail;
  if !fail > 0 then exit 1
