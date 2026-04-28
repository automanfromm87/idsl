(* Regression tests for the Round-5/6/7 architecture changes.

   Each test pins down a specific cross-cutting behavior that is easy to
   "locally optimize" back into a bug:

     1. Multi-file include compiles cleanly through the workspace
        (regression for "include not resolved" reappearing).
     2. Unsaved cross-file edits propagate (regression for compile_doc
        reading from disk while an editor has unsaved changes).
     3. Named-instance evaluation works the same way across CLI / Web /
        LSP (regression for the Web-side `~instances` drop we already
        fixed once).
     4. Rename indexes references across included files (covers the
        Round-6 binder pass and confirms multi-file ref aggregation
        produces real edits — including any that span files).
*)

open IDSL

let tmpdir = ref ""
let cleanup_paths : string list ref = ref []

let setup_tmpdir () =
  tmpdir := Filename.temp_dir "idsl_ws_test" "";
  cleanup_paths := []

let write_file ~name ~content =
  let path = Filename.concat !tmpdir name in
  let oc = open_out path in
  output_string oc content;
  close_out oc;
  cleanup_paths := path :: !cleanup_paths;
  path

let teardown () =
  List.iter (fun p -> try Sys.remove p with _ -> ()) !cleanup_paths;
  (try Unix.rmdir !tmpdir with _ -> ());
  tmpdir := ""

(* Run `f` inside a freshly-created tmpdir, guaranteeing teardown even
   when an assertion in `f` raises. Without `Fun.protect` a failing
   test would leak the directory. *)
let with_tmp_workspace f =
  setup_tmpdir ();
  Fun.protect ~finally:teardown f

let read_file path =
  let ic = open_in path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () -> really_input_string ic (in_channel_length ic))

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

let check_eq label ~expected ~actual =
  let ok = expected = actual in
  if ok then begin
    incr pass;
    Printf.printf "ok   %s\n" label
  end else begin
    incr fail;
    Printf.printf "FAIL %s — expected %S, got %S\n" label expected actual
  end

(* ---------------- Test 1: multi-file include compiles cleanly ----- *)

let test_multifile_include () =
  with_tmp_workspace (fun () ->
    let path_a = write_file ~name:"a.idsl"
      ~content:"schema Inner:\n  - K: e.g. 1\n" in
    let path_main = write_file ~name:"main.idsl"
      ~content:"include \"a.idsl\"\n\nschema Outer:\n  - I: e.g. [Inner]\n" in
    let ws = Workspace.create () in
    let main_uri = "file://" ^ path_main in
    let a_uri    = "file://" ^ path_a in
    Workspace.put_doc ws ~uri:main_uri
      ~content:(read_file path_main) ~version:1;
    let s = Workspace.compile_doc ws ~uri:main_uri in
    check "[mf] no diagnostics on valid include"
      (s.diagnostics = []);
    check "[mf] typed program built (cross-file resolution)"
      (s.typed <> None);
    check "[mf] both schemas visible after include"
      (match s.ast with
       | Some prog ->
           let names = List.map (fun s -> s.Ast.sname) (Ast.schemas prog) in
           List.mem "Inner" names && List.mem "Outer" names
       | None -> false);
    check "[mf] dependency graph: a.idsl → main.idsl"
      (List.mem main_uri (Workspace.dependents_of ws ~uri:a_uri)))

(* ---------------- Test 2: unsaved cross-file edit propagates ------ *)

let test_unsaved_cross_file_edit () =
  setup_tmpdir ();
  let path_a = write_file ~name:"a.idsl"
    ~content:"schema Inner:\n  - K: e.g. 1\n" in
  let path_main = write_file ~name:"main.idsl"
    ~content:"include \"a.idsl\"\n\nschema Outer:\n  - I: e.g. [Inner]\n" in

  let ws = Workspace.create () in
  let main_uri = "file://" ^ path_main in
  let a_uri    = "file://" ^ path_a in

  (* First compile from disk to register the include edge. *)
  Workspace.put_doc ws ~uri:main_uri
    ~content:"include \"a.idsl\"\n\nschema Outer:\n  - I: e.g. [Inner]\n"
    ~version:1;
  let _ = Workspace.compile_doc ws ~uri:main_uri in

  (* Now open a.idsl in the editor with an unsaved extra field; the
     disk file still has just one. *)
  Workspace.put_doc ws ~uri:a_uri
    ~content:"schema Inner:\n  - K: e.g. 1\n  - L: e.g. true\n"
    ~version:1;
  let _ = Workspace.invalidate ws ~uri:a_uri in
  let s = Workspace.compile_doc ws ~uri:main_uri in

  let inner_field_count =
    match s.ast with
    | Some prog ->
        (match List.find_opt (fun s -> s.Ast.sname = "Inner")
                 (Ast.schemas prog) with
         | Some s -> List.length s.sfields
         | None -> -1)
    | None -> -1 in
  check "[edit] main sees the unsaved field added in a.idsl"
    (inner_field_count = 2);
  teardown ()

(* ---------------- Test 3: named instance three-way consistency ---- *)

(* Goal: the same source compiles to a typed program where `[Alpha]`
   resolves to the `Party Alpha` instance regardless of which entry
   point compiles it. *)
let test_named_instance_consistency () =
  let src = {|schema Party:
  - Name: e.g. "Alpha"

schema Contract:
  - Parties: e.g. [Party]

instance Party Alpha:
  Name = "Alpha"

@action notify(level: {Low|High})

rule R on Contract:
  when:
    any p in Parties: p.Name == "Alpha"
  then:
    notify(High)

test "uses-instance":
  given Contract:
    Parties = [Alpha]
  expect:
    notify(High)
|} in

  (* Path 1: CLI / direct Session.compile_string *)
  let s1 = Session.compile_string src in
  check "[ni] direct compile produces typed program" (s1.typed <> None);

  (* Path 2: Workspace.compile_doc on an in-memory URI (LSP path) *)
  let ws = Workspace.create () in
  let uri = "file:///tmp/ni_test.idsl" in
  Workspace.put_doc ws ~uri ~content:src ~version:1;
  let s2 = Workspace.compile_doc ws ~uri in
  check "[ni] workspace compile produces typed program"
    (s2.typed <> None);

  (* Both paths should see the same instance set. *)
  let inst_names s =
    match s.Session.typed with
    | Some tp ->
        List.map (fun (i : Typed.tinstance) -> i.ti_name) tp.instances
        |> List.sort compare
    | None -> [] in
  check_eq "[ni] CLI and LSP agree on instance set"
    ~expected:(String.concat "," (inst_names s1))
    ~actual:(String.concat "," (inst_names s2));

  (* Run the test block via the same evaluation pipeline both CLI
     (`bin/main.ml cmd_test`) and Web (`web/idsl_js.ml run_tests`) use. *)
  (match s1.typed with
   | None -> check "[ni] eval pipeline succeeds" false
   | Some tp ->
       let results, _ = Eval.run_all tp in
       let r = List.hd results in
       check "[ni] test passes when named instance resolves"
         r.Eval.passed)

(* ---------------- Test 4: cross-file rename coverage -------------- *)

(* Verifies that after a cross-file include is resolved via Workspace,
   the semantic index lists references whose source filename includes
   the included file (or the main file). This pins down the Round-6
   binder pass + Round-5/8 multi-file include behavior together: the
   rename-edit list must contain all sites the user expects to see. *)
let test_cross_file_rename () =
  setup_tmpdir ();
  let path_a = write_file ~name:"a.idsl"
    ~content:"schema Inner:\n  - K: e.g. 1\n" in
  let path_main = write_file ~name:"main.idsl"
    ~content:"include \"a.idsl\"\n\nschema Outer:\n  - Items: e.g. [Inner]\n" in

  let ws = Workspace.create () in
  let main_uri = "file://" ^ path_main in
  Workspace.put_doc ws ~uri:main_uri
    ~content:"include \"a.idsl\"\n\nschema Outer:\n  - Items: e.g. [Inner]\n"
    ~version:1;
  let s = Workspace.compile_doc ws ~uri:main_uri in
  let idx = match Session.index s with
    | Some i -> i
    | None -> failwith "no index" in

  (* Find Inner schema and ask the index for its references. The
     declaration lives in a.idsl; the reference (`[Inner]`) is in
     main.idsl. Each ref_site carries a Lexing.position whose
     pos_fname tells us which source file. *)
  let sym = Semantic_index.symbol_of_kind idx (Symbol.KSchema "Inner") in
  let refs = match sym with
    | Some s -> Semantic_index.references_of idx s
    | None -> [] in
  check "[rn] schema Inner is in the index" (sym <> None);
  check "[rn] cross-file reference is recorded"
    (List.length refs >= 1);

  (* The decl filename should be a.idsl, the ref filename should be
     main.idsl — that's the multi-file rename invariant. *)
  let decl_file = match sym with
    | Some s -> s.decl_pos.Lexing.pos_fname
    | None -> "" in
  let ref_files = List.map (fun (r : Semantic_index.ref_site) ->
    r.pos.Lexing.pos_fname) refs in
  check "[rn] decl pos points at a.idsl"
    (Filename.basename decl_file = "a.idsl");
  check "[rn] at least one ref points at main.idsl"
    (List.exists (fun f -> Filename.basename f = "main.idsl") ref_files);
  ignore path_a;
  teardown ()

(* ---------------- Test 5: instance resolver is per-call ----------- *)

(* Two sequential `build_env` calls with different instance tables must
   not contaminate each other.  Before #2, `Load.global_instances` was a
   module-level ref that `build_env` mutated — meaning the *second*
   call's `$ref "Alpha"` could resolve into the *first* call's table
   under unfortunate orderings.  This test pins the resolver to its
   per-call argument. *)
let test_instance_resolver_isolation () =
  let src = {|schema Party:
  - Name: e.g. "Alpha"

schema Wrap:
  - Inner: e.g. [Party]

instance Party Alpha:
  Name = "AlphaName"

instance Party Beta:
  Name = "BetaName"
|} in
  let s = Session.compile_string src in
  let tp = match s.typed with Some t -> t | None -> assert false in
  let ctx = Eval.make_ctx tp in

  (* Custom instance tables, each holding only one of the two. *)
  let only_alpha = Hashtbl.create 1 in
  Hashtbl.add only_alpha "Alpha"
    (Hashtbl.find ctx.instances "Alpha");
  let only_beta = Hashtbl.create 1 in
  Hashtbl.add only_beta "Beta"
    (Hashtbl.find ctx.instances "Beta");

  let json_with_alpha = Json.of_string
    {|{"Inner": [{"$ref": "Alpha"}]}|} in
  let json_with_beta = Json.of_string
    {|{"Inner": [{"$ref": "Beta"}]}|} in

  let load_with table j =
    try
      let _ = Load.build_env ~instances:table ctx.schemas "Wrap" j in
      `Ok
    with Load.Load_error m -> `Err m
  in
  check "[iso] alpha-only table resolves Alpha"
    (load_with only_alpha json_with_alpha = `Ok);
  check "[iso] alpha-only table rejects Beta"
    (load_with only_alpha json_with_beta = `Err "unknown instance reference \"Beta\"");
  check "[iso] beta-only table resolves Beta"
    (load_with only_beta json_with_beta = `Ok);
  check "[iso] beta-only table rejects Alpha"
    (load_with only_beta json_with_alpha = `Err "unknown instance reference \"Alpha\"");

  (* Sequential ordering must not matter — no global side-effect leaks. *)
  let _ = load_with only_alpha json_with_alpha in
  check "[iso] empty table after alpha-call rejects everything"
    (load_with (Hashtbl.create 0) json_with_alpha
     = `Err "unknown instance reference \"Alpha\"")

(* ---------------- Test 6: rename produces cross-file edits -------- *)

(* Phase-A regression: every Lsp_query.text_edit emitted by `rename_at`
   must carry the source filename so the LSP adapter can route the edit
   to the right URI. Without this, a rename of a schema declared in
   a.idsl would patch a.idsl correctly but dump the cross-file ref
   edits onto main.idsl's URI. *)
let test_rename_records_pos_fname () =
  setup_tmpdir ();
  let path_a = write_file ~name:"a.idsl"
    ~content:"schema Inner:\n  - K: e.g. 1\n" in
  let path_main = write_file ~name:"main.idsl"
    ~content:"include \"a.idsl\"\n\nschema Outer:\n  - I: e.g. [Inner]\n" in
  let ws = Workspace.create () in
  let main_uri = "file://" ^ path_main in
  Workspace.put_doc ws ~uri:main_uri
    ~content:"include \"a.idsl\"\n\nschema Outer:\n  - I: e.g. [Inner]\n"
    ~version:1;
  let s = Workspace.compile_doc ws ~uri:main_uri in
  let idx = match Session.index s with
    | Some i -> i | None -> failwith "no index" in

  (* Click on the `Inner` use site in main.idsl line 3 col 14; the
     symbol_at lookup matches it as a ref to schema Inner.  Rename to
     "Foo" should yield two edits — one in a.idsl (decl) and one in
     main.idsl (ref) — each tagged with the right pos_fname. *)
  let edits =
    match Lsp_query.rename_at idx
            { line = 3; character = 14 } ~new_name:"Foo" with
    | Some es -> es | None -> [] in
  check "[xrn] rename produced edits" (List.length edits >= 2);
  let by_basename = List.map (fun (e : Lsp_query.text_edit) ->
    Filename.basename e.te_pos_fname) edits in
  check "[xrn] one edit tagged with a.idsl"
    (List.mem "a.idsl" by_basename);
  check "[xrn] one edit tagged with main.idsl"
    (List.mem "main.idsl" by_basename);
  ignore path_a;
  teardown ()

(* ---------------- Test 7: call_item carries pos_fname ------------- *)

let test_call_item_records_pos_fname () =
  setup_tmpdir ();
  let path_actions = write_file ~name:"actions.idsl"
    ~content:"@action notify(level: {Low|High})\n" in
  let path_main = write_file ~name:"main.idsl"
    ~content:{|include "actions.idsl"

schema Order:
  - V: e.g. 1

rule R on Order:
  when:
    V > 0
  then:
    notify(High)
|} in
  let ws = Workspace.create () in
  let main_uri = "file://" ^ path_main in
  Workspace.put_doc ws ~uri:main_uri
    ~content:(read_file path_main)
    ~version:1;
  let s = Workspace.compile_doc ws ~uri:main_uri in
  let idx = match Session.index s with
    | Some i -> i | None -> failwith "no index" in

  (* Cursor on `notify` in main.idsl line 9 — incoming-calls should
     report the rule R as a caller; outgoing for R should report
     notify.  Each call_item must carry pos_fname so the adapter can
     route the result to the correct file. *)
  let it = match Lsp_query.prepare_call_hierarchy idx
                   { line = 9; character = 4 } with
    | Some it -> it
    | None -> failwith "no call item" in
  check "[ch] call_item.ci_pos_fname is non-empty"
    (it.ci_pos_fname <> "");
  check "[ch] notify decl points at actions.idsl"
    (Filename.basename it.ci_pos_fname = "actions.idsl");

  ignore path_actions;
  teardown ()

(* ---------------- Test 8: rename works *from* an included file ---- *)

(* Phase-B regression: standing in a.idsl (the included file) and
   asking for "find references" or "rename" must walk reverse-deps so
   the answer includes uses inside main.idsl.  Without aggregation,
   a.idsl's own session sees only its declaration. *)
let test_rename_from_included_file () =
  setup_tmpdir ();
  let path_a = write_file ~name:"a.idsl"
    ~content:"schema Inner:\n  - K: e.g. 1\n" in
  let path_main = write_file ~name:"main.idsl"
    ~content:"include \"a.idsl\"\n\nschema Outer:\n  - I: e.g. [Inner]\n" in
  let ws = Workspace.create () in
  let main_uri = "file://" ^ path_main in
  let a_uri    = "file://" ^ path_a in

  (* Open both and compile main first so the dep edge is registered. *)
  Workspace.put_doc ws ~uri:main_uri
    ~content:"include \"a.idsl\"\n\nschema Outer:\n  - I: e.g. [Inner]\n"
    ~version:1;
  Workspace.put_doc ws ~uri:a_uri
    ~content:"schema Inner:\n  - K: e.g. 1\n"
    ~version:1;
  let _ = Workspace.compile_doc ws ~uri:main_uri in

  (* Now query rename *from a.idsl's perspective* — cursor on `Inner`
     in the schema declaration line 0 col 7. *)
  let s_a = Workspace.compile_doc ws ~uri:a_uri in
  let idx_a = match Session.index s_a with
    | Some i -> i | None -> failwith "no a.idsl index" in
  let refs sym =
    Workspace.aggregated_references ws ~current_uri:a_uri sym in
  let edits = match Lsp_query.rename_at ~refs idx_a
                       { line = 0; character = 7 } ~new_name:"Foo" with
    | Some es -> es | None -> [] in
  let by_basename = List.map (fun (e : Lsp_query.text_edit) ->
    Filename.basename e.te_pos_fname) edits in
  check "[bk] rename from a.idsl produced ≥ 2 edits"
    (List.length edits >= 2);
  check "[bk] rename from a.idsl includes a.idsl decl"
    (List.mem "a.idsl" by_basename);
  check "[bk] rename from a.idsl includes main.idsl ref"
    (List.mem "main.idsl" by_basename);
  ignore path_a;
  teardown ()

(* ---------------- Driver ------------------------------------------ *)

(* ---------------- Test 9: workspace folder scan covers closed files - *)

(* Phase-C regression: workspace-level capabilities (workspace/symbol,
   willRenameFiles) must cover *.idsl files under workspace folders
   even when the editor hasn't opened them. *)
let test_folder_scan_includes_closed_files () =
  setup_tmpdir ();
  let path_a = write_file ~name:"a.idsl"
    ~content:"schema OnlyOnDisk:\n  - K: e.g. 1\n" in
  let path_b = write_file ~name:"b.idsl"
    ~content:"schema AlsoOnDisk:\n  - X: e.g. true\n" in

  let ws = Workspace.create () in
  Workspace.set_folders ws ["file://" ^ !tmpdir];

  (* No put_doc calls — both files are closed. *)
  let scanned = Workspace.scan_folder_files ws in
  let basenames = List.map Filename.basename scanned |> List.sort compare in
  check_eq "[fs] folder scan finds both files"
    ~expected:"a.idsl,b.idsl"
    ~actual:(String.concat "," basenames);

  let known = Workspace.all_known_uris ws in
  check "[fs] all_known_uris >= 2"
    (List.length known >= 2);

  let compiled = Workspace.compile_all_known ws in
  let names_seen = List.concat_map (fun (_uri, (s : Session.t)) ->
    match s.ast with
    | Some prog ->
        List.map (fun s -> s.IDSL.Ast.sname) (IDSL.Ast.schemas prog)
    | None -> []) compiled
    |> List.sort compare in
  check "[fs] compile_all_known sees OnlyOnDisk"
    (List.mem "OnlyOnDisk" names_seen);
  check "[fs] compile_all_known sees AlsoOnDisk"
    (List.mem "AlsoOnDisk" names_seen);
  ignore path_a; ignore path_b;
  teardown ()

(* ---------------- Driver ------------------------------------------ *)

(* ---------------- Test 10: rename across two-hop include chain ---- *)

(* Regression: aggregated_references must walk the full transitive
   reverse-dep closure, not just direct parents.  For the chain
       a.idsl  ←  b.idsl  ←  main.idsl
   standing in a.idsl on `Inner` and asking for rename must produce
   edits in *all three* files. *)
let test_rename_two_hop_includes () =
  setup_tmpdir ();
  let path_a = write_file ~name:"a.idsl"
    ~content:"schema Inner:\n  - K: e.g. 1\n" in
  let path_b = write_file ~name:"b.idsl"
    ~content:"include \"a.idsl\"\n\nschema Mid:\n  - X: e.g. [Inner]\n" in
  let path_main = write_file ~name:"main.idsl"
    ~content:"include \"b.idsl\"\n\nschema Top:\n  - Y: e.g. [Inner]\n" in
  let ws = Workspace.create () in
  let main_uri = "file://" ^ path_main in
  let b_uri    = "file://" ^ path_b in
  let a_uri    = "file://" ^ path_a in
  Workspace.put_doc ws ~uri:main_uri ~content:(read_file path_main) ~version:1;
  Workspace.put_doc ws ~uri:b_uri    ~content:(read_file path_b)    ~version:1;
  Workspace.put_doc ws ~uri:a_uri    ~content:(read_file path_a)    ~version:1;
  let _ = Workspace.compile_doc ws ~uri:main_uri in
  let _ = Workspace.compile_doc ws ~uri:b_uri in

  (* Rename `Inner` from a.idsl's perspective. *)
  let s_a = Workspace.compile_doc ws ~uri:a_uri in
  let idx_a = match Session.index s_a with
    | Some i -> i | None -> failwith "no a.idsl index" in
  let refs sym =
    Workspace.aggregated_references ws ~current_uri:a_uri sym in
  let edits = match Lsp_query.rename_at ~refs idx_a
                       { line = 0; character = 7 } ~new_name:"Foo" with
    | Some es -> es | None -> [] in
  let by_basename = List.map (fun (e : Lsp_query.text_edit) ->
    Filename.basename e.te_pos_fname) edits |> List.sort_uniq compare in
  check "[2hop] rename from a.idsl reaches a.idsl"
    (List.mem "a.idsl" by_basename);
  check "[2hop] rename from a.idsl reaches b.idsl"
    (List.mem "b.idsl" by_basename);
  check "[2hop] rename from a.idsl reaches main.idsl (transitive)"
    (List.mem "main.idsl" by_basename);
  ignore path_a; ignore path_b;
  teardown ()

(* ---------------- Test 11: documentSymbol filters by file --------- *)

let test_document_symbol_only_local_file () =
  setup_tmpdir ();
  let path_a = write_file ~name:"a.idsl"
    ~content:"schema Inner:\n  - K: e.g. 1\n" in
  let path_main = write_file ~name:"main.idsl"
    ~content:"include \"a.idsl\"\n\nschema Outer:\n  - I: e.g. [Inner]\n" in
  let ws = Workspace.create () in
  let main_uri = "file://" ^ path_main in
  Workspace.put_doc ws ~uri:main_uri ~content:(read_file path_main) ~version:1;
  let s = Workspace.compile_doc ws ~uri:main_uri in
  let idx = match Session.index s with
    | Some i -> i | None -> failwith "no index" in

  (* Without a filter the index returns both `Inner` and `Outer`. *)
  let unfiltered = Lsp_query.document_symbols idx s.cst in
  let names_unfiltered = List.map (fun (s : Lsp_query.doc_symbol) -> s.ds_name)
                           unfiltered in
  check "[ds] unfiltered outline contains Inner (from include)"
    (List.mem "Inner" names_unfiltered);

  (* With ?in_file:main, the outline must NOT include Inner. *)
  let filtered = Lsp_query.document_symbols ~in_file:path_main idx s.cst in
  let names = List.map (fun (s : Lsp_query.doc_symbol) -> s.ds_name) filtered in
  check "[ds] filtered outline contains Outer"
    (List.mem "Outer" names);
  check "[ds] filtered outline EXCLUDES Inner (declared in a.idsl)"
    (not (List.mem "Inner" names));
  ignore path_a;
  teardown ()

(* ---------------- Test 12: domain blocks scope same-name decls ---- *)

(* `domain shipping: schema Item …` and `domain billing: schema Item …`
   should both compile cleanly — qualified names in the index keep the
   two distinct.  Without scope semantics, this would error as
   `duplicate schema "Item"`. *)
let test_domain_scopes_same_name () =
  let src = {|domain shipping:
  schema Item:
    - X: e.g. 1

domain billing:
  schema Item:
    - Y: e.g. true
|} in
  let s = IDSL.Session.compile_string src in
  check "[dom] same-name schemas in two domains compile"
    (s.diagnostics = [] && s.typed <> None);

  match Session.index s with
  | None -> check "[dom] index built" false
  | Some idx ->
      let names = IDSL.Semantic_index.all_symbols idx
        |> List.filter (fun s ->
             match s.IDSL.Symbol.kind with
             | KSchema _ -> true | _ -> false)
        |> List.map (fun s -> s.IDSL.Symbol.label)
        |> List.sort compare in
      check "[dom] both qualified schemas appear in the index"
        (names = ["schema billing.Item"; "schema shipping.Item"])

(* ---------------- Test 13: domain prevents cross-domain leakage --- *)

let test_domain_blocks_cross_reference () =
  let src = {|domain shipping:
  schema Item:
    - X: e.g. 1

domain billing:
  schema Invoice:
    - Lines: e.g. [Item]   (* should fail — Item is in shipping *)
|} in
  let s = IDSL.Session.compile_string src in
  check "[dom-x] cross-domain reference is rejected"
    (s.diagnostics <> [])

(* ---------- Test 14: didChange semantics — empty buffers + version order ---- *)

(* Regression for two long-life-server bugs:

   - Emptying the buffer (Ctrl-A + Delete) is a legitimate edit;
     `put_doc_versioned` must accept an empty content, not silently
     discard it.

   - Out-of-order didChange notifications (re-deliveries via plugin
     bridges, proxy retries) must not roll the document back: a smaller
     incoming version is stale and must be rejected.  Equal versions
     are idempotent re-deliveries and may be re-applied without harm. *)
let test_versioned_put_doc () =
  let ws = Workspace.create () in
  let uri = "file:///tmp/v_test.idsl" in
  (match Workspace.put_doc_versioned ws ~uri ~content:"schema A:\n  - K: e.g. 1\n"
           ~version:1 with
   | `Updated -> check "[ver] initial put accepted" true
   | `Stale _ -> check "[ver] initial put accepted" false);

  (* Newer version overwrites. *)
  (match Workspace.put_doc_versioned ws ~uri ~content:"schema B:\n  - K: e.g. 1\n"
           ~version:5 with
   | `Updated -> check "[ver] newer put accepted" true
   | `Stale _ -> check "[ver] newer put accepted" false);
  let cur1 = match Workspace.get_doc ws ~uri with
    | Some d -> d.content | None -> "" in
  check "[ver] doc holds the v=5 content"
    (cur1 = "schema B:\n  - K: e.g. 1\n");

  (* Stale (older) version is dropped. *)
  (match Workspace.put_doc_versioned ws ~uri ~content:"schema STALE:\n  - K: e.g. 1\n"
           ~version:2 with
   | `Stale n -> check "[ver] stale put rejected (current=5)" (n = 5)
   | `Updated -> check "[ver] stale put rejected" false);
  let cur2 = match Workspace.get_doc ws ~uri with
    | Some d -> d.content | None -> "" in
  check "[ver] stale put did not overwrite"
    (cur2 = "schema B:\n  - K: e.g. 1\n");

  (* Empty content at a newer version is a *legitimate* edit
     (regression: the bin used to skip empty `updated`). *)
  (match Workspace.put_doc_versioned ws ~uri ~content:""
           ~version:6 with
   | `Updated -> check "[ver] empty content accepted at v=6" true
   | `Stale _ -> check "[ver] empty content accepted at v=6" false);
  let cur3 = match Workspace.get_doc ws ~uri with
    | Some d -> d.content | None -> "" in
  check "[ver] empty content stored verbatim"
    (cur3 = "")

(* ---------- Test 15: doc-removal hooks fire on remove_doc ---- *)

(* `last_good` and similar per-doc caches in the LSP binary subscribe
   via `Workspace.on_remove`; a missed callback keeps stale typed
   programs alive forever and grows the table without bound. *)
let test_remove_hook_fires () =
  let ws = Workspace.create () in
  let removed = ref [] in
  Workspace.on_remove ws (fun ~uri -> removed := uri :: !removed);
  let uri = "file:///tmp/hook_test.idsl" in
  Workspace.put_doc ws ~uri ~content:"schema A:\n  - K: e.g. 1\n" ~version:1;
  let _ = Workspace.compile_doc ws ~uri in
  Workspace.remove_doc ws ~uri;
  check "[hook] on_remove fired with the closed URI"
    (!removed = [uri]);
  check "[hook] doc table no longer holds the URI"
    (Workspace.get_doc ws ~uri = None)

(* ---------- Test 16: watched-file delete preserves open docs --------- *)

(* Two long-running-server failure modes that the new
   `Workspace.handle_watched_change` is meant to prevent:

   - `delete` on a path the editor still has open should NOT erase the
     in-memory doc.  The disk delete is irrelevant when the buffer is
     authoritative; throwing away the doc would also strand every
     dependent file.

   - `delete` on a path that is *not* open must still notify open
     parents so they re-publish diagnostics for the now-missing
     include — dependents are snapshotted before remove_doc runs. *)
let test_watched_delete_preserves_open_docs () =
  setup_tmpdir ();
  let path_a = write_file ~name:"a.idsl"
    ~content:"schema Inner:\n  - K: e.g. 1\n" in
  let path_main = write_file ~name:"main.idsl"
    ~content:"include \"a.idsl\"\n\nschema Outer:\n  - I: e.g. [Inner]\n" in
  let ws = Workspace.create () in
  let main_uri = "file://" ^ path_main in
  let a_uri    = "file://" ^ path_a in
  Workspace.put_doc ws ~uri:main_uri ~content:(read_file path_main) ~version:1;
  Workspace.put_doc ws ~uri:a_uri    ~content:(read_file path_a)    ~version:1;
  let _ = Workspace.compile_doc ws ~uri:main_uri in

  (* Simulate a disk delete of a.idsl *while* the editor still has it
     open. The in-memory doc is authoritative. *)
  let to_publish =
    Workspace.handle_watched_change ws ~uri:a_uri ~change:Workspace.Deleted in
  check "[wd] open doc survives disk-delete notification"
    (Workspace.get_doc ws ~uri:a_uri <> None);
  check "[wd] dependent main is in the re-publish set"
    (List.mem main_uri to_publish);

  teardown ()

let test_watched_delete_unopened_notifies_dependents () =
  setup_tmpdir ();
  let path_a = write_file ~name:"a.idsl"
    ~content:"schema Inner:\n  - K: e.g. 1\n" in
  let path_main = write_file ~name:"main.idsl"
    ~content:"include \"a.idsl\"\n\nschema Outer:\n  - I: e.g. [Inner]\n" in
  let ws = Workspace.create () in
  let main_uri = "file://" ^ path_main in
  let a_uri    = "file://" ^ path_a in
  (* Only main is opened; a.idsl is closed but on disk. *)
  Workspace.put_doc ws ~uri:main_uri ~content:(read_file path_main) ~version:1;
  let _ = Workspace.compile_doc ws ~uri:main_uri in

  (* Sanity: dep edge exists pre-delete. *)
  check "[wd2] dep edge registered"
    (List.mem main_uri (Workspace.dependents_of ws ~uri:a_uri));

  let to_publish =
    Workspace.handle_watched_change ws ~uri:a_uri ~change:Workspace.Deleted in
  check "[wd2] closed file's doc entry is removed"
    (Workspace.get_doc ws ~uri:a_uri = None);
  check "[wd2] open dependent main is still in publish set"
    (List.mem main_uri to_publish);
  ignore path_a;
  teardown ()

(* ---------- Test 17+18: subprocess-driven LSP protocol coverage ----- *)

let lsp_bin =
  let candidates = [
    "../bin/idsl_lsp.exe";
    "_build/default/bin/idsl_lsp.exe";
    "bin/idsl_lsp.exe";
  ] in
  List.find_opt Sys.file_exists candidates

let frame body =
  Printf.sprintf "Content-Length: %d\r\n\r\n%s"
    (String.length body) body

let init_msg = frame
  {|{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}|}
let exit_msg = frame
  {|{"jsonrpc":"2.0","method":"exit","params":null}|}

let contains haystack needle =
  try
    let _ = Str.search_forward (Str.regexp_string needle) haystack 0 in
    true
  with Not_found -> false

let id_match n =
  Printf.sprintf "\"id\"[ \t]*:[ \t]*%d" n

let contains_re haystack pat =
  try let _ = Str.search_forward (Str.regexp pat) haystack 0 in true
  with Not_found -> false

(* Spawn the LSP, feed `input`, return stdout. stderr is redirected to
   `/dev/null` so the child can never block on a full stderr pipe (the
   server logs every bad frame and exception, which adds up fast). *)
let collect_responses ~bin ~input ~deadline_s : string =
  let in_r,  in_w  = Unix.pipe () in
  let out_r, out_w = Unix.pipe () in
  let dev_null = Unix.openfile "/dev/null" [O_WRONLY] 0 in
  let pid = Unix.create_process bin [| bin |] in_r out_w dev_null in
  Unix.close in_r;
  Unix.close out_w;
  Unix.close dev_null;
  let in_oc = Unix.out_channel_of_descr in_w in
  output_string in_oc input;
  close_out in_oc;
  let buf = Buffer.create 4096 in
  let chunk = Bytes.create 4096 in
  let deadline = Unix.gettimeofday () +. deadline_s in
  let rec drain () =
    if Unix.gettimeofday () > deadline then ()
    else
      let r, _, _ = Unix.select [out_r] [] [] 0.5 in
      if r = [] then drain ()
      else
        match Unix.read out_r chunk 0 (Bytes.length chunk) with
        | 0 -> ()
        | n -> Buffer.add_subbytes buf chunk 0 n; drain ()
        | exception _ -> ()
  in
  drain ();
  let _ = Unix.waitpid [] pid in
  Unix.close out_r;
  Buffer.contents buf

let with_lsp ~tag ~input ~deadline_s f =
  match lsp_bin with
  | None -> check (tag ^ " LSP binary present") false
  | Some bin -> f (collect_responses ~bin ~input ~deadline_s)

(* A truncated body would steal bytes from subsequent frames and isn't
   recoverable in any LSP server, so we don't exercise it here. *)
let test_lsp_framing_survives_bad_frames () =
  let bad_negative = "Content-Length: -7\r\n\r\n" in
  let bad_huge     = "Content-Length: 999999999999\r\n\r\n" in
  let bad_json     = frame "{not json" in
  let input = bad_negative ^ bad_huge ^ bad_json ^ init_msg ^ exit_msg in
  with_lsp ~tag:"[frame]" ~input ~deadline_s:5.0 (fun out ->
    check "[frame] server survived bad frames and responded to initialize"
      (contains_re out (id_match 1)))

let test_lsp_method_not_found () =
  let unknown = frame
    {|{"jsonrpc":"2.0","id":42,"method":"textDocument/totallyMadeUp","params":{}}|} in
  with_lsp ~tag:"[mnf]"
    ~input:(init_msg ^ unknown ^ exit_msg) ~deadline_s:5.0 (fun out ->
    check "[mnf] server returned an error envelope for unknown method"
      (contains out "-32601");
    check "[mnf] error response carries the original request id (42)"
      (contains_re out (id_match 42)))

let test_lsp_shutdown_gates_requests () =
  let shutdown = frame
    {|{"jsonrpc":"2.0","id":2,"method":"shutdown","params":null}|} in
  let post = frame
    {|{"jsonrpc":"2.0","id":3,"method":"textDocument/documentSymbol","params":{"textDocument":{"uri":"file:///x.idsl"}}}|} in
  with_lsp ~tag:"[sg]"
    ~input:(init_msg ^ shutdown ^ post ^ exit_msg) ~deadline_s:5.0 (fun out ->
    check "[sg] post-shutdown request gets -32600"
      (contains out "-32600");
    check "[sg] post-shutdown error envelope carries id 3"
      (contains_re out (id_match 3)))

(* Client refuses dynamic registration; workspace/symbol must still
   succeed (server falls back to per-request rescans). *)
let test_lsp_watcher_rejection_does_not_crash () =
  let initialized = frame
    {|{"jsonrpc":"2.0","method":"initialized","params":{}}|} in
  let reg_error = frame
    {|{"jsonrpc":"2.0","id":"watcher-registration","error":{"code":-32601,"message":"dynamic registration not supported"}}|} in
  let ws_sym = frame
    {|{"jsonrpc":"2.0","id":99,"method":"workspace/symbol","params":{"query":""}}|} in
  let input = init_msg ^ initialized ^ reg_error ^ ws_sym ^ exit_msg in
  with_lsp ~tag:"[wr]" ~input ~deadline_s:5.0 (fun out ->
    check "[wr] server kept processing after watcher rejection"
      (contains_re out (id_match 99));
    check "[wr] server did not emit an internal-error for the rejection"
      (not (contains out "-32603")))

(* ---------- Test 19: URI encoding round-trips ----------

   Real LSP clients send file URIs with percent-encoding, an optional
   `localhost` authority, and (rarely, via bridges) a trailing fragment
   or query.  All four must decode to the same path the workspace uses
   internally; the encode side has to round-trip through decode. *)
let test_uri_encoding () =
  let cases = [
    "file:///tmp/plain.idsl",                   "/tmp/plain.idsl";
    "file:///tmp/My%20Spec.idsl",               "/tmp/My Spec.idsl";
    "file:///tmp/%E4%BE%8B.idsl",               "/tmp/\xe4\xbe\x8b.idsl";
    "file://localhost/tmp/x.idsl",              "/tmp/x.idsl";
    "file:///tmp/x.idsl#frag",                  "/tmp/x.idsl";
    "file:///tmp/x.idsl?q=1",                   "/tmp/x.idsl";
  ] in
  List.iter (fun (uri, expected) ->
    let got = Workspace.path_of_uri uri in
    check (Printf.sprintf "[uri] decode %s" uri)
      (got = expected)) cases;
  (* Encode then decode must round-trip, including non-ASCII. *)
  let paths = [
    "/tmp/plain.idsl";
    "/tmp/My Spec.idsl";
    "/tmp/\xe4\xbe\x8b.idsl";
    "/tmp/path with #hash.idsl";
  ] in
  List.iter (fun p ->
    let encoded = Workspace.uri_of_path p in
    let decoded = Workspace.path_of_uri encoded in
    check (Printf.sprintf "[uri] round-trip %S" p)
      (decoded = p)) paths

(* ---------- Test 20: symlink cycle protection ----------

   A workspace folder containing a symlink to one of its ancestors
   used to make scan_folder_files recurse forever (or until stack
   overflow). Visited-set + lstat-aware traversal should walk it once
   and stop. *)
let test_symlink_cycle () =
  setup_tmpdir ();
  let outer = !tmpdir in
  let inner = Filename.concat outer "sub" in
  Unix.mkdir inner 0o755;
  let _ = write_file ~name:"a.idsl"
    ~content:"schema A:\n  - K: e.g. 1\n" in
  let _ = write_file ~name:"sub/b.idsl"
    ~content:"schema B:\n  - K: e.g. 1\n" in
  (* Create a self-referential symlink: sub/loop -> ../sub *)
  Unix.symlink "../sub" (Filename.concat inner "loop");

  let ws = Workspace.create () in
  Workspace.set_folders ws ["file://" ^ outer];

  (* Without cycle protection this hangs / stack-overflows. With
     protection it returns at most O(real files) entries. *)
  let scanned = Workspace.scan_folder_files ws in
  check "[cycle] scan completes despite symlink loop"
    (List.length scanned >= 2 && List.length scanned < 100);
  let basenames = List.map Filename.basename scanned
                  |> List.sort_uniq compare in
  check "[cycle] both real files surfaced"
    (List.mem "a.idsl" basenames && List.mem "b.idsl" basenames);
  teardown ()

(* ---------- Test 21: closed-file cache invalidated when watcher fails -- *)

(* The fallback for a watcher-less server isn't just "rescan the
   folder" — closed files whose content changes on disk must also have
   their compile cache evicted, otherwise workspace/symbol returns
   ASTs from a Session.t that's been stale since startup. *)
let test_drop_closed_doc_cache () =
  setup_tmpdir ();
  let path_a = write_file ~name:"a.idsl"
    ~content:"schema Old:\n  - K: e.g. 1\n" in
  let ws = Workspace.create () in
  let a_uri = "file://" ^ path_a in

  (* Compile while a.idsl is closed (no put_doc). *)
  let s1 = Workspace.compile_doc ws ~uri:a_uri in
  let names1 =
    match s1.ast with
    | Some prog -> List.map (fun s -> s.Ast.sname) (Ast.schemas prog)
    | None -> [] in
  check "[stale] initial compile sees Old"
    (List.mem "Old" names1);

  (* Disk changes while watcher would normally tell us; simulate the
     watcher being unavailable by *not* invalidating manually. *)
  let oc = open_out path_a in
  output_string oc "schema New:\n  - K: e.g. 1\n";
  close_out oc;

  (* Without intervention, compile_doc returns the cached Old session. *)
  let s2 = Workspace.compile_doc ws ~uri:a_uri in
  let names2 =
    match s2.ast with
    | Some prog -> List.map (fun s -> s.Ast.sname) (Ast.schemas prog)
    | None -> [] in
  check "[stale] without invalidation, cache returns stale Old"
    (List.mem "Old" names2);

  (* drop_closed_doc_cache must force a re-compile next time. *)
  Workspace.drop_closed_doc_cache ws;
  let s3 = Workspace.compile_doc ws ~uri:a_uri in
  let names3 =
    match s3.ast with
    | Some prog -> List.map (fun s -> s.Ast.sname) (Ast.schemas prog)
    | None -> [] in
  check "[stale] after drop_closed_doc_cache, re-compile sees New"
    (List.mem "New" names3 && not (List.mem "Old" names3));

  (* Open docs are *not* dropped — their in-memory text is authoritative. *)
  let path_b = write_file ~name:"b.idsl"
    ~content:"schema OnDisk:\n  - K: e.g. 1\n" in
  let b_uri = "file://" ^ path_b in
  Workspace.put_doc ws ~uri:b_uri
    ~content:"schema InMem:\n  - K: e.g. 1\n" ~version:1;
  let _ = Workspace.compile_doc ws ~uri:b_uri in
  Workspace.drop_closed_doc_cache ws;
  let s4 = Workspace.compile_doc ws ~uri:b_uri in
  let names4 =
    match s4.ast with
    | Some prog -> List.map (fun s -> s.Ast.sname) (Ast.schemas prog)
    | None -> [] in
  check "[stale] open doc cache survives the drop"
    (List.mem "InMem" names4);
  teardown ()

(* ---------- Test 22: didClose invalidates dependents -----------

   Scenario: a.idsl is included by main.idsl and the user has both
   open with unsaved edits in a.idsl. They close a.idsl. main.idsl's
   compile cache reflects the *unsaved* a.idsl text and must be
   evicted, otherwise hover/diagnostics on main keep returning answers
   shaped by content the editor no longer has. *)
let test_didclose_invalidates_dependents () =
  setup_tmpdir ();
  let path_a = write_file ~name:"a.idsl"
    ~content:"schema OnDisk:\n  - K: e.g. 1\n" in
  let path_main = write_file ~name:"main.idsl"
    ~content:"include \"a.idsl\"\n\nschema Outer:\n  - I: e.g. [OnDisk]\n" in
  let ws = Workspace.create () in
  let a_uri    = "file://" ^ path_a in
  let main_uri = "file://" ^ path_main in

  (* Both open. a.idsl's in-memory content renames the schema. main's
     compile resolves [InMem] against the in-memory a.idsl. *)
  Workspace.put_doc ws ~uri:main_uri
    ~content:"include \"a.idsl\"\n\nschema Outer:\n  - I: e.g. [InMem]\n"
    ~version:1;
  Workspace.put_doc ws ~uri:a_uri
    ~content:"schema InMem:\n  - K: e.g. 1\n" ~version:1;
  let s_pre = Workspace.compile_doc ws ~uri:main_uri in
  check "[close] main compiles cleanly against in-memory a.idsl"
    (s_pre.diagnostics = []);

  (* didClose on a.idsl: the bin first walks dependents (drops main's
     cache), then removes a.idsl. *)
  let affected = Workspace.invalidate ws ~uri:a_uri in
  Workspace.remove_doc ws ~uri:a_uri;
  check "[close] invalidate surfaced main as a dependent"
    (List.mem main_uri affected);

  (* main re-compiles against the on-disk a.idsl (which has `OnDisk`,
     not `InMem`) — should now error because main's text references
     [InMem]. *)
  let s_post = Workspace.compile_doc ws ~uri:main_uri in
  check "[close] main re-compiled against disk and now sees the gap"
    (s_post.diagnostics <> []);
  teardown ()

(* ---------- Test 23: canonical URI keying --------------------------

   `file:///x.idsl` and `file://localhost/x.idsl` denote the same
   file; the workspace must collapse them so a putDoc under one form
   is observable through the other. *)
let test_canonical_uri_keying () =
  setup_tmpdir ();
  let path = write_file ~name:"shared.idsl"
    ~content:"schema A:\n  - K: e.g. 1\n" in
  let ws = Workspace.create () in
  let plain     = "file://"          ^ path in
  let localhost = "file://localhost" ^ path in
  Workspace.put_doc ws ~uri:plain ~content:"schema A:\n" ~version:1;
  check "[canon] put under file:/// is visible via file://localhost/"
    (Workspace.get_doc ws ~uri:localhost <> None);

  Workspace.put_doc ws ~uri:localhost
    ~content:"schema B:\n" ~version:2;
  let via_plain = match Workspace.get_doc ws ~uri:plain with
    | Some d -> d.content | None -> "" in
  check "[canon] update via localhost-form lands at the same identity"
    (via_plain = "schema B:\n");

  (* Compile under one form, hit cache under the other. *)
  let _ = Workspace.compile_doc ws ~uri:plain in
  Workspace.put_doc ws ~uri:plain
    ~content:"schema C:\n" ~version:3;
  let _ = Workspace.invalidate ws ~uri:localhost in
  let s = Workspace.compile_doc ws ~uri:localhost in
  let names =
    match s.ast with
    | Some prog -> List.map (fun s -> s.Ast.sname) (Ast.schemas prog)
    | None -> [] in
  check "[canon] invalidate via localhost drops the plain-form cache"
    (List.mem "C" names);
  teardown ()

(* ---------- Test 24: workspace folder canonicalization -----------

   Equivalent folder URIs (`file:///x`, `file://localhost/x`) must
   collapse to a single root in `set_folders`, and remove must work
   under either form. *)
let test_workspace_folder_canon () =
  let ws = Workspace.create () in
  Workspace.set_folders ws [
    "file:///tmp/proj";
    "file://localhost/tmp/proj";       (* same file as above *)
    "file:///tmp/other";
  ];
  let folders = Workspace.folders ws in
  check "[fold] equivalent folders collapse to one"
    (List.length folders = 2);
  check "[fold] only the canonical form is stored"
    (List.for_all (fun u ->
       match u with
       | "file:///tmp/proj" | "file:///tmp/other" -> true
       | _ -> false) folders);

  (* Re-set with localhost-form removal — canonicalization makes the
     compare match. *)
  Workspace.set_folders ws ["file://localhost/tmp/other"];
  check "[fold] subsequent set under different form still picks the canonical"
    (Workspace.folders ws = ["file:///tmp/other"])

(* ---------- Test 25: UTF-16 column on a non-ASCII line --------------

   Diagnostics / hints / outline ranges must use UTF-16 columns —
   i.e. a 4-byte UTF-8 character emits as 2 UTF-16 code units, and
   any column-after-it must reflect that.  The bin's wire writers
   route every range through `utf16_pos_to_json ~src`, so this test
   pins down the underlying conversion the writers depend on. *)
let test_utf16_column_on_non_ascii () =
  (* Line with a 3-byte UTF-8 char (例 = U+4F8B = ascii=1 BMP code unit). *)
  let src = "schema 例:\n  - K: e.g. 1\n" in
  let line = IDSL.Utf16.line_of_source src 0 in
  let byte_col_after = String.index src ':' in
  let utf16_col = IDSL.Utf16.utf16_of_byte_col line byte_col_after in
  (* "schema " (7 ascii) + "例" (1 BMP) → utf16 col 8 for the colon. *)
  check "[utf16] BMP non-ASCII counted as 1 UTF-16 unit" (utf16_col = 8);

  (* Round-trip: utf16 → byte must invert exactly. *)
  let back = IDSL.Utf16.byte_col_of_utf16 ~src ~line:0 utf16_col in
  check "[utf16] byte ↔ utf16 round-trip" (back = byte_col_after);

  (* Surrogate pair: 4-byte UTF-8 (𝄞 = U+1D11E) → 2 UTF-16 units. *)
  let src2 = "schema 𝄞:\n" in
  let line2 = IDSL.Utf16.line_of_source src2 0 in
  let byte_col2 = String.index src2 ':' in
  let utf16_col2 = IDSL.Utf16.utf16_of_byte_col line2 byte_col2 in
  (* "schema " (7) + "𝄞" (2 utf16 units) → col 9. *)
  check "[utf16] supplementary char counted as 2 UTF-16 units"
    (utf16_col2 = 9)

(* ---------- Test 26: Last_good keying is canonical ----------------

   Subprocess-driven: open a doc under one URI form, request something
   while the doc has a transient parse error and observe the fallback
   path stays consistent across equivalent URI forms. We can only
   validate the observable contract: the server doesn't crash and the
   document is still tracked under either form. *)
let test_last_good_canonical_keying () =
  match lsp_bin with
  | None -> check "[lg] LSP binary present" false
  | Some bin ->
      (* Open under localhost form, then ask for documentSymbol under
         plain form. With canonical keying both should land on the
         same internal session; at minimum the server must not crash
         and must answer the request. *)
      let did_open = frame
        {|{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file://localhost/tmp/x.idsl","languageId":"idsl","version":1,"text":"schema A:\n  - K: e.g. 1\n"}}}|} in
      let doc_sym = frame
        {|{"jsonrpc":"2.0","id":7,"method":"textDocument/documentSymbol","params":{"textDocument":{"uri":"file:///tmp/x.idsl"}}}|} in
      let input = init_msg ^ did_open ^ doc_sym ^ exit_msg in
      let out = collect_responses ~bin ~input ~deadline_s:5.0 in
      check "[lg] documentSymbol via plain URI hits the localhost-opened doc"
        (contains_re out (id_match 7) && contains out "\"name\"")

let () =
  Printf.printf "\n--- workspace regressions ---\n";
  test_multifile_include ();
  test_unsaved_cross_file_edit ();
  test_named_instance_consistency ();
  test_cross_file_rename ();
  test_instance_resolver_isolation ();
  test_rename_records_pos_fname ();
  test_call_item_records_pos_fname ();
  test_rename_from_included_file ();
  test_folder_scan_includes_closed_files ();
  test_rename_two_hop_includes ();
  test_document_symbol_only_local_file ();
  test_domain_scopes_same_name ();
  test_domain_blocks_cross_reference ();
  test_versioned_put_doc ();
  test_remove_hook_fires ();
  test_watched_delete_preserves_open_docs ();
  test_watched_delete_unopened_notifies_dependents ();
  test_lsp_framing_survives_bad_frames ();
  test_lsp_method_not_found ();
  test_lsp_shutdown_gates_requests ();
  test_lsp_watcher_rejection_does_not_crash ();
  test_uri_encoding ();
  test_symlink_cycle ();
  test_drop_closed_doc_cache ();
  test_didclose_invalidates_dependents ();
  test_canonical_uri_keying ();
  test_workspace_folder_canon ();
  test_utf16_column_on_non_ascii ();
  test_last_good_canonical_keying ();
  Printf.printf "%d passed, %d failed\n" !pass !fail;
  if !fail > 0 then exit 1
