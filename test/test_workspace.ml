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
  Printf.printf "%d passed, %d failed\n" !pass !fail;
  if !fail > 0 then exit 1
