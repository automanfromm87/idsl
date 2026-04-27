(* JS API surface for iDSL.

   Exposes window.IDSL with:
     IDSL.compile(src) → { ok, errors, program?: Program }
     program.schemas, program.rules, program.tests, program.actions
     program.run(schemaName, inputObj)         → { ok, outcomes?, error? }
     program.explain(schemaName, inputObj)     → trace JSON
     program.runTests()                        → array of test results
     program.diff(schemaName, before, after)   → diff JSON
   I/O is all via JS objects (auto-converted to/from internal JSON). *)

open Js_of_ocaml
open IDSL

(* ---------- Js value <-> internal Json ---------- *)

let rec json_of_js (v : 'a Js.t) : Json.t =
  let t = Js.to_string (Js.typeof v) in
  match t with
  | "string"    -> JStr (Js.to_string (Js.Unsafe.coerce v))
  | "number"    -> JNum (Js.float_of_number (Js.Unsafe.coerce v))
  | "boolean"   -> JBool (Js.to_bool (Js.Unsafe.coerce v))
  | "object" ->
      if Js.Opt.test (Js.some v) = false then JNull
      else if Js.to_bool (Js.Unsafe.global##.Array##isArray v) then
        let arr : Js.Unsafe.any Js.js_array Js.t = Js.Unsafe.coerce v in
        JArr (List.init arr##.length (fun i ->
          json_of_js (Js.Unsafe.get arr i)))
      else
        let keys : Js.js_string Js.t Js.js_array Js.t =
          Js.Unsafe.global##.Object##keys v in
        JObj (List.init keys##.length (fun i ->
          let k = Js.to_string (Js.Unsafe.get keys i) in
          (k, json_of_js (Js.Unsafe.get v k))))
  | _ -> JNull

let rec js_of_json (j : Json.t) : Js.Unsafe.any =
  match j with
  | JNull   -> Js.Unsafe.inject Js.null
  | JBool b -> Js.Unsafe.inject (Js.bool b)
  | JNum n  -> Js.Unsafe.inject (Js.number_of_float n)
  | JStr s  -> Js.Unsafe.inject (Js.string s)
  | JArr xs ->
      Js.Unsafe.inject (Js.array (Array.of_list (List.map js_of_json xs)))
  | JObj kvs ->
      Js.Unsafe.obj
        (Array.of_list (List.map (fun (k, v) -> (k, js_of_json v)) kvs))

(* ---------- error wrapping ---------- *)

let str_arr xs =
  Js.Unsafe.inject (Js.array (Array.of_list (List.map Js.string xs)))

let err_response msgs =
  Js.Unsafe.obj [|
    "ok",      Js.Unsafe.inject Js._false;
    "errors",  str_arr msgs;
  |]

(* ---------- per-program JS handle ---------- *)

let make_program (prog : Ast.program) (tp : Typed.tprogram)
                 (cst : Cst.node) (cst_tokens : Cst.tok list) =
  let ctx = Eval.make_ctx tp in

  let schema_names =
    List.map (fun s -> Js.string s.Typed.ts_name) tp.schemas in
  let rule_names =
    List.map (fun r -> Js.string (String.concat "." r.Typed.tr_path)) tp.rules in
  let test_names =
    List.map (fun t -> Js.string t.Typed.tt_name) tp.tests in

  let env_for schema input_js =
    let j = json_of_js input_js in
    Load.build_env ~instances:ctx.instances ctx.schemas schema j
  in

  let outcomes_to_js outs =
    js_of_json (Dump.outcomes_to_json outs) in

  let run schema_js input_js =
    try
      let schema = Js.to_string schema_js in
      let env = env_for schema input_js in
      let _, outs = Eval.run_rules env ctx.rules in
      Js.Unsafe.obj [|
        "ok",       Js.Unsafe.inject Js._true;
        "outcomes", outcomes_to_js outs;
      |]
    with
    | Load.Load_error m -> err_response ["input: " ^ m]
    | Eval.Eval_error m -> err_response ["eval: " ^ m]
  in

  let explain schema_js input_js =
    try
      let schema = Js.to_string schema_js in
      let env = env_for schema input_js in
      let traces = Explain.run ctx env in
      js_of_json (Explain.to_json traces)
    with
    | Load.Load_error m -> err_response ["input: " ^ m]
    | Eval.Eval_error m -> err_response ["eval: " ^ m]
  in

  let run_tests () =
    let results, _ = Eval.run_all tp in
    let test_to_json (r : Eval.test_result) =
      Json.JObj [
        "name",     JStr r.rname;
        "passed",   JBool r.passed;
        "failures", JArr (List.map (fun s -> Json.JStr s) r.failures);
        "fired",    JArr (List.map (fun s -> Json.JStr s) r.fired);
        "outcomes", Dump.outcomes_to_json r.outcomes;
      ] in
    js_of_json (Json.JArr (List.map test_to_json results))
  in

  let hover_at line col =
    let pos : Lsp_query.lsp_pos = { line; character = col } in
    match Lsp_query.hover_at tp pos with
    | None   -> Js.Unsafe.inject Js.null
    | Some s -> Js.Unsafe.inject (Js.string s)
  in

  let comp_kind_to_int = function
    | Lsp_query.CompField    -> 5
    | Lsp_query.CompTag      -> 13
    | Lsp_query.CompSchema   -> 7
    | Lsp_query.CompInstance -> 6
    | Lsp_query.CompKeyword  -> 14
    | Lsp_query.CompSnippet  -> 27   (* monaco/LSP CompletionItemKind.Snippet *)
  in
  (* Position / range converters used by every LSP-style bridge below. *)
  let pos_to_js (p : Lsp_query.lsp_pos) =
    Js.Unsafe.obj [|
      "line",      Js.Unsafe.inject (Js.number_of_float (float_of_int p.line));
      "character", Js.Unsafe.inject (Js.number_of_float (float_of_int p.character));
    |]
  in
  let range_to_js (r : Lsp_query.sym_range) =
    Js.Unsafe.obj [|
      "start", Js.Unsafe.inject (pos_to_js r.sr_start);
      "end",   Js.Unsafe.inject (pos_to_js r.sr_end);
    |]
  in

  let completions_at src_js line col =
    let src = Js.to_string src_js in
    let pos : Lsp_query.lsp_pos = { line; character = col } in
    let s = Session.compile_string src in
    let items = Lsp_query.completions_at s.cst_tokens prog tp pos in
    Js.array (Array.of_list (List.map (fun (c : Lsp_query.completion) ->
      let kvs = [
        "label",      Js.Unsafe.inject (Js.string c.c_label);
        "kind",       Js.Unsafe.inject (Js.number_of_float
                        (float_of_int (comp_kind_to_int c.c_kind)));
        "insertText", Js.Unsafe.inject (Js.string
                        (Option.value c.c_insert_text ~default:c.c_label));
        "isSnippet",  Js.Unsafe.inject (Js.bool c.c_is_snippet);
      ] in
      let kvs = match c.c_detail with
        | Some s -> kvs @ [ "detail", Js.Unsafe.inject (Js.string s) ]
        | None   -> kvs in
      let kvs = match c.c_data_id with
        | Some d -> kvs @ [ "dataId", Js.Unsafe.inject (Js.string d) ]
        | None   -> kvs
      in
      Js.Unsafe.obj (Array.of_list kvs)) items))
  in
  let resolve_completion data_id_js =
    let data = Js.to_string data_id_js in
    match Lsp_query.resolve_completion tp data with
    | None -> Js.Unsafe.inject Js.null
    | Some md -> Js.Unsafe.inject (Js.string md)
  in
  let format_full () =
    Js.string (Lsp_query.format_full cst)
  in
  let format_range_js src_js s_ln e_ln =
    let src = Js.to_string src_js in
    let formatted, r =
      Lsp_query.format_range src ~start_line:s_ln ~end_line:e_ln in
    Js.Unsafe.obj [|
      "text",  Js.Unsafe.inject (Js.string formatted);
      "range", Js.Unsafe.inject (range_to_js r);
    |]
  in
  let edit_to_js_pub (e : Lsp_query.text_edit) =
    Js.Unsafe.obj [|
      "range",   Js.Unsafe.inject (range_to_js e.te_range);
      "newText", Js.Unsafe.inject (Js.string e.te_new_text);
    |]
  in
  let on_type_format_js src_js line ch_js =
    let src = Js.to_string src_js in
    let ch  = Js.to_string ch_js in
    let edits = Lsp_query.on_type_format ~src ~line ~ch in
    Js.array (Array.of_list (List.map edit_to_js_pub edits))
  in

  let idx = Semantic_index.build prog tp cst in
  let def_at _src_js line col =
    let pos : Lsp_query.lsp_pos = { line; character = col } in
    match Lsp_query.def_at idx pos with
    | None -> Js.Unsafe.inject Js.null
    | Some (decl_pos, label) ->
        let lp = Lsp_query.pos_lsp_of_lex decl_pos in
        Js.Unsafe.obj [|
          "line",      Js.Unsafe.inject (Js.number_of_float (float_of_int lp.line));
          "character", Js.Unsafe.inject (Js.number_of_float (float_of_int lp.character));
          "label",     Js.Unsafe.inject (Js.string label);
        |]
  in
  let references_at line col =
    let pos : Lsp_query.lsp_pos = { line; character = col } in
    match Lsp_query.references_at idx pos with
    | None -> Js.array [||]
    | Some sites ->
        let arr = List.filter_map (fun (p, len) ->
          if p = Lexing.dummy_pos then None
          else
            let lp = Lsp_query.pos_lsp_of_lex p in
            Some (Js.Unsafe.obj [|
              "line",      Js.Unsafe.inject (Js.number_of_float (float_of_int lp.line));
              "character", Js.Unsafe.inject (Js.number_of_float (float_of_int lp.character));
              "length",    Js.Unsafe.inject (Js.number_of_float (float_of_int len));
            |])) sites in
        Js.array (Array.of_list arr)
  in

  let diff schema_js before_js after_js =
    try
      let schema = Js.to_string schema_js in
      let env_b = env_for schema before_js in
      let env_a = env_for schema after_js in
      let traces_b = Explain.run ctx env_b in
      let traces_a = Explain.run ctx env_a in
      let tsch = Hashtbl.find ctx.schemas schema in
      let d = Whatif.compute tsch env_b env_a traces_b traces_a in
      let outcome_arr xs =
        Json.JArr (List.map (fun (n, args) ->
          Json.JObj [
            "call", JStr n;
            "args", Dump.outcomes_to_json [(n, args)] |> (function
              | Json.JArr [JObj kvs] ->
                  (match List.assoc_opt "args" kvs with
                   | Some a -> a | None -> JArr [])
              | _ -> JArr []);
          ]) xs) in
      let value_to_js = Dump.value_to_json in
      let pred_change_to_json (pc : Whatif.pred_change) =
        Json.JObj [
          "text",   JStr pc.pc_text;
          "before", value_to_js pc.pc_before;
          "after",  value_to_js pc.pc_after;
        ] in
      let rule_change_to_json (rc : Whatif.rule_change) =
        Json.JObj [
          "rule",         JStr rc.rc_path;
          "firedBefore",  JBool rc.rc_fired_before;
          "firedAfter",   JBool rc.rc_fired_after;
          "predChanges",  JArr (List.map pred_change_to_json rc.rc_pred_changes);
        ] in
      let field_change_to_json (fc : Whatif.field_change) =
        Json.JObj [
          "name",   JStr fc.fc_name;
          "before", value_to_js fc.fc_before;
          "after",  value_to_js fc.fc_after;
        ] in
      js_of_json (Json.JObj [
        "fields",   JArr (List.map field_change_to_json d.fields);
        "rules",    JArr (List.map rule_change_to_json d.rules);
        "outcomes", JObj [
          "added",   outcome_arr d.outcomes.od_added;
          "removed", outcome_arr d.outcomes.od_removed;
        ];
      ])
    with
    | Load.Load_error m -> err_response ["input: " ^ m]
    | Eval.Eval_error m -> err_response ["eval: " ^ m]
  in

  (* ---------- Round-1 / Round-2 LSP-style queries (JS surface) ---------- *)

  let rec doc_sym_to_js (s : Lsp_query.doc_symbol) : Js.Unsafe.any =
    let kvs = [
      "name",           Js.Unsafe.inject (Js.string s.ds_name);
      "kind",           Js.Unsafe.inject (Js.number_of_float
                          (float_of_int s.ds_kind));
      "range",          Js.Unsafe.inject (range_to_js s.ds_range);
      "selectionRange", Js.Unsafe.inject (range_to_js s.ds_selection);
      "children",       Js.Unsafe.inject (Js.array
                          (Array.of_list
                             (List.map doc_sym_to_js s.ds_children)));
    ] in
    let kvs = match s.ds_detail with
      | Some d -> kvs @ [ "detail", Js.Unsafe.inject (Js.string d) ]
      | None   -> kvs in
    Js.Unsafe.obj (Array.of_list kvs)
  in

  let document_symbols () =
    Js.array (Array.of_list
      (List.map doc_sym_to_js (Lsp_query.document_symbols idx cst))) in

  let workspace_symbols q_js =
    let q = Js.to_string q_js in
    let syms = Lsp_query.workspace_symbols idx q in
    Js.array (Array.of_list
      (List.map (fun (s : Symbol.t) ->
         let lp = Lsp_query.pos_lsp_of_lex s.decl_pos in
         let len = String.length (Lsp_query.symbol_name s.kind) in
         let end_p = { lp with character = lp.character + len } in
         Js.Unsafe.obj [|
           "name",  Js.Unsafe.inject (Js.string s.label);
           "kind",  Js.Unsafe.inject (Js.number_of_float
                      (float_of_int (Lsp_query.lsp_kind_of_symbol_kind s.kind)));
           "range", Js.Unsafe.inject (Js.Unsafe.obj [|
             "start", Js.Unsafe.inject (pos_to_js lp);
             "end",   Js.Unsafe.inject (pos_to_js end_p);
           |]);
         |]) syms))
  in

  let document_highlights_at line col =
    let pos : Lsp_query.lsp_pos = { line; character = col } in
    match Lsp_query.document_highlights_at idx pos with
    | None -> Js.array [||]
    | Some sites ->
        let arr = List.filter_map (fun (p, len) ->
          if p = Lexing.dummy_pos then None
          else
            let lp = Lsp_query.pos_lsp_of_lex p in
            let end_p = { lp with character = lp.character + len } in
            Some (Js.Unsafe.obj [|
              "start", Js.Unsafe.inject (pos_to_js lp);
              "end",   Js.Unsafe.inject (pos_to_js end_p);
            |])) sites in
        Js.array (Array.of_list arr)
  in

  let folding_ranges () =
    let rs = Lsp_query.folding_ranges cst in
    Js.array (Array.of_list (List.map (fun (s, e) ->
      Js.Unsafe.obj [|
        "start", Js.Unsafe.inject (Js.number_of_float (float_of_int s));
        "end",   Js.Unsafe.inject (Js.number_of_float (float_of_int e));
      |]) rs))
  in

  let selection_ranges_at line col =
    let pos : Lsp_query.lsp_pos = { line; character = col } in
    let chain = Lsp_query.selection_ranges_at cst pos in
    Js.array (Array.of_list (List.map range_to_js chain))
  in

  let signature_help_at line col =
    let pos : Lsp_query.lsp_pos = { line; character = col } in
    match Lsp_query.signature_help_at tp cst_tokens pos with
    | None -> Js.Unsafe.inject Js.null
    | Some sh ->
        let sigs = List.map (fun (si : Lsp_query.signature_info) ->
          Js.Unsafe.obj [|
            "label",      Js.Unsafe.inject (Js.string si.si_label);
            "parameters", Js.Unsafe.inject
              (Js.array (Array.of_list
                (List.map (fun (p : Lsp_query.sig_param) ->
                  Js.Unsafe.obj [|
                    "label", Js.Unsafe.inject (Js.array [|
                      Js.Unsafe.inject (Js.number_of_float
                        (float_of_int p.sp_start));
                      Js.Unsafe.inject (Js.number_of_float
                        (float_of_int p.sp_end));
                    |]);
                  |]) si.si_params)));
          |]) sh.sh_signatures in
        Js.Unsafe.obj [|
          "signatures",      Js.Unsafe.inject
                               (Js.array (Array.of_list sigs));
          "activeSignature", Js.Unsafe.inject (Js.number_of_float 0.0);
          "activeParameter", Js.Unsafe.inject (Js.number_of_float
                               (float_of_int sh.sh_active_param));
        |]
  in

  let inlay_hints_in start_line end_line =
    let hs = Lsp_query.inlay_hints_in_range tp ~start_line ~end_line in
    Js.array (Array.of_list (List.map (fun (h : Lsp_query.inlay_hint) ->
      Js.Unsafe.obj [|
        "position",     Js.Unsafe.inject (pos_to_js h.ih_pos);
        "label",        Js.Unsafe.inject (Js.string h.ih_label);
        "kind",         Js.Unsafe.inject (Js.number_of_float
                          (float_of_int h.ih_kind));
        "paddingRight", Js.Unsafe.inject (Js.bool h.ih_pad_r);
      |]) hs))
  in

  let code_lenses () =
    let ls = Lsp_query.code_lenses_for idx in
    Js.array (Array.of_list (List.map (fun (l : Lsp_query.code_lens) ->
      let target = Lsp_query.pos_lsp_of_lex l.cl_target in
      Js.Unsafe.obj [|
        "range",  Js.Unsafe.inject (range_to_js l.cl_range);
        "title",  Js.Unsafe.inject (Js.string l.cl_label);
        "target", Js.Unsafe.inject (pos_to_js target);
      |]) ls))
  in

  (* ---------- Round-3 refactoring ---------- *)

  let prepare_rename line col =
    let pos : Lsp_query.lsp_pos = { line; character = col } in
    match Lsp_query.prepare_rename idx pos with
    | None -> Js.Unsafe.inject Js.null
    | Some rt ->
        Js.Unsafe.obj [|
          "range",       Js.Unsafe.inject (range_to_js rt.rt_range);
          "placeholder", Js.Unsafe.inject (Js.string rt.rt_label);
        |]
  in

  let edit_to_js = edit_to_js_pub in

  let rename_at line col new_name_js =
    let pos : Lsp_query.lsp_pos = { line; character = col } in
    let new_name = Js.to_string new_name_js in
    match Lsp_query.rename_at idx pos ~new_name with
    | None -> Js.array [||]
    | Some edits ->
        Js.array (Array.of_list (List.map edit_to_js edits))
  in

  let quick_fixes_for line col msg_js =
    let msg = Js.to_string msg_js in
    let qfs = Lsp_query.quick_fixes_for_message ~line ~col msg in
    Js.array (Array.of_list (List.map (fun (q : Lsp_query.quick_fix) ->
      Js.Unsafe.obj [|
        "title",    Js.Unsafe.inject (Js.string q.qf_title);
        "find",     Js.Unsafe.inject (Js.string q.qf_find);
        "replace",  Js.Unsafe.inject (Js.string q.qf_replace);
        "diagLine", Js.Unsafe.inject (Js.number_of_float
                      (float_of_int q.qf_diag_line));
        "diagCol",  Js.Unsafe.inject (Js.number_of_float
                      (float_of_int q.qf_diag_col));
      |]) qfs))
  in

  (* ---------- Round-7 advanced bridges (helpers) ---------- *)

  let pos_arg l c : Lsp_query.lsp_pos = { line = l; character = c } in
  let inj_num n = Js.Unsafe.inject (Js.number_of_float (float_of_int n)) in
  let inj_str s = Js.Unsafe.inject (Js.string s) in

  let call_item_to_js (c : Lsp_query.call_item) =
    Js.Unsafe.obj [|
      "name",  inj_str c.ci_name;
      "kind",  inj_num c.ci_kind_int;
      "range", Js.Unsafe.inject (range_to_js c.ci_range);
    |]
  in

  let type_definition_at l c =
    match Lsp_query.type_definition_at idx tp (pos_arg l c) with
    | None -> Js.Unsafe.inject Js.null
    | Some (p, label) ->
        let lp = Lsp_query.pos_lsp_of_lex p in
        Js.Unsafe.obj [|
          "line",      inj_num lp.line;
          "character", inj_num lp.character;
          "label",     inj_str label;
        |]
  in
  let hierarchy fn l c =
    match Lsp_query.prepare_call_hierarchy idx (pos_arg l c) with
    | None -> Js.array [||]
    | Some it ->
        Js.array (Array.of_list
          (List.map call_item_to_js (fn idx tp it)))
  in
  let type_hierarchy fn l c =
    match Lsp_query.prepare_type_hierarchy idx (pos_arg l c) with
    | None -> Js.array [||]
    | Some it ->
        Js.array (Array.of_list
          (List.map call_item_to_js (fn idx tp it)))
  in
  let unused_at () =
    Js.array (Array.of_list (List.map (fun (p, len, msg) ->
      let lp = Lsp_query.pos_lsp_of_lex p in
      Js.Unsafe.obj [|
        "line",      inj_num lp.line;
        "character", inj_num lp.character;
        "length",    inj_num len;
        "message",   inj_str msg;
      |]) (Lsp_query.unused_diagnostics idx)))
  in

  let semantic_tokens () =
    let data = Lsp_query.semantic_tokens_of idx cst_tokens in
    let ints = Array.of_list
                 (List.map (fun n ->
                    Js.Unsafe.inject (Js.number_of_float (float_of_int n)))
                    data) in
    Js.Unsafe.obj [|
      "data",       Js.Unsafe.inject (Js.array ints);
      "tokenTypes", Js.Unsafe.inject (Js.array
                      (Array.of_list (List.map Js.string
                                        Lsp_query.semantic_token_types)));
    |]
  in

  Js.Unsafe.obj [|
    "schemas",   Js.Unsafe.inject (Js.array (Array.of_list schema_names));
    "rules",     Js.Unsafe.inject (Js.array (Array.of_list rule_names));
    "tests",     Js.Unsafe.inject (Js.array (Array.of_list test_names));
    "run",            Js.Unsafe.inject (Js.wrap_callback (fun s i -> run s i));
    "explain",        Js.Unsafe.inject (Js.wrap_callback (fun s i -> explain s i));
    "runTests",       Js.Unsafe.inject (Js.wrap_callback run_tests);
    "diff",           Js.Unsafe.inject (Js.wrap_callback
                        (fun s b a -> diff s b a));
    "hover_at",       Js.Unsafe.inject (Js.wrap_callback
                        (fun l c -> hover_at l c));
    "completions_at", Js.Unsafe.inject (Js.wrap_callback
                        (fun s l c -> completions_at s l c));
    "def_at",         Js.Unsafe.inject (Js.wrap_callback
                        (fun s l c -> def_at s l c));
    "references_at",  Js.Unsafe.inject (Js.wrap_callback
                        (fun l c -> references_at l c));
    (* Round-1 navigation *)
    "document_symbols",        Js.Unsafe.inject (Js.wrap_callback
                                 document_symbols);
    "workspace_symbols",       Js.Unsafe.inject (Js.wrap_callback
                                 workspace_symbols);
    "document_highlights_at",  Js.Unsafe.inject (Js.wrap_callback
                                 (fun l c -> document_highlights_at l c));
    "folding_ranges",          Js.Unsafe.inject (Js.wrap_callback
                                 folding_ranges);
    "selection_ranges_at",     Js.Unsafe.inject (Js.wrap_callback
                                 (fun l c -> selection_ranges_at l c));
    (* Round-2 information *)
    "signature_help_at",       Js.Unsafe.inject (Js.wrap_callback
                                 (fun l c -> signature_help_at l c));
    "inlay_hints_in",          Js.Unsafe.inject (Js.wrap_callback
                                 (fun s e -> inlay_hints_in s e));
    "code_lenses",             Js.Unsafe.inject (Js.wrap_callback
                                 code_lenses);
    "semantic_tokens",         Js.Unsafe.inject (Js.wrap_callback
                                 semantic_tokens);
    (* Round-3 refactoring *)
    "prepare_rename",          Js.Unsafe.inject (Js.wrap_callback
                                 (fun l c -> prepare_rename l c));
    "rename_at",               Js.Unsafe.inject (Js.wrap_callback
                                 (fun l c n -> rename_at l c n));
    "quick_fixes_for",         Js.Unsafe.inject (Js.wrap_callback
                                 (fun l c m -> quick_fixes_for l c m));
    (* Advanced navigation / hierarchy / lint *)
    "type_definition_at", Js.Unsafe.inject (Js.wrap_callback type_definition_at);
    "call_incoming",      Js.Unsafe.inject (Js.wrap_callback
                            (fun l c -> hierarchy Lsp_query.incoming_calls l c));
    "call_outgoing",      Js.Unsafe.inject (Js.wrap_callback
                            (fun l c -> hierarchy Lsp_query.outgoing_calls l c));
    "type_supertypes",    Js.Unsafe.inject (Js.wrap_callback
                            (fun l c -> type_hierarchy Lsp_query.supertypes l c));
    "type_subtypes",      Js.Unsafe.inject (Js.wrap_callback
                            (fun l c -> type_hierarchy Lsp_query.subtypes l c));
    "unused_diagnostics", Js.Unsafe.inject (Js.wrap_callback unused_at);
    (* Round-4 formatting + completion resolve *)
    "format_full",             Js.Unsafe.inject (Js.wrap_callback
                                 format_full);
    "format_range",            Js.Unsafe.inject (Js.wrap_callback
                                 (fun src s e -> format_range_js src s e));
    "on_type_format",          Js.Unsafe.inject (Js.wrap_callback
                                 (fun src l ch -> on_type_format_js src l ch));
    "resolve_completion",      Js.Unsafe.inject (Js.wrap_callback
                                 resolve_completion);
  |]

(* ---------- top-level compile ---------- *)

let diag_to_js (d : Diagnostic.t) : Js.Unsafe.any =
  let r = Lsp_query.lsp_of_diag d in
  Js.Unsafe.obj [|
    "stage",     Js.Unsafe.inject (Js.string r.d_stage);
    "severity",  Js.Unsafe.inject (Js.string (Diagnostic.pp_severity d.severity));
    "message",   Js.Unsafe.inject (Js.string r.d_message);
    "line",      Js.Unsafe.inject (Js.number_of_float (float_of_int r.d_pos.line));
    "column",    Js.Unsafe.inject (Js.number_of_float (float_of_int r.d_pos.character));
    "endLine",   Js.Unsafe.inject (Js.number_of_float (float_of_int r.d_end.line));
    "endColumn", Js.Unsafe.inject (Js.number_of_float (float_of_int r.d_end.character));
  |]

let diag_response diags =
  Js.Unsafe.obj [|
    "ok",          Js.Unsafe.inject Js._false;
    "errors",      str_arr (List.map Diagnostic.to_string diags);
    "diagnostics", Js.Unsafe.inject (Js.array
                     (Array.of_list (List.map diag_to_js diags)));
  |]

let compile src_js =
  let src = Js.to_string src_js in
  let s = Session.compile_string src in
  match s.ast, s.typed with
  | Some prog, Some tp ->
      Js.Unsafe.obj [|
        "ok",          Js.Unsafe.inject Js._true;
        "errors",      str_arr [];
        "diagnostics", Js.Unsafe.inject (Js.array [||]);
        "program",     make_program prog tp s.cst s.cst_tokens;
      |]
  | _ -> diag_response s.diagnostics

(* ---------- format helpers (same renderers as CLI) ---------- *)

let format_explain traces_json =
  (* Re-route: caller passes JSON we got from program.explain — convert back?
     Simpler: expose pp_report directly by re-running. But we don't keep ctx.
     For now expose a JS function that takes the typed program (not exposed) — skip.
     Instead: provide pre-formatted strings via run_explain_text. *)
  ignore traces_json; Js.string ""

let _ = format_explain  (* future use *)

(* ---------- export ---------- *)

let () =
  let api = object%js
    method compile (src : Js.js_string Js.t) = compile src
    val version = Js.string "0.8"
  end in
  Js.Unsafe.set Js.Unsafe.global "IDSL" api
