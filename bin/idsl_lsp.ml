(* iDSL LSP server.
   Speaks JSON-RPC over stdin/stdout. Capabilities: textDocument/{didOpen,
   didChange, didSave, hover}, plus the lifecycle (initialize, shutdown,
   exit). Diagnostics are pushed via textDocument/publishDiagnostics on
   every doc-change. *)

open IDSL

(* Single workspace for the lifetime of this server. All requests fetch
   sessions through it; it owns the document table, cache, and
   dependency graph. *)
let ws : Workspace.t = Workspace.create ()

(* Most-recent successful compile per doc. Kept separately from the
   Workspace cache so that completion/hover stay live while the user
   has a transient parse error. *)
let last_good : (string, Ast.program * Typed.tprogram) Hashtbl.t = Hashtbl.create 4

(* ---------- JSON-RPC framing ---------- *)

let log fmt = Printf.eprintf ("[idsl-lsp] " ^^ fmt ^^ "\n%!")

let read_message ic : Json.t option =
  let read_headers () =
    let len = ref None in
    let rec loop () =
      let line = input_line ic in
      let line = String.trim line in
      if line = "" then ()
      else begin
        (try
          let prefix = "Content-Length:" in
          let plen = String.length prefix in
          if String.length line > plen
             && String.sub line 0 plen = prefix then
            len := Some (int_of_string (String.trim
              (String.sub line plen (String.length line - plen))))
         with _ -> ());
        loop ()
      end
    in
    (try loop () with End_of_file -> ());
    !len
  in
  match read_headers () with
  | None -> None
  | Some n ->
      let buf = Bytes.create n in
      really_input ic buf 0 n;
      try Some (Json.of_string (Bytes.unsafe_to_string buf))
      with Json.Parse_error msg ->
        log "JSON parse error: %s" msg; None

let write_message oc (j : Json.t) =
  let body = Json.to_string j in
  Printf.fprintf oc "Content-Length: %d\r\n\r\n%s"
    (String.length body) body;
  flush oc

(* ---------- response builders ---------- *)

let result id (v : Json.t) : Json.t =
  JObj [ "jsonrpc", JStr "2.0"; "id", id; "result", v ]

let notif method_ params : Json.t =
  JObj [ "jsonrpc", JStr "2.0"; "method", JStr method_; "params", params ]

let ok_response id = result id JNull

(* ---------- LSP value helpers ---------- *)

(* Internal `lsp_pos.character` is a *byte* column — that's what the
   parser/CST work in.  At the LSP wire we must hand the client a
   UTF-16 column.  `wire_pos_of_doc_pos` does the conversion using the
   source text of the position's host file; `wire_pos_of_pos_fname`
   resolves the host via `pos_fname` so cross-file results don't
   silently fall through to byte columns. *)
let source_for_uri uri =
  match Workspace.get_doc ws ~uri with
  | Some d -> d.content
  | None   ->
      match Workspace.read_file_opt (Workspace.path_of_uri uri) with
      | Some s -> s
      | None   -> ""

let utf16_pos_to_json ~src (p : Lsp_query.lsp_pos) : Json.t =
  (* `p.line` is already 0-indexed; `p.character` is a byte column. *)
  let line = p.line in
  let utf16_col =
    if src = "" then p.character
    else
      let l = Utf16.line_of_source src line in
      Utf16.utf16_of_byte_col l p.character
  in
  JObj [ "line", JNum (float_of_int line);
         "character", JNum (float_of_int utf16_col) ]

let utf16_range ~src (s : Lsp_query.lsp_pos) (e : Lsp_query.lsp_pos) : Json.t =
  JObj [ "start", utf16_pos_to_json ~src s;
         "end",   utf16_pos_to_json ~src e ]

(* Backwards-compat shims: byte-column wire writers used by the few
   handlers that have no convenient way to grab a per-URI source.
   These are only correct for ASCII-only docs and should be removed
   once every call site routes through `utf16_pos_to_json`. *)
let lsp_pos_json (p : Lsp_query.lsp_pos) : Json.t =
  utf16_pos_to_json ~src:"" p

let range_json (s : Lsp_query.lsp_pos) (e : Lsp_query.lsp_pos) : Json.t =
  utf16_range ~src:"" s e

let diagnostic_json ~src (d : Lsp_query.diagnostic) : Json.t =
  JObj [
    "range",    utf16_range ~src d.d_pos d.d_end;
    "severity", JNum 1.0;
    "source",   JStr ("idsl-" ^ d.d_stage);
    "message",  JStr d.d_message;
  ]

let publish_diagnostics oc uri diags =
  let src = source_for_uri uri in
  write_message oc (notif "textDocument/publishDiagnostics" (JObj [
    "uri",         JStr uri;
    "diagnostics", JArr (List.map (diagnostic_json ~src) diags);
  ]))

(* ---------- workspace shims ---------- *)

(* Doc-content lookup matching the pre-Workspace surface (returns None
   for unknown URIs, the raw source otherwise). Lets the rest of the
   handler code stay structurally identical to its old form. *)
let get_src uri =
  match Workspace.get_doc ws ~uri with
  | Some d -> Some d.content
  | None   -> None

(* ---------- handlers ---------- *)

let analyze_and_publish oc uri =
  let s = Workspace.compile_doc ws ~uri in
  (match s.ast, s.typed with
   | Some p, Some tp -> Hashtbl.replace last_good uri (p, tp)
   | _ -> ());
  let diags = List.map Lsp_query.lsp_of_diag s.diagnostics in
  publish_diagnostics oc uri diags

(* Best-effort programs for completion / hover / def: prefer the
   workspace-cached compile, fall back to the last good one so completion
   stays live across transient parse errors. *)
let best_effort_progs uri _src =
  let s = Workspace.compile_doc ws ~uri in
  match s.ast, s.typed with
  | Some p, Some tp -> Some (p, tp), s.cst_tokens
  | _               -> Hashtbl.find_opt last_good uri, s.cst_tokens

let json_field obj k =
  match obj with
  | Json.JObj kvs -> List.assoc_opt k kvs
  | _ -> None

let json_str = function Json.JStr s -> s | _ -> ""
let json_num = function Json.JNum n -> int_of_float n | _ -> 0

(* UTF-16 → byte at the wire boundary.  The client sends a UTF-16
   `character` column; OCaml's parser indexes by byte.  Translation
   needs the doc's source text — this helper looks it up by URI. *)
let lsp_pos_of_json_for_uri ~uri j : Lsp_query.lsp_pos =
  let line = match json_field j "line"      with Some n -> json_num n | None -> 0 in
  let utf16_col = match json_field j "character" with
    | Some n -> json_num n | None -> 0 in
  let src = source_for_uri uri in
  { line; character = Utf16.byte_col_of_utf16 ~src ~line utf16_col }

let handle_initialize id params =
  (* Capture workspaceFolders the client sent at startup. *)
  (match json_field params "workspaceFolders" with
   | Some (JArr xs) ->
       let urls = List.filter_map (fun f ->
         match json_field f "uri" with Some j -> Some (json_str j) | _ -> None) xs in
       Workspace.set_folders ws urls
   | _ ->
     (* legacy single-root field *)
     (match json_field params "rootUri" with
      | Some (JStr u) -> Workspace.set_folders ws [u]
      | _ -> ()));
  result id (JObj [
    "capabilities", JObj [
      "textDocumentSync", JNum 2.0;       (* incremental sync *)
      "hoverProvider",    JBool true;
      "definitionProvider",        JBool true;
      "referencesProvider",        JBool true;
      "documentSymbolProvider",    JBool true;
      "workspaceSymbolProvider",   JBool true;
      "documentHighlightProvider", JBool true;
      "foldingRangeProvider",      JBool true;
      "selectionRangeProvider",    JBool true;
      "signatureHelpProvider",     JObj [
        "triggerCharacters", JArr [JStr "("; JStr ","];
      ];
      "inlayHintProvider",         JBool true;
      "codeLensProvider",          JObj [
        "resolveProvider", JBool false;
      ];
      "semanticTokensProvider",    JObj [
        "legend", JObj [
          "tokenTypes",     JArr (List.map (fun s -> Json.JStr s)
                                    Lsp_query.semantic_token_types);
          "tokenModifiers", JArr (List.map (fun s -> Json.JStr s)
                                    Lsp_query.semantic_token_modifiers);
        ];
        "full",  JBool true;
        "range", JBool false;
      ];
      "renameProvider",            JObj [
        "prepareProvider", JBool true;
      ];
      "codeActionProvider",        JBool true;
      "documentFormattingProvider",      JBool true;
      "documentRangeFormattingProvider", JBool true;
      "documentOnTypeFormattingProvider", JObj [
        "firstTriggerCharacter", JStr "\n";
      ];
      "completionProvider", JObj [
        "triggerCharacters", JArr [JStr "."; JStr "="; JStr "(";
                                   JStr ","; JStr "@"];
        "resolveProvider",   JBool true;
      ];
      "executeCommandProvider", JObj [
        "commands", JArr [
          JStr "idsl.runTests";
          JStr "idsl.printSymbols";
        ];
      ];
      "declarationProvider",        JBool true;
      "typeDefinitionProvider",     JBool true;
      "implementationProvider",     JBool true;
      "callHierarchyProvider",      JBool true;
      "typeHierarchyProvider",      JBool true;
      "diagnosticProvider",         JObj [
        "interFileDependencies", JBool true;
        "workspaceDiagnostics",  JBool false;
      ];
      "workspace", JObj [
        "workspaceFolders", JObj [
          "supported",          JBool true;
          "changeNotifications", JBool true;
        ];
        "fileOperations", JObj [
          "willRename", JObj [
            "filters", JArr [
              JObj [
                "scheme", JStr "file";
                "pattern", JObj [ "glob", JStr "**/*.idsl" ];
              ]
            ];
          ];
        ];
      ];
    ];
    "serverInfo", JObj [
      "name",    JStr "idsl-lsp";
      "version", JStr "0.1";
    ];
  ])

let handle_did_open oc params =
  let td = json_field params "textDocument" in
  match td with
  | None -> ()
  | Some td ->
      let uri  = match json_field td "uri"  with Some j -> json_str j | _ -> "" in
      let text = match json_field td "text" with Some j -> json_str j | _ -> "" in
      let version = match json_field td "version" with
        | Some n -> json_num n | None -> 0 in
      Workspace.put_doc ws ~uri ~content:text ~version;
      ignore (Workspace.invalidate ws ~uri);
      analyze_and_publish oc uri

(* Apply a range-based edit: replace text in `src` between (start_line,
   start_char) and (end_line, end_char) with `new_text`. LSP positions are
   0-indexed UTF-16 — we treat as byte offsets which works for ASCII / one
   BMP code unit per char. Multi-byte / surrogate-pair handling can be
   added later. *)
let apply_range_edit (src : string) ~sl ~sc ~el ~ec (new_text : string) =
  let lines = String.split_on_char '\n' src in
  let line_count = List.length lines in
  let lines = Array.of_list lines in
  let pre =
    let buf = Buffer.create (String.length src) in
    for i = 0 to sl - 1 do
      if i < line_count then begin
        Buffer.add_string buf lines.(i);
        Buffer.add_char buf '\n'
      end
    done;
    if sl < line_count then begin
      let line = lines.(sl) in
      let take = min sc (String.length line) in
      Buffer.add_string buf (String.sub line 0 take)
    end;
    Buffer.contents buf
  in
  let post =
    let buf = Buffer.create (String.length src) in
    if el < line_count then begin
      let line = lines.(el) in
      let drop = min ec (String.length line) in
      Buffer.add_string buf (String.sub line drop (String.length line - drop));
      if el < line_count - 1 then Buffer.add_char buf '\n'
    end;
    for i = el + 1 to line_count - 1 do
      Buffer.add_string buf lines.(i);
      if i < line_count - 1 then Buffer.add_char buf '\n'
    done;
    Buffer.contents buf
  in
  pre ^ new_text ^ post

let handle_did_change oc params =
  let uri =
    match json_field params "textDocument" with
    | Some td ->
        (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> ""
  in
  let current = match get_src uri with Some s -> s | None -> "" in
  let changes =
    match json_field params "contentChanges" with
    | Some (JArr xs) -> xs
    | _ -> []
  in
  let updated = List.fold_left (fun src change ->
    match json_field change "range" with
    | None ->
        (match json_field change "text" with
         | Some (JStr s) -> s
         | _ -> src)
    | Some range ->
        (* Range positions arrive as UTF-16 columns; convert to byte
           columns *against the pre-edit `src`* before slicing.  Doing
           this inside the fold means each iteration uses the correct
           snapshot to interpret subsequent edits. *)
        let parse_pos field =
          match json_field range field with
          | Some j ->
              let line = match json_field j "line"
                with Some n -> json_num n | None -> 0 in
              let utf16_col = match json_field j "character"
                with Some n -> json_num n | None -> 0 in
              { Lsp_query.line;
                character = Utf16.byte_col_of_utf16 ~src ~line utf16_col }
          | None -> { Lsp_query.line = 0; character = 0 }
        in
        let start_p = parse_pos "start" in
        let end_p   = parse_pos "end" in
        let new_text = match json_field change "text" with
          | Some (JStr s) -> s | _ -> "" in
        apply_range_edit src
          ~sl:start_p.line ~sc:start_p.character
          ~el:end_p.line ~ec:end_p.character
          new_text
  ) current changes in
  if updated <> "" then begin
    let version = match json_field params "textDocument" with
      | Some td -> (match json_field td "version" with
                    | Some n -> json_num n | None -> 0)
      | None -> 0 in
    Workspace.put_doc ws ~uri ~content:updated ~version;
    let affected = Workspace.invalidate ws ~uri in
    analyze_and_publish oc uri;
    (* Re-publish diagnostics for every doc whose cache we just dropped
       — they may now show new errors (or have errors cleared). *)
    List.iter (fun u ->
      if u <> uri then analyze_and_publish oc u) affected
  end

let kind_of_comp = function
  | Lsp_query.CompField    -> 5    (* Field *)
  | Lsp_query.CompTag      -> 13   (* Enum *)
  | Lsp_query.CompSchema   -> 7    (* Class *)
  | Lsp_query.CompInstance -> 6    (* Variable *)
  | Lsp_query.CompKeyword  -> 14   (* Keyword *)
  | Lsp_query.CompSnippet  -> 27   (* Snippet *)

(* Each completion item gets `data = {"uri": <originating-doc>,
   "id": <key>}` so that `completionItem/resolve` can fetch the right
   typed program — picking any open doc would risk pulling
   documentation from an unrelated session that happens to share a
   bare name (e.g. two `schema Item` in different domains). *)
let comp_to_json ~uri (c : Lsp_query.completion) =
  let base = [
    "label",            Json.JStr c.c_label;
    "kind",             Json.JNum (float_of_int (kind_of_comp c.c_kind));
    "insertText",       Json.JStr (Option.value c.c_insert_text
                                     ~default:c.c_label);
    "insertTextFormat", Json.JNum (float_of_int (if c.c_is_snippet then 2 else 1));
  ] in
  let base = match c.c_detail with
    | Some s -> base @ [ "detail", Json.JStr s ]
    | None   -> base in
  let base = match c.c_data_id with
    | Some d ->
        let data = Json.JObj [ "uri", Json.JStr uri; "id", Json.JStr d ] in
        base @ [ "data", data ]
    | None -> base in
  Json.JObj base

let handle_completion_resolve id params =
  (* `data` is the JSON object we tucked into the original completion
     item.  Both fields must be present for resolve to be deterministic
     — the URI binds the lookup to the session we offered the item
     from, the id is the kind-tagged key that `Lsp_query.resolve_completion`
     understands. *)
  let data = json_field params "data" in
  let uri = match data with
    | Some d -> (match json_field d "uri" with Some (JStr u) -> u | _ -> "")
    | None -> "" in
  let data_id = match data with
    | Some d -> (match json_field d "id"  with Some (JStr s) -> Some s | _ -> None)
    | None -> None in
  match data_id, uri with
  | None, _ | _, "" -> result id params
  | Some key, _ ->
    let s = Workspace.compile_doc ws ~uri in
    (match s.typed with
     | None -> result id params
     | Some tp ->
       match Lsp_query.resolve_completion tp key with
       | None -> result id params
       | Some md ->
         let doc = Json.JObj [ "kind", Json.JStr "markdown";
                               "value", Json.JStr md ] in
         let extended = match params with
           | Json.JObj kvs -> Json.JObj (kvs @ [ "documentation", doc ])
           | other -> other in
         result id extended)

let handle_completion id params =
  let uri = match json_field params "textDocument" with
    | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> "" in
  let pos = match json_field params "position" with
    | Some j -> lsp_pos_of_json_for_uri ~uri j
    | None   -> { Lsp_query.line = 0; character = 0 } in
  let empty () = result id (JObj [ "isIncomplete", JBool false; "items", JArr [] ]) in
  match get_src uri with
  | None -> empty ()
  | Some src ->
    match best_effort_progs uri src with
    | None, _ -> empty ()
    | Some (prog, tp), cst ->
      let items = Lsp_query.completions_at cst prog tp pos in
      result id (JObj [
        "isIncomplete", JBool false;
        "items", JArr (List.map (comp_to_json ~uri) items);
      ])

(* The semantic index now lives on the Session and is computed lazily
   on first access — every subsequent request returns the cached value.
   We keep this helper because `_src` callers don't have a session
   handle. *)
let index_for uri _src = Session.index (Workspace.compile_doc ws ~uri)

(* `length` is given in bytes (it's a `String.length name` produced by
   the indexer, which is byte-counting).  Convert both endpoints to
   UTF-16 against the source file the position belongs to.  When
   `pos_fname` is empty we fall back to byte cols, which is the legacy
   ASCII-only behavior. *)
let range_of_pos (p : Lexing.position) ~length =
  let lp = Lsp_query.pos_lsp_of_lex p in
  let end_p = { lp with character = lp.character + length } in
  let src =
    if p.pos_fname = "" then ""
    else
      let uri = Workspace.uri_of_pos_fname ~fallback:"" p.pos_fname in
      source_for_uri uri
  in
  utf16_range ~src lp end_p

let handle_definition id params =
  let uri = match json_field params "textDocument" with
    | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> "" in
  let pos = match json_field params "position" with
    | Some j -> lsp_pos_of_json_for_uri ~uri j
    | None   -> { Lsp_query.line = 0; character = 0 } in
  match get_src uri with
  | None -> result id JNull
  | Some src ->
    match index_for uri src with
    | None -> result id JNull
    | Some idx ->
      match Lsp_query.def_at idx pos with
      | None -> result id JNull
      | Some (decl_pos, _) ->
          result id (JObj [
            "uri",   JStr (Workspace.uri_of_pos_fname
                             ~fallback:uri decl_pos.pos_fname);
            "range", range_of_pos decl_pos ~length:1;
          ])

let handle_references id params =
  let uri = match json_field params "textDocument" with
    | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> "" in
  let pos = match json_field params "position" with
    | Some j -> lsp_pos_of_json_for_uri ~uri j
    | None   -> { Lsp_query.line = 0; character = 0 } in
  let include_decl =
    match json_field params "context" with
    | Some ctx ->
        (match json_field ctx "includeDeclaration" with
         | Some (JBool b) -> b
         | _ -> true)
    | None -> true
  in
  match get_src uri with
  | None -> result id (JArr [])
  | Some src ->
    match index_for uri src with
    | None -> result id (JArr [])
    | Some idx ->
      let refs sym = Workspace.aggregated_references ws ~current_uri:uri sym in
      match Lsp_query.references_at ~refs idx pos with
      | None -> result id (JArr [])
      | Some sites ->
          let sites =
            if include_decl then sites else List.tl sites
          in
          let locs = List.filter_map (fun (p, len) ->
            if p = Lexing.dummy_pos then None
            else Some (Json.JObj [
              "uri",   Json.JStr (Workspace.uri_of_pos_fname
                                     ~fallback:uri p.pos_fname);
              "range", range_of_pos p ~length:len;
            ])) sites in
          result id (JArr locs)

let handle_hover id params =
  let uri = match json_field params "textDocument" with
    | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> "" in
  let pos = match json_field params "position" with
    | Some j -> lsp_pos_of_json_for_uri ~uri j
    | None   -> { line = 0; character = 0 } in
  match get_src uri with
  | None -> result id JNull
  | Some src ->
    match best_effort_progs uri src with
    | None, _ -> result id JNull
    | Some (_, tp), _ ->
      match Lsp_query.hover_at tp pos with
      | None -> result id JNull
      | Some text ->
          result id (JObj [
            "contents", JObj [
              "kind", JStr "markdown";
              "value", JStr ("```idsl\n" ^ text ^ "\n```");
            ];
          ])

(* ---------- Round-1 navigation handlers ---------- *)

let lsp_pos_to_json = lsp_pos_json

let sym_range_to_json (r : Lsp_query.sym_range) : Json.t =
  range_json r.sr_start r.sr_end

let rec doc_symbol_to_json (s : Lsp_query.doc_symbol) : Json.t =
  let base = [
    "name",           Json.JStr s.ds_name;
    "kind",           JNum (float_of_int s.ds_kind);
    "range",          sym_range_to_json s.ds_range;
    "selectionRange", sym_range_to_json s.ds_selection;
    "children",       JArr (List.map doc_symbol_to_json s.ds_children);
  ] in
  let with_detail = match s.ds_detail with
    | Some d -> base @ [ "detail", JStr d ]
    | None   -> base
  in
  JObj with_detail

let handle_document_symbol id params =
  let uri = match json_field params "textDocument" with
    | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> "" in
  match get_src uri with
  | None -> result id (JArr [])
  | Some _ ->
    let in_file = Workspace.path_of_uri uri in
    let s = Workspace.compile_doc ws ~uri in
    match Session.index s with
    | Some idx ->
        let syms = Lsp_query.document_symbols ~in_file idx s.cst in
        result id (JArr (List.map doc_symbol_to_json syms))
    | None ->
        (* Fall back to the last good compile when the current doc has
           parse / typecheck errors — keeps the outline visible. *)
        match Hashtbl.find_opt last_good uri with
        | Some (prog, tp) ->
            let idx = Semantic_index.build prog tp s.cst in
            let syms = Lsp_query.document_symbols ~in_file idx s.cst in
            result id (JArr (List.map doc_symbol_to_json syms))
        | None -> result id (JArr [])

(* SymbolInformation: the URI must be the symbol's *own* declaration
   site, not the URI of whichever session happened to surface it.  A
   single symbol declared in a.idsl is reachable from main.idsl's
   flattened session too, but its location must always be a.idsl. *)
let symbol_info_to_json ~fallback_uri (s : Symbol.t) : Json.t =
  let kind = Lsp_query.lsp_kind_of_symbol_kind s.kind in
  let lp = Lsp_query.pos_lsp_of_lex s.decl_pos in
  let len = String.length (Lsp_query.symbol_name s.kind) in
  let end_p = { lp with character = lp.character + len } in
  let uri =
    Workspace.uri_of_pos_fname ~fallback:fallback_uri s.decl_pos.pos_fname in
  JObj [
    "name", JStr s.label;
    "kind", JNum (float_of_int kind);
    "location", JObj [
      "uri",   JStr uri;
      "range", JObj [
        "start", lsp_pos_to_json lp;
        "end",   lsp_pos_to_json end_p;
      ]
    ]
  ]

let handle_workspace_symbol id params =
  let q = match json_field params "query" with
    | Some (JStr s) -> s | _ -> "" in
  (* `compile_all_known` covers open + on-disk files; sessions that
     flatten includes will surface the same Symbol.kind multiple times,
     so dedupe by kind across the whole walk. *)
  let seen : (Symbol.kind, unit) Hashtbl.t = Hashtbl.create 32 in
  let acc = ref [] in
  List.iter (fun (uri, (s : Session.t)) ->
    match s.ast, s.typed with
    | Some prog, Some tp ->
        let idx = Semantic_index.build prog tp s.cst in
        let matches = Lsp_query.workspace_symbols idx q in
        List.iter (fun (sym : Symbol.t) ->
          if not (Hashtbl.mem seen sym.kind) then begin
            Hashtbl.add seen sym.kind ();
            acc := symbol_info_to_json ~fallback_uri:uri sym :: !acc
          end) matches
    | _ -> ()) (Workspace.compile_all_known ws);
  result id (JArr !acc)

let handle_document_highlight id params =
  let uri = match json_field params "textDocument" with
    | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> "" in
  let pos = match json_field params "position" with
    | Some j -> lsp_pos_of_json_for_uri ~uri j
    | None   -> { Lsp_query.line = 0; character = 0 } in
  match get_src uri with
  | None -> result id (JArr [])
  | Some src ->
    match index_for uri src with
    | None -> result id (JArr [])
    | Some idx ->
      match Lsp_query.document_highlights_at idx pos with
      | None -> result id (JArr [])
      | Some sites ->
          (* DocumentHighlightKind: 1=Text, 2=Read, 3=Write. We don't yet
             distinguish reads from writes, so report everything as Text. *)
          let hs = List.filter_map (fun (p, len) ->
            if p = Lexing.dummy_pos then None
            else Some (Json.JObj [
              "range", range_of_pos p ~length:len;
              "kind",  Json.JNum 1.0;
            ])) sites in
          result id (JArr hs)

let handle_folding_range id params =
  let uri = match json_field params "textDocument" with
    | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> "" in
  match get_src uri with
  | None -> result id (JArr [])
  | Some _ ->
    let s = Workspace.compile_doc ws ~uri in
    let ranges = Lsp_query.folding_ranges s.cst in
    let arr = List.map (fun (s, e) ->
      Json.JObj [
        "startLine", JNum (float_of_int s);
        "endLine",   JNum (float_of_int e);
        "kind",      JStr "region";
      ]) ranges in
    result id (JArr arr)

let handle_selection_range id params =
  let uri = match json_field params "textDocument" with
    | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> "" in
  let positions = match json_field params "positions" with
    | Some (JArr xs) -> List.map (lsp_pos_of_json_for_uri ~uri) xs
    | _ -> [] in
  match get_src uri with
  | None -> result id (JArr [])
  | Some _ ->
    let s = Workspace.compile_doc ws ~uri in
    (* For each requested cursor, fold the chain of CST ranges (root-most
       first) into a linked Selection structure (innermost first, parent
       link to outer). *)
    let chain_of pos =
      let chain = Lsp_query.selection_ranges_at s.cst pos in
      let chain = List.rev chain in   (* innermost first *)
      let rec build = function
        | [] -> Json.JNull
        | r :: rest ->
            let parent = build rest in
            JObj [
              "range",  sym_range_to_json r;
              "parent", parent;
            ]
      in
      build chain
    in
    let arr = List.map chain_of positions in
    result id (JArr arr)

(* ---------- Round-2 information handlers ---------- *)

let sig_param_to_json (p : Lsp_query.sig_param) : Json.t =
  JObj [
    "label", JArr [
      JNum (float_of_int p.sp_start);
      JNum (float_of_int p.sp_end);
    ];
  ]

let signature_info_to_json (s : Lsp_query.signature_info) : Json.t =
  JObj [
    "label",      JStr s.si_label;
    "parameters", JArr (List.map sig_param_to_json s.si_params);
  ]

let handle_signature_help id params =
  let uri = match json_field params "textDocument" with
    | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> "" in
  let pos = match json_field params "position" with
    | Some j -> lsp_pos_of_json_for_uri ~uri j
    | None   -> { Lsp_query.line = 0; character = 0 } in
  match get_src uri with
  | None -> result id JNull
  | Some src ->
    match best_effort_progs uri src with
    | None, _ -> result id JNull
    | Some (_, tp), cst ->
      match Lsp_query.signature_help_at tp cst pos with
      | None -> result id JNull
      | Some sh ->
          result id (JObj [
            "signatures",      JArr (List.map signature_info_to_json sh.sh_signatures);
            "activeSignature", JNum 0.0;
            "activeParameter", JNum (float_of_int sh.sh_active_param);
          ])

let handle_inlay_hint id params =
  let uri = match json_field params "textDocument" with
    | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> "" in
  let start_line, end_line =
    match json_field params "range" with
    | Some r ->
        let s = match json_field r "start" with
          | Some j -> lsp_pos_of_json_for_uri ~uri j
          | None   -> { Lsp_query.line = 0; character = 0 } in
        let e = match json_field r "end" with
          | Some j -> lsp_pos_of_json_for_uri ~uri j
          | None   -> { Lsp_query.line = max_int / 2; character = 0 } in
        s.line, e.line
    | None -> 0, max_int / 2
  in
  match get_src uri with
  | None -> result id (JArr [])
  | Some src ->
    match best_effort_progs uri src with
    | None, _ -> result id (JArr [])
    | Some (_, tp), _ ->
        let hints = Lsp_query.inlay_hints_in_range tp ~start_line ~end_line in
        let arr = List.map (fun (h : Lsp_query.inlay_hint) ->
          Json.JObj [
            "position",     lsp_pos_to_json h.ih_pos;
            "label",        JStr h.ih_label;
            "kind",         JNum (float_of_int h.ih_kind);
            "paddingRight", JBool h.ih_pad_r;
          ]) hints in
        result id (JArr arr)

let handle_code_lens id params =
  let uri = match json_field params "textDocument" with
    | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> "" in
  match get_src uri with
  | None -> result id (JArr [])
  | Some src ->
    match index_for uri src with
    | None -> result id (JArr [])
    | Some idx ->
        let lenses = Lsp_query.code_lenses_for idx in
        let arr = List.map (fun (l : Lsp_query.code_lens) ->
          let lp = Lsp_query.pos_lsp_of_lex l.cl_target in
          Json.JObj [
            "range",   sym_range_to_json l.cl_range;
            "command", JObj [
              "title",     JStr l.cl_label;
              "command",   JStr "editor.action.showReferences";
              "arguments", JArr [
                JStr uri;
                lsp_pos_to_json lp;
                JArr [];
              ];
            ];
          ]) lenses in
        result id (JArr arr)

let handle_semantic_tokens id params =
  let uri = match json_field params "textDocument" with
    | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> "" in
  match get_src uri with
  | None -> result id (JObj [ "data", JArr [] ])
  | Some src ->
    match index_for uri src with
    | None -> result id (JObj [ "data", JArr [] ])
    | Some idx ->
        let s = Workspace.compile_doc ws ~uri in
        let data = Lsp_query.semantic_tokens_of idx s.cst_tokens in
        let arr = List.map (fun n -> Json.JNum (float_of_int n)) data in
        result id (JObj [ "data", JArr arr ])

(* ---------- Round-3 refactor handlers ---------- *)

(* Group `(uri, JSON-encoded TextEdit)` pairs into the LSP WorkspaceEdit
   `changes` shape: `{ uri -> TextEdit[] }`. Used by both rename and
   willRenameFiles so neither has to redo the bucketize-then-fold dance. *)
let workspace_edit_changes (pairs : (string * Json.t) list) : Json.t =
  let by_uri : (string, Json.t list) Hashtbl.t = Hashtbl.create 4 in
  List.iter (fun (u, e) ->
    let cur = try Hashtbl.find by_uri u with Not_found -> [] in
    Hashtbl.replace by_uri u (e :: cur)) pairs;
  let changes = Hashtbl.fold (fun u xs acc ->
    (u, Json.JArr (List.rev xs)) :: acc) by_uri [] in
  Json.JObj [ "changes", Json.JObj changes ]

(* Each edit's range is in *byte* columns (the indexer counts bytes
   when computing decl/ref lengths).  Convert to UTF-16 against the
   target file's source so `Range.character` is wire-correct. *)
let text_edit_to_json (e : Lsp_query.text_edit) : Json.t =
  let src =
    if e.te_pos_fname = "" then ""
    else
      let uri = Workspace.uri_of_pos_fname ~fallback:"" e.te_pos_fname in
      source_for_uri uri
  in
  JObj [
    "range",   utf16_range ~src e.te_range.sr_start e.te_range.sr_end;
    "newText", JStr e.te_new_text;
  ]

let handle_prepare_rename id params =
  let uri = match json_field params "textDocument" with
    | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> "" in
  let pos = match json_field params "position" with
    | Some j -> lsp_pos_of_json_for_uri ~uri j
    | None   -> { Lsp_query.line = 0; character = 0 } in
  match get_src uri with
  | None -> result id JNull
  | Some src ->
    match index_for uri src with
    | None -> result id JNull
    | Some idx ->
      match Lsp_query.prepare_rename idx pos with
      | None -> result id JNull
      | Some rt ->
          (* LSP allows three return shapes; we use the {range,placeholder}
             form so the inline rename box is pre-populated. *)
          result id (JObj [
            "range",       sym_range_to_json rt.rt_range;
            "placeholder", JStr rt.rt_label;
          ])

let handle_rename id params =
  let uri = match json_field params "textDocument" with
    | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> "" in
  let pos = match json_field params "position" with
    | Some j -> lsp_pos_of_json_for_uri ~uri j
    | None   -> { Lsp_query.line = 0; character = 0 } in
  let new_name = match json_field params "newName" with
    | Some (JStr s) -> s | _ -> "" in
  match get_src uri with
  | None -> result id JNull
  | Some src ->
    match index_for uri src with
    | None -> result id JNull
    | Some idx ->
      let refs sym = Workspace.aggregated_references ws ~current_uri:uri sym in
      match Lsp_query.rename_at ~refs idx pos ~new_name with
      | None -> result id JNull
      | Some edits ->
          let pairs = List.map (fun (e : Lsp_query.text_edit) ->
            Workspace.uri_of_pos_fname ~fallback:uri e.te_pos_fname,
            text_edit_to_json e) edits in
          result id (workspace_edit_changes pairs)

(* For each diagnostic in the request, find a quick fix by message
   pattern, then build a TextEdit by locating the bad identifier on the
   source line — this side has the document text. *)
let handle_code_action id params =
  let uri = match json_field params "textDocument" with
    | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> "" in
  let diags = match json_field params "context" with
    | Some ctx ->
        (match json_field ctx "diagnostics" with
         | Some (JArr xs) -> xs | _ -> [])
    | None -> [] in
  match get_src uri with
  | None -> result id (JArr [])
  | Some src ->
    let lines = String.split_on_char '\n' src in
    let line_at i =
      if i < 0 || i >= List.length lines then "" else List.nth lines i in
    let actions = ref [] in
    List.iter (fun d ->
      let msg = match json_field d "message" with
        | Some (JStr s) -> s | _ -> "" in
      let line, col =
        match json_field d "range" with
        | Some r ->
            let s = match json_field r "start" with
              | Some j -> lsp_pos_of_json_for_uri ~uri j
              | None   -> { Lsp_query.line = 0; character = 0 } in
            s.line, s.character
        | None -> 0, 0
      in
      let qfs = Lsp_query.quick_fixes_for_message ~line ~col msg in
      List.iter (fun (qf : Lsp_query.quick_fix) ->
        (* Find bad identifier on the diagnostic's line, starting at col. *)
        let l_text = line_at qf.qf_diag_line in
        let needle = qf.qf_find in
        let idx_opt =
          try Some (Str.search_forward
                      (Str.regexp_string needle) l_text qf.qf_diag_col)
          with Not_found ->
            (try Some (Str.search_forward
                         (Str.regexp_string needle) l_text 0)
             with Not_found -> None)
        in
        match idx_opt with
        | None -> ()
        | Some col0 ->
            let edit = {
              Lsp_query.te_pos_fname = "";
              te_range = {
                sr_start = { line = qf.qf_diag_line; character = col0 };
                sr_end   = { line = qf.qf_diag_line;
                             character = col0 + String.length needle };
              };
              te_new_text = qf.qf_replace;
            } in
            actions := Json.JObj [
              "title",       Json.JStr qf.qf_title;
              "kind",        Json.JStr "quickfix";
              "isPreferred", Json.JBool true;
              "edit",        Json.JObj [
                "changes", Json.JObj [
                  uri, Json.JArr [text_edit_to_json edit];
                ];
              ];
              "diagnostics", Json.JArr [d];
            ] :: !actions) qfs) diags;
    result id (JArr (List.rev !actions))

(* ---------- Round-4 formatting handlers ---------- *)

let line_count_of (s : string) : int =
  let n = ref 1 in
  String.iter (fun c -> if c = '\n' then incr n) s;
  !n

let last_line_text (s : string) : string =
  match String.rindex_opt s '\n' with
  | None   -> s
  | Some i -> String.sub s (i + 1) (String.length s - i - 1)

let handle_formatting id params =
  let uri = match json_field params "textDocument" with
    | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> "" in
  match get_src uri with
  | None -> result id (JArr [])
  | Some src ->
      let s = Workspace.compile_doc ws ~uri in
      let formatted = Lsp_query.format_full s.cst in
      if formatted = src then result id (JArr [])
      else
        let last_ln = line_count_of src - 1 in
        let last_col = String.length (last_line_text src) in
        let edit = Json.JObj [
          "range", Json.JObj [
            "start", Json.JObj [ "line", JNum 0.0; "character", JNum 0.0 ];
            "end",   Json.JObj [ "line", JNum (float_of_int last_ln);
                                 "character", JNum (float_of_int last_col) ];
          ];
          "newText", JStr formatted;
        ] in
        result id (JArr [edit])

let handle_range_formatting id params =
  let uri = match json_field params "textDocument" with
    | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> "" in
  let s_ln, e_ln =
    match json_field params "range" with
    | Some r ->
        let s = match json_field r "start" with
          | Some j -> lsp_pos_of_json_for_uri ~uri j
          | None   -> { Lsp_query.line = 0; character = 0 } in
        let e = match json_field r "end" with
          | Some j -> lsp_pos_of_json_for_uri ~uri j
          | None   -> s in
        s.line, e.line
    | None -> 0, 0
  in
  match get_src uri with
  | None -> result id (JArr [])
  | Some src ->
      let formatted, range =
        Lsp_query.format_range src ~start_line:s_ln ~end_line:e_ln in
      let edit = Json.JObj [
        "range",   sym_range_to_json range;
        "newText", JStr formatted;
      ] in
      result id (JArr [edit])

let handle_on_type_formatting id params =
  let uri = match json_field params "textDocument" with
    | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> "" in
  let pos = match json_field params "position" with
    | Some j -> lsp_pos_of_json_for_uri ~uri j
    | None   -> { Lsp_query.line = 0; character = 0 } in
  let ch = match json_field params "ch" with
    | Some (JStr s) -> s | _ -> "" in
  match get_src uri with
  | None -> result id (JArr [])
  | Some src ->
      let edits = Lsp_query.on_type_format ~src ~line:pos.line ~ch in
      let arr = List.map text_edit_to_json edits in
      result id (JArr arr)

(* ---------- Round-7 advanced handlers ---------- *)

(* `uri` is the *fallback* — used when the position carries no source
   filename (in-memory buffer not stamped via `Lexing.set_filename`).
   When `pos_fname` is set, the location is routed to that file. *)
let location_of_pos ~fallback (p : Lexing.position) ~length : Json.t =
  let lp = Lsp_query.pos_lsp_of_lex p in
  let end_p = { lp with character = lp.character + length } in
  let target_uri = Workspace.uri_of_pos_fname ~fallback p.pos_fname in
  let src = source_for_uri target_uri in
  Json.JObj [
    "uri",   Json.JStr target_uri;
    "range", utf16_range ~src lp end_p;
  ]

(* Standard "textDocument + position → optional (uri, pos, idx)" pull.
   Centralizes the four-line boilerplate every position-driven handler
   would otherwise repeat. *)
let with_text_doc_pos params : (string * Lsp_query.lsp_pos * Semantic_index.t) option =
  let uri = match json_field params "textDocument" with
    | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> "" in
  let pos = match json_field params "position" with
    | Some j -> lsp_pos_of_json_for_uri ~uri j
    | None   -> { Lsp_query.line = 0; character = 0 } in
  match get_src uri with
  | None -> None
  | Some src ->
    match index_for uri src with
    | None -> None
    | Some idx -> Some (uri, pos, idx)

let handle_declaration id params =
  match with_text_doc_pos params with
  | None -> result id JNull
  | Some (uri, pos, idx) ->
    match Lsp_query.declaration_at idx pos with
    | None -> result id JNull
    | Some (p, _) -> result id (location_of_pos ~fallback:uri p ~length:1)

let handle_type_definition id params =
  let uri = match json_field params "textDocument" with
    | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> "" in
  let pos = match json_field params "position" with
    | Some j -> lsp_pos_of_json_for_uri ~uri j
    | None   -> { Lsp_query.line = 0; character = 0 } in
  match get_src uri with
  | None -> result id JNull
  | Some src ->
    match best_effort_progs uri src with
    | None, _ -> result id JNull
    | Some (_, tp), _ ->
      match index_for uri src with
      | None -> result id JNull
      | Some idx ->
        match Lsp_query.type_definition_at idx tp pos with
        | None -> result id JNull
        | Some (p, _label) ->
            result id (location_of_pos ~fallback:uri p ~length:1)

let handle_implementation = handle_declaration

(* Call / type hierarchy *)

let call_item_to_json ~fallback_uri (it : Lsp_query.call_item) : Json.t =
  let uri = Workspace.uri_of_pos_fname ~fallback:fallback_uri it.ci_pos_fname in
  Json.JObj [
    "name",           Json.JStr it.ci_name;
    "kind",           Json.JNum (float_of_int it.ci_kind_int);
    "uri",            Json.JStr uri;
    "range",          sym_range_to_json it.ci_range;
    "selectionRange", sym_range_to_json it.ci_selection;
    "data",           Json.JStr it.ci_data_id;
  ]

let handle_prepare_call_hierarchy id params =
  let uri = match json_field params "textDocument" with
    | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> "" in
  let pos = match json_field params "position" with
    | Some j -> lsp_pos_of_json_for_uri ~uri j
    | None   -> { Lsp_query.line = 0; character = 0 } in
  match get_src uri with
  | None -> result id (JArr [])
  | Some src ->
    match index_for uri src with
    | None -> result id (JArr [])
    | Some idx ->
      match Lsp_query.prepare_call_hierarchy idx pos with
      | None -> result id (JArr [])
      | Some it -> result id (JArr [call_item_to_json ~fallback_uri:uri it])

let parse_item params : (string * Lsp_query.call_item) option =
  match json_field params "item" with
  | Some it ->
      let uri = match json_field it "uri" with
        | Some j -> json_str j | _ -> "" in
      let name = match json_field it "name" with
        | Some j -> json_str j | _ -> "" in
      let data = match json_field it "data" with
        | Some j -> json_str j | _ -> "" in
      let kind = match json_field it "kind" with
        | Some n -> json_num n | _ -> 0 in
      let dummy_range = {
        Lsp_query.sr_start = { line = 0; character = 0 };
        sr_end             = { line = 0; character = 0 };
      } in
      let pos_fname = match json_field it "data" with
        | Some _ -> ""    (* not threaded across protocol boundary *)
        | None   -> "" in
      Some (uri, {
        ci_name      = name;
        ci_kind_int  = kind;
        ci_pos_fname = pos_fname;
        ci_range     = dummy_range;
        ci_selection = dummy_range;
        ci_data_id   = data;
      })
  | None -> None

let handle_call_hierarchy_incoming id params =
  match parse_item params with
  | None -> result id (JArr [])
  | Some (uri, it) ->
    match get_src uri with
    | None -> result id (JArr [])
    | Some src ->
      match best_effort_progs uri src with
      | None, _ -> result id (JArr [])
      | Some (_, tp), _ ->
        match index_for uri src with
        | None -> result id (JArr [])
        | Some idx ->
          let items = Lsp_query.incoming_calls idx tp it in
          result id (JArr (List.map (fun caller ->
            Json.JObj [
              "from",       call_item_to_json ~fallback_uri:uri caller;
              "fromRanges", Json.JArr [sym_range_to_json caller.ci_range];
            ]) items))

let handle_call_hierarchy_outgoing id params =
  match parse_item params with
  | None -> result id (JArr [])
  | Some (uri, it) ->
    match get_src uri with
    | None -> result id (JArr [])
    | Some src ->
      match best_effort_progs uri src with
      | None, _ -> result id (JArr [])
      | Some (_, tp), _ ->
        match index_for uri src with
        | None -> result id (JArr [])
        | Some idx ->
          let items = Lsp_query.outgoing_calls idx tp it in
          result id (JArr (List.map (fun callee ->
            Json.JObj [
              "to",         call_item_to_json ~fallback_uri:uri callee;
              "fromRanges", Json.JArr [sym_range_to_json callee.ci_range];
            ]) items))

let handle_prepare_type_hierarchy id params =
  let uri = match json_field params "textDocument" with
    | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> "" in
  let pos = match json_field params "position" with
    | Some j -> lsp_pos_of_json_for_uri ~uri j
    | None   -> { Lsp_query.line = 0; character = 0 } in
  match get_src uri with
  | None -> result id (JArr [])
  | Some src ->
    match index_for uri src with
    | None -> result id (JArr [])
    | Some idx ->
      match Lsp_query.prepare_type_hierarchy idx pos with
      | None -> result id (JArr [])
      | Some it -> result id (JArr [call_item_to_json ~fallback_uri:uri it])

let type_hierarchy_dispatch fn id params =
  match parse_item params with
  | None -> result id (JArr [])
  | Some (uri, it) ->
    match get_src uri with
    | None -> result id (JArr [])
    | Some src ->
      match best_effort_progs uri src with
      | None, _ -> result id (JArr [])
      | Some (_, tp), _ ->
        match index_for uri src with
        | None -> result id (JArr [])
        | Some idx ->
          let items = fn idx tp it in
          result id (JArr (List.map (call_item_to_json ~fallback_uri:uri) items))

let handle_type_hierarchy_supertypes =
  type_hierarchy_dispatch Lsp_query.supertypes
let handle_type_hierarchy_subtypes =
  type_hierarchy_dispatch Lsp_query.subtypes

(* pullDiagnostics — same data we already push, packaged as a "full
   document diagnostic report" per LSP 3.17. Each call also surfaces
   unused-symbol hints from the index. *)

let unused_diag_json (p, len, msg) : Json.t =
  let lp = Lsp_query.pos_lsp_of_lex p in
  let end_p = { lp with character = lp.character + len } in
  Json.JObj [
    "range",    range_json lp end_p;
    "severity", Json.JNum 4.0;            (* Hint *)
    "source",   Json.JStr "idsl-lint";
    "message",  Json.JStr msg;
    "tags",     Json.JArr [Json.JNum 1.0]; (* Unnecessary *)
  ]

let handle_pull_diagnostics id params =
  let uri = match json_field params "textDocument" with
    | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
    | _ -> "" in
  match get_src uri with
  | None -> result id (Json.JObj [
      "kind",  Json.JStr "full";
      "items", Json.JArr [];
    ])
  | Some _ ->
    let s = Workspace.compile_doc ws ~uri in
    let src = source_for_uri uri in
    let regular =
      List.map (fun d -> diagnostic_json ~src (Lsp_query.lsp_of_diag d))
        s.diagnostics in
    let unused = match Session.index s with
      | Some idx -> List.map unused_diag_json (Lsp_query.unused_diagnostics idx)
      | None     -> [] in
    result id (Json.JObj [
      "kind",  Json.JStr "full";
      "items", Json.JArr (regular @ unused);
    ])

(* willRenameFiles — client wants to rename files; we look at every open
   doc and patch its `include "..."` strings. *)

let handle_will_rename_files id params =
  let files = match json_field params "files" with
    | Some (JArr xs) -> xs | _ -> [] in
  (* Scan every known *.idsl (open + on-disk) so file rename also
     patches `include` strings in files the editor hasn't opened.
     Open buffers' unsaved content wins over the disk copy. *)
  let docs =
    Workspace.all_known_uris ws
    |> List.filter_map (fun u ->
         match Workspace.get_doc ws ~uri:u with
         | Some d -> Some (u, d.content)
         | None ->
             match Workspace.read_file_opt (Workspace.path_of_uri u) with
             | Some content -> Some (u, content)
             | None -> None) in
  let all_edits = List.concat_map (fun f ->
    let old_uri = match json_field f "oldUri" with
      | Some j -> json_str j | _ -> "" in
    let new_uri = match json_field f "newUri" with
      | Some j -> json_str j | _ -> "" in
    Lsp_query.rename_files_edits ~docs ~old_uri ~new_uri) files in
  let pairs = List.map (fun (uri, e) -> uri, text_edit_to_json e) all_edits in
  result id (workspace_edit_changes pairs)

(* ---------- Round-5 workspace handlers ----------

   - workspace/didChangeWatchedFiles  invalidate caches for files that
     changed on disk while the editor was idle (e.g., rebase, save in
     another tool).
   - workspace/didChangeConfiguration  store user-settable options on
     the Workspace (currently unused; demo path).
   - workspace/didChangeWorkspaceFolders  keep workspace.folders in sync.
   - workspace/executeCommand  custom server actions; used here to run
     all `test "..."` blocks of the focused doc and return the report.
*)

let handle_did_change_watched_files oc params =
  let changes = match json_field params "changes" with
    | Some (JArr xs) -> xs | _ -> [] in
  (* Any create / delete shifts the set of files under workspace
     folders; invalidate the scan cache so the next workspace/symbol
     query sees the new state. *)
  Workspace.invalidate_folder_scan ws;
  List.iter (fun c ->
    let uri = match json_field c "uri" with
      | Some j -> json_str j | _ -> "" in
    let typ = match json_field c "type" with
      | Some n -> json_num n | None -> 0 in
    (* type: 1=Created, 2=Changed, 3=Deleted *)
    if typ = 3 then Workspace.remove_doc ws ~uri
    else begin
      let affected = Workspace.invalidate ws ~uri in
      List.iter (fun u ->
        if Workspace.get_doc ws ~uri:u <> None then
          analyze_and_publish oc u) affected
    end) changes

let handle_did_change_configuration _oc params =
  match json_field params "settings" with
  | Some (Json.JObj kvs) ->
      List.iter (fun (k, v) ->
        let value = match v with
          | Json.JStr s -> s
          | JNum n      -> string_of_float n
          | JBool b     -> string_of_bool b
          | _ -> "" in
        Workspace.set_config ws ~key:k ~value) kvs
  | _ -> ()

let handle_did_change_workspace_folders _oc params =
  match json_field params "event" with
  | Some ev ->
      let added = match json_field ev "added" with
        | Some (JArr xs) -> List.filter_map (fun f ->
            match json_field f "uri" with
            | Some j -> Some (json_str j) | _ -> None) xs
        | _ -> [] in
      let removed = match json_field ev "removed" with
        | Some (JArr xs) -> List.filter_map (fun f ->
            match json_field f "uri" with
            | Some j -> Some (json_str j) | _ -> None) xs
        | _ -> [] in
      let cur = Workspace.folders ws in
      let cur = List.filter (fun u -> not (List.mem u removed)) cur in
      Workspace.set_folders ws (cur @ added)
  | None -> ()

(* Pretty-print the test report into a JSON object the client can render. *)
let run_tests_for_uri uri =
  match Workspace.get_doc ws ~uri with
  | None -> Json.JObj [ "ok", JBool false; "error", JStr "no such doc" ]
  | Some _ ->
    let s = Workspace.compile_doc ws ~uri in
    match s.typed with
    | None ->
        JObj [ "ok", JBool false;
               "error", JStr "doc has compile errors" ]
    | Some tp ->
        let results, _ = Eval.run_all tp in
        let to_json (r : Eval.test_result) = Json.JObj [
          "name",     JStr r.rname;
          "passed",   JBool r.passed;
          "failures", JArr (List.map (fun s -> Json.JStr s) r.failures);
          "fired",    JArr (List.map (fun s -> Json.JStr s) r.fired);
        ] in
        JObj [
          "ok",      JBool true;
          "total",   JNum (float_of_int (List.length results));
          "passed",  JNum (float_of_int (List.length
                            (List.filter (fun r -> r.Eval.passed) results)));
          "results", JArr (List.map to_json results);
        ]

let handle_execute_command id params =
  let cmd = match json_field params "command" with
    | Some (JStr s) -> s | _ -> "" in
  let args = match json_field params "arguments" with
    | Some (JArr xs) -> xs | _ -> [] in
  match cmd with
  | "idsl.runTests" ->
      let uri = match args with
        | (JStr s) :: _ -> s
        | _ -> match Workspace.all_uris ws with u :: _ -> u | _ -> "" in
      result id (run_tests_for_uri uri)
  | "idsl.printSymbols" ->
      let uri = match args with
        | (JStr s) :: _ -> s
        | _ -> match Workspace.all_uris ws with u :: _ -> u | _ -> "" in
      let s = Workspace.compile_doc ws ~uri in
      let arr = match s.ast, s.typed with
        | Some prog, Some tp ->
            let idx = Semantic_index.build prog tp s.cst in
            Lsp_query.workspace_symbols idx ""
            |> List.map (fun (sy : Symbol.t) -> Json.JStr sy.label)
        | _ -> [] in
      result id (JObj [ "ok", JBool true; "symbols", JArr arr ])
  | _ ->
      result id (JObj [ "ok", JBool false;
                        "error", JStr ("unknown command: " ^ cmd) ])

(* ---------- main loop ---------- *)

let () =
  let ic = stdin and oc = stdout in
  set_binary_mode_in ic true;
  set_binary_mode_out oc true;
  let running = ref true in
  while !running do
    match read_message ic with
    | None -> running := false
    | Some msg ->
        let method_ = match json_field msg "method" with
          | Some (JStr s) -> s | _ -> "" in
        let id = match json_field msg "id" with Some j -> j | _ -> JNull in
        let params = match json_field msg "params" with
          | Some j -> j | _ -> JNull in
        (match method_ with
         | "initialize"  -> write_message oc (handle_initialize id params)
         | "initialized" ->
             (* Server → client: dynamically register interest in
                file-system events for *.idsl. Without this, the
                workspace cache only learns about disk changes when
                the editor *happens* to be configured to forward them
                — which most clients don't do without an explicit
                registration request. *)
             let req = Json.JObj [
               "jsonrpc", Json.JStr "2.0";
               "id",      Json.JStr "watcher-registration";
               "method",  Json.JStr "client/registerCapability";
               "params",  Json.JObj [
                 "registrations", Json.JArr [
                   Json.JObj [
                     "id",     Json.JStr "idsl-file-watcher";
                     "method", Json.JStr "workspace/didChangeWatchedFiles";
                     "registerOptions", Json.JObj [
                       "watchers", Json.JArr [
                         Json.JObj [ "globPattern", Json.JStr "**/*.idsl" ];
                       ];
                     ];
                   ];
                 ];
               ];
             ] in
             write_message oc req
         | "textDocument/didOpen"   -> handle_did_open oc params
         | "textDocument/didChange" -> handle_did_change oc params
         | "textDocument/didSave"   -> ()
         | "textDocument/didClose"  ->
             let uri = match json_field params "textDocument" with
               | Some td -> (match json_field td "uri" with Some j -> json_str j | _ -> "")
               | _ -> "" in
             Workspace.remove_doc ws ~uri
         | "textDocument/hover" ->
             write_message oc (handle_hover id params)
         | "textDocument/completion" ->
             write_message oc (handle_completion id params)
         | "textDocument/definition" ->
             write_message oc (handle_definition id params)
         | "textDocument/references" ->
             write_message oc (handle_references id params)
         | "textDocument/documentSymbol" ->
             write_message oc (handle_document_symbol id params)
         | "workspace/symbol" ->
             write_message oc (handle_workspace_symbol id params)
         | "textDocument/documentHighlight" ->
             write_message oc (handle_document_highlight id params)
         | "textDocument/foldingRange" ->
             write_message oc (handle_folding_range id params)
         | "textDocument/selectionRange" ->
             write_message oc (handle_selection_range id params)
         | "textDocument/signatureHelp" ->
             write_message oc (handle_signature_help id params)
         | "textDocument/inlayHint" ->
             write_message oc (handle_inlay_hint id params)
         | "textDocument/codeLens" ->
             write_message oc (handle_code_lens id params)
         | "textDocument/semanticTokens/full" ->
             write_message oc (handle_semantic_tokens id params)
         | "textDocument/prepareRename" ->
             write_message oc (handle_prepare_rename id params)
         | "textDocument/rename" ->
             write_message oc (handle_rename id params)
         | "textDocument/codeAction" ->
             write_message oc (handle_code_action id params)
         | "textDocument/formatting" ->
             write_message oc (handle_formatting id params)
         | "textDocument/rangeFormatting" ->
             write_message oc (handle_range_formatting id params)
         | "textDocument/onTypeFormatting" ->
             write_message oc (handle_on_type_formatting id params)
         | "completionItem/resolve" ->
             write_message oc (handle_completion_resolve id params)
         | "workspace/didChangeWatchedFiles" ->
             handle_did_change_watched_files oc params
         | "workspace/didChangeConfiguration" ->
             handle_did_change_configuration oc params
         | "workspace/didChangeWorkspaceFolders" ->
             handle_did_change_workspace_folders oc params
         | "workspace/executeCommand" ->
             write_message oc (handle_execute_command id params)
         | "textDocument/declaration" ->
             write_message oc (handle_declaration id params)
         | "textDocument/typeDefinition" ->
             write_message oc (handle_type_definition id params)
         | "textDocument/implementation" ->
             write_message oc (handle_implementation id params)
         | "textDocument/prepareCallHierarchy" ->
             write_message oc (handle_prepare_call_hierarchy id params)
         | "callHierarchy/incomingCalls" ->
             write_message oc (handle_call_hierarchy_incoming id params)
         | "callHierarchy/outgoingCalls" ->
             write_message oc (handle_call_hierarchy_outgoing id params)
         | "textDocument/prepareTypeHierarchy" ->
             write_message oc (handle_prepare_type_hierarchy id params)
         | "typeHierarchy/supertypes" ->
             write_message oc (handle_type_hierarchy_supertypes id params)
         | "typeHierarchy/subtypes" ->
             write_message oc (handle_type_hierarchy_subtypes id params)
         | "textDocument/diagnostic" ->
             write_message oc (handle_pull_diagnostics id params)
         | "workspace/willRenameFiles" ->
             write_message oc (handle_will_rename_files id params)
         | "shutdown" -> write_message oc (ok_response id)
         | "exit"     -> running := false
         | other -> log "ignoring %s" other)
  done
