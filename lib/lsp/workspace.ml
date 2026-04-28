(* Workspace state for the language server.

   Holds the open-document table, a per-document compile cache, an
   include dependency graph, and the workspace-folder roots.

   Key idea: *every* request handler should fetch its compile through
   `compile_doc` instead of running `Session.compile_string` directly.
   That makes the LSP cache-aware (no recompile per hover) and
   incrementally correct (a `didChange` invalidates only affected docs).

   We do not yet inject in-memory document contents into include
   resolution — `compile_doc` runs `Session.compile_file` for files on
   disk and `Session.compile_string` for in-memory text. The hybrid case
   (file A includes B; both open with unsaved changes) reads B from disk
   and is therefore stale. The plumbing is sketched in `parse_with_docs`
   below for the next iteration. *)

type doc = {
  uri             : string;
  mutable content : string;
  mutable version : int;     (* LSP textDocument version *)
}

type t = {
  docs                       : (string, doc) Hashtbl.t;
  cache                      : (string, Session.t) Hashtbl.t;
  deps                       : (string, string list) Hashtbl.t;
  rdeps                      : (string, string list) Hashtbl.t;
  mutable folders            : string list;
  config                     : (string, string) Hashtbl.t;
  mutable folder_scan_cache  : string list option;
  mutable on_remove          : (uri:string -> unit) list;
}

let create () : t = {
  docs              = Hashtbl.create 16;
  cache             = Hashtbl.create 16;
  deps              = Hashtbl.create 16;
  rdeps             = Hashtbl.create 16;
  folders           = [];
  config            = Hashtbl.create 8;
  folder_scan_cache = None;
  on_remove         = [];
}

(* Subscribers fire whenever a doc is removed (didClose, watched-file
   delete). External caches that mirror per-doc data — `last_good` in
   the LSP binary, for example — register here so they don't grow
   unbounded as the user opens / closes files over a long session. *)
let on_remove ws (cb : uri:string -> unit) =
  ws.on_remove <- cb :: ws.on_remove

(* Folder-scan results are stable until folders change or watched files
   announce a create/delete. Centralizing the invalidation here keeps
   the hot path on every `workspace/symbol` keystroke at O(1). *)
let invalidate_folder_scan ws = ws.folder_scan_cache <- None

let folders ws = ws.folders

let set_config ws ~key ~value = Hashtbl.replace ws.config key value
let get_config ws ~key = Hashtbl.find_opt ws.config key

(* ---------- URI ↔ path ----------

   Real LSP clients send RFC 3986 file URIs: percent-encoded, sometimes
   with an authority component (`file://localhost/...`), sometimes
   without (`file:///...`). Naive prefix stripping breaks on every one
   of: spaces (`%20`), unicode (`%E4%BE%8B`), the `localhost` authority
   form, and `#` fragments / `?` queries (which the protocol shouldn't
   send but bridges sometimes append). *)

let hex_digit c =
  match c with
  | '0'..'9' -> Some (Char.code c - Char.code '0')
  | 'a'..'f' -> Some (Char.code c - Char.code 'a' + 10)
  | 'A'..'F' -> Some (Char.code c - Char.code 'A' + 10)
  | _ -> None

let percent_decode (s : string) : string =
  let n = String.length s in
  let b = Buffer.create n in
  let i = ref 0 in
  while !i < n do
    let c = s.[!i] in
    if c = '%' && !i + 2 < n then begin
      match hex_digit s.[!i + 1], hex_digit s.[!i + 2] with
      | Some hi, Some lo ->
          Buffer.add_char b (Char.chr (hi lsl 4 lor lo));
          i := !i + 3
      | _ ->
          Buffer.add_char b c; incr i
    end else begin
      Buffer.add_char b c; incr i
    end
  done;
  Buffer.contents b

(* Per RFC 3986: unreserved = ALPHA / DIGIT / "-" / "." / "_" / "~",
   plus "/" preserved as a path separator. Everything else encoded. *)
let percent_encode_path (s : string) : string =
  let n = String.length s in
  let b = Buffer.create (n + 8) in
  String.iter (fun c ->
    let safe = match c with
      | 'A'..'Z' | 'a'..'z' | '0'..'9'
      | '-' | '.' | '_' | '~' | '/' -> true
      | _ -> false
    in
    if safe then Buffer.add_char b c
    else Buffer.add_string b (Printf.sprintf "%%%02X" (Char.code c))) s;
  Buffer.contents b

(* Strip the scheme and an optional authority, percent-decode the path,
   and drop any `?query` / `#fragment` we shouldn't ever receive but
   sometimes do via bridge layers. *)
let path_of_uri (uri : string) : string =
  let drop_after_first_of (s : string) (chars : char list) : string =
    let len = String.length s in
    let stop = ref len in
    String.iteri (fun i c ->
      if !stop = len && List.mem c chars then stop := i) s;
    String.sub s 0 !stop
  in
  let scheme = "file://" in
  let scheme_len = String.length scheme in
  if String.length uri >= scheme_len
     && String.sub uri 0 scheme_len = scheme
  then begin
    let rest = String.sub uri scheme_len (String.length uri - scheme_len) in
    let path =
      (* `file://localhost/...` and `file:///...` both denote the local
         host; an authority is everything up to the next `/`. *)
      match String.index_opt rest '/' with
      | Some 0 -> rest                                 (* file:///abs *)
      | Some i -> String.sub rest i (String.length rest - i)
      | None   -> "/" ^ rest                           (* file://host *)
    in
    percent_decode (drop_after_first_of path ['?'; '#'])
  end
  else uri

let uri_of_path (p : string) : string =
  if String.length p > 0 && p.[0] = '/'
  then "file://" ^ percent_encode_path p
  else p

(* The single canonical form every public Workspace entry point sees.
   Two equivalent file URIs (`file:///x`, `file://localhost/x`,
   `file:///dir/../x`, `file:///x?q=1`) all collapse to the same key
   here, so `docs` / `cache` / `deps` / `rdeps` can never end up with
   two parallel entries for the same physical file. *)
let canon_uri (uri : string) : string =
  let scheme = "file://" in
  let scheme_len = String.length scheme in
  if String.length uri >= scheme_len
     && String.sub uri 0 scheme_len = scheme
  then uri_of_path (Driver.canon (path_of_uri uri))
  else uri

(* Folders go through canon_uri + dedupe so two equivalent forms
   (`file:///proj`, `file://localhost/proj`, with/without trailing
   slash) collapse to one root. Without this the scan double-walks
   and didChangeWorkspaceFolders.add/remove can't reliably match. *)
let dedup_canon (urls : string list) : string list =
  let seen = Hashtbl.create 8 in
  List.filter_map (fun u ->
    let c = canon_uri u in
    if Hashtbl.mem seen c then None
    else begin Hashtbl.add seen c (); Some c end) urls

let set_folders ws (urls : string list) =
  ws.folders <- dedup_canon urls;
  invalidate_folder_scan ws

(* Map a `Lexing.position.pos_fname` into a `file://` URI, falling back
   to a caller-supplied URI when the position has no filename — most
   commonly: when the source came from a string buffer that wasn't
   stamped with `Lexing.set_filename`. *)
let uri_of_pos_fname ~fallback (fname : string) : string =
  if fname = "" then fallback
  else uri_of_path (Driver.canon fname)

(* Best-effort file read; the only file IO helper in this module so it
   can also clean up via Fun.protect (the rest of the codebase tends to
   leak file descriptors on exception). *)
let read_file_opt (path : string) : string option =
  try
    let ic = open_in path in
    Fun.protect
      ~finally:(fun () -> close_in_noerr ic)
      (fun () ->
         let len = in_channel_length ic in
         Some (really_input_string ic len))
  with _ -> None

(* ---------- doc table ---------- *)

let put_doc ws ~uri ~content ~version =
  let uri = canon_uri uri in
  match Hashtbl.find_opt ws.docs uri with
  | Some d ->
      d.content <- content;
      d.version <- version
  | None ->
      Hashtbl.add ws.docs uri { uri; content; version }

(* Monotonic version guard.  Equal versions are accepted as idempotent
   re-deliveries; strictly older ones are rejected with the current
   version so the caller can log and ignore. *)
let put_doc_versioned ws ~uri ~content ~version
    : [`Updated | `Stale of int] =
  let uri = canon_uri uri in
  match Hashtbl.find_opt ws.docs uri with
  | Some d when version < d.version -> `Stale d.version
  | Some d ->
      d.content <- content;
      d.version <- version;
      `Updated
  | None ->
      Hashtbl.add ws.docs uri { uri; content; version };
      `Updated

let remove_doc ws ~uri =
  let uri = canon_uri uri in
  Hashtbl.remove ws.docs uri;
  Hashtbl.remove ws.cache uri;
  Hashtbl.remove ws.deps uri;
  Hashtbl.iter (fun u xs ->
    let kept = List.filter (fun v -> v <> uri) xs in
    Hashtbl.replace ws.rdeps u kept) ws.rdeps;
  List.iter (fun cb -> cb ~uri) ws.on_remove

let get_doc ws ~uri = Hashtbl.find_opt ws.docs (canon_uri uri)

let all_uris ws = Hashtbl.fold (fun k _ acc -> k :: acc) ws.docs []

(* ---------- dep graph ---------- *)

(* Replace this doc's include set, updating reverse deps consistently. *)
let set_deps ws ~uri ~includes =
  let uri = canon_uri uri in
  let includes = List.map canon_uri includes in
  let prev = try Hashtbl.find ws.deps uri with Not_found -> [] in
  Hashtbl.replace ws.deps uri includes;
  (* Remove this uri from old reverse-dep entries no longer relevant. *)
  List.iter (fun old ->
    if not (List.mem old includes) then begin
      let kept =
        try List.filter (fun v -> v <> uri) (Hashtbl.find ws.rdeps old)
        with Not_found -> [] in
      if kept = [] then Hashtbl.remove ws.rdeps old
      else Hashtbl.replace ws.rdeps old kept
    end) prev;
  (* Add this uri to new reverse-dep entries. *)
  List.iter (fun newd ->
    let cur = try Hashtbl.find ws.rdeps newd with Not_found -> [] in
    if not (List.mem uri cur) then
      Hashtbl.replace ws.rdeps newd (uri :: cur))
    includes

let dependents_of ws ~uri =
  try Hashtbl.find ws.rdeps (canon_uri uri) with Not_found -> []

(* Drop compile-cache entries for every URI that isn't currently open
   in the editor. Open buffers are authoritative (every didChange
   invalidates them); closed-doc cache entries can only be trusted when
   we're confident nothing has touched them on disk — exactly the
   guarantee we lose when watcher registration fails. The next request
   re-compiles those files, so semantic state catches up with disk
   without us needing to know which file actually changed. *)
let drop_closed_doc_cache ws : unit =
  let to_drop = Hashtbl.fold (fun uri _ acc ->
    if Hashtbl.mem ws.docs uri then acc else uri :: acc) ws.cache [] in
  List.iter (fun uri ->
    Hashtbl.remove ws.cache uri;
    Hashtbl.remove ws.deps uri;
    Hashtbl.iter (fun u xs ->
      let kept = List.filter (fun v -> v <> uri) xs in
      Hashtbl.replace ws.rdeps u kept) ws.rdeps) to_drop

(* ---------- cache invalidation ----------

   When a doc changes, drop its cache entry plus everything transitively
   depending on it. Returns the set of URIs whose stored Session is now
   gone — handlers can use this list to push fresh diagnostics. *)
let invalidate ws ~uri : string list =
  let uri = canon_uri uri in
  let visited : (string, unit) Hashtbl.t = Hashtbl.create 8 in
  let rec walk u =
    if Hashtbl.mem visited u then []
    else begin
      Hashtbl.add visited u ();
      Hashtbl.remove ws.cache u;
      u :: List.concat_map walk (dependents_of ws ~uri:u)
    end
  in
  walk uri

(* ---------- compile ----------

   Strategy: prefer in-memory content. If the URI maps to an open doc,
   compile its content as a string. Otherwise fall back to file-on-disk
   compilation (which also resolves `include` directives via the file
   system). The path-based fallback is what makes goto-def into a
   non-open included file still work. *)
(* Build a content lookup that prefers in-memory doc text over disk for
   any URI (or its canonicalized path) the workspace has open. This is
   what makes editor unsaved changes visible across `include` boundaries. *)
let make_lookup ws : string -> string option =
  (* Index all open docs by canonicalized path for O(1) lookup. *)
  let by_path : (string, string) Hashtbl.t = Hashtbl.create 8 in
  Hashtbl.iter (fun uri d ->
    let key = Driver.canon (path_of_uri uri) in
    Hashtbl.replace by_path key d.content) ws.docs;
  fun canon_path -> Hashtbl.find_opt by_path canon_path

let compile_doc ws ~uri : Session.t =
  let uri = canon_uri uri in
  match Hashtbl.find_opt ws.cache uri with
  | Some s -> s
  | None ->
    (* Always go through `compile_file` so includes are resolved.  When
       the URI corresponds to an open doc we substitute the in-memory
       content via `~lookup`; the same lookup also redirects any include
       that points at another open doc, so unsaved edits propagate. *)
    let lookup = make_lookup ws in
    let path = path_of_uri uri in
    let s =
      if Hashtbl.mem ws.docs uri then
        (* Open in-memory doc: ensure the root file is its in-memory text
           even if no disk file exists. *)
        let canon_path = Driver.canon path in
        let root_lookup p =
          if p = canon_path then Some (Hashtbl.find ws.docs uri).content
          else lookup p
        in
        Session.compile_file ~lookup:root_lookup path
      else
        Session.compile_file ~lookup path
    in
    let dir = Filename.dirname path in
    let inc_uris = List.map (fun ip ->
      let abs = if Filename.is_relative ip
                then Filename.concat dir ip else ip in
      uri_of_path (Driver.canon abs)) s.includes in
    set_deps ws ~uri ~includes:inc_uris;
    Hashtbl.replace ws.cache uri s;
    s

(* Compile every open doc — used by per-doc workspace queries that
   only care about editor state. *)
let compile_all ws : (string * Session.t) list =
  Hashtbl.fold (fun uri _ acc -> (uri, compile_doc ws ~uri) :: acc) ws.docs []

(* Walk every workspace folder for *.idsl files. Result is cached on
   the workspace; `invalidate_folder_scan` (called from `set_folders`
   and from didChangeWatchedFiles handler) flushes it. *)
(* Defensive cap so a hostile / pathological tree can't run unbounded
   even with the cycle guard in place (very deep but non-cyclic trees
   can still stall a single-threaded server). *)
let max_scan_depth = 64

let scan_folder_files ws : string list =
  match ws.folder_scan_cache with
  | Some xs -> xs
  | None ->
    let out = ref [] in
    (* Identity by (device, inode) so symlinks pointing at an already-
       visited directory don't recurse forever; works for both intra-
       tree symlinks and cross-mount cycles. *)
    let visited : (int * int, unit) Hashtbl.t = Hashtbl.create 64 in
    let rec walk dir depth =
      if depth > max_scan_depth then ()
      else
        match Unix.lstat dir with
        | exception Unix.Unix_error _ -> ()
        | st when st.st_kind <> Unix.S_DIR -> ()
        | st ->
            let key = (st.st_dev, st.st_ino) in
            if Hashtbl.mem visited key then ()
            else begin
              Hashtbl.add visited key ();
              match Sys.readdir dir with
              | exception _ -> ()
              | entries ->
                  Array.iter (fun name ->
                    if String.length name > 0 && name.[0] = '.' then ()
                    else
                      let full = Filename.concat dir name in
                      match Unix.lstat full with
                      | exception Unix.Unix_error _ -> ()
                      | est when est.st_kind = Unix.S_DIR ->
                          walk full (depth + 1)
                      | est when est.st_kind = Unix.S_LNK ->
                          (* Resolve and recurse only if it points at a
                             *directory* — file symlinks can't cycle. *)
                          (match Unix.stat full with
                           | exception Unix.Unix_error _ -> ()
                           | tst when tst.st_kind = Unix.S_DIR ->
                               walk full (depth + 1)
                           | tst when tst.st_kind = Unix.S_REG
                                   && Filename.check_suffix name ".idsl" ->
                               out := full :: !out
                           | _ -> ())
                      | est when est.st_kind = Unix.S_REG
                              && Filename.check_suffix name ".idsl" ->
                          out := full :: !out
                      | _ -> ()) entries
            end
    in
    List.iter (fun folder_uri ->
      walk (path_of_uri folder_uri) 0) ws.folders;
    let result = List.sort_uniq compare !out in
    ws.folder_scan_cache <- Some result;
    result

(* Universe of URIs the workspace knows about: every open doc plus
   every *.idsl file under any workspace folder. Open docs win when the
   same path appears in both lists (so unsaved changes take precedence). *)
let all_known_uris ws : string list =
  let from_disk =
    scan_folder_files ws |> List.map uri_of_path in
  let opened   = all_uris ws in
  let seen = Hashtbl.create 16 in
  List.iter (fun u -> Hashtbl.replace seen u ()) opened;
  let extras = List.filter (fun u -> not (Hashtbl.mem seen u)) from_disk in
  opened @ extras

(* Compile every URI we know about (open docs + on-disk *.idsl files
   under any workspace folder). Used by `workspace/symbol` so the
   answer covers files the editor hasn't opened yet. *)
let compile_all_known ws : (string * Session.t) list =
  List.map (fun uri -> uri, compile_doc ws ~uri) (all_known_uris ws)

type fs_change = Created | Changed | Deleted

(* Apply one `workspace/didChangeWatchedFiles` entry, returning the
   open-in-editor parents the caller should re-analyze.  The Deleted
   case is non-trivial: when a file is open in the editor we keep the
   in-memory text authoritative; when it isn't, we snapshot dependents
   *before* `remove_doc` cleans up the rdeps edges, so open parents
   still get notified that their include just vanished. *)
let handle_watched_change ws ~uri ~change : string list =
  let uri = canon_uri uri in
  invalidate_folder_scan ws;
  let open_parents = List.filter (fun u -> Hashtbl.mem ws.docs u) in
  match change with
  | Deleted when not (Hashtbl.mem ws.docs uri) ->
      let deps = dependents_of ws ~uri in
      remove_doc ws ~uri;
      open_parents deps
  | Created | Changed | Deleted ->
      open_parents (invalidate ws ~uri)

(* Aggregate references for a symbol across the local session and the
   *transitive* reverse-dependency closure.  This is what makes find-
   references / rename complete when you click in a deeply included
   file: a.idsl ← b.idsl ← main.idsl.  Without the closure, standing
   in a.idsl would only surface b.idsl's refs and miss main.idsl's. *)
let aggregated_references ws ~current_uri (sym : Symbol.t)
    : Semantic_index.ref_site list =
  let current_uri = canon_uri current_uri in
  let dedup = Hashtbl.create 16 in
  let key (r : Semantic_index.ref_site) =
    (r.pos.pos_fname, r.pos.pos_lnum,
     r.pos.pos_cnum - r.pos.pos_bol, r.length)
  in
  let collect_from u acc =
    let s = compile_doc ws ~uri:u in
    match Session.index s with
    | None -> acc
    | Some i ->
        Semantic_index.references_of i sym
        |> List.fold_left (fun acc r ->
             let k = key r in
             if Hashtbl.mem dedup k then acc
             else (Hashtbl.add dedup k (); r :: acc)) acc
  in
  let visited : (string, unit) Hashtbl.t = Hashtbl.create 8 in
  let rec walk u acc =
    if Hashtbl.mem visited u then acc
    else begin
      Hashtbl.add visited u ();
      let acc = collect_from u acc in
      List.fold_left (fun acc d -> walk d acc) acc
        (dependents_of ws ~uri:u)
    end
  in
  List.rev (walk current_uri [])
