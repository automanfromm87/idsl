(* Position queries for LSP / Monaco hover.

   Coordinate convention:
   - LSP positions are 0-indexed (line, character).
   - Lexing.position is 1-indexed for line, 0-indexed for column. *)

open Typed

type lsp_pos = { line : int; character : int }

let pos_lsp_of_lex (p : Lexing.position) : lsp_pos =
  { line = p.pos_lnum - 1; character = p.pos_cnum - p.pos_bol }

(* True iff cursor lies in [span_start, span_start + len). *)
let pos_within (cursor : lsp_pos) (span_start : Lexing.position) (len : int) =
  let s = pos_lsp_of_lex span_start in
  cursor.line = s.line
  && cursor.character >= s.character
  && cursor.character < s.character + len

(* Walk a typed expression tree, accumulating texpr nodes whose start lies
   on the same line as the cursor and whose [start, start+heuristic_span)
   contains the cursor column. The deepest such node wins. *)
let texpr_at (cursor : lsp_pos) (root : texpr) : texpr option =
  let best = ref None in
  let consider te span =
    if pos_within cursor te.pos span then begin
      match !best with
      | None -> best := Some te
      | Some prev ->
          let p_prev = pos_lsp_of_lex prev.pos in
          let p_te   = pos_lsp_of_lex te.pos in
          (* prefer the deeper / later-starting node *)
          if p_te.character >= p_prev.character then best := Some te
    end
  in
  let rec walk te =
    let span = match te.node with
      | TVar (VarLocal id) | TVar (VarField id) | TVar (VarTag id)
      | TVar (VarInstance id) -> String.length id
      | TLit _ | TWildcard | TMissing -> 1
      | _ -> 0   (* compound nodes use 0 → only direct identifier hits *)
    in
    if span > 0 then consider te span;
    Typed.iter_expr (fun sub -> if sub != te then walk sub) te
  in
  walk root;
  !best

(* Look up a node's "hover" string: pretty type + short context. *)
let hover_of_texpr (te : texpr) : string =
  let lead = match te.node with
    | TVar (VarField id)    -> Printf.sprintf "field %s" id
    | TVar (VarLocal id)    -> Printf.sprintf "local %s" id
    | TVar (VarTag id)      -> Printf.sprintf "tag `%s`" id
    | TVar (VarInstance id) -> Printf.sprintf "instance %s" id
    | TLit _                -> "literal"
    | _                     -> "expression"
  in
  Printf.sprintf "%s : %s" lead (Types.pp_ty te.ty)

(* Top-level hover entry: walks all derived/rule/test/instance bodies in
   the typed program, returns the deepest match. *)
let hover_at (tp : tprogram) (cursor : lsp_pos) : string option =
  let candidates = ref [] in
  let scan te =
    match texpr_at cursor te with
    | Some hit -> candidates := hit :: !candidates
    | None -> ()
  in
  List.iter (fun s ->
    List.iter (function
      | TFRaw _ -> ()
      | TFDerived (_, body) -> scan body) s.ts_fields) tp.schemas;
  List.iter (fun (i : tinstance) ->
    List.iter (fun (_, te) -> scan te) i.ti_values) tp.instances;
  List.iter (fun (r : trule) ->
    List.iter scan r.tr_when;
    List.iter (fun (_, _, args) -> List.iter scan args) r.tr_then) tp.rules;
  List.iter (fun (t : ttest) ->
    List.iter (fun (_, te) -> scan te) t.tt_given.tg_values;
    List.iter (function
      | TMust (_, _, args) | TMustNot (_, _, args) -> List.iter scan args)
      t.tt_expect) tp.tests;
  match List.rev !candidates with
  | []   -> None
  | hits ->
      (* among candidates, prefer the one whose start col is the largest *)
      let best = List.fold_left (fun acc te ->
        match acc with
        | None -> Some te
        | Some prev ->
            let pp = pos_lsp_of_lex prev.pos in
            let pn = pos_lsp_of_lex te.pos in
            if pn.character >= pp.character then Some te else acc)
        None hits in
      match best with
      | Some te -> Some (hover_of_texpr te)
      | None    -> None

(* ---------- diagnostics ---------- *)

(* Convert a Diagnostic.t (carrying Lexing.position) to LSP coords. *)
type diagnostic = {
  d_pos     : lsp_pos;
  d_end     : lsp_pos;
  d_message : string;
  d_stage   : string;
}

let lsp_of_diag (d : Diagnostic.t) : diagnostic =
  let p =
    if d.pos = Lexing.dummy_pos
    then { line = 0; character = 0 }
    else pos_lsp_of_lex d.pos
  in
  let e =
    if d.end_pos = Lexing.dummy_pos
    then { line = p.line; character = p.character + 1 }
    else pos_lsp_of_lex d.end_pos
  in
  { d_pos = p; d_end = e;
    d_message = d.message; d_stage = Diagnostic.pp_stage d.stage }

(* ---------- document / workspace symbols ----------

   LSP reports `DocumentSymbol`s as a tree (each entry has children) plus
   two ranges: `range` covers the whole declaration block (used to
   highlight on outline-click) and `selectionRange` covers just the name
   (used for the actual cursor jump). *)

type sym_range = { sr_start : lsp_pos; sr_end : lsp_pos }

type doc_symbol = {
  ds_name           : string;
  ds_kind           : int;          (* LSP SymbolKind *)
  ds_detail         : string option;
  ds_range          : sym_range;
  ds_selection      : sym_range;
  ds_children       : doc_symbol list;
}

(* LSP SymbolKind code points we use. *)
let kind_class    = 5
let kind_field    = 8
let kind_function = 12
let kind_constant = 14
let kind_event    = 24
let kind_method   = 6

let lsp_kind_of_symbol_kind = function
  | Symbol.KSchema _    -> kind_class
  | Symbol.KField _     -> kind_field
  | Symbol.KRule _      -> kind_function
  | Symbol.KTest _      -> kind_event
  | Symbol.KInstance _  -> kind_constant
  | Symbol.KAction _    -> kind_method
  | Symbol.KPredicate _ -> kind_function

let symbol_name = function
  | Symbol.KSchema n
  | Symbol.KInstance n
  | Symbol.KAction n
  | Symbol.KPredicate n  -> n
  | Symbol.KField (_, n) -> n
  | Symbol.KRule path    -> String.concat "." path
  | Symbol.KTest n       -> n

let decl_token_length = Semantic_index.decl_token_length

(* Range that covers exactly the declared name token. *)
let name_range_of (sym : Symbol.t) : sym_range =
  let p = pos_lsp_of_lex sym.decl_pos in
  let len = decl_token_length sym in
  { sr_start = p; sr_end = { p with character = p.character + len } }

(* Block range from a CST node's span. *)
let range_of_cst_node (n : Cst.node) : sym_range =
  let s, e = n.nspan in
  { sr_start = pos_lsp_of_lex s; sr_end = pos_lsp_of_lex e }

(* Pair each top-level decl Symbol with its CST block by matching on the
   schema/rule/test/instance/action production at the same start line. *)
let cst_top_level (root : Cst.node) : Cst.node list =
  List.filter_map (function
    | Cst.GNode n
      when (match n.nkind with
            | NSchema | NRule | NTest | NInstance | NAction
            | NMetadata | NInclude -> true
            | _ -> false) -> Some n
    | _ -> None) root.nchildren

(* Same node start position as a symbol's decl_pos? Used to associate
   each Symbol.t with its CST block for range info. *)
let same_start (a : Lexing.position) (b : Lexing.position) =
  a.pos_lnum = b.pos_lnum && a.pos_cnum = b.pos_cnum

(* `?in_file` confines the outline to symbols declared in a specific
   physical file — when the index belongs to a session that flattened
   includes, the index covers more than the user's current document.
   Without this filter, opening main.idsl makes the outline list every
   schema/rule/etc. from every transitively-included file. *)
let document_symbols ?in_file (idx : Semantic_index.t) (root : Cst.node)
    : doc_symbol list =
  let same_canon =
    match in_file with
    | None -> fun _ -> true
    | Some path ->
        let want = Driver.canon path in
        fun (s : Symbol.t) ->
          let f = s.decl_pos.pos_fname in
          f = "" || Driver.canon f = want
  in
  let tops = cst_top_level root in
  let block_for (decl : Lexing.position) =
    List.find_opt (fun n ->
      let s, _ = n.Cst.nspan in same_start s decl) tops
  in
  let mk_for (sym : Symbol.t) ?(children = []) ?detail () : doc_symbol =
    let sel = name_range_of sym in
    let range = match block_for sym.decl_pos with
      | Some n -> range_of_cst_node n
      | None   -> sel
    in
    { ds_name = symbol_name sym.kind;
      ds_kind = lsp_kind_of_symbol_kind sym.kind;
      ds_detail = detail;
      ds_range = range;
      ds_selection = sel;
      ds_children = children }
  in
  let all =
    Semantic_index.all_symbols idx |> List.filter same_canon in
  let pick pred = List.filter pred all in
  let schemas = pick (fun s -> match s.Symbol.kind with KSchema _ -> true | _ -> false) in
  let fields_of sname =
    pick (fun s -> match s.Symbol.kind with
                   | KField (s', _) -> s' = sname | _ -> false)
    |> List.sort (fun a b ->
         let pa = pos_lsp_of_lex a.Symbol.decl_pos in
         let pb = pos_lsp_of_lex b.Symbol.decl_pos in
         if pa.line <> pb.line then compare pa.line pb.line
         else compare pa.character pb.character)
  in
  let schema_syms =
    List.map (fun (s : Symbol.t) ->
      let sname = match s.kind with KSchema n -> n | _ -> assert false in
      let fields = List.map (fun f -> mk_for f ()) (fields_of sname) in
      mk_for s ~children:fields ()) schemas in
  let other =
    List.filter (fun s ->
      match s.Symbol.kind with
      | KRule _ | KTest _ | KInstance _ | KAction _ -> true
      | _ -> false) all
    |> List.map (fun s ->
         let detail = match s.Symbol.kind with
           | KInstance _ -> Some "instance" | _ -> None in
         mk_for s ?detail ())
  in
  let all_top = schema_syms @ other in
  List.sort (fun a b ->
    if a.ds_range.sr_start.line <> b.ds_range.sr_start.line
    then compare a.ds_range.sr_start.line b.ds_range.sr_start.line
    else compare a.ds_range.sr_start.character b.ds_range.sr_start.character)
    all_top

(* Workspace symbols: filter `all_symbols` by a substring query.
   Single-doc for now; will broaden once Document Store / Workspace lands. *)
let workspace_symbols (idx : Semantic_index.t) (query : string) =
  let q = String.lowercase_ascii query in
  let matches name =
    if q = "" then true
    else
      let n = String.lowercase_ascii name in
      try ignore (Str.search_forward (Str.regexp_string q) n 0); true
      with Not_found -> false
  in
  Semantic_index.all_symbols idx
  |> List.filter (fun s -> matches (symbol_name s.Symbol.kind))

(* ---------- document highlight ---------- *)

(* Same shape as references_at but lighter — LSP `documentHighlight` is
   intra-file and decoration-only, so we deliberately return the same list
   the reference query would produce. The handler will dedupe with
   reference_at if it ever needs to differ. *)
let document_highlights_at (idx : Semantic_index.t) (cursor : lsp_pos)
    : (Lexing.position * int) list option =
  match Semantic_index.symbol_at idx ~line:cursor.line ~col:cursor.character with
  | None -> None
  | Some s ->
      let decl_len = decl_token_length s in
      let refs = Semantic_index.references_of idx s in
      let pairs =
        List.map (fun (r : Semantic_index.ref_site) -> r.pos, r.length) refs in
      Some ((s.decl_pos, decl_len) :: pairs)

(* ---------- folding ---------- *)

(* One fold per top-level block (schema / rule / test / instance / action).
   Could go finer (per `when:` / `then:` block) but coarse is the LSP
   convention — VS Code already collapses inner indented blocks itself. *)
let folding_ranges (root : Cst.node) : (int * int) list =
  cst_top_level root
  |> List.filter_map (fun n ->
       let s, e = n.Cst.nspan in
       let s_ln = s.pos_lnum - 1 in
       let e_ln = e.pos_lnum - 1 in
       if e_ln > s_ln then Some (s_ln, e_ln) else None)

(* ---------- selection range ---------- *)

(* For each cursor position the LSP returns a chain of ever-larger ranges
   (smart selection expansion: select identifier → its expression → its
   statement → its block, etc.). We walk the CST from root down to the
   deepest node containing the cursor and return that path. *)
let selection_ranges_at (root : Cst.node) (cursor : lsp_pos) : sym_range list =
  let rec walk (n : Cst.node) acc =
    let r = range_of_cst_node n in
    let acc = r :: acc in
    let inner =
      List.find_map (function
        | Cst.GNode child ->
            let s, e = child.nspan in
            let s_ln = s.pos_lnum - 1 in
            let s_co = s.pos_cnum - s.pos_bol in
            let e_ln = e.pos_lnum - 1 in
            let e_co = e.pos_cnum - e.pos_bol in
            let after_start =
              cursor.line > s_ln
              || (cursor.line = s_ln && cursor.character >= s_co) in
            let before_end =
              cursor.line < e_ln
              || (cursor.line = e_ln && cursor.character <= e_co) in
            if after_start && before_end then Some child else None
        | _ -> None) n.nchildren
    in
    match inner with
    | Some child -> walk child acc
    | None -> List.rev acc
  in
  walk root []

(* ---------- cursor context (also used by completion below) ---------- *)

type ctx =
  | After_dot   of string
  | After_eq    of string list
  | In_call_arg of string * int
  | General

let analyze_ctx (cst : Cst.tok list) ~line ~col : ctx =
  let arr = Cst.tokens_before cst ~line ~col in
  let n = Array.length arr in
  match Cst.prev_significant arr (n - 1) with
  | None -> General
  | Some i ->
    match arr.(i).kind with
    | Cst.Punct "." ->
        (match Cst.prev_significant arr (i - 1) with
         | Some j ->
             (match arr.(j).kind with
              | Cst.Ident s -> After_dot s
              | _ -> General)
         | None -> General)
    | Cst.Op "==" | Cst.Op "!=" ->
        let path = Cst.read_path_back arr (i - 1) in
        if path = [] then General else After_eq path
    | Cst.Punct "(" ->
        (match Cst.prev_significant arr (i - 1) with
         | Some j ->
             (match arr.(j).kind with
              | Cst.Ident s | Cst.KW s -> In_call_arg (s, 0)
              | _ -> General)
         | None -> General)
    | Cst.Punct "," ->
        let depth = ref 0 in
        let commas = ref 0 in
        let j = ref i in
        let call = ref None in
        while !j >= 0 && !call = None do
          (match arr.(!j).kind with
           | Cst.Punct ")" | Cst.Punct "]" | Cst.Punct "}" -> incr depth
           | Cst.Punct "[" | Cst.Punct "{" -> decr depth
           | Cst.Punct "(" ->
               if !depth = 0 then begin
                 (match Cst.prev_significant arr (!j - 1) with
                  | Some k ->
                      (match arr.(k).kind with
                       | Cst.Ident s | Cst.KW s -> call := Some s
                       | _ -> j := -1)
                  | None -> j := -1)
               end else decr depth
           | Cst.Punct "," when !depth = 0 -> incr commas
           | _ -> ());
          decr j
        done;
        (match !call with
         | Some id -> In_call_arg (id, !commas)
         | None -> General)
    | _ -> General

(* ---------- signatureHelp ----------

   Reuses the same `In_call_arg (name, ix)` context the completion system
   already produces from the CST. Looks up the action signature by name
   in the typed program and renders both a label and per-parameter
   substring offsets so the client can highlight the active one. *)

type sig_param = {
  sp_label : string;             (* "level: {Low|High}" *)
  sp_start : int;                (* offset within signature label *)
  sp_end   : int;
}

type signature_info = {
  si_label  : string;            (* "notify(level: {Low|High})" *)
  si_params : sig_param list;
}

type signature_help = {
  sh_signatures   : signature_info list;
  sh_active_param : int;
}

(* Walk tokens left-of-cursor; find the deepest unmatched `(` and the
   identifier preceding it. Counts commas at that paren's depth to
   compute the active-parameter index. Stricter than analyze_ctx:
   keeps reporting In_call_arg even when the user has already typed
   characters of the current argument. *)
let enclosing_call (cst : Cst.tok list) ~line ~col
    : (string * int) option =
  let arr = Cst.tokens_before cst ~line ~col in
  let n = Array.length arr in
  let depth = ref 0 in
  let commas = ref 0 in
  let result = ref None in
  let i = ref (n - 1) in
  while !result = None && !i >= 0 do
    (match arr.(!i).kind with
     | Cst.Punct ")" | Cst.Punct "]" | Cst.Punct "}" -> incr depth
     | Cst.Punct "[" | Cst.Punct "{" ->
         if !depth > 0 then decr depth
     | Cst.Punct "(" ->
         if !depth > 0 then decr depth
         else begin
           match Cst.prev_significant arr (!i - 1) with
           | Some k ->
               (match arr.(k).kind with
                | Cst.Ident s | Cst.KW s -> result := Some (s, !commas)
                | _ -> i := 0)
           | None -> i := 0
         end
     | Cst.Punct "," when !depth = 0 -> incr commas
     | _ -> ());
    decr i
  done;
  !result

let signature_help_at (tp : Typed.tprogram) (cst : Cst.tok list)
                      (cursor : lsp_pos) : signature_help option =
  match enclosing_call cst ~line:cursor.line ~col:cursor.character with
  | Some (name, ix) ->
    (match List.find_opt
       (fun (a : Typed.taction) -> a.ta_name = name || a.ta_bare = name)
       tp.actions with
     | None -> None
     | Some a ->
       let head = name ^ "(" in
       let params, label =
         List.fold_left (fun (params, label) (pname, pty) ->
           let prefix = if label = head then label else label ^ ", " in
           let frag = Printf.sprintf "%s: %s" pname (Types.pp_ty pty) in
           let start = String.length prefix in
           let stop  = start + String.length frag in
           let p = { sp_label = frag; sp_start = start; sp_end = stop } in
           (params @ [p], prefix ^ frag))
           ([], head) a.ta_params in
       Some { sh_signatures = [{ si_label = label ^ ")"; si_params = params }];
              sh_active_param = ix })
  | _ -> None

(* ---------- inlayHint ----------

   We currently emit one kind of hint: a parameter-name annotation in
   front of each action-call argument (`notify(level: High)` shows
   `level:` as a virtual token). That's the highest-value hint given
   the iteration-binder positions are not yet plumbed through the AST. *)

type inlay_hint = {
  ih_pos    : lsp_pos;
  ih_label  : string;
  ih_kind   : int;               (* 1=Type, 2=Parameter *)
  ih_pad_r  : bool;              (* render trailing space? *)
}

let inlay_hints_in_range (tp : Typed.tprogram)
                         ~start_line ~end_line : inlay_hint list =
  let in_range (p : Lexing.position) =
    let ln = p.pos_lnum - 1 in
    ln >= start_line && ln <= end_line && p <> Lexing.dummy_pos
  in
  let acc = ref [] in
  let push h = acc := h :: !acc in
  let action_table = Hashtbl.create 8 in
  List.iter (fun (a : Typed.taction) ->
    Hashtbl.replace action_table a.ta_name a.ta_params) tp.actions;
  let walk_args name args =
    match Hashtbl.find_opt action_table name with
    | None -> ()
    | Some params ->
        List.iteri (fun i (arg : Typed.texpr) ->
          match List.nth_opt params i with
          | Some (pname, _) when in_range arg.pos ->
              push { ih_pos = pos_lsp_of_lex arg.pos;
                     ih_label = pname ^ ":";
                     ih_kind = 2;
                     ih_pad_r = true }
          | _ -> ()) args
  in
  let walk_tcall ((_pos, name, args) : Typed.tcall) = walk_args name args in
  let walk_expr (root : Typed.texpr) =
    Typed.iter_expr (fun e ->
      match e.node with
      | TCall (n, args) -> walk_args n args
      | _ -> ()) root
  in
  List.iter (fun (r : Typed.trule) ->
    List.iter walk_expr r.tr_when;
    List.iter walk_tcall r.tr_then) tp.rules;
  List.iter (fun (t : Typed.ttest) ->
    List.iter (fun (_, te) -> walk_expr te) t.tt_given.tg_values;
    List.iter (function
      | TMust c | TMustNot c -> walk_tcall c) t.tt_expect) tp.tests;
  List.rev !acc

(* ---------- codeLens ----------

   One lens above each declaration with its reference count. Clicking
   the lens triggers the editor's built-in references command — we don't
   ship a custom command yet, so the lens is title-only (the JSON layer
   wires it up to the standard "editor.action.showReferences" client-
   side command in the LSP adapter). *)

type code_lens = {
  cl_range  : sym_range;
  cl_label  : string;
  cl_target : Lexing.position;   (* where references would be queried *)
}

let code_lenses_for (idx : Semantic_index.t) : code_lens list =
  Semantic_index.all_symbols idx
  |> List.map (fun (s : Symbol.t) ->
       let n = List.length (Semantic_index.references_of idx s) in
       let label =
         if n = 1 then "1 reference" else Printf.sprintf "%d references" n
       in
       { cl_range  = name_range_of s;
         cl_label  = label;
         cl_target = s.decl_pos })

(* ---------- semanticTokens ----------

   Token classification combines (a) intrinsic kind (KW, Str, Int…) and
   (b) for identifiers, lookup against the semantic index. Output is the
   LSP-mandated delta-encoded uint stream:
     [deltaLine, deltaCol, length, tokenType, tokenModifiers] × n. *)

(* Legend — index in this list is the integer the protocol wants. *)
let semantic_token_types = [
  "keyword";        (* 0 *)
  "string";         (* 1 *)
  "number";         (* 2 *)
  "operator";       (* 3 *)
  "comment";        (* 4 *)
  "class";          (* 5 — schema *)
  "property";       (* 6 — field *)
  "function";       (* 7 — rule / action *)
  "variable";       (* 8 — instance / iter var *)
  "enumMember";     (* 9 — tag *)
  "macro";          (* 10 — metadata @keys *)
]
let semantic_token_modifiers = [ "declaration" ]

let kw_type        = 0
let str_type       = 1
let num_type       = 2
let op_type        = 3
let comment_type   = 4
let class_type     = 5
let property_type  = 6
let function_type  = 7
let variable_type  = 8
let enummember_type = 9

let token_type_of_kind = function
  | Cst.KW _                                      -> Some kw_type
  | Cst.Bool _                                    -> Some kw_type
  | Cst.Str _ | Cst.TStr _                        -> Some str_type
  | Cst.Int _ | Cst.Flt _ | Cst.Money _ | Cst.Date _ -> Some num_type
  | Cst.Op _                                      -> Some op_type
  | Cst.Comment _                                 -> Some comment_type
  | Cst.Ident _ | Cst.Punct _ | Cst.Newline
  | Cst.Whitespace | Cst.Eof                      -> None

(* Position-keyed lookup tables built from the semantic index. *)
module PosKey = struct
  type t = int * int  (* line (1-based), col (0-based) *)
  let compare = compare
end
module PosMap = Map.Make (PosKey)

let key_of (p : Lexing.position) : PosKey.t =
  (p.pos_lnum, p.pos_cnum - p.pos_bol)

let class_for_symbol_kind = function
  | Symbol.KSchema _    -> class_type
  | Symbol.KField _     -> property_type
  | Symbol.KRule _      -> function_type
  | Symbol.KAction _
  | Symbol.KPredicate _ -> function_type
  | Symbol.KInstance _  -> variable_type
  | Symbol.KTest _      -> function_type

(* Classify identifier tokens via the semantic index: (a) decl positions
   and (b) reference sites are mapped to a token type by symbol kind.
   Tokens that don't match are emitted as `variable` (a sane default). *)
let build_ident_classifier (idx : Semantic_index.t) =
  let table = ref PosMap.empty in
  let add k pos = table := PosMap.add (key_of pos) k !table in
  Semantic_index.SymTable.iter (fun _ (s : Symbol.t) ->
    add (class_for_symbol_kind s.kind) s.decl_pos) idx.symbols;
  Semantic_index.SymTable.iter (fun kind sites ->
    let cls = class_for_symbol_kind kind in
    List.iter (fun (r : Semantic_index.ref_site) ->
      add cls r.pos) sites) idx.refs;
  fun (t : Cst.tok) ->
    try Some (PosMap.find (key_of t.start) !table)
    with Not_found -> None

(* Render a token list to the LSP delta-encoded stream. *)
let semantic_tokens_of (idx : Semantic_index.t) (tokens : Cst.tok list) : int list =
  let classify_ident = build_ident_classifier idx in
  let prev_line = ref 0 and prev_col = ref 0 in
  (* Accumulate in reverse — append-with-`@` would be O(n²). *)
  let out = ref [] in
  let push line col len ty =
    let dl = line - !prev_line in
    let dc = if dl = 0 then col - !prev_col else col in
    out := 0 :: ty :: len :: dc :: dl :: !out;
    prev_line := line; prev_col := col
  in
  let emit_token (t : Cst.tok) =
    let line = t.start.pos_lnum - 1 in
    let col  = t.start.pos_cnum - t.start.pos_bol in
    let len  = String.length t.text in
    let ty =
      match t.kind with
      | Cst.Ident _ ->
          (match classify_ident t with
           | Some c -> Some c
           | None   -> Some variable_type)
      | k -> token_type_of_kind k
    in
    match ty with
    | Some t -> push line col len t
    | None   -> ()
  in
  let emit_trivia (xs : Cst.trivia list) =
    List.iter (fun (t : Cst.trivia) ->
      match t.trk_kind with
      | Cst.Comment _ ->
          let line = t.trk_pos.pos_lnum - 1 in
          let col  = t.trk_pos.pos_cnum - t.trk_pos.pos_bol in
          push line col (String.length t.trk_text) comment_type
      | _ -> ()) xs
  in
  List.iter (fun (t : Cst.tok) ->
    emit_trivia t.leading;
    emit_token t;
    emit_trivia t.trailing) tokens;
  List.rev !out

(* ---------- prepareRename / rename ----------

   `prepareRename` validates that a rename is meaningful at the cursor
   and returns the range of the identifier; `rename_at` returns the full
   list of edits (one per declaration + reference site). The data quality
   of `rename_at` is a direct proxy for binder-model quality — anywhere
   the index is missing a position, that occurrence won't get rewritten. *)

type text_edit = {
  (* The file the edit applies to.  Empty string means "the request's
     own document"; non-empty is a `Lexing.position.pos_fname` — the LSP
     adapter converts it to a `file://` URI on the way out so cross-file
     edits land where they belong. *)
  te_pos_fname : string;
  te_range     : sym_range;
  te_new_text  : string;
}

type rename_target = {
  rt_range : sym_range;
  rt_label : string;
}

let prepare_rename (idx : Semantic_index.t) (cursor : lsp_pos)
    : rename_target option =
  match Semantic_index.symbol_at idx ~line:cursor.line ~col:cursor.character with
  | None -> None
  | Some s ->
      Some { rt_range = name_range_of s; rt_label = s.label }

(* Helper used by rename / quick fixes alike. The edit inherits the
   position's source-file stamp so the LSP adapter can route it to the
   right document — this is what makes cross-file rename actually patch
   both files instead of dumping every edit into the request's URI. *)
let edit_for_pos ~pos ~length ~new_text : text_edit =
  let lp = pos_lsp_of_lex pos in
  let end_p = { lp with character = lp.character + length } in
  { te_pos_fname = pos.Lexing.pos_fname;
    te_range = { sr_start = lp; sr_end = end_p };
    te_new_text = new_text }

let rename_at ?refs (idx : Semantic_index.t) (cursor : lsp_pos)
              ~(new_name : string) : text_edit list option =
  if new_name = "" then None
  else
    match Semantic_index.symbol_at idx ~line:cursor.line ~col:cursor.character with
    | None -> None
    | Some s ->
        let decl_len = decl_token_length s in
        let decl_edit = edit_for_pos ~pos:s.decl_pos ~length:decl_len
                                     ~new_text:new_name in
        let ref_sites = match refs with
          | Some f -> f s
          | None   -> Semantic_index.references_of idx s in
        let ref_edits =
          List.filter_map (fun (r : Semantic_index.ref_site) ->
            if r.pos = Lexing.dummy_pos then None
            else Some (edit_for_pos ~pos:r.pos ~length:r.length
                                    ~new_text:new_name))
            ref_sites
        in
        Some (decl_edit :: ref_edits)

(* ---------- codeAction (quick fixes) ----------

   Two patterns the typechecker emits today admit obvious mechanical
   fixes: unknown fields and unknown enum tags. We pattern-match the
   diagnostic message, extract the bad identifier and the legal options,
   pick the Levenshtein-closest, and emit a "find/replace" hint. The
   client (Monaco / VS Code adapter) does the actual range computation
   against its model — it's the only one that has the source text. *)

type quick_fix = {
  qf_title   : string;
  qf_find    : string;          (* bad identifier the client should locate *)
  qf_replace : string;
  qf_diag_line : int;           (* LSP-line where the diagnostic landed *)
  qf_diag_col  : int;
}

let levenshtein (a : string) (b : string) =
  let la = String.length a and lb = String.length b in
  let d = Array.make_matrix (la + 1) (lb + 1) 0 in
  for i = 0 to la do d.(i).(0) <- i done;
  for j = 0 to lb do d.(0).(j) <- j done;
  for i = 1 to la do
    for j = 1 to lb do
      let cost = if a.[i - 1] = b.[j - 1] then 0 else 1 in
      d.(i).(j) <-
        min (min (d.(i - 1).(j) + 1) (d.(i).(j - 1) + 1))
            (d.(i - 1).(j - 1) + cost)
    done
  done;
  d.(la).(lb)

let closest target candidates =
  match candidates with
  | [] -> None
  | _ ->
    let scored = List.map (fun c -> c, levenshtein target c) candidates in
    let best, dist =
      List.fold_left (fun (bn, bd) (n, d) ->
        if d < bd then (n, d) else (bn, bd))
        (List.hd candidates, max_int) scored in
    let threshold = max 2 (String.length target / 2) in
    if dist <= threshold then Some best else None

let quick_fixes_for_message ~line ~col (msg : string) : quick_fix list =
  let mk title find replace =
    { qf_title = title; qf_find = find; qf_replace = replace;
      qf_diag_line = line; qf_diag_col = col }
  in
  let acc = ref [] in
  (* "no field `X` in S (have: a, b, c)" *)
  (let re = Str.regexp "no field `\\([^`]+\\)` in [^ ]+ (have: \\([^)]*\\))" in
   try
     ignore (Str.search_forward re msg 0);
     let bad  = Str.matched_group 1 msg in
     let opts =
       String.split_on_char ',' (Str.matched_group 2 msg)
       |> List.map String.trim
       |> List.filter (fun s -> s <> "") in
     (match closest bad opts with
      | Some pick ->
          acc := mk (Printf.sprintf "Replace `%s` with `%s`" bad pick)
                    bad pick :: !acc
      | None -> ())
   with Not_found -> ());
  (* "tag `X` not in {a|b|c}" *)
  (let re = Str.regexp "tag `\\([^`]+\\)` not in {\\([^}]*\\)}" in
   try
     ignore (Str.search_forward re msg 0);
     let bad  = Str.matched_group 1 msg in
     let opts = String.split_on_char '|' (Str.matched_group 2 msg) in
     (match closest bad opts with
      | Some pick ->
          acc := mk (Printf.sprintf "Replace `%s` with `%s`" bad pick)
                    bad pick :: !acc
      | None -> ())
   with Not_found -> ());
  (* "unknown name `X`" — try schema names from context. Skipped for now;
     the index doesn't expose its name table externally yet. *)
  !acc

(* ---------- typeDefinition / declaration / implementation ----------

   In iDSL these all collapse to the same lookup as definition, with one
   exception: `typeDefinition` resolves a field/var to *its type's*
   declaration, not its own. We compute this by inspecting the typed
   expression at the cursor and chasing TSchema names. *)

let rec type_schema_of (ty : Types.ty) : ident option =
  match ty with
  | Types.TSchema s   -> Some s
  | Types.TList t     -> type_schema_of t
  | _ -> None

let type_definition_at (idx : Semantic_index.t) (tp : Typed.tprogram)
                       (cursor : lsp_pos) : (Ast.pos * string) option =
  match Semantic_index.symbol_at idx
          ~line:cursor.line ~col:cursor.character with
  | None -> None
  | Some s ->
    let target_schema_name = match s.kind with
      | Symbol.KField (sname, fname) ->
          (match List.find_opt (fun ts -> ts.Typed.ts_name = sname)
                   tp.schemas with
           | None -> None
           | Some ts ->
               (match List.assoc_opt fname ts.ts_types with
                | Some ty -> type_schema_of ty
                | None -> None))
      | Symbol.KInstance _ ->
          (* `instance Foo X:` — the instance's type is its schema *)
          (match List.find_opt (fun (i : Typed.tinstance) ->
                   i.ti_name = symbol_name s.kind) tp.instances with
           | Some i -> Some i.ti_schema
           | None -> None)
      | _ -> None
    in
    match target_schema_name with
    | None -> None
    | Some sname ->
      match Semantic_index.symbol_of_kind idx (Symbol.KSchema sname) with
      | None -> None
      | Some sym -> Some (sym.decl_pos, sym.label)

(* `declaration` and `implementation` are aliases for `definition` in a
   language without forward decls or interface/impl distinction. The
   actual implementation is shared with `def_at` further below — we
   re-export it under the protocol's preferred names at the bottom of
   the module. *)

(* ---------- callHierarchy ----------

   "Who calls X" is the index's reverse map for actions. "Outgoing from
   rule R" is the calls in R's then-block. We surface only actions and
   rules — instances/tests don't participate in the call graph. *)

type call_item = {
  ci_name       : string;
  ci_kind_int   : int;          (* LSP SymbolKind *)
  ci_pos_fname  : string;       (* source file of the declaration *)
  ci_range      : sym_range;    (* whole decl block *)
  ci_selection  : sym_range;    (* just the name *)
  ci_data_id    : string;       (* opaque round-trip key *)
}

let call_data_of (k : Symbol.kind) : string =
  match k with
  | KAction n -> "action:" ^ n
  | KPredicate n -> "predicate:" ^ n
  | KRule p   -> "rule:" ^ String.concat "." p
  | KSchema n -> "schema:" ^ n
  | KField (s, n) -> Printf.sprintf "field:%s.%s" s n
  | KTest n -> "test:" ^ n
  | KInstance n -> "instance:" ^ n

let call_data_to_kind (s : string) : Symbol.kind option =
  match String.index_opt s ':' with
  | None -> None
  | Some i ->
    let prefix = String.sub s 0 i in
    let rest   = String.sub s (i + 1) (String.length s - i - 1) in
    (match prefix with
     | "action"   -> Some (Symbol.KAction rest)
     | "predicate" -> Some (Symbol.KPredicate rest)
     | "rule"     -> Some (Symbol.KRule (String.split_on_char '.' rest))
     | "schema"   -> Some (Symbol.KSchema rest)
     | "instance" -> Some (Symbol.KInstance rest)
     | "test"     -> Some (Symbol.KTest rest)
     | _ -> None)

let item_of_symbol (sym : Symbol.t) : call_item =
  let sel = name_range_of sym in
  { ci_name      = symbol_name sym.kind;
    ci_kind_int  = lsp_kind_of_symbol_kind sym.kind;
    ci_pos_fname = sym.decl_pos.pos_fname;
    ci_range     = sel;
    ci_selection = sel;
    ci_data_id   = call_data_of sym.kind }

let prepare_call_hierarchy (idx : Semantic_index.t) (cursor : lsp_pos)
    : call_item option =
  match Semantic_index.symbol_at idx
          ~line:cursor.line ~col:cursor.character with
  | None -> None
  | Some s ->
    (* Only meaningful for callable kinds. *)
    (match s.kind with
     | KAction _ | KRule _ -> Some (item_of_symbol s)
     | _ -> None)

(* Return the rule whose then-block textually contains a given Lexing.pos. *)
let enclosing_rule (tp : Typed.tprogram) (p : Lexing.position)
    : Typed.trule option =
  (* A rule's span is hard to recover from typed AST; approximate by:
     pos is in [first when's pos, last then's pos]. Cheap and accurate
     enough for call hierarchy. *)
  let pos_le a b =
    a.Lexing.pos_lnum < b.Lexing.pos_lnum
    || (a.pos_lnum = b.pos_lnum
        && a.pos_cnum - a.pos_bol <= b.pos_cnum - b.pos_bol) in
  let first_pos (r : Typed.trule) =
    match r.tr_when, r.tr_then with
    | (e :: _), _ -> e.pos
    | _, ((cp, _, _) :: _) -> cp
    | _ -> Lexing.dummy_pos in
  let last_pos (r : Typed.trule) =
    let last_in xs = List.fold_left (fun _ x -> Some x) None xs in
    match last_in r.tr_then with
    | Some (cp, _, _) -> cp
    | None ->
      (match last_in r.tr_when with
       | Some e -> e.pos
       | None -> Lexing.dummy_pos)
  in
  List.find_opt (fun r ->
    let s = first_pos r and e = last_pos r in
    pos_le s p && pos_le p e) tp.rules

let incoming_calls (idx : Semantic_index.t) (tp : Typed.tprogram)
                   (item : call_item) : call_item list =
  match call_data_to_kind item.ci_data_id with
  | Some (KAction _ as k) ->
    let refs = match Semantic_index.symbol_of_kind idx k with
      | Some s -> Semantic_index.references_of idx s
      | None -> [] in
    (* For each ref site, find the enclosing rule (if any) and report
       it as a caller. Dedupe by rule path. *)
    let seen : (string, unit) Hashtbl.t = Hashtbl.create 8 in
    List.filter_map (fun (r : Semantic_index.ref_site) ->
      match enclosing_rule tp r.pos with
      | None -> None
      | Some tr ->
        let path_key = String.concat "." tr.tr_path in
        if Hashtbl.mem seen path_key then None
        else begin
          Hashtbl.add seen path_key ();
          match Semantic_index.symbol_of_kind idx (KRule tr.tr_path) with
          | Some sym -> Some (item_of_symbol sym)
          | None -> None
        end) refs
  | _ -> []

let outgoing_calls (idx : Semantic_index.t) (tp : Typed.tprogram)
                   (item : call_item) : call_item list =
  match call_data_to_kind item.ci_data_id with
  | Some (KRule path) ->
    (match List.find_opt (fun r -> r.Typed.tr_path = path) tp.rules with
     | None -> []
     | Some r ->
       let names = List.map (fun (_, n, _) -> n) r.tr_then in
       let dedup = List.sort_uniq compare names in
       List.filter_map (fun name ->
         match Semantic_index.symbol_of_kind idx (KAction name) with
         | Some sym -> Some (item_of_symbol sym)
         | None -> None) dedup)
  | _ -> []

(* ---------- typeHierarchy ----------

   We model a schema's "supertypes" as the schemas its fields reference
   in their types — i.e. the dependencies. Subtypes are the inverse:
   schemas that mention me in their fields. This is structural, not
   nominal subtyping — but it's the most useful relation in iDSL given
   there is no inheritance keyword. *)

type type_item = call_item   (* same shape *)

let prepare_type_hierarchy (idx : Semantic_index.t) (cursor : lsp_pos)
    : type_item option =
  match Semantic_index.symbol_at idx
          ~line:cursor.line ~col:cursor.character with
  | None -> None
  | Some s ->
    (match s.kind with
     | KSchema _ -> Some (item_of_symbol s)
     | _ -> None)

let schema_field_schemas (ts : Typed.tschema) : ident list =
  List.filter_map (fun (_, ty) -> type_schema_of ty) ts.ts_types
  |> List.sort_uniq compare

let supertypes (idx : Semantic_index.t) (tp : Typed.tprogram)
               (item : type_item) : type_item list =
  match call_data_to_kind item.ci_data_id with
  | Some (KSchema name) ->
    (match List.find_opt (fun ts -> ts.Typed.ts_name = name) tp.schemas with
     | None -> []
     | Some ts ->
       List.filter_map (fun s ->
         match Semantic_index.symbol_of_kind idx (KSchema s) with
         | Some sym -> Some (item_of_symbol sym)
         | None -> None) (schema_field_schemas ts))
  | _ -> []

let subtypes (idx : Semantic_index.t) (tp : Typed.tprogram)
             (item : type_item) : type_item list =
  match call_data_to_kind item.ci_data_id with
  | Some (KSchema target) ->
    let users = List.filter (fun ts ->
      List.mem target (schema_field_schemas ts)) tp.schemas in
    List.filter_map (fun ts ->
      match Semantic_index.symbol_of_kind idx
              (KSchema ts.Typed.ts_name) with
      | Some sym -> Some (item_of_symbol sym)
      | None -> None) users
  | _ -> []

(* ---------- unused-symbol diagnostics ----------

   A symbol whose `references_of` list is empty (and which isn't a
   declaration that would have references on a different surface, like
   tests / rules) is reported as hint-severity with the LSP `Unnecessary`
   tag. The client then renders it dimmed. *)
let unused_diagnostics (idx : Semantic_index.t) : (Lexing.position * int * string) list =
  Semantic_index.all_symbols idx
  |> List.filter_map (fun (s : Symbol.t) ->
       let consider = match s.kind with
         | KSchema _ | KAction _ | KInstance _ -> true
         | KField _ -> true
         | _ -> false in
       if not consider then None
       else if Semantic_index.references_of idx s <> [] then None
       else
         let len = decl_token_length s in
         let msg = Printf.sprintf "%s is never used" s.label in
         Some (s.decl_pos, len, msg))

(* ---------- willRenameFiles ----------

   Pre-rename hook: client tells us "old_uri → new_uri"; we look at every
   open document, search for `include "..."` directives whose resolved
   absolute path matches old_uri, and produce TextEdits replacing the
   string literal with a path relative to that doc's directory.

   The resolver is a callback `path_for : string -> string option` that
   returns a doc's content given its URI; the LSP layer wires that to
   the workspace.

   We do not depend on Workspace here — the wiring is at the call site
   so this stays a pure function. *)
let path_of_uri = Workspace.path_of_uri

(* Compute path to `target` relative to `from_dir`. Naive: drops the
   common prefix and prepends `..` for each remaining segment of
   from_dir. Good enough for a same-tree workspace. *)
let make_relative ~from_dir ~target =
  let split p = String.split_on_char '/' p
                |> List.filter (fun s -> s <> "") in
  let rec strip a b =
    match a, b with
    | x :: ax, y :: bx when x = y -> strip ax bx
    | _ -> a, b
  in
  let dir_parts = split from_dir in
  let tgt_parts = split target in
  let dir_left, tgt_left = strip dir_parts tgt_parts in
  let ups = List.map (fun _ -> "..") dir_left in
  String.concat "/" (ups @ tgt_left)

(* Pull the STRING token out of an `include "..."` node, if any. *)
let include_string_token (n : Cst.node) : Cst.tok option =
  if n.nkind <> NInclude then None
  else List.find_map (function
    | Cst.GTok t when (match t.kind with Cst.Str _ -> true | _ -> false) ->
        Some t
    | _ -> None) n.nchildren

let rename_files_edits ~docs ~old_uri ~new_uri : (string * text_edit) list =
  let old_canon = Driver.canon (path_of_uri old_uri) in
  let new_path  = path_of_uri new_uri in
  List.concat_map (fun (uri, content) ->
    let dir = Filename.dirname (path_of_uri uri) in
    let pr  = Driver.parse_string content in
    cst_top_level pr.tree
    |> List.filter_map (fun n ->
         match include_string_token n with
         | None -> None
         | Some t ->
             let inc_path = match t.kind with Cst.Str s -> s | _ -> "" in
             let abs = if Filename.is_relative inc_path
                       then Filename.concat dir inc_path else inc_path in
             if Driver.canon abs <> old_canon then None
             else
               let new_rel = make_relative ~from_dir:dir ~target:new_path in
               let lp = pos_lsp_of_lex t.start in
               let end_p = { lp with
                 character = lp.character + String.length t.text } in
               Some (uri, {
                 te_pos_fname = "";
                 te_range     = { sr_start = lp; sr_end = end_p };
                 te_new_text  = "\"" ^ new_rel ^ "\"";
               })))
    docs

(* ---------- formatting ----------

   The CST-based byte-perfect renderer (`Cst.text_of_node`) already
   produces the canonical layout for every well-formed document, but
   real source acquires trailing whitespace and runs of blank lines.
   `normalize_text` is a tiny post-pass that trims trailing whitespace
   per line and caps consecutive blank lines at two — small enough that
   reformatting never reorders or restructures, only cleans up. *)

let normalize_text (s : string) : string =
  let lines = String.split_on_char '\n' s in
  let trimmed = List.map (fun l ->
    let n = String.length l in
    let r = ref n in
    while !r > 0 &&
          (let c = l.[!r - 1] in c = ' ' || c = '\t' || c = '\r') do
      decr r
    done;
    String.sub l 0 !r) lines in
  let buf = Buffer.create (String.length s) in
  let blanks = ref 0 in
  let last = List.length trimmed - 1 in
  List.iteri (fun i l ->
    if l = "" then incr blanks else blanks := 0;
    if !blanks <= 2 then begin
      Buffer.add_string buf l;
      if i <> last then Buffer.add_char buf '\n'
    end) trimmed;
  Buffer.contents buf

let format_full (cst : Cst.node) : string =
  normalize_text (Cst.text_of_node cst)

(* Range formatter: re-emit the lines [start_line..end_line] from the
   provided source with normalization. We do not reformat across the
   range boundary — stable behavior even if the user selected a
   misaligned slice. *)
let format_range (src : string) ~start_line ~end_line : string * sym_range =
  let lines = String.split_on_char '\n' src in
  let n = List.length lines in
  let s_ln = max 0 (min start_line (n - 1)) in
  let e_ln = max s_ln (min end_line (n - 1)) in
  let slice =
    let buf = Buffer.create 64 in
    List.iteri (fun i l ->
      if i >= s_ln && i <= e_ln then begin
        Buffer.add_string buf l;
        if i < e_ln then Buffer.add_char buf '\n'
      end) lines;
    Buffer.contents buf
  in
  let normalized = normalize_text slice in
  let last_line_text =
    try List.nth lines e_ln with _ -> ""
  in
  let r = {
    sr_start = { line = s_ln; character = 0 };
    sr_end   = { line = e_ln; character = String.length last_line_text };
  } in
  normalized, r

(* On-type formatting: user just typed `ch` at (line, col).
   Only fires for `\n` after a colon-terminated header (schema / rule /
   test / instance). Returns indent-only edits. *)
let on_type_format ~src ~line ~ch : text_edit list =
  if ch <> "\n" || line = 0 then []
  else
    let lines = String.split_on_char '\n' src in
    let prev = try List.nth lines (line - 1) with _ -> "" in
    let trimmed =
      let n = String.length prev in
      let r = ref n in
      while !r > 0 && (let c = prev.[!r - 1] in c = ' ' || c = '\t') do
        decr r
      done;
      String.sub prev 0 !r
    in
    let cur = try List.nth lines line with _ -> "" in
    if cur <> "" then []
    else if trimmed = "" then []
    else if trimmed.[String.length trimmed - 1] <> ':' then []
    else
      [{
        te_pos_fname = "";
        te_range = {
          sr_start = { line; character = 0 };
          sr_end   = { line; character = 0 };
        };
        te_new_text = "  ";
      }]

(* ---------- completions ---------- *)

type comp_kind =
  | CompField | CompTag | CompSchema | CompInstance | CompKeyword
  | CompSnippet

type completion = {
  c_label       : string;
  c_kind        : comp_kind;
  c_detail      : string option;
  c_insert_text : string option;     (* None = use label *)
  c_is_snippet  : bool;              (* InsertTextFormat = 2 when true *)
  c_data_id     : string option;     (* opaque id for completionItem/resolve *)
}

(* Provide markdown documentation for a previously-emitted completion
   item, looked up by `c_data_id` (which we set during completion). The
   documentation is computed lazily on resolve to keep the list-time
   payload small. *)
let resolve_completion (tp : Typed.tprogram) (data_id : string)
    : string option =
  let split2 sep s =
    match String.index_opt s sep with
    | None -> None
    | Some i -> Some (String.sub s 0 i,
                      String.sub s (i + 1) (String.length s - i - 1))
  in
  match split2 ':' data_id with
  | Some ("schema", name) ->
      (match List.find_opt (fun s -> s.Typed.ts_name = name) tp.schemas with
       | None -> None
       | Some s ->
           let fields = List.map (fun (n, t) ->
             Printf.sprintf "  - **%s**: `%s`" n (Types.pp_ty t)) s.ts_types in
           Some (Printf.sprintf "**schema %s**\n\nFields:\n%s"
                   name (String.concat "\n" fields)))
  | Some ("instance", name) ->
      (match List.find_opt (fun (i : Typed.tinstance) -> i.ti_name = name)
               tp.instances with
       | None -> None
       | Some i -> Some (Printf.sprintf "**instance %s** of `%s`"
                           name i.ti_schema))
  | Some ("action", name) ->
      (match List.find_opt (fun (a : Typed.taction) -> a.ta_name = name)
               tp.actions with
       | None -> None
       | Some a ->
           let params = List.map (fun (n, t) ->
             Printf.sprintf "%s: %s" n (Types.pp_ty t)) a.ta_params in
           Some (Printf.sprintf "**@action %s**\n\n```idsl\n%s(%s)\n```"
                   name name (String.concat ", " params)))
  | Some ("field", spec) ->
      (match split2 '.' spec with
       | Some (sname, fname) ->
           (match List.find_opt (fun s -> s.Typed.ts_name = sname)
                    tp.schemas with
            | None -> None
            | Some s ->
                (match List.assoc_opt fname s.ts_types with
                 | None -> None
                 | Some t -> Some (Printf.sprintf "**field %s.%s**: `%s`"
                                     sname fname (Types.pp_ty t))))
       | None -> None)
  | _ -> None

(* Helpers to find a schema / its field type. *)
let find_field tp name =
  let r = ref None in
  List.iter (fun s ->
    if !r = None then
      match List.assoc_opt name s.Typed.ts_types with
      | Some t -> r := Some (s, t)
      | None -> ()) tp.Typed.schemas;
  !r

(* Lenient lookup by canonical key OR bare token. Hover / completion
   gets bare names from the user's cursor; the typed program now stores
   qualified keys. Match either form so domain-scoped decls remain
   reachable from completion paths that don't yet thread domain
   context. *)
let find_schema tp name =
  List.find_opt
    (fun s -> s.Typed.ts_name = name || s.Typed.ts_bare = name)
    tp.Typed.schemas

let find_instance tp name =
  List.find_opt
    (fun (i : Typed.tinstance) -> i.ti_name = name || i.ti_bare = name)
    tp.instances

let mk_comp ?detail ?insert_text ?(snippet = false) ?data_id label kind =
  { c_label = label; c_kind = kind; c_detail = detail;
    c_insert_text = insert_text; c_is_snippet = snippet;
    c_data_id = data_id }

(* Generate suggestions for each context. *)
(* Scan the CST for the most recent iteration binding of `var_name` above
   the cursor. Patterns recognized: `any X in Y`, `every X in Y`,
   `count of X in Y`, `for X in Y` (sum body). Pure token-level — no
   false positives from string contents or comments. *)
let find_iter_binding (cst : Cst.tok list) (cursor : lsp_pos)
                      (var_name : string) : string option =
  let arr = Cst.tokens_before cst ~line:cursor.line ~col:cursor.character in
  let n = Array.length arr in
  let last = ref None in
  let i = ref 0 in
  let next_sig from =
    let r = ref from in
    while !r < n &&
      (match arr.(!r).kind with
       | Whitespace | Newline | Comment _ -> true
       | _ -> false)
    do incr r done;
    if !r < n then Some !r else None
  in
  while !i < n do
    (match arr.(!i).kind with
     | KW "any" | KW "every" | KW "for" ->
         (* expect: KW <var> in <Y> *)
         (match next_sig (!i + 1) with
          | Some j ->
            (match arr.(j).kind with
             | Ident x when x = var_name ->
               (match next_sig (j + 1) with
                | Some k when (match arr.(k).kind with KW "in" -> true | _ -> false) ->
                  (match next_sig (k + 1) with
                   | Some l ->
                     (match arr.(l).kind with
                      | Ident y -> last := Some y
                      | _ -> ())
                   | None -> ())
                | _ -> ())
             | _ -> ())
          | None -> ())
     | KW "count" ->
         (* expect: count of <var> in <Y> *)
         (match next_sig (!i + 1) with
          | Some j when (match arr.(j).kind with KW "of" -> true | _ -> false) ->
            (match next_sig (j + 1) with
             | Some k ->
               (match arr.(k).kind with
                | Ident x when x = var_name ->
                  (match next_sig (k + 1) with
                   | Some l when (match arr.(l).kind with KW "in" -> true | _ -> false) ->
                     (match next_sig (l + 1) with
                      | Some m ->
                        (match arr.(m).kind with
                         | Ident y -> last := Some y
                         | _ -> ())
                      | None -> ())
                   | _ -> ())
                | _ -> ())
             | None -> ())
          | _ -> ())
     | _ -> ());
    incr i
  done;
  !last

(* Resolve a path expression like ["clause"; "Kind"] to a static type. *)
let resolve_path (cst : Cst.tok list) (cursor : lsp_pos)
                 (tp : Typed.tprogram)
                 (current_schema : Ast.ident option)
                 (path : string list)
    : Types.ty option =
  let field_in_schema sname f =
    match find_schema tp sname with
    | Some s -> List.assoc_opt f s.ts_types
    | None -> None
  in
  match path with
  | [] -> None
  | [name] ->
      (* Bare ident — treat as a field of the current schema, or an
         iteration variable, or a top-level instance. *)
      (match current_schema with
       | Some sname ->
           (match field_in_schema sname name with
            | Some t -> Some t
            | None -> None)
       | None ->
           (match find_field tp name with
            | Some (_, t) -> Some t
            | None -> None))
  | recv :: rest ->
      let recv_ty =
        (* Receiver could be: schema name, instance name, or iter var *)
        match find_schema tp recv with
          | Some _ -> Some (Types.TSchema recv)
          | None ->
            match find_instance tp recv with
            | Some i -> Some (Types.TSchema i.ti_schema)
            | None ->
              (* Iteration variable — find binding *)
              match find_iter_binding cst cursor recv with
              | None -> None
              | Some y ->
                let cur = current_schema in
                (* Y is a field of the current schema; its type should be
                   TList (TSchema ...). The element type is the iter var. *)
                let y_ty = match cur with
                  | Some sname -> field_in_schema sname y
                  | None -> Option.map snd (find_field tp y) in
                (match y_ty with
                 | Some (Types.TList (TSchema s)) -> Some (Types.TSchema s)
                 | _ -> None)
      in
      (* Walk the rest of the path *)
      let rec walk ty fields =
        match fields, ty with
        | [], _ -> ty
        | f :: more, Some (Types.TSchema s) ->
            walk (field_in_schema s f) more
        | _ -> None
      in
      walk recv_ty rest

let complete_after_eq ?current_schema cst cursor tp path =
  match resolve_path cst cursor tp current_schema path with
  | Some (Types.TEnum tags) ->
      let detail = String.concat "." path in
      List.map (fun t -> mk_comp ~detail t CompTag) tags
  | Some Types.TBool ->
      [ mk_comp "true" CompTag; mk_comp "false" CompTag ]
  | _ -> []

let complete_after_dot tp recv =
  let from_schema s =
    List.map (fun (n, t) ->
      mk_comp ~detail:(Types.pp_ty t) n CompField) s.Typed.ts_types in
  match find_schema tp recv with
  | Some s -> from_schema s
  | None ->
    match find_instance tp recv with
    | Some i ->
        (match find_schema tp i.ti_schema with
         | Some s -> from_schema s
         | None -> [])
    | None -> []

let complete_call_arg (tp : Typed.tprogram) call arg_ix =
  match List.find_opt
    (fun (a : Typed.taction) -> a.ta_name = call || a.ta_bare = call)
    tp.actions with
  | None -> []
  | Some a ->
      if arg_ix >= List.length a.ta_params then []
      else
        let (param_name, param_ty) = List.nth a.ta_params arg_ix in
        match param_ty with
        | Types.TEnum tags ->
            List.map (fun t ->
              mk_comp ~detail:(call ^ ":" ^ param_name) t CompTag) tags
        | TBool ->
            [ mk_comp ~detail:(call ^ ":" ^ param_name) "true"  CompTag;
              mk_comp ~detail:(call ^ ":" ^ param_name) "false" CompTag ]
        | _ -> []

(* Top-level decl scaffolds — when the user types `schema`, suggest the
   full block as a snippet with cursor stops in the right places.
   `${1:Foo}` etc. is the LSP-standard placeholder syntax; the client
   moves the cursor through them on Tab. *)
let snippet_completions = [
  ("schema",
   "schema ${1:Name}:\n  - ${2:Field}: ${3:Type} default ${4:value}$0",
   "Block: schema with one field");
  ("predicate",
   "predicate ${1:name} on { ${2:Field}: ${3:Type} }:\n  ${4:expr}$0",
   "Block: predicate (named pure-Bool, structurally typed)");
  ("rule",
   "rule ${1:name} on ${2:Schema}:\n  when:\n    ${3:predicate}\n  then:\n    ${4:action}$0",
   "Block: rule with when/then");
  ("test",
   "test \"${1:name}\":\n  given ${2:Schema}:\n    ${3:field} = ${4:value}\n  expect:\n    ${5:action}$0",
   "Block: test with given/expect");
  ("test-table",
   "test \"${1:name}\" on ${2:Schema}:\n  cases:\n    ${3:field} = ${4:value} -> ${5:action}$0",
   "Block: table-driven test (cases with arrows)");
  ("instance",
   "instance ${1:Schema} ${2:Name}:\n  ${3:field} = ${4:value}$0",
   "Block: instance assignment");
  ("domain",
   "domain ${1:name}:\n  ${2:body}$0",
   "Block: domain (scoped namespace)");
  ("@action",
   "@action ${1:name}(${2:param}: ${3:Type})$0",
   "Block: @action declaration");
  ("@version",
   "@version(\"${1:0.0.4}\")$0",
   "Metadata: source language version");
  ("@status",
   "@status(\"${1:Active}\")$0",
   "Metadata: program status");
  ("@strict_actions",
   "@strict_actions$0",
   "Metadata: require @action declarations for every call");
]

let complete_general ?current_schema tp =
  let local_fields = match current_schema with
    | Some name ->
        (match find_schema tp name with
         | Some s ->
             List.map (fun (n, t) ->
               mk_comp ~detail:(name ^ "  " ^ Types.pp_ty t)
                       ~data_id:(Printf.sprintf "field:%s.%s" name n)
                       n CompField)
               s.Typed.ts_types
         | None -> [])
    | None -> [] in
  let schemas =
    List.map (fun s ->
      mk_comp ~detail:"schema"
              ~data_id:("schema:" ^ s.Typed.ts_name)
              s.Typed.ts_name CompSchema) tp.Typed.schemas in
  let instances =
    List.map (fun (i : Typed.tinstance) ->
      mk_comp ~detail:("instance " ^ i.ti_schema)
              ~data_id:("instance:" ^ i.ti_name)
              i.ti_name CompInstance)
      tp.instances in
  let actions =
    List.map (fun (a : Typed.taction) ->
      mk_comp ~detail:"@action"
              ~data_id:("action:" ^ a.ta_name)
              a.ta_name CompKeyword)
      tp.actions in
  let snippets =
    List.map (fun (label, body, detail) ->
      mk_comp ~detail ~insert_text:body ~snippet:true label CompSnippet)
      snippet_completions in
  let keywords =
    List.map (fun k -> mk_comp k CompKeyword)
      ["when"; "then"; "given"; "expect"; "include";
       "if"; "else"; "and"; "or"; "not"; "any"; "every";
       "is"; "missing"; "present"; "min"; "max"] in
  snippets @ local_fields @ schemas @ instances @ actions @ keywords

(* Find which top-level schema (if any) lexically contains a position.
   Walk top items in source order; the cursor falls within an item's body
   if it's after the item's start and before the next item's start. *)
let containing_schema (prog : Ast.program) (cursor : lsp_pos) : Ast.ident option =
  let with_pos = List.filter_map (fun top ->
    let p = match top with
      | Ast.TSchema s   -> Some s.spos
      | TRule r         -> Some r.rpos
      | TTest t         -> Some t.tpos
      | TInstance i     -> Some i.ipos
      | TPredicate p    -> Some p.ppos
      | TAction _ | TMeta _ | TInclude _ -> None
    in match p with Some pp -> Some (pp, top) | None -> None) prog in
  let sorted = List.sort (fun (a, _) (b, _) ->
    let pa = pos_lsp_of_lex a and pb = pos_lsp_of_lex b in
    if pa.line <> pb.line then compare pa.line pb.line
    else compare pa.character pb.character) with_pos in
  let after p =
    let lp = pos_lsp_of_lex p in
    cursor.line > lp.line ||
    (cursor.line = lp.line && cursor.character >= lp.character) in
  let before p =
    let lp = pos_lsp_of_lex p in
    cursor.line < lp.line ||
    (cursor.line = lp.line && cursor.character < lp.character) in
  let pick top =
    match top with
    | Ast.TSchema s   -> Some s.sname
    | TRule r         -> r.rschema
    | TTest t         -> Some t.tgiven.gschema
    | TInstance i     -> Some i.ischema
    | _ -> None
  in
  let rec walk = function
    | [] -> None
    | [(p, top)] -> if after p then pick top else None
    | (p, top) :: ((np, _) :: _ as rest) ->
        if after p && before np then pick top
        else walk rest
  in
  walk sorted

(* ---------- goto-definition ---------- *)

(* Identify the word under the cursor on a given line. Returns the
   identifier text plus the (1-based) start column range it occupies, or
   None if there is no identifier at that position. *)
let word_at (src : string) (pos : lsp_pos) : (string * int * int) option =
  let lines = String.split_on_char '\n' src in
  match List.nth_opt lines pos.line with
  | None -> None
  | Some line ->
    let n = String.length line in
    let is_ident c =
      (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
      (c >= '0' && c <= '9') || c = '_' in
    if pos.character > n || pos.character < 0 then None
    else if pos.character < n && not (is_ident line.[pos.character])
            && (pos.character = 0 || not (is_ident line.[pos.character - 1])) then None
    else begin
      let start = ref pos.character in
      while !start > 0 && is_ident line.[!start - 1] do decr start done;
      let stop = ref pos.character in
      while !stop < n && is_ident line.[!stop] do incr stop done;
      if !stop <= !start then None
      else Some (String.sub line !start (!stop - !start), !start, !stop)
    end

(* Find the declaration of the symbol the cursor is on. Drives goto-def.

   Goes through the semantic index instead of the old word-then-search
   heuristic; the index already knows where each declaration sits and
   which sites refer to it, so we just ask which symbol covers the cursor
   and read its decl_pos. *)
let def_at (idx : Semantic_index.t) (cursor : lsp_pos)
           : (Ast.pos * string) option =
  match Semantic_index.symbol_at idx ~line:cursor.line ~col:cursor.character with
  | None -> None
  | Some s -> Some (s.decl_pos, s.label)

let decl_length = decl_token_length

(* References for the symbol the cursor is on, including its declaration
   so the LSP "Find All References" list always has the decl as item 0.

   `?refs` is a callback the caller can use to plug in cross-file
   aggregation (Workspace.aggregated_references); when omitted we fall
   back to the local index — single-doc behavior unchanged. *)
let references_at ?refs (idx : Semantic_index.t) (cursor : lsp_pos)
    : (Ast.pos * int) list option =
  match Semantic_index.symbol_at idx ~line:cursor.line ~col:cursor.character with
  | None -> None
  | Some s ->
      let ref_sites = match refs with
        | Some f -> f s
        | None   -> Semantic_index.references_of idx s in
      let ref_pairs =
        List.map (fun (r : Semantic_index.ref_site) -> r.pos, r.length)
          ref_sites in
      Some ((s.decl_pos, decl_length s) :: ref_pairs)

(* `declaration` and `implementation` collapse to `definition` in a
   language without forward decls or interface/impl distinction. *)
let declaration_at = def_at
let implementation_at = def_at

(* Public entry. The cursor is at LSP (line, character).
   `cst` is the token stream from the most recent lex of `src` (driver
   provides it alongside the AST). *)
let completions_at (cst : Cst.tok list) (prog : Ast.program)
                   (tp : Typed.tprogram) (pos : lsp_pos) =
  let current_schema = containing_schema prog pos in
  match analyze_ctx cst ~line:pos.line ~col:pos.character with
  | After_eq path      ->
      complete_after_eq ?current_schema cst pos tp path
  | After_dot recv ->
      let xs = complete_after_dot tp recv in
      if xs <> [] then xs else complete_general ?current_schema tp
  | In_call_arg (n, i) -> complete_call_arg  tp n i
  | General            -> complete_general ?current_schema tp
