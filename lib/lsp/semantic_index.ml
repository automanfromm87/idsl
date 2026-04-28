(* Semantic index — a flat map "Symbol.t → declaration site + reference
   sites" derived from the AST and typed AST.

   Identity model: every Symbol.kind carries a *canonical qualified*
   name (e.g. "shipping.Item").  Two same-bare-name decls in different
   `domain` blocks therefore produce distinct symbols.  Reference sites
   are recorded under the same canonical key — so when typed expressions
   carry `TSchema "shipping.Item"` (because typecheck canonicalized
   them), we can look them up directly without re-resolving here.

   The bare token text is stored on Symbol.t (`decl_name`) and is what
   range / span computations consume — using the qualified key as a
   length would overshoot the real source token. *)

open Typed

module SymTable = Hashtbl.Make (struct
  type t = Symbol.kind
  let equal = Symbol.equal_kind
  let hash = Hashtbl.hash
end)

type ref_site = {
  pos    : Lexing.position;
  length : int;             (* approximate span length; used for end-pos *)
}

(* Length of a declaration's bare source token. Tests cover the +2 case
   (surrounding quotes around test names). *)
let decl_token_length (s : Symbol.t) : int =
  match s.kind with
  | KTest _ -> String.length s.decl_name + 2
  | KSchema _ | KInstance _ | KAction _ | KField _ | KRule _ ->
      String.length s.decl_name

type t = {
  symbols : Symbol.t SymTable.t;
  refs    : ref_site list SymTable.t;
}

let create () = {
  symbols = SymTable.create 64;
  refs    = SymTable.create 128;
}

let add_symbol idx (s : Symbol.t) =
  if not (SymTable.mem idx.symbols s.kind) then
    SymTable.add idx.symbols s.kind s

let add_ref idx (kind : Symbol.kind) ?(length = 1) (p : Lexing.position) =
  let cur = try SymTable.find idx.refs kind with Not_found -> [] in
  SymTable.replace idx.refs kind ({ pos = p; length } :: cur)

(* Bare names at reference sites (`include`-side type lists, instance
   heads, `given Schema:`, etc.) are resolved against the canonical key
   the index uses via the same helper the typechecker uses, so the two
   layers can never disagree on what "shipping.Item" means. *)
let qualify = Typecheck.qualify
let resolve_ref = Typecheck.resolve_key

type canon_tables = {
  schemas   : (string, unit) Hashtbl.t;
  instances : (string, unit) Hashtbl.t;
  actions   : (string, unit) Hashtbl.t;
}

let collect_canon_tables (prog : Ast.program) : canon_tables =
  let schemas   = Ast.new_table () in
  let instances = Ast.new_table () in
  let actions   = Ast.new_table () in
  List.iter (function
    | Ast.TSchema s ->
        Hashtbl.replace schemas (qualify s.sdomain s.sname) ()
    | Ast.TInstance i ->
        Hashtbl.replace instances (qualify i.idomain i.iname) ()
    | Ast.TAction a ->
        Hashtbl.replace actions (qualify a.asdomain a.asname) ()
    | Ast.TRule _ | Ast.TTest _ | Ast.TMeta _ | Ast.TInclude _ -> ())
    prog;
  { schemas; instances; actions }

(* ---------- collect declarations from AST ---------- *)

let collect_decls idx (prog : Ast.program) (_root : Cst.node) =
  let mk kind ~bare pos label_kind =
    add_symbol idx
      { kind; decl_pos = pos; decl_name = bare;
        label = Symbol.label_of_kind label_kind } in
  List.iter (function
    | Ast.TSchema s ->
        let q = qualify s.sdomain s.sname in
        let k = Symbol.KSchema q in
        mk k ~bare:s.sname s.spos k;
        List.iter (fun f ->
          let pos, name = match f with
            | Ast.FRaw (p, n, _)     -> p, n
            | Ast.FDerived (p, n, _) -> p, n in
          let k = Symbol.KField (q, name) in
          mk k ~bare:name pos k) s.sfields
    | Ast.TRule r ->
        let pos = match r.rpath_locs with p :: _ -> p | [] -> r.rpos in
        let path = match r.rdomain with
          | Some d -> d :: r.rpath
          | None   -> r.rpath in
        let bare = match r.rpath with x :: _ -> x | [] -> "" in
        let k = Symbol.KRule path in
        mk k ~bare pos k
    | Ast.TTest t ->
        let q = qualify t.tdomain t.tname in
        let k = Symbol.KTest q in
        (* +2 covers the surrounding quotes around the test name. *)
        mk k ~bare:t.tname t.tpos k
    | Ast.TInstance i ->
        let q = qualify i.idomain i.iname in
        let k = Symbol.KInstance q in
        mk k ~bare:i.iname i.iname_pos k
    | Ast.TAction a ->
        let q = qualify a.asdomain a.asname in
        let k = Symbol.KAction q in
        mk k ~bare:a.asname a.aspos k
    | Ast.TMeta _ | Ast.TInclude _ -> ()) prog

(* Schema references that live in declaration heads (not inside typed
   expressions) — they aren't reachable from `collect_typed_refs`. *)
let collect_decl_refs idx (prog : Ast.program) (canon : canon_tables) =
  List.iter (function
    | Ast.TInstance i ->
        let key = resolve_ref canon.schemas ~domain:i.idomain i.ischema in
        add_ref idx (KSchema key)
          ~length:(String.length i.ischema) i.ischema_pos
    | Ast.TRule r ->
        (match r.rschema, r.rschema_pos with
         | Some s, Some p ->
             let key = resolve_ref canon.schemas ~domain:r.rdomain s in
             add_ref idx (KSchema key) ~length:(String.length s) p
         | _ -> ())
    | Ast.TTest t ->
        let g = t.tgiven in
        let key = resolve_ref canon.schemas ~domain:t.tdomain g.gschema in
        add_ref idx (KSchema key)
          ~length:(String.length g.gschema) g.gschema_pos
    | _ -> ()) prog

(* `instance Foo X:\n  Field = …` and the `given` block of a test both
   produce `field_assign` records whose LHS is a field reference. *)
let collect_field_assign_refs idx (prog : Ast.program) (canon : canon_tables) =
  let push schema_key (a : Ast.field_assign) =
    add_ref idx (KField (schema_key, a.aname))
      ~length:(String.length a.aname) a.aname_pos in
  List.iter (function
    | Ast.TInstance i ->
        let key = resolve_ref canon.schemas ~domain:i.idomain i.ischema in
        List.iter (push key) i.ivalues
    | Ast.TTest t ->
        let key = resolve_ref canon.schemas ~domain:t.tdomain t.tgiven.gschema in
        List.iter (push key) t.tgiven.gvalues
    | _ -> ()) prog

(* ---------- collect references from typed expressions ----------

   `~schema` is the canonical key (qualified) — typecheck has already
   resolved it before storing it on tr_schema / tg_schema / ti_schema. *)

let walk_expr ~schema idx (root : texpr) =
  iter_expr (fun (e : texpr) ->
    match e.node with
    | TVar (VarField name) ->
        add_ref idx (KField (schema, name)) ~length:(String.length name) e.pos
    | TVar (VarInstance name) ->
        add_ref idx (KInstance name) ~length:(String.length name) e.pos
    | TCall (name, _) ->
        add_ref idx (KAction name) ~length:(String.length name) e.pos
    | TPath (recv, fpos, fname) ->
        (* recv.ty is the canonical schema key after typecheck. *)
        (match recv.ty with
         | Types.TSchema sname ->
             add_ref idx (KField (sname, fname))
               ~length:(String.length fname) fpos
         | _ -> ())
    | _ -> ()) root

(* Schema references in raw field decls — these positions live on the
   AST. Two sources: the type annotation (`[Foo]` / `Foo`) and the
   sample (`e.g. [Foo]` style), both lower to ident-bearing nodes. *)
let collect_schema_list_refs idx (prog : Ast.program) (canon : canon_tables) =
  let push_schema_ref ~domain id pos =
    let key = resolve_ref canon.schemas ~domain id in
    add_ref idx (KSchema key) ~length:(String.length id) pos
  in
  let walk_sample ~domain (e : Ast.expr) =
    Ast.iter_expr (function
      | Ast.EVar id ->
          (match canon.schemas with
           | tbl when Hashtbl.mem tbl (qualify domain id)
                  || Hashtbl.mem tbl id ->
               (* Position recovery: iter_expr loses positions, so we
                  fall back on the EList walk below for sample refs. *)
               ignore (id, tbl)
           | _ -> ())
      | _ -> ()) e
  in
  ignore walk_sample;
  let walk_list_sample ~domain (es : Ast.expr list) =
    List.iter (fun e ->
      match e.Ast.e_node with
      | Ast.EVar id when Hashtbl.mem canon.schemas (qualify domain id)
                      || Hashtbl.mem canon.schemas id ->
          push_schema_ref ~domain id e.Ast.e_pos
      | _ -> ()) es
  in
  List.iter (function
    | Ast.TSchema s ->
        List.iter (function
          | Ast.FRaw (pos, _, decl) ->
              (* Type annotation refs *)
              let rec ty_refs = function
                | Ast.AnnSchema name | Ast.AnnScalar name
                  when Hashtbl.mem canon.schemas (qualify s.sdomain name)
                    || Hashtbl.mem canon.schemas name ->
                    push_schema_ref ~domain:s.sdomain name pos
                | Ast.AnnList t -> ty_refs t
                | _ -> ()
              in
              Option.iter ty_refs decl.fd_ty;
              (* Sample-side refs: only the `e.g. [Foo]` shape. *)
              (match decl.fd_sample with
               | Some { e_node = EList es; _ } ->
                   walk_list_sample ~domain:s.sdomain es
               | _ -> ())
          | _ -> ()) s.sfields
    | _ -> ()) prog

let collect_typed_refs idx (tp : tprogram) =
  List.iter (fun (s : tschema) ->
    List.iter (function
      | TFRaw _ -> ()
      | TFDerived (_, body) -> walk_expr ~schema:s.ts_name idx body)
      s.ts_fields) tp.schemas;
  List.iter (fun (r : trule) ->
    List.iter (walk_expr ~schema:r.tr_schema idx) r.tr_when;
    List.iter (fun ((cpos, name, args) : tcall) ->
      add_ref idx (KAction name) ~length:(String.length name) cpos;
      List.iter (walk_expr ~schema:r.tr_schema idx) args) r.tr_then)
    tp.rules;
  List.iter (fun (t : ttest) ->
    let sname = t.tt_given.tg_schema in
    List.iter (fun (_, te) -> walk_expr ~schema:sname idx te)
      t.tt_given.tg_values;
    List.iter (function
      | TMust ((cpos, name, args) : tcall)
      | TMustNot (cpos, name, args) ->
          add_ref idx (KAction name) ~length:(String.length name) cpos;
          List.iter (walk_expr ~schema:sname idx) args)
      t.tt_expect) tp.tests;
  List.iter (fun (i : tinstance) ->
    List.iter (fun (_, te) -> walk_expr ~schema:i.ti_schema idx te)
      i.ti_values) tp.instances

(* ---------- public build ---------- *)

let build (prog : Ast.program) (tp : tprogram) (cst : Cst.node) : t =
  let idx = create () in
  let canon = collect_canon_tables prog in
  collect_decls idx prog cst;
  collect_schema_list_refs idx prog canon;
  collect_decl_refs idx prog canon;
  collect_field_assign_refs idx prog canon;
  collect_typed_refs idx tp;
  idx

(* ---------- queries ---------- *)

let symbol_of_kind idx kind =
  SymTable.find_opt idx.symbols kind

let all_symbols idx =
  SymTable.fold (fun _ s acc -> s :: acc) idx.symbols []

let references_of idx (sym : Symbol.t) : ref_site list =
  let raw = try SymTable.find idx.refs sym.kind with Not_found -> [] in
  List.rev raw

(* Find the symbol whose declaration name OR a recorded reference site
   covers the given position. Reference sites win when both apply (the
   user is more likely clicking a use than a decl name). *)
let pos_covers (p : Lexing.position) ~line ~col len =
  let p_line = p.pos_lnum - 1 in
  let p_col  = p.pos_cnum - p.pos_bol in
  p_line = line && col >= p_col && col < p_col + len

let symbol_at idx ~line ~col : Symbol.t option =
  let from_refs =
    SymTable.fold (fun kind sites acc ->
      match acc with
      | Some _ -> acc
      | None ->
        if List.exists (fun s -> pos_covers s.pos ~line ~col s.length) sites
        then SymTable.find_opt idx.symbols kind
        else None) idx.refs None
  in
  match from_refs with
  | Some _ -> from_refs
  | None ->
    SymTable.fold (fun _ (s : Symbol.t) acc ->
      match acc with
      | Some _ -> acc
      | None ->
        let len = decl_token_length s in
        if pos_covers s.decl_pos ~line ~col len then Some s else None)
      idx.symbols None
