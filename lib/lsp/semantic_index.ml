(* Semantic index — a flat map "Symbol.t → declaration site + reference
   sites" derived from the AST and typed AST.

   This is intentionally minimal. It's the smallest model that lets
   textDocument/references and a symbol-id-based textDocument/definition
   work; it will grow as the consumers (rename, references-with-tail-of-
   path, codeAction) demand.

   Known omissions today (each documents a position that the AST/Typed
   tree does not currently carry):
     - The schema name in `rule X on Foo:` — `rule.rschema` is a bare
       string; we record the rule's pos but cannot mark "Foo" specifically.
     - The schema name in `test "x" on Foo:` and `instance Foo X:`.
     - The field name on the right of a path expression (`clause.Kind`):
       `TPath` carries only the receiver's pos, not the field's.

   Each of those is a follow-up that requires plumbing positions into
   either Ast or the typed elaboration. References for the above slots
   simply won't appear in the index until then. *)

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

(* ---------- collect declarations from AST ----------

   After the binder pass, every declaration carries its identifier's
   position directly in the AST — there's no CST traversal here anymore.
   The `_root` argument is retained so the call site signature is stable
   while we hand the CST to future binder-pass extensions (e.g.
   action-param symbols, which still rely on CST tokens). *)

let collect_decls idx (prog : Ast.program) (_root : Cst.node) =
  let mk kind pos label_kind =
    add_symbol idx
      { kind; decl_pos = pos; label = Symbol.label_of_kind label_kind } in
  List.iter (function
    | Ast.TSchema s ->
        let k = Symbol.KSchema s.sname in
        mk k s.spos k;
        List.iter (fun f ->
          let pos, name = match f with
            | Ast.FRaw (p, n, _)     -> p, n
            | Ast.FDerived (p, n, _) -> p, n in
          let k = Symbol.KField (s.sname, name) in
          mk k pos k) s.sfields
    | Ast.TRule r ->
        (* The rule's identity is the joined dotted path; its decl_pos
           is the *first* segment's position. Each segment's individual
           ref site is recorded by `collect_decl_refs` below. *)
        let pos = match r.rpath_locs with p :: _ -> p | [] -> r.rpos in
        let k = Symbol.KRule r.rpath in
        mk k pos k
    | Ast.TTest t ->
        let k = Symbol.KTest t.tname in
        mk k t.tpos k
    | Ast.TInstance i ->
        let k = Symbol.KInstance i.iname in
        mk k i.iname_pos k
    | Ast.TAction a ->
        let k = Symbol.KAction a.asname in
        mk k a.aspos k
    | Ast.TMeta _ | Ast.TInclude _ -> ()) prog

(* Schema references that live in declaration heads (not inside typed
   expressions) — they aren't reachable from `collect_typed_refs`. *)
let collect_decl_refs idx (prog : Ast.program) =
  List.iter (function
    | Ast.TInstance i ->
        add_ref idx (KSchema i.ischema)
          ~length:(String.length i.ischema) i.ischema_pos
    | Ast.TRule r ->
        (match r.rschema, r.rschema_pos with
         | Some s, Some p ->
             add_ref idx (KSchema s) ~length:(String.length s) p
         | _ -> ())
    | Ast.TTest t ->
        let g = t.tgiven in
        add_ref idx (KSchema g.gschema)
          ~length:(String.length g.gschema) g.gschema_pos
    | _ -> ()) prog

(* `instance Foo X:\n  Field = …` and the `given` block of a test both
   produce `field_assign` records whose LHS is a field reference. *)
let collect_field_assign_refs idx (prog : Ast.program) =
  let push schema (a : Ast.field_assign) =
    add_ref idx (KField (schema, a.aname))
      ~length:(String.length a.aname) a.aname_pos in
  List.iter (function
    | Ast.TInstance i -> List.iter (push i.ischema) i.ivalues
    | Ast.TTest t     -> List.iter (push t.tgiven.gschema) t.tgiven.gvalues
    | _ -> ()) prog

(* ---------- collect references from typed expressions ---------- *)

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
        (* `clause.Kind` — the field name's pos is now plumbed; we
           classify it against the receiver's static type so the index
           knows which schema's field is being referenced. *)
        (match recv.ty with
         | Types.TSchema sname ->
             add_ref idx (KField (sname, fname))
               ~length:(String.length fname) fpos
         | _ -> ())
    | _ -> ()) root

(* Schema references hidden in `e.g. [Foo]` raw lists — these positions
   live on the AST (the typed pipeline collapses them into a list type). *)
let collect_schema_list_refs idx (prog : Ast.program) =
  List.iter (function
    | Ast.TSchema s ->
        List.iter (function
          | Ast.FRaw (_, _, ExList es) ->
              List.iter (fun e ->
                match e.Ast.e_node with
                | Ast.EVar id ->
                    add_ref idx (KSchema id)
                      ~length:(String.length id) e.Ast.e_pos
                | _ -> ()) es
          | _ -> ()) s.sfields
    | _ -> ()) prog

let collect_typed_refs idx (tp : tprogram) =
  List.iter (fun (s : tschema) ->
    List.iter (function
      | TFRaw _ -> ()
      | TFDerived (_, body) -> walk_expr ~schema:s.ts_name idx body)
      s.ts_fields) tp.schemas;
  (* Top-level `then:` / `expect:` calls — `tcall` now carries the call
     name's position, so we can index the action ref accurately. *)
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
  collect_decls idx prog cst;
  collect_schema_list_refs idx prog;
  collect_decl_refs idx prog;
  collect_field_assign_refs idx prog;
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
        let len = match s.kind with
          | KSchema n | KInstance n | KAction n -> String.length n
          | KField (_, n) -> String.length n
          | KRule p -> String.length (String.concat "." p)
          | KTest n -> String.length n + 2 (* quotes *)
        in
        if pos_covers s.decl_pos ~line ~col len then Some s else None)
      idx.symbols None
