(* Compilation session — single source of truth for parse → resolve →
   typecheck. CLI, LSP, and Web all consume Session.t; per-stage errors
   accumulate as Diagnostic.t. *)

type t = {
  src                : string option;
  cst_tokens         : Cst.tok list;
  cst                : Cst.node;
  ast                : Ast.program option;
  typed              : Typed.tprogram option;
  diagnostics        : Diagnostic.t list;
  includes           : string list;       (* root-file include paths *)
  mutable index_cache : Semantic_index.t option;
}

let pipeline ?src (pr : Driver.parse_result) =
  let base = {
    src;
    cst_tokens  = pr.tokens;
    cst         = pr.tree;
    ast         = None;
    typed       = None;
    diagnostics = [];
    includes    = pr.includes;
    index_cache = None;
  } in
  match pr.ast with
  | Error ds -> { base with diagnostics = ds }
  | Ok ast ->
    match Resolve.run ast with
    | Error ds -> { base with ast = Some ast; diagnostics = ds }
    | Ok () ->
      match Typecheck.run ast with
      | Error ds -> { base with ast = Some ast; diagnostics = ds }
      | Ok tp    -> { base with ast = Some ast; typed = Some tp }

let compile_string src = pipeline ~src (Driver.parse_string src)
let compile_file ?lookup path = pipeline (Driver.parse_file ?lookup path)

(* Lazy semantic index — built once per Session. Hot LSP paths can call
   this on every request; the second and later calls are O(1). *)
let index (s : t) : Semantic_index.t option =
  match s.index_cache with
  | Some _ as r -> r
  | None ->
    match s.ast, s.typed with
    | Some prog, Some tp ->
        let idx = Semantic_index.build prog tp s.cst in
        s.index_cache <- Some idx;
        Some idx
    | _ -> None

let has_errors s =
  List.exists (fun d -> d.Diagnostic.severity = Diagnostic.Error) s.diagnostics

let errors_only s =
  List.filter (fun d -> d.Diagnostic.severity = Diagnostic.Error) s.diagnostics
