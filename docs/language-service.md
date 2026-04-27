# Language Service Design

This document describes how iDSL's IDE story is built, why each layer
exists, and which industry pattern each piece corresponds to. The
implementation is small enough (~3 kLOC across the language-service
modules) that the design is meant to be readable end-to-end; this doc
explains the *shape* so you can find the right file for a given task.

## Goals

- **One backend, many frontends.** The CLI, LSP server, browser
  bundle, and test harness should all consume the same compilation
  results. No frontend reaches around the others to recompile or
  reparse.
- **Position fidelity.** Every diagnostic, every reference, every
  rename edit carries a precise source-file URI + (line, character)
  span. There are no `"in this file somewhere"` results.
- **Multi-file by default.** `include "..."` is a first-class language
  feature; the IDE story respects it instead of pretending each open
  buffer is its own world.
- **Roslyn-shaped layering.** The architecture borrows liberally from
  Roslyn / rust-analyzer / TypeScript LS — those projects solved this
  problem at industrial scale, and matching their model means anyone
  who's worked on a real language service can read this codebase.

## The four layers

```
┌────────────────────────────────────────────────────┐
│  LSP Adapter (bin/idsl_lsp.ml)                     │  ← protocol only
│    JSON-RPC framing, capability advertisement,     │
│    URI ↔ pos_fname routing, parameter parsing      │
└──────────────────────┬─────────────────────────────┘
                       │
┌──────────────────────▼─────────────────────────────┐
│  IDE Query Surface (lib/lsp/lsp_query.ml)          │  ← semantic queries
│    hover, def_at, references_at, document_symbols, │
│    rename_at, signature_help_at, semantic_tokens…  │
└──────────────────────┬─────────────────────────────┘
                       │
┌──────────────────────▼─────────────────────────────┐
│  Semantic Model (lib/lsp/{symbol, semantic_index,  │  ← stable identity +
│                            workspace}.ml)          │    cross-file graph
│    Symbol.kind = KSchema | KField | KRule | …      │
│    Semantic_index: name → decl + refs              │
│    Workspace: doc store + cache + dep graph        │
└──────────────────────┬─────────────────────────────┘
                       │
┌──────────────────────▼─────────────────────────────┐
│  Compiler Frontend (lib/{syntax,ir,sem}/…)         │  ← parse → typed
│    Lexer / Parser / CST / Lower → AST →            │
│    Resolve → Typecheck → Typed AST                 │
│    All output collected into a Session.t snapshot. │
└────────────────────────────────────────────────────┘
```

Each layer depends only on what's below it. The compiler frontend has
no idea LSP exists; the semantic model knows nothing about JSON-RPC;
the LSP adapter never invokes a parser directly.

## Compilation: `Session.t` is the unit of truth

A `Session.t` (lib/sem/session.ml) is a compilation snapshot:

```ocaml
type t = {
  src         : string option;       (* original text, if any *)
  cst_tokens  : Cst.tok list;        (* trivia-preserving token stream *)
  cst         : Cst.node;            (* concrete syntax tree (root) *)
  ast         : Ast.program option;  (* None on parse error *)
  typed       : Typed.tprogram option;  (* None if typecheck failed *)
  diagnostics : Diagnostic.t list;   (* accumulated, structured *)
  includes    : string list;         (* root file's include paths *)
  mutable index_cache : Semantic_index.t option;  (* lazy *)
}
```

Two construction paths:

```ocaml
val compile_string : string -> t                 (* in-memory text *)
val compile_file   : ?lookup:(string -> string option) -> string -> t
```

`compile_file`'s `~lookup` is the **multi-file injection point**:
when the LSP server compiles `main.idsl`, it passes a lookup that
checks open buffers first and only falls through to disk when the URI
isn't open. This is what makes unsaved cross-file edits propagate
through `include` boundaries.

`Session.index s` lazily builds the semantic index on first access;
every later request returns the cached value, so per-keystroke hot
paths don't pay an O(N) rebuild.

### Diagnostics are structured

```ocaml
type stage    = Parse | Resolve | Typecheck | Lint
type severity = Error | Warning | Info
type t = {
  stage; severity; pos; end_pos; code; message; related;
}
```

The CLI renders `pp_pos d.pos ^ ": " ^ pp_stage d.stage ^ ": " ^ d.message`;
the LSP adapter maps each field directly to LSP wire types; the web
bundle exposes the structured array unchanged.

## Semantic Model: stable identity + cross-file graph

### `Symbol.t`

Every "thing you can hover, jump to, or rename" gets a kind:

```ocaml
type kind =
  | KSchema   of ident
  | KField    of ident (*schema*) * ident (*field*)
  | KRule     of ident list
  | KTest     of string
  | KInstance of ident
  | KAction   of ident
```

Identity is the kind itself. Two `Symbol.t` values are equal iff
their kinds compare equal — this is what lets us look up the same
schema in different sessions and know it's the same thing across
files.

### `Semantic_index.t`

Two tables keyed on `Symbol.kind`:

```ocaml
type t = {
  symbols : Symbol.t SymTable.t;       (* kind → declaration *)
  refs    : ref_site list SymTable.t;  (* kind → list of use sites *)
}
```

`build : Ast.program -> Typed.tprogram -> Cst.node -> t` walks all
three IRs:

- `collect_decls` — schema, rule, test, instance, action declarations
- `collect_decl_refs` — schema names in `instance Foo X:`,
  `rule X on Foo:`, `test X: given Foo:`
- `collect_field_assign_refs` — LHS of `Field = value` in instance /
  given blocks
- `collect_typed_refs` — every `TVar (VarField _)`, `TVar (VarInstance _)`,
  `TCall (name, _)`, `TPath (recv, fpos, fname)` in expressions

Every site carries the original `Lexing.position`, including
`pos_fname` — that's the multi-file routing key.

### `Workspace.t`

Holds:

```ocaml
type t = {
  docs    : (uri,    doc) Hashtbl.t;        (* open buffers *)
  cache   : (uri, Session.t) Hashtbl.t;     (* compile cache *)
  deps    : (uri, uri list) Hashtbl.t;      (* doc → its includes *)
  rdeps   : (uri, uri list) Hashtbl.t;      (* doc → who includes it *)
  mutable folders : uri list;               (* workspace roots *)
  mutable folder_scan_cache : string list option;  (* memoized fs scan *)
}
```

Operations:

| | what |
|--|--|
| `put_doc` / `remove_doc` | maintain the doc table; `remove_doc` cleans rdeps |
| `compile_doc ~uri` | cached compile; first call also records the include edge |
| `invalidate ~uri` | drop the cache entry plus every dependent transitively |
| `set_deps` | bidirectionally update deps + rdeps |
| `aggregated_references ~current_uri sym` | reverse-dep DFS closure with dedup |
| `scan_folder_files` | list all `*.idsl` under workspace folders (memoized) |
| `compile_all_known` | open buffers + on-disk discoveries, with open winning |

The dependency graph is built incrementally from `parse_result.includes`
(which `Driver.parse_file` reports) — no second pass over the tree.

`aggregated_references` is the key cross-file query: it walks the
**transitive** rdeps closure with a `visited` set, so a symbol declared
in `a.idsl` and used through `b.idsl ← main.idsl` returns refs from
all three sessions. This is what makes find-references / rename
complete from any vantage point in the dependency chain.

## IDE Query Surface: `Lsp_query`

The single module the LSP adapter calls into. Functions are organized
by capability category:

| Category | Functions |
|----------|-----------|
| Diagnostics | `lsp_of_diag` |
| Navigation | `def_at`, `declaration_at`, `implementation_at`, `type_definition_at`, `references_at`, `document_symbols`, `workspace_symbols`, `document_highlights_at`, `folding_ranges`, `selection_ranges_at` |
| Hierarchy | `prepare_call_hierarchy`, `incoming_calls`, `outgoing_calls`, `prepare_type_hierarchy`, `supertypes`, `subtypes` |
| Information | `hover_at`, `signature_help_at`, `inlay_hints_in_range`, `code_lenses_for`, `semantic_tokens_of` |
| Refactor | `prepare_rename`, `rename_at`, `quick_fixes_for_message`, `rename_files_edits` |
| Format | `format_full`, `format_range`, `on_type_format`, `normalize_text` |
| Completion | `completions_at`, `resolve_completion`, `analyze_ctx`, `enclosing_call`, `find_iter_binding` |
| Lint | `unused_diagnostics`, `decl_length`, `levenshtein` |

Two patterns recur:

- **Optional resolver injection.** `references_at ?refs` and
  `rename_at ?refs` accept a `Symbol.t -> ref_site list` callback. The
  LSP adapter passes `Workspace.aggregated_references`; offline
  callers (CLI tests) can omit it for single-session behavior.
- **Result types carry source provenance.** `text_edit` has
  `te_pos_fname`; `call_item` has `ci_pos_fname`. The LSP adapter
  routes each result to its true URI via `Workspace.uri_of_pos_fname
  ~fallback:request_uri pos_fname`.

## LSP Adapter: protocol only

`bin/idsl_lsp.ml` does three things and nothing else:

1. **Framing**: read JSON-RPC over stdio, dispatch by method name.
2. **Parameter parsing**: pull `uri`, `position`, `range`, etc. out of
   the request `params` object via `json_field` helpers.
3. **Result serialization**: package the `Lsp_query` return value into
   the LSP wire shape (Locations, WorkspaceEdits, SymbolInformation,
   …). URI routing happens at this boundary.

There are 30+ handlers but each is structurally similar: extract the
position parameters, call into `Lsp_query` (sometimes via a
`Workspace.compile_doc` for cache hits), serialize. The
`with_text_doc_pos` helper collapses the common `(uri, pos, idx)`
boilerplate.

URI routing is centralized in `Workspace.uri_of_pos_fname`:

```ocaml
val uri_of_pos_fname : fallback:string -> string -> string
```

Every position-bearing result (definition, references, rename edits,
call hierarchy items) goes through it. When the position has a
`pos_fname`, the URI is computed from it (canonical absolute path);
when it's blank (for in-memory buffers without `Lexing.set_filename`
stamping), the request URI is the fallback. **Every multi-file
correctness bug we've fixed has been a missing call to this function.**

## Web bundle

The browser bundle (`web/idsl_js.ml`) wraps the same `Lsp_query`
functions with `Js_of_ocaml`'s callback interface. Each method on the
`program` JS object is a thin shim that:

1. Converts JS arguments to OCaml types.
2. Calls into `Lsp_query` (single-session — no workspace).
3. Materializes results as `Js.Unsafe.obj` literals.

The Playground (`web/index.html`) registers Monaco providers that map
1:1 onto the JS surface. Round-7's `documentSymbol` uses
`registerDocumentSymbolProvider`; `prepareRename` + `rename` go
through `registerRenameProvider`; semantic tokens come through
`registerDocumentSemanticTokensProvider` with a legend probed at
registration time. This is intentionally a thin shim — no JS-side
caching or interpretation; if the OCaml says X, the editor renders X.

The web bundle does *not* include `Workspace.t`; the playground is
single-document by construction. Multi-file workflows go through the
CLI or the LSP server.

## Cross-file routing: a worked example

User opens `main.idsl`, which `include`s `a.idsl`. Both files are
saved on disk. The user clicks on `Inner` in `main.idsl` line 4
column 17 (where it appears as `[Inner]`).

```
1.  Editor sends textDocument/definition with uri=main.idsl, pos=(3,16)

2.  bin/idsl_lsp.ml handle_definition:
    - get_src(main.idsl) → Some _
    - index_for(main.idsl) → Session.index of cached Workspace.compile_doc:
      Driver.parse_file(main.idsl) flattened both files into one program;
      Lower preserved each token's pos_fname; typecheck produced
      a Typed.tprogram covering both files;
      Semantic_index built once, lazily.
    - Lsp_query.def_at idx pos → symbol_at finds the ref site at
      (3,16) → returns its Symbol.t plus decl_pos pointing at a.idsl L0 C7

3.  Adapter wraps decl_pos into a Location:
      uri   = Workspace.uri_of_pos_fname ~fallback:main_uri "a.idsl"
            = "file:///abs/path/a.idsl"
      range = (line 0, character 7) — (line 0, character 12)

4.  Editor jumps to a.idsl line 0 col 7. Done.
```

The same pattern works for the four-step inverse: the user selects
`Inner` at its declaration in `a.idsl` and asks for "Find All
References". `Workspace.aggregated_references` walks
`rdeps[a.idsl] = [main.idsl]` (and onwards transitively if there's a
deeper chain), collects every site whose pos_fname canonicalizes to
either file, deduplicates by `(fname, lnum, col, length)`, returns
the merged list. The adapter serializes each ref through
`uri_of_pos_fname` with no shared "current URI" assumption, so refs
from `a.idsl` and `main.idsl` come back with their own URIs.

## Performance

The hot path is **per-keystroke**: every character typed in the editor
triggers a `didChange` notification. The chain is:

```
didChange
 → Workspace.put_doc + Workspace.invalidate(uri)
 → analyze_and_publish(uri)                       [push diagnostics]
 → analyze_and_publish for every URI in the
   transitive rdeps closure                       [cascade]
```

After this, individual handlers (hover, completion, semanticTokens,
…) hit `Workspace.compile_doc` and `Session.index`. Both are cached;
amortized cost is O(1) per request after the initial compile.

Three caches keep this responsive:

| cache | invalidated by |
|-------|----------------|
| `Workspace.cache : uri → Session.t` | `Workspace.invalidate ~uri` (DFS over rdeps) |
| `Session.index_cache : Semantic_index.t option` | implicitly via Session lifetime |
| `Workspace.folder_scan_cache : string list option` | `set_folders`, `didChangeWatchedFiles` |

The folder-scan cache is the one that matters most: without it, every
`workspace/symbol` keypress would re-walk the entire tree.

## Known architectural debt

- **Lexer / CST state is process-global.** `lib/syntax/cst.ml`'s
  `pending_leading` / `buf` and `lib/lexer.mll`'s `paren_depth` /
  `at_eof` / `last_token` are module-level refs, reset before each
  parse via `Lexer.reset` / `Cst.reset`. Today the LSP server is
  single-threaded so this is safe; it blocks future work on
  background indexing, parallel pre-compilation, request
  cancellation, or worker-style compilation. The right fix is to
  thread a per-parse state record through the lexer and CST
  builders — ocamllex supports it via `rule … state = parse …`.

- **Outgoing wire conversion to UTF-16 is partial.** The four highest-
  traffic paths (`location_of_pos`, `range_of_pos`,
  `text_edit_to_json`, `diagnostic_json`) route through
  `Utf16.utf16_of_byte_col` against the per-result file's source.
  A handful of less-trafficked sites still use the byte-column shims
  (`lsp_pos_json`, `range_json`); these are noted in the source and
  only matter when emitting positions for files containing codepoints
  outside the BMP / multibyte UTF-8.

## What's *not* here

- **Incremental reparse.** Today every `didChange` does a full
  reparse of the changed document. With CST trivia preservation in
  place the data structures are ready for tree-diffing; the rebuild
  cost just hasn't shown up in profiling yet.
- **CST-Roslyn red layer.** We have green nodes (immutable trees with
  trivia in `Cst.tok.leading / trailing`); we don't have a red layer
  with parent pointers and absolute offsets. For format-preserving
  rewrites this would be the next step.
- **Symbol resolution at completion time.** Three `Lsp_query`
  helpers (`analyze_ctx`, `find_iter_binding`, `read_path_back`)
  still walk the CST token stream with hand-rolled heuristics because
  the user is mid-typing and the AST is incomplete. The right
  long-term answer is a structured "completion context inference"
  module separate from the binder; for now the heuristics are
  documented and tested.
- **Type-aware code actions.** Quick fixes today match diagnostic
  *messages* with regex. Adding `Diagnostic.code` (which the type
  already reserves) would let codeAction match on stable error codes
  instead of message strings.

## Test surface

Two test executables, run together by `dune runtest`:

- `test/test_iDSL.ml` — 15 assertions on parser / resolve / typecheck
  primitives. Each is small and pinpointed.
- `test/test_workspace.ml` — 36 assertions on the workspace +
  binder + cross-file routing surface. Every workspace bug we've
  fixed contributed at least one regression here. Categories:
  - `[mf]` multi-file include compiles cleanly
  - `[edit]` unsaved cross-file edits propagate
  - `[ni]` named-instance evaluation is consistent CLI ↔ LSP
  - `[rn]` cross-file references in the index
  - `[iso]` per-call instance resolver isolation (no global state)
  - `[xrn]` rename edits carry pos_fname
  - `[ch]` call_item carries pos_fname
  - `[bk]` rename from an included file finds upstream uses
  - `[fs]` folder scan picks up closed files
  - `[2hop]` rename traverses transitive rdeps
  - `[ds]` documentSymbol filters to local file

When fixing a bug here, add a test under one of these prefixes; the
suite exists specifically to make these regressions impossible to
re-introduce.

## Glossary mapping

For readers familiar with other language services:

| iDSL term | Roslyn | rust-analyzer | TypeScript LS |
|-----------|--------|---------------|----------------|
| `Session.t` | `Compilation` | `crate Snapshot` | `Program` |
| `Semantic_index.t` | `SymbolFinder` cache | `RootDatabase` selectors | `SourceFile` symbol table |
| `Symbol.kind` | `ISymbol` | `Definition` | `ts.Symbol` |
| `Workspace.t` | `Workspace` | `RootDatabase` | `Project` |
| `Workspace.aggregated_references` | `SymbolFinder.FindReferencesAsync` | `references` | `findReferences` |
| `Cst.node` | `SyntaxNode` (green) | rowan green node | `ts.Node` |
| `Lower` | (no direct analogue; Roslyn AST is the syntax tree) | `lower` (HIR) | (binder pass) |

The shapes are smaller than those projects' full implementations
because the language is small — but the layer boundaries are the same,
which is what matters for understanding.
