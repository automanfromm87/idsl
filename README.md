# iDSL

A small rules DSL with type inference, named instances, derived fields,
and explainable evaluation. Compiles to a CLI, an LSP server, and a
browser bundle (via `js_of_ocaml`).

The mental model is a **spreadsheet plus a checker**:

- **raw fields** (`e.g.`) — *given* inputs, sample-typed
- **derived fields** (`i.e.`) — *computed* attributes, formulas
- **rules** — `when <predicates> then <action calls>`, predicate-and-action pairs
- **tests** — `given <Schema>: …` + `expect: …` assertions, run end-to-end

Inputs flow through derived fields (DAG-evaluated), rules fire on the
resulting object, outcomes get collected. Everything else (typecheck,
test runner, explain trace, counterfactual diff, browser playground,
language server) is built on those primitives.

---

## Quick demo

```bash
$ dune exec -- iDSL test examples/order.idsl
PASS  express tier picks the express channel
PASS  heavy multi-item order routes to freight
PASS  high-value uninsured triggers alert
PASS  insured high-value clears the alert
PASS  overseas destination routes via air
PASS  tight delivery window flagged
PASS  named-instance carriers pass through

7/7 test(s) passed

Rule coverage:
  ✓ shipping.tier.express     (fired in 1 test)
  ✓ shipping.weight.heavy     (fired in 1 test)
  ✓ shipping.region.overseas  (fired in 1 test)
  ✓ shipping.value.uninsured  (fired in 1 test)
  ✓ shipping.deadline.tight   (fired in 1 test)
```

```bash
$ iDSL explain examples/order.idsl --schema Order --input order.json
── FIRED ──

shipping.value.uninsured  [FIRED]  on Order
  when:
    [✓]  IsHighValue
          • IsHighValue = (TotalValue > $5,000)   →  true
          • TotalValue  = $10,000
    [✓]  (not Insured)
          • Insured = false
  produced:
    → flag(alert, "high-value uninsured")
    → notify("ops")
```

---

## Build / run

Prerequisites: `ocaml` ≥ 4.14, `dune` ≥ 3.20, `menhir`. For the web
bundle also `js_of_ocaml`, `js_of_ocaml-ppx`, `js_of_ocaml-compiler`.

```bash
opam install -y dune menhir js_of_ocaml js_of_ocaml-ppx js_of_ocaml-compiler

dune build                                # CLI + LSP + JS bundle
dune runtest                              # OCaml + workspace regressions
dune exec -- iDSL test examples/order.idsl
```

Continuous reload: `dune build --watch` rebuilds on file change.

---

## CLI reference

| command | what it does |
|---------|--------------|
| `iDSL <file>` | parse + resolve + typecheck, dump untyped AST |
| `iDSL typed <file>` | dump typed AST with inferred field types |
| `iDSL fmt <file>` | parse + re-print (canonicalize whitespace) |
| `iDSL cst <file>` | dump the concrete syntax tree (debug) |
| `iDSL test <file> [--filter <substr>]` | run `test` blocks, report pass/fail + rule coverage |
| `iDSL run <file> --schema S --input obj.json` | run rules on a JSON input, emit outcomes |
| `iDSL explain <file> --schema S --input obj.json [--json]` | per-rule audit trail |
| `iDSL whatif <file> --schema S --input obj.json --set F=V …` | counterfactual: override fields, diff outcomes |
| `iDSL diff <file> --schema S --before a.json --after b.json` | diff two inputs end-to-end |

JSON shorthand for schema-typed fields: a full object literal, the bare
instance name (`"UPS"`), or `{"$ref": "UPS"}` to refer to a top-level
`instance` declaration.

`--set F=V` accepts any JSON literal as the right-hand side (e.g.
`--set 'TotalValue="$5,000,000"'` or `--set DueDate=\"2025-02-01\"`).

Errors carry source positions: ``line 5, col 5: typecheck: rule r.x when: tag `FOO` not in {NDA|MSA}``.

---

## Language tour

```
@version("0.0.1")
@status("Active")

# Action signatures (optional). Declared calls are arity- and
# type-checked at compile time.
@action flag(severity: {info|warn|alert}, reason: String)
@action route(channel: {ground|air|express|freight})

# Schemas: e.g. = raw input field, i.e. = derived formula.
# Types are inferred from `e.g.` literals — no annotations needed.
schema Item:
  - SKU:    e.g. "WIDGET-A"          # → String
  - Weight: e.g. 1.5                 # → Float
  - Value:  e.g. $50                 # → Money

schema Carrier:
  - Name:    e.g. "ACME"
  - Express: e.g. true               # → Bool

# Named instances are reusable fixtures, referenced by bare name in
# DSL contexts and by `{"$ref": "UPS"}` in JSON inputs.
instance Carrier UPS:
  Name    = "UPS"
  Express = true

schema Order:
  - Tier:        e.g. Standard, Priority, Express   # → enum
  - DueDate:     e.g. 2025-01-25                    # → Date
  - PlacedDate:  e.g. 2025-01-15                    # → Date
  - Items:       e.g. [Item]                        # → [Item]
  - Carriers:    e.g. [Carrier]                     # → [Carrier]

  - TotalValue: i.e. sum of x.Value for x in Items where true
  - LeadDays:   i.e. (DueDate - PlacedDate).days
  - IsExpedited: i.e. (Tier == Priority or Tier == Express)

# Rules: when all predicates ✓, fire and produce outcomes. Higher
# `priority` fires earlier (default 0).
rule shipping.tier.express on Order priority 10:
  """Optional triple-quoted description."""
  when:
    Tier == Express
  then:
    route(express)
    flag(info, "express handling")

# Tests: end-to-end checks. given supplies an object, expect matches outcomes.
test "express picks express channel":
  given Order:
    Tier = Express
    Items = []
    Carriers = []
    PlacedDate = 2025-01-15
    DueDate = 2025-01-25
  expect:
    route(express)
    not flag(alert, _)               # _ = wildcard
```

Supported in expressions:

- arithmetic: `+ - * /`, `min(a, b)`, `max(a, b)`
- comparison: `== != < > <= >=`, plus `is missing` / `is present`
- logic: `and / or / not`
- conditional: `if-then-else`
- collections: `[…]`, `{F: v}`, `x.y.z` paths
- iteration: `any / every <x> in <list> : <pred>`,
  `count of <x> in <list> where <pred>`,
  `sum of <expr> for <x> in <list> where <pred>`
- temporal: `Date - Date → Duration` (then `.days` / `.years`)

Comments: `# to end of line`. Multi-line expressions: wrap in `()`, or
break after a binary operator (parser auto-continues).

### Domains (namespacing)

`domain X:` blocks scope every declaration inside, so the same bare
name can be reused in unrelated areas of the same file (or workspace):

```
domain shipping:
  schema Item:
    - SKU: e.g. "X"

  schema Order:
    - Items: e.g. [Item]              # same-domain ref, bare name OK

domain billing:
  schema Item:                        # not a duplicate of shipping.Item
    - Price: e.g. $20

  schema Invoice:
    - Lines: e.g. [Item]              # billing.Item, not shipping.Item
```

Inside a `domain D:` block, an unqualified reference `X` resolves to
`D.X` first and falls back to the global (top-level) `X`. Cross-domain
references are not yet supported in Phase 1 — `domain billing:` cannot
see `shipping.Item`. Actions and metadata declared at the top level
remain visible to every domain.

---

## Multi-file projects

```
include "items.idsl"
include "carriers.idsl"

schema Order:
  - Items: e.g. [Item]            # comes from items.idsl
  ...
```

Paths resolve relative to the current file. Each path is parsed once
even if reachable through multiple `include` paths; cycles terminate
silently. Names (schema / rule / instance / action) live in a flat
global namespace; cross-file duplicates surface as ordinary
"duplicate" errors.

The language server (see below) is workspace-aware: opening a file
that uses an `include` resolves transitively, edits in unsaved
included files propagate, and `find references` / `rename` traverse
the full reverse-dependency closure.

The browser bundle accepts only single-file source.

---

## Pipeline

```
source ─► tokens ─► CST ─► AST ─► resolve ─► typecheck/elab ─► typed AST
                            │                                         │
                            └─► Lower (CST → AST)                     └─► Eval
                                                                          Explain
                                                                          Whatif
```

- **CST** preserves trivia (whitespace, comments) for byte-perfect fmt
- **Lower** translates CST → AST and is where source positions get plumbed
- **Resolve** validates schema-name references (e.g. `e.g. [Foo]`)
- **Typecheck** is full bidirectional inference + elaboration; emits
  `Typed.tprogram` with every `EVar` resolved into one of
  `VarLocal | VarField | VarTag | VarInstance`
- **Diagnostic** carries `(stage, severity, position, end_pos, message)`;
  CLI / LSP / Web all consume the same structured form

---

## Editor / IDE support

### LSP server (`idsl-lsp`)

Built alongside the CLI. Speaks LSP over stdio. **Implements the full
LSP 3.17 surface** that's meaningful for this language:

| Category | Supported |
|----------|-----------|
| Lifecycle | initialize, didOpen / didChange / didClose, didSave, shutdown, exit |
| Diagnostics | push (`publishDiagnostics`) + pull (`textDocument/diagnostic`); `DiagnosticTag.Unnecessary` for unused-symbol hints |
| Navigation | definition, declaration, typeDefinition, implementation, references, documentHighlight, documentSymbol, workspaceSymbol, callHierarchy, typeHierarchy |
| Editing | hover, signatureHelp, inlayHint, codeLens, semanticTokens, foldingRange, selectionRange |
| Completion | trigger on `. = ( , @`, snippet items for `schema / rule / test / instance / @action / @version / @status`, lazy `completionItem/resolve` for documentation |
| Refactor | prepareRename + rename (cross-file, follows reverse-dep closure), codeAction (quick-fix for unknown field / unknown enum tag, Levenshtein-suggested replacement) |
| Formatting | full document, range, on-type (auto-indent after `:`-terminated headers) |
| Workspace | workspaceFolders, didChangeWatchedFiles, didChangeConfiguration, executeCommand (`idsl.runTests`, `idsl.printSymbols`), willRenameFiles (rewrites `include` strings) |

Cross-file semantics:
- Goto / hover / references / rename all carry source-file URIs through
  the protocol — clicking on a symbol declared in an `include`d file
  jumps to that file, not the request URI.
- Find-references walks the *transitive* reverse-dependency closure,
  so standing in a deeply-included file finds usages all the way up
  the chain.
- Workspace-wide queries (`workspace/symbol`, `willRenameFiles`)
  scan every `*.idsl` under each workspace folder, even those the
  editor hasn't opened; unsaved buffers take precedence over disk.
- documentSymbol filters to the current file (without the filter,
  flattened-include sessions would surface symbols from other files).

```bash
dune build                                  # binary at _build/install/default/bin/idsl-lsp
```

### VS Code extension (`vscode/`)

```bash
cd vscode && npm install
# in VS Code: open the folder, F5 launches an Extension Development Host
```

The extension's `idsl.serverPath` setting points at `idsl-lsp`
(default: `$PATH`). Any `.idsl` file gets syntax highlighting + the
full LSP surface.

---

## Web playground

```bash
dune build @web                              # builds web/idsl_js.bc.js
cd web && python3 -m http.server 8765
open http://localhost:8765
```

Single-page `web/index.html`. Editor is **Monaco** wired to the
in-browser compiler — every LSP capability listed above (except
multi-file workspace ones) is registered as a Monaco provider, so
F2-rename, F12-goto, Ctrl-Shift-O outline, F1 → "Format Document",
inline `level:` parameter hints, semantic-token coloring, and `@v`
trigger-completion all work without leaving the browser.

JSON input panel on the right; buttons Run / Explain / Run-tests /
Diff. All evaluation runs client-side.

---

## JS API

The browser bundle exposes `window.IDSL.compile(src)`:

```js
const { ok, errors, diagnostics, program } = IDSL.compile(srcText);

// program metadata
program.schemas    // string[]
program.rules      // string[]
program.tests      // string[]

// evaluation
program.run(schema, inputObj)         // → { ok, outcomes: [{call, args}] }
program.explain(schema, inputObj)     // → [{rule, schema, fired, when, outcomes}]
program.runTests()                    // → [{name, passed, failures, fired, outcomes}]
program.diff(schema, before, after)   // → {fields, rules, outcomes:{added,removed}}

// LSP-style queries (every method takes 0-indexed line/character)
program.hover_at(line, col)
program.completions_at(src, line, col)
program.def_at(src, line, col)
program.type_definition_at(line, col)
program.references_at(line, col)
program.document_symbols()
program.workspace_symbols(query)
program.document_highlights_at(line, col)
program.folding_ranges()
program.selection_ranges_at(line, col)
program.signature_help_at(line, col)
program.inlay_hints_in(startLine, endLine)
program.code_lenses()
program.semantic_tokens()
program.prepare_rename(line, col)
program.rename_at(line, col, newName)
program.quick_fixes_for(line, col, msg)
program.format_full()
program.format_range(src, startLine, endLine)
program.on_type_format(src, line, ch)
program.resolve_completion(dataId)
program.call_incoming(line, col)
program.call_outgoing(line, col)
program.type_supertypes(line, col)
program.type_subtypes(line, col)
program.unused_diagnostics()
```

---

## Project layout

```
lib/
  lexer.mll               # ocamllex source
  parser.mly              # menhir LR(1) grammar

  syntax/                 # concrete syntax tree
    cst.ml                #   trivia-preserving green tree
    lower.ml              #   CST → AST

  ir/                     # intermediate representations
    ast.ml                #   surface AST
    types.ml              #   static type lattice + unify
    typed.ml              #   typed AST + helpers
    diagnostic.ml         #   structured (stage, severity, range, msg)
    printer.ml            #   AST pretty-printer

  sem/                    # compilation pipeline
    driver.ml             #   string / file → parse_result
    resolve.ml            #   schema-name validation
    typecheck.ml          #   bidirectional inference / elaboration
    session.ml            #   parse + resolve + typecheck snapshot

  runtime/                # interpretation
    eval.ml{,.mli}        #   value model + rule evaluator + test runner
    explain.ml            #   per-rule audit trail
    whatif.ml             #   counterfactual / diff
    json.ml               #   0-dep JSON parser + writer
    load.ml               #   schema-aware JSON → value
    dump.ml               #   value / outcome → JSON

  lsp/                    # language service kernel
    symbol.ml             #   stable identity (KSchema | KField | …)
    semantic_index.ml     #   name → decl + ref site graph
    workspace.ml          #   document store, dep graph, cache
    lsp_query.ml          #   IDE query surface (hover / def / refs / …)

bin/
  main.ml                 # CLI dispatcher
  idsl_lsp.ml             # LSP server (stdio JSON-RPC)

web/
  idsl_js.ml              # JS API surface (js_of_ocaml)
  index.html              # browser playground (Monaco editor)

vscode/                   # VS Code extension scaffolding

test/
  test_iDSL.ml            # parser / typecheck unit tests (15)
  test_workspace.ml       # workspace + binder regression suite (36)
  recov_test.ml           # error-recovery smoke

examples/
  order.idsl              # single-file demo (3 schemas, 5 rules, 7 tests)
  shipping/               # multi-file demo (include carriers + items)
```

---

## Status

**Stable**: parse / resolve / typecheck (full bidirectional inference
+ elaboration), eval, test runner, rule coverage, JSON I/O, explain,
counterfactual / diff, named instances, action signatures, multi-file
include with cross-file rename + references, LSP server with the full
3.17 surface, browser bundle, structured diagnostics with source
positions.

**Out of scope today**: type-annotated `expect` patterns, compiled
action backends (currently opaque sinks), `.mli` interface sealing for
typed/typecheck modules, parser performance tuning, security review of
JSON parser.
