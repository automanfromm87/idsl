# iDSL for Neovim

Lua entry point + baseline syntax. Talks to `idsl-lsp` over stdin/stdout
using nvim's built-in LSP client (no third-party plugin required).

## Install

### 1. Build and install the language server

From this repo's root:

```sh
opam install . --deps-only      # one-time
dune build
dune install                    # puts `idsl-lsp` and `iDSL` on $PATH
```

If you don't want a system install, point nvim at the dev binary
instead — see "Custom binary path" below.

### 2. Make this directory visible to nvim

Pick whichever fits your plugin manager.

**Manual `runtimepath`** (no plugin manager):

```lua
-- in init.lua
vim.opt.rtp:append('/abs/path/to/iDSL/editors/nvim')
require('idsl').setup{}
```

**lazy.nvim**:

```lua
{
  dir = '/abs/path/to/iDSL/editors/nvim',
  ft = 'idsl',
  config = function() require('idsl').setup{} end,
}
```

**packer.nvim**:

```lua
use {
  '/abs/path/to/iDSL/editors/nvim',
  ft = 'idsl',
  config = function() require('idsl').setup{} end,
}
```

### 3. Open an `.idsl` file

`:e examples/contract_review.idsl`. The LSP attaches automatically.
Verify with `:LspInfo` — you should see `idsl-lsp` listed as attached.

## Optional: keymaps

`setup{}` accepts an `on_attach` you can use to bind keys per buffer:

```lua
require('idsl').setup{
  on_attach = function(_, bufnr)
    local map = function(mode, lhs, rhs)
      vim.keymap.set(mode, lhs, rhs, { buffer = bufnr })
    end
    map('n', 'gd',         vim.lsp.buf.definition)
    map('n', 'gr',         vim.lsp.buf.references)
    map('n', 'gi',         vim.lsp.buf.implementation)
    map('n', 'K',          vim.lsp.buf.hover)
    map('n', '<leader>rn', vim.lsp.buf.rename)
    map('n', '<leader>ca', vim.lsp.buf.code_action)
    map('n', '[d',         vim.diagnostic.goto_prev)
    map('n', ']d',         vim.diagnostic.goto_next)
  end,
}
```

## Custom binary path

If you didn't `dune install`, point at the dev build directly:

```lua
require('idsl').setup{
  cmd = { '/abs/path/to/iDSL/_build/default/bin/idsl_lsp.exe' },
}
```

## What works

The server implements the LSP 3.17 surfaces listed in `docs/language-service.md`:

- diagnostics (parse, typecheck, unused-symbol hints)
- hover, definition, references, document/workspace symbols
- rename (cross-file), prepareRename
- completion (context-aware: after `.`, after `=`, in call args)
- signature help, inlay hints, code lens
- semantic tokens (full)
- folding ranges, selection ranges, document highlight
- formatting (full + range), on-type formatting
- call hierarchy, type hierarchy
- code actions (quick fixes for typo'd field / enum tag names)
- workspace folder support, watched-file events

## Troubleshooting

**`idsl-lsp` not found.** Run `which idsl-lsp` — if empty, either
`dune install` didn't finish or your shell hasn't picked up the new
$PATH. Open a fresh shell.

**`:LspInfo` shows no client attached.** Check `:checkhealth lsp`
and `:messages` for spawn errors. Most likely the binary path
is wrong; pass an absolute path via `cmd = {...}`.

**Server crashes on a specific file.** Run the binary by hand from
the project root with that file's content piped in — server logs
to stderr. File a bug with the log + the offending input.
