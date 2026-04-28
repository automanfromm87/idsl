-- iDSL nvim integration.  Drop this directory anywhere on your
-- runtimepath (e.g. via Lazy / packer / a manual `:set rtp+=`) and
-- call `require('idsl').setup{}` from your init.lua.
--
-- The setup function:
--   1. Registers `.idsl` files as filetype `idsl`.
--   2. Spawns the language server (`idsl-lsp` on $PATH by default)
--      whenever an `idsl` buffer is opened, scoped to the project
--      root (.git / dune-project, or the file's directory if neither
--      is present).
--   3. Forwards `on_attach` and other config straight to vim.lsp.start
--      so users can layer their own keymaps / capabilities.
--
-- Minimal usage:
--   require('idsl').setup{}
--
-- With a custom binary path and an on_attach hook:
--   require('idsl').setup{
--     cmd = { '/abs/path/to/idsl_lsp.exe' },
--     on_attach = function(client, bufnr)
--       local map = function(mode, lhs, rhs)
--         vim.keymap.set(mode, lhs, rhs, { buffer = bufnr })
--       end
--       map('n', 'gd',    vim.lsp.buf.definition)
--       map('n', 'gr',    vim.lsp.buf.references)
--       map('n', 'K',     vim.lsp.buf.hover)
--       map('n', '<leader>rn', vim.lsp.buf.rename)
--     end,
--   }

local M = {}

local function find_root(start)
  local found = vim.fs.find({ '.git', 'dune-project', '.idsl-root' },
    { upward = true, path = start })[1]
  if found then return vim.fs.dirname(found) end
  return vim.fs.dirname(start)
end

function M.setup(opts)
  opts = opts or {}
  local cmd = opts.cmd or { 'idsl-lsp' }

  -- Filetype detection.  Run unconditionally so even users who only
  -- want syntax highlighting (no LSP) get the right filetype.
  vim.filetype.add({ extension = { idsl = 'idsl' } })

  vim.api.nvim_create_autocmd('FileType', {
    pattern = 'idsl',
    callback = function(args)
      vim.lsp.start({
        name      = 'idsl-lsp',
        cmd       = cmd,
        root_dir  = find_root(args.file),
        on_attach = opts.on_attach,
        capabilities = opts.capabilities,
        settings  = opts.settings,
      })
    end,
  })
end

return M
