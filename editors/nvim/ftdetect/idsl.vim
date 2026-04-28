" Filetype detection for .idsl files.  The lua `setup()` registers
" the same mapping via `vim.filetype.add`; this file is a fallback
" for users who only want syntax + commenting (no LSP) and never call
" the lua entry point.
autocmd BufRead,BufNewFile *.idsl set filetype=idsl
