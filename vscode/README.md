# vscode-idsl

VSCode extension for [iDSL](../README.md): syntax highlighting + LSP-driven
diagnostics and hover.

## Install (dev)

1. Build the LSP server:
   ```
   cd ..
   dune build
   # The binary lands at _build/install/default/bin/idsl-lsp ;
   # either put _build/install/default/bin on $PATH or set
   # idsl.serverPath in VSCode settings to its absolute path.
   ```
2. Install the extension's npm dep:
   ```
   cd vscode
   npm install
   ```
3. Open this folder in VSCode and press F5 to launch an "Extension
   Development Host" window. Open any `.idsl` file there.

## Features

- Syntax highlighting (via TextMate grammar)
- Diagnostics on save / change (parse / resolve / typecheck errors)
- Hover: shows the inferred type / role of an identifier under the cursor

## Settings

- `idsl.serverPath` — defaults to `idsl-lsp`. Set to an absolute path if
  the binary isn't on `$PATH`.
