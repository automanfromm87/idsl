// Minimal LSP client wrapper. Spawns idsl-lsp and lets VSCode handle the rest.
const path = require('path');
const { workspace } = require('vscode');
const { LanguageClient, TransportKind } = require('vscode-languageclient/node');

let client;

function activate(context) {
  const config = workspace.getConfiguration('idsl');
  const serverCommand = config.get('serverPath') || 'idsl-lsp';

  const serverOptions = {
    command: serverCommand,
    args: [],
    transport: TransportKind.stdio
  };

  const clientOptions = {
    documentSelector: [{ scheme: 'file', language: 'idsl' }],
    synchronize: {
      fileEvents: workspace.createFileSystemWatcher('**/*.idsl')
    }
  };

  client = new LanguageClient('idsl', 'iDSL Language Server',
                              serverOptions, clientOptions);
  client.start();
  context.subscriptions.push({ dispose: () => client.stop() });
}

function deactivate() {
  if (!client) return undefined;
  return client.stop();
}

module.exports = { activate, deactivate };
