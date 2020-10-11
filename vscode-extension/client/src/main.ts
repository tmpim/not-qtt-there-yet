import * as path from 'path';
import { workspace, ExtensionContext, commands } from 'vscode';

import {
	LanguageClient,
	LanguageClientOptions,
	ServerOptions,
	TransportKind
} from 'vscode-languageclient';

let client: LanguageClient | undefined;

const start = async () => {
  console.info("Starting")
  const command = workspace.getConfiguration("qtt").get("qttExecutable", "Qtt");
  const options: ServerOptions = { command, };
  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ scheme: "file", language: "qtt" }],
    synchronize: {
      fileEvents: workspace.createFileSystemWatcher("**/*.tt")
    }
  };

  client = new LanguageClient("qtt", "Qtt Language Server", options, clientOptions, true);
  client.start();
}

let stop = () => client ? client.stop() : Promise.resolve();

export const activate = async (context: ExtensionContext) => {
  context.subscriptions.push(commands.registerCommand("qtt.restartServer", async () => {
    await stop();
    start();
  }));

  await start();
}

export const deactivate = () => {
  if (!client) return;
  return client.stop();
}