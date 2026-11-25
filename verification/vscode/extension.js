'use strict';
// Commands that move between Rust and the Lean that Aeneas generates from it.

const vscode = require('vscode');
const { Index, isGenerated } = require('./lib/index');

/** The index of the workspace's generated Lean, built on first use and dropped on change. */
let pending = null;

function settings() {
  const cfg = vscode.workspace.getConfiguration('aeneasLink');
  return {
    include: cfg.get('include', '**/*.lean'),
    exclude: cfg.get('exclude', '**/{.lake,node_modules,target}/**'),
    toSide: cfg.get('openToSide', false),
  };
}

async function build() {
  const { include, exclude } = settings();
  const uris = await vscode.workspace.findFiles(include, exclude);
  const files = [];
  for (const uri of uris) {
    const text = Buffer.from(await vscode.workspace.fs.readFile(uri)).toString('utf8');
    if (isGenerated(text)) files.push({ path: uri.fsPath, text });
  }
  const index = Index.build(files);
  for (const file of index.unresolved) {
    vscode.window.showWarningMessage(
      `Aeneas Link: no crate root holds the Rust sources of ${vscode.workspace.asRelativePath(file)}.`,
    );
  }
  return index;
}

function index() {
  if (!pending) {
    pending = build();
    pending.catch(() => {
      pending = null;
    });
  }
  return pending;
}

function describe(e) {
  const where = `${vscode.workspace.asRelativePath(e.leanFile)}:${e.declLine + 1}`;
  return { label: e.fullName, description: e.kind === 'item' ? '' : e.kind, detail: where, entry: e };
}

/** One of `entries`: the first when `pick` is false or there is one, else the user's choice. */
async function choose(entries, pick, placeHolder) {
  if (entries.length === 0) return null;
  if (entries.length === 1 || !pick) return entries[0];
  const chosen = await vscode.window.showQuickPick(entries.map(describe), { placeHolder });
  return chosen ? chosen.entry : null;
}

/** The declarations generated from the Rust at the cursor of the active editor, or null. */
async function atCursor() {
  const editor = vscode.window.activeTextEditor;
  if (!editor) return null;
  const { document, selection } = editor;
  const lines = document.getText().split('\n');
  const pos = selection.active;
  const hit = (await index()).atRust(document.uri.fsPath, pos.line + 1, pos.character, lines);
  if (!hit) {
    vscode.window.showInformationMessage(
      `Aeneas Link: no generated Lean comes from line ${pos.line + 1} of ${vscode.workspace.asRelativePath(document.uri)}.`,
    );
  }
  return hit;
}

async function reveal(file, range) {
  const document = await vscode.workspace.openTextDocument(vscode.Uri.file(file));
  const column = settings().toSide ? vscode.ViewColumn.Beside : vscode.ViewColumn.Active;
  const editor = await vscode.window.showTextDocument(document, { viewColumn: column, selection: range });
  editor.revealRange(range, vscode.TextEditorRevealType.InCenterIfOutsideViewport);
}

/** Open the generated Lean declaration of the Rust item at the cursor. */
async function openLean() {
  const hit = await atCursor();
  if (!hit) return;
  // Loops and loop bodies are separate declarations; offer them when the cursor is in one.
  const entry = await choose(hit.all, hit.all.length > 1, 'Generated declarations at the cursor');
  if (!entry) return;
  const line = new vscode.Range(entry.declLine, 0, entry.declLine, 0);
  await reveal(entry.leanFile, line);
}

/** Search the workspace's Lean for the name of the generated declaration at the cursor. */
async function findLeanUses() {
  const hit = await atCursor();
  if (!hit) return;
  const entry = await choose(hit.all, hit.all.length > 1, 'Find the Lean uses of');
  if (!entry) return;
  const escaped = entry.leanName.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  await vscode.commands.executeCommand('workbench.action.findInFiles', {
    query: `\\b${escaped}\\b`,
    isRegex: true,
    isCaseSensitive: true,
    filesToInclude: '**/*.lean',
    filesToExclude: settings().exclude,
    triggerSearch: true,
  });
}

/** Open the Rust that the Lean name at the cursor, or the generated declaration around it, comes from. */
async function openRust() {
  const editor = vscode.window.activeTextEditor;
  if (!editor) return;
  const { document, selection } = editor;
  const idx = await index();
  const range = document.getWordRangeAtPosition(selection.active, /[\w'.!?]+/);
  const word = range ? document.getText(range).replace(/^\.+|\.+$/g, '') : '';
  let entries = word ? idx.byName(word) : [];
  if (entries.length === 0) {
    const around = idx.atLean(document.uri.fsPath, selection.active.line);
    entries = around ? [around] : [];
  }
  const entry = await choose(entries, true, `Rust items named ${word}`);
  if (!entry) {
    vscode.window.showInformationMessage(
      word
        ? `Aeneas Link: ${word} is not a declaration that Aeneas generated.`
        : 'Aeneas Link: no generated declaration at the cursor.',
    );
    return;
  }
  const span = new vscode.Range(
    entry.start.line - 1,
    entry.start.col,
    entry.end.line - 1,
    entry.end.col,
  );
  await reveal(entry.rustFile, span);
}

function activate(context) {
  const watcher = vscode.workspace.createFileSystemWatcher('**/*.lean');
  const drop = () => {
    pending = null;
  };
  context.subscriptions.push(
    watcher,
    watcher.onDidChange(drop),
    watcher.onDidCreate(drop),
    watcher.onDidDelete(drop),
    vscode.commands.registerCommand('aeneasLink.openLean', openLean),
    vscode.commands.registerCommand('aeneasLink.findLeanUses', findLeanUses),
    vscode.commands.registerCommand('aeneasLink.openRust', openRust),
    vscode.commands.registerCommand('aeneasLink.reindex', async () => {
      drop();
      const idx = await index();
      vscode.window.showInformationMessage(
        `Aeneas Link: ${idx.entries.length} generated declarations indexed.`,
      );
    }),
  );
}

function deactivate() {}

module.exports = { activate, deactivate };
