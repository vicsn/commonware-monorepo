'use strict';
// Drives the extension's commands through a stand-in for the `vscode` module, on the
// repository's own files, and checks what they open or search for.

const assert = require('node:assert/strict');
const fs = require('node:fs');
const Module = require('node:module');
const path = require('node:path');
const test = require('node:test');

const REPO = path.resolve(__dirname, '../../..');
const EXTRACTION = path.join(
  REPO,
  'verification/symbolic/proofs/lean/CommonwareSymbolic/Extraction',
);

class Range {
  constructor(sl, sc, el, ec) {
    this.start = { line: sl, character: sc };
    this.end = { line: el, character: ec };
  }
}

/** A stand-in for the parts of the `vscode` API that the extension uses. */
function fake() {
  const calls = { opened: [], executed: [], picks: [], messages: [] };
  const commands = new Map();
  const document = (file) => {
    const text = fs.readFileSync(file, 'utf8');
    const lines = text.split('\n');
    return {
      uri: { fsPath: file },
      getText: (range) => {
        if (!range) return text;
        return lines[range.start.line].slice(range.start.character, range.end.character);
      },
      getWordRangeAtPosition: (pos, regex) => {
        const line = lines[pos.line];
        const re = new RegExp(regex.source, 'g');
        for (let m; (m = re.exec(line)); ) {
          if (m.index <= pos.character && pos.character <= m.index + m[0].length) {
            return new Range(pos.line, m.index, pos.line, m.index + m[0].length);
          }
        }
        return undefined;
      },
    };
  };
  const vscode = {
    Range,
    ViewColumn: { Active: -1, Beside: -2 },
    TextEditorRevealType: { InCenterIfOutsideViewport: 2 },
    Uri: { file: (fsPath) => ({ fsPath }) },
    workspace: {
      getConfiguration: () => ({ get: (_key, fallback) => fallback }),
      findFiles: async () =>
        fs
          .readdirSync(EXTRACTION)
          .filter((f) => f.endsWith('.lean'))
          .map((f) => ({ fsPath: path.join(EXTRACTION, f) }))
          .concat([{ fsPath: path.join(REPO, 'verification/lean/Qmdb/Inclusion.lean') }]),
      fs: { readFile: async (uri) => fs.readFileSync(uri.fsPath) },
      asRelativePath: (p) => path.relative(REPO, p.fsPath || p),
      openTextDocument: async (uri) => document(uri.fsPath),
      createFileSystemWatcher: () => ({
        onDidChange: () => ({}),
        onDidCreate: () => ({}),
        onDidDelete: () => ({}),
        dispose() {},
      }),
    },
    window: {
      activeTextEditor: null,
      showTextDocument: async (doc, options) => {
        calls.opened.push({ file: doc.uri.fsPath, selection: options.selection });
        return { revealRange() {} };
      },
      showQuickPick: async (items) => {
        calls.picks.push(items);
        return items[0];
      },
      showInformationMessage: (m) => calls.messages.push(m),
      showWarningMessage: (m) => calls.messages.push(m),
    },
    commands: {
      registerCommand: (name, f) => commands.set(name, f),
      executeCommand: async (name, args) => calls.executed.push({ name, args }),
    },
  };
  const open = (file, line, character) => {
    vscode.window.activeTextEditor = {
      document: document(file),
      selection: { active: { line, character } },
    };
  };
  return { vscode, calls, commands, open };
}

function activate() {
  const env = fake();
  const load = Module._load;
  Module._load = function (request, ...rest) {
    return request === 'vscode' ? env.vscode : load.call(this, request, ...rest);
  };
  try {
    delete require.cache[require.resolve('../extension')];
    require('../extension').activate({ subscriptions: [] });
  } finally {
    Module._load = load;
  }
  return env;
}

function lineOf(file, needle) {
  const i = fs.readFileSync(file, 'utf8').split('\n').findIndex((l) => l.includes(needle));
  assert.ok(i >= 0, needle);
  return i;
}

const INCLUSION_RS = path.join(REPO, 'verification/symbolic/src/inclusion.rs');

test('Open Lean Extraction opens the generated definition', async () => {
  const { calls, commands, open } = activate();
  open(INCLUSION_RS, lineOf(INCLUSION_RS, 'fn verify_element_inclusion'), 20);
  await commands.get('aeneasLink.openLean')();
  assert.equal(calls.picks.length, 0);
  assert.equal(calls.opened.length, 1);
  const { file, selection } = calls.opened[0];
  assert.equal(path.basename(file), 'Funs.lean');
  const line = fs.readFileSync(file, 'utf8').split('\n')[selection.start.line];
  assert.equal(line, 'def inclusion.verify_element_inclusion');
});

test('Find Lean Uses searches the Lean for the generated name', async () => {
  const { calls, commands, open } = activate();
  open(INCLUSION_RS, lineOf(INCLUSION_RS, 'fn verify_element_inclusion') + 3, 4);
  await commands.get('aeneasLink.findLeanUses')();
  assert.equal(calls.executed.length, 1);
  const { name, args } = calls.executed[0];
  assert.equal(name, 'workbench.action.findInFiles');
  assert.equal(args.query, '\\binclusion\\.verify_element_inclusion\\b');
  assert.equal(args.filesToInclude, '**/*.lean');
});

test('Open Rust Source on a Lean name opens the Rust span', async () => {
  const { calls, commands, open } = activate();
  const lean = path.join(REPO, 'verification/lean/Qmdb/Inclusion.lean');
  const line = lineOf(lean, 'inclusion.verify_element_inclusion dyTerms');
  const col = fs.readFileSync(lean, 'utf8').split('\n')[line].indexOf('verify_element');
  open(lean, line, col);
  await commands.get('aeneasLink.openRust')();
  assert.deepEqual(calls.messages, []);
  const { file, selection } = calls.opened[0];
  assert.equal(file, fs.realpathSync.native(INCLUSION_RS));
  const rust = fs.readFileSync(file, 'utf8').split('\n')[selection.start.line];
  assert.match(rust, /fn verify_element_inclusion/);
});

test('Open Rust Source inside a generated body opens its Rust', async () => {
  const { calls, commands, open } = activate();
  const funs = path.join(EXTRACTION, 'Funs.lean');
  // A blank spot in the body of the generated definition, on no name.
  open(funs, lineOf(funs, 'def inclusion.verify_element_inclusion') + 7, 0);
  await commands.get('aeneasLink.openRust')();
  const rust = fs.readFileSync(calls.opened[0].file, 'utf8').split('\n');
  assert.match(rust[calls.opened[0].selection.start.line], /fn verify_element_inclusion/);
});

test('Inside a loop the function and its loop parts are offered', async () => {
  const { calls, commands, open } = activate();
  const rules = path.join(REPO, 'cryptography/src/bls12381/certificate/rules.rs');
  const text = fs.readFileSync(path.join(EXTRACTION, 'Funs.lean'), 'utf8');
  const span = /\[commonware_symbolic::rules::count\]: loop body 0:\n\s+Source: '[^']+', lines (\d+):/.exec(text);
  assert.ok(span);
  open(rules, Number(span[1]), 8);
  await commands.get('aeneasLink.openLean')();
  assert.equal(calls.picks.length, 1);
  assert.deepEqual(
    calls.picks[0].map((i) => [i.label, i.description]),
    [
      ['commonware_symbolic.rules.count', ''],
      ['commonware_symbolic.rules.count_loop.body', 'loop body'],
      ['commonware_symbolic.rules.count_loop', 'loop'],
    ],
  );
});

test('A line with no extraction says so', async () => {
  const { calls, commands, open } = activate();
  open(INCLUSION_RS, 0, 0);
  await commands.get('aeneasLink.openLean')();
  assert.equal(calls.opened.length, 0);
  assert.match(calls.messages[0], /no generated Lean comes from line 1/);
});
