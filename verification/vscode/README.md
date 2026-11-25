# Aeneas Link

A VS Code extension that moves between a Rust item and the Lean declaration that Aeneas generates
from it, which `hax into lean` writes to
`symbolic/proofs/lean/CommonwareSymbolic/Extraction/`.

| Right-click in | Command | What it does |
|---|---|---|
| Rust | **Open Lean Extraction** | Opens the generated declaration of the item at the cursor. In a loop it also offers the loop's own declarations. |
| Rust | **Find Lean Uses of Extraction** | Searches every `.lean` file for the generated name, so the handwritten statements about the item show up. |
| Lean | **Open Rust Source** | On a generated name, in handwritten or generated Lean, or anywhere inside a generated declaration, opens and selects the Rust it comes from. |

Hovering the first line of an extracted Rust item, such as a function's signature, shows the names
of its generated declarations, each with a link that opens it. A loop's first line shows the loop's
declarations. The rest of an item shows nothing, so rust-analyzer's own hovers stay uncluttered.

The command palette also has **Aeneas: Rebuild Extraction Index**.

## How it links the two

Aeneas writes a comment above every declaration it generates:

```lean
/-- [commonware_symbolic::inclusion::verify_element_inclusion]:
    Source: 'src/inclusion.rs', lines 24:0-52:1 -/
def inclusion.verify_element_inclusion
```

The extension indexes every `.lean` file whose header says Aeneas generated it, and reads these
comments. A source path is relative to the crate that Charon read. The extension takes the
crate's root to be the nearest folder above the generated file under which the source files exist,
so production files that the crate includes by `#[path]` resolve to the files in `storage/` and
`cryptography/`. Lines are 1-based and columns 0-based, as Aeneas writes them.

On a line of an item's doc comment or attributes, the item below is used. A span on one line,
such as a name in a derive list, counts only under its columns. Rust that Aeneas did not
translate has no link, and the extension says so.

The index is rebuilt when any `.lean` file changes, so it follows a fresh extraction. **Find Lean
Uses** is a text search for the name relative to the crate's namespace, such as
`inclusion.verify_element_inclusion`. For references that Lean resolves, open the generated
declaration and use **Find All References** from the Lean 4 extension.

## Install

From a checkout of this branch, in VS Code: **Developer: Install Extension from Location...**, then
choose `verification/vscode`. To install a copy instead, package it and install the package:

```bash
cd verification/vscode
npx @vscode/vsce package --allow-missing-repository --skip-license -o aeneas-link.vsix
code --install-extension aeneas-link.vsix
```

Settings: `aeneasLink.include` and `aeneasLink.exclude` choose the Lean files to index (by
default every `.lean` file outside `.lake`, `node_modules` and `target`),
`aeneasLink.openToSide` opens the other side of a link beside the current editor, and
`aeneasLink.hover` turns the hover off.

## Tests

```bash
node --test verification/vscode/test/
```

`test/index.test.js` checks the index against this repository's extraction: every source path
resolves, every named item's span starts at that item, and the lookups in both directions.
`test/extension.test.js` runs the commands through a stand-in for the `vscode` module.
