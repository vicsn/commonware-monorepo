#!/usr/bin/env bash
# Trace the exact Commonware verifier in Tempo's Cargo.lock, then replay its paths in Lean.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
worktree=$(git -C "$here" rev-parse --show-toplevel)
source "$worktree/verification/toolchain.sh"
pin=789e9e5d47288b4138183e51f8d3cf1beedd8561
if ! git -C "$worktree" cat-file -e "$pin^{commit}" 2>/dev/null; then
    echo "Fetch the Tempo dependency with git fetch https://github.com/klkvr/monorepo $pin" >&2
    exit 1
fi
for extractor in "$here"/extract-*.py; do
    python3 "$extractor" --hax "$hax"
done
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
# The pinned fork stays in the tool cache, at a fixed path with its own target directory, so only
# the first run for a pin compiles its dependencies.
src="$cache/tempo/$pin"
if [[ ! -d "$src" ]]; then
    # Extract beside the destination and rename, so an interrupted run leaves no partial tree.
    mkdir -p "$cache/tempo"
    partial=$(mktemp -d "$cache/tempo/.partial.XXXXXX")
    git -C "$worktree" archive "$pin" | tar -x -C "$partial"
    [[ -d "$src" ]] || mv "$partial" "$src"
    rm -rf "$partial"
fi
mkdir -p "$src/storage/examples"
# Copying an unchanged trace.rs would refresh its mtime and rebuild the example.
cmp -s "$here/trace.rs" "$src/storage/examples/trace.rs" ||
    cp "$here/trace.rs" "$src/storage/examples/trace.rs"
(cd "$src" && cargo run --locked -j 1 -p commonware-storage --example trace) > "$tmp/paths"
cd "$worktree/verification/lean"
lake build Qmdb.CheckpointAudit
lake env lean -DwarningAsError=true --run "$here/Compare.lean" "$tmp/paths"
