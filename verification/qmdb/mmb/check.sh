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
git -C "$worktree" archive "$pin" | tar -x -C "$tmp"
mkdir -p "$tmp/storage/examples"
cp "$here/trace.rs" "$tmp/storage/examples/trace.rs"
(cd "$tmp" && cargo run --locked -j 1 -p commonware-storage --example trace) > "$tmp/paths"
cd "$worktree/verification/lean"
lake build Qmdb.CheckpointAudit
lake env lean -DwarningAsError=true --run "$here/Compare.lean" "$tmp/paths"
