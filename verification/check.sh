#!/usr/bin/env bash
# Check the symbolic verification: the extracted Rust against production, reproducible extraction,
# the Lean proofs with their axiom audit and executed checks, the mutations, and the BLS protocol.
# Logs go to verification/.lake/logs.
set -euo pipefail
source "$(dirname "$0")/toolchain.sh"
cd "$verification"

# The DyLean checkout is at its pin with no local changes.
test "$(git -C "$dy" rev-parse HEAD)" = "$dy_pin"
git -C "$dy" diff --quiet HEAD --
prepare_dylean

# The extracted crate, built on the production modules it includes, agrees with production.
(cd symbolic && cargo test --offline --quiet) 2>&1 | tee "$logs/rust-tests.log"

# Regenerating the extraction must reproduce the committed files exactly.
pkg=symbolic/proofs/lean
rm -rf .lake/extraction
cp -R "$pkg/CommonwareSymbolic" .lake/extraction
(cd symbolic && "$hax" hax into lean) > "$logs/extract.log" 2>&1
diff -r .lake/extraction "$pkg/CommonwareSymbolic"
echo 'Extraction matches the committed files.'

# The extraction and the proofs share one set of dependency builds, optionally the hax Lean
# experiment's.
link_packages "$pkg" "$repo/.worktrees/qmdb-hax-lean/verification/qmdb/general/proofs/lean/.lake/packages"
(cd "$pkg" && lake build CommonwareSymbolic.Extraction) > "$logs/extraction-build.log"
if [[ ! -e lean/.lake/packages ]]; then
    mkdir -p lean/.lake
    ln -s ../../symbolic/proofs/lean/.lake/packages lean/.lake/packages
fi

# Every proof module, the executed checks in SanityChecks and the axiom audit of every theorem.
(cd lean && lake build) > "$logs/lean-build.log" 2>&1 || { tail -40 "$logs/lean-build.log"; exit 1; }
grep 'depend only on standard axioms' "$logs/lean-build.log"

# Each mutation of the extracted Rust must break the named proof module.
python3 mutate.py qmdb/mutations.toml | tee "$logs/mutations.log"

bash bls/check.sh
