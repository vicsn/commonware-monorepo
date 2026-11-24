#!/usr/bin/env bash
# Check the symbolic verification: the extracted Rust against production, reproducible extraction,
# the audit guide against the sources, the Lean proofs of every target with their axiom audits and
# executed checks, and the pinned Tempo replay. With --mutation-testing, also require each mutation
# of the extracted Rust to break its named proof modules; this takes about 20 minutes.
# Logs go to verification/.lake/logs.
#
# Usage: check.sh [--mutation-testing]
set -euo pipefail
mutation_testing=false
for arg in "$@"; do
    case "$arg" in
        --mutation-testing) mutation_testing=true ;;
        *) echo "usage: $0 [--mutation-testing]" >&2; exit 2 ;;
    esac
done
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

# The audit guide shows the current Rust and Lean side by side.
python3 audit/build.py --check

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

# A warning in the handwritten Lean fails the check: the style linters that lakefile.toml turns
# on, a missing doc string and a proof that uses `sorry` all report as warnings.
if grep -A6 '^warning: ' "$logs/lean-build.log"; then exit 1; fi
echo 'The Lean build has no warnings.'

# The declaration graph of the audit guide is the one that Lean prints for these proofs.
python3 audit/build.py --dag --check

# Reproduce the selected extraction from Tempo's pinned fork and compare its proof traces.
bash qmdb/mmb/check.sh | tee "$logs/tempo-mmb.log"

# Each mutation of the extracted Rust must break the named proof modules.
if [[ "$mutation_testing" == true ]]; then
    python3 mutate.py qmdb/mutations.toml | tee "$logs/mutations.log"
    python3 mutate.py bls/mutations.toml | tee -a "$logs/mutations.log"
    python3 mutate.py sake/mutations.toml | tee -a "$logs/mutations.log"
else
    echo 'Skipped mutation testing; run with --mutation-testing to include it.'
fi
