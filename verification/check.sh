#!/usr/bin/env bash
# Check the symbolic verification: the extracted Rust against production, reproducible extraction,
# the audit guide against the sources, the Lean proofs of every target with their axiom audits and
# executed checks, and the pinned Tempo replay. With --mutation-testing, also require each mutation
# of the extracted Rust to break its named proof modules; --mutation-jobs=N|auto checks that many
# mutations at once (see mutate.py). Logs and the wall time of each stage (timings.log) go to
# verification/.lake/logs.
#
# Usage: check.sh [--mutation-testing] [--mutation-jobs=N|auto]
set -euo pipefail
mutation_testing=false
mutation_jobs=()
for arg in "$@"; do
    case "$arg" in
        --mutation-testing) mutation_testing=true ;;
        --mutation-jobs=*) mutation_jobs=(--jobs "${arg#*=}") ;;
        *) echo "usage: $0 [--mutation-testing] [--mutation-jobs=N|auto]" >&2; exit 2 ;;
    esac
done
source "$(dirname "$0")/toolchain.sh"
cd "$verification"

# Wall time of each stage, in seconds, goes to timings.log.
timings="$logs/timings.log"
: > "$timings"
stage_start=$SECONDS
mark() {
    echo "$1 $((SECONDS - stage_start))" >> "$timings"
    stage_start=$SECONDS
}

# The DyLean checkout is at its pin with no local changes.
test "$(git -C "$dy" rev-parse HEAD)" = "$dy_pin"
git -C "$dy" diff --quiet HEAD --
prepare_dylean
mark dylean

# The extracted crate, built on the production modules it includes, agrees with production.
(cd symbolic && cargo test --offline --quiet) 2>&1 | tee "$logs/rust-tests.log"
mark rust-tests

# Regenerating the extraction must reproduce the committed files exactly.
pkg=symbolic/proofs/lean
rm -rf .lake/extraction
cp -R "$pkg/CommonwareSymbolic" .lake/extraction
(cd symbolic && "$hax" hax into lean) > "$logs/extract.log" 2>&1
diff -r .lake/extraction "$pkg/CommonwareSymbolic"
echo 'Extraction matches the committed files.'
mark extraction

# The audit guide shows the current Rust and Lean side by side.
python3 audit/build.py --check
mark audit-guide

# The extraction and the proofs share one set of dependency builds, optionally the hax Lean
# experiment's.
link_packages "$pkg" "$repo/.worktrees/qmdb-hax-lean/verification/qmdb/general/proofs/lean/.lake/packages"
(cd "$pkg" && lake build CommonwareSymbolic.Extraction) > "$logs/extraction-build.log"
mark extraction-build
if [[ ! -e lean/.lake/packages ]]; then
    mkdir -p lean/.lake
    ln -s ../../symbolic/proofs/lean/.lake/packages lean/.lake/packages
fi

# Every proof module, the executed checks in SanityChecks and the axiom audit of every theorem.
(cd lean && lake build) > "$logs/lean-build.log" 2>&1 || { tail -40 "$logs/lean-build.log"; exit 1; }
grep 'depend only on standard axioms' "$logs/lean-build.log"
mark lean-build

# A warning in the handwritten Lean fails the check: the style linters that lakefile.toml turns
# on, a missing doc string and a proof that uses `sorry` all report as warnings.
if grep -A6 '^warning: ' "$logs/lean-build.log"; then exit 1; fi
echo 'The Lean build has no warnings.'

# The declaration graph of the audit guide is the one that Lean prints for these proofs.
python3 audit/build.py --dag --check
mark audit-dag

# Reproduce the selected extraction from Tempo's pinned fork and compare its proof traces.
bash qmdb/mmb/check.sh | tee "$logs/tempo-mmb.log"
mark tempo-mmb

# Each mutation of the extracted Rust must break the named proof modules.
if [[ "$mutation_testing" == true ]]; then
    python3 mutate.py ${mutation_jobs[@]+"${mutation_jobs[@]}"} \
        qmdb/mutations.toml bls/mutations.toml sake/mutations.toml | tee "$logs/mutations.log"
    mark mutations
else
    echo 'Skipped mutation testing; run with --mutation-testing to include it.'
fi
cat "$timings"
