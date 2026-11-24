#!/usr/bin/env bash
# Profile the Lean build of every target: elaborate each module of the extraction and of the
# handwritten Lean on its own, one at a time, with Lean's profiler on, and summarise where the time
# goes with profile.py. Run after check.sh, which builds every module and its dependencies.
# Logs go to verification/.lake/logs/profile; the summary is summary.md there.
#
# Usage: profile.sh [THRESHOLD_MS]
#   THRESHOLD_MS: report declarations and tactic runs that take at least this long (default 100).
set -euo pipefail
threshold=${1:-100}
source "$(dirname "$0")/toolchain.sh"
cd "$verification"
out="$logs/profile"
rm -rf "$out"
mkdir -p "$out"

# Elaborate the module $2 of the package in $1. Theorem bodies are elaborated synchronously, so
# each declaration's time is its own and the times of a module add up to its elaboration.
profile() {
    local file="${2//.//}.lean"
    (cd "$1" && /usr/bin/time -p lake env lean -DElab.async=false -Dprofiler=true \
        -Dprofiler.threshold="$threshold" -Dtrace.profiler=true \
        -Dtrace.profiler.threshold="$threshold" "$file") > "$out/$2.log" 2>&1 \
        || echo "profile.sh: $2 failed; see $out/$2.log" >&2
}

pkg=symbolic/proofs/lean
for file in $(cd "$pkg" && find CommonwareSymbolic -name '*.lean' | sort); do
    module=${file%.lean}
    profile "$pkg" "${module//\//.}"
done
for file in $(cd lean && find Commonware Qmdb Bls Sake -name '*.lean' | sort); do
    module=${file%.lean}
    profile lean "${module//\//.}"
done

python3 profile.py "$out" "$pkg" lean > "$out/summary.md"
cat "$out/summary.md"
