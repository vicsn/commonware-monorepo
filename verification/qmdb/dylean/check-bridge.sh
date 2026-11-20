#!/usr/bin/env bash
# Test the client against production, regenerate the Lean extraction of the client with the
# production traversal and hash-input encodings it includes, and check the DyLean proofs over it.
set -euo pipefail
cd "$(dirname "$0")"
here=$PWD
repo=$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")
dy=${DYLEAN:-"$(dirname "$repo")/dylean"}
cache="$repo/.verification-tools/qmdb"
toolchain=leanprover/lean4:v4.35.0
dy_pin=2254f7d1943acb33008e6018130aef34438dd6b2
hax=${HAX:-"$cache/qmdb-hax-tools/target/release/cargo-hax"}
export XDG_CACHE_HOME=${XDG_CACHE_HOME:-"$cache/modern-cache"}
src="$here/.lake/compat"
out="$here/.lake/bridge"
logs="$here/.lake/logs"
pkg="$here/rust/proofs/lean"
mkdir -p "$src" "$out" "$logs"

# The client, built on the production traversal and encodings, agrees with the production verifier.
(cd rust && cargo test --offline --quiet) 2>&1 | tee "$logs/rust-tests.log"

# Regenerating the extraction must reproduce the committed files exactly.
rm -rf "$here/.lake/extraction"
cp -R "$pkg/QmdbDylean" "$here/.lake/extraction"
(cd rust && "$hax" hax into lean) > "$logs/extract.log" 2>&1
diff -r "$here/.lake/extraction" "$pkg/QmdbDylean"
echo 'Extraction matches the committed files.'

# Optional: reuse the hax Lean experiment's dependency builds instead of building them here.
deps="$repo/.worktrees/qmdb-hax-lean/verification/qmdb/general/proofs/lean/.lake/packages"
mkdir -p "$pkg/.lake"
if [[ -d "$deps" && ! -e "$pkg/.lake/packages" ]]; then
    ln -s "$deps" "$pkg/.lake/packages"
fi
(cd "$pkg" && lake build QmdbDylean.Extraction) > "$logs/extraction-build.log"

# The bridge's Lake package, used by editors, shares the extraction's dependencies.
if [[ ! -e "$here/.lake/packages" ]]; then
    ln -s ../rust/proofs/lean/.lake/packages "$here/.lake/packages"
fi

# DyLean at its pin, patched for the extraction's Lean 4.35 and to load beside Aeneas.
git -C "$dy" archive "$dy_pin" | tar xf - -C "$src"
patch -s -d "$src" -p1 < lean435.patch
(cd "$src" && lake +"$toolchain" build DY.EquationalTheory.Hash DY.EquationalTheory.Concat \
    DY.EquationalTheory.Literal DY.Actions.Network DY.Actions.ProtocolEvent DY.Meta) \
    > "$logs/dylean-build.log"

paths=$(cd "$pkg" && lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$src/.lake/build/lib/lean:$paths"
for mod in Hashing Verifier DyTerms Symbolic Protocol SecurityTheorems SanityChecks; do
    lean +"$toolchain" -o "$out/$mod.olean" "$mod.lean"
done | tee "$out/audit.log"
python3 - "$out/audit.log" <<'PY'
from pathlib import Path
import re, sys
allowed = {"propext", "Classical.choice", "Quot.sound"}
audit = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", Path(sys.argv[1]).read_text()))
names = [
    "Qmdb.Verifier.binding_or_collision", "Qmdb.Verifier.byte_binding_or_collision",
    "Qmdb.Verifier.honest_opening", "Qmdb.Verifier.extra_sibling_rejected",
    "Qmdb.Verifier.verify_total", "Qmdb.Symbolic.binding", "Qmdb.Symbolic.client_step_sound",
    "Qmdb.Symbolic.honest_accepted", "Qmdb.Symbolic.substitution_rejected",
    "Qmdb.Protocol.client_authentication", "Qmdb.production_binding_or_collision",
    "Qmdb.production_binding", "Qmdb.honest_snapshots_exist",
    "Qmdb.extracted_client_authentication", "Qmdb.Sanity.accepts_alice",
    "Qmdb.Sanity.accepts_bob", "Qmdb.Sanity.rejects_substituted",
    "Qmdb.Sanity.rejects_misplaced", "Qmdb.Sanity.rejects_long", "Qmdb.Sanity.finder_finds",
    "Qmdb.Sanity.attempt_reachable",
]
for name in names:
    assert name in audit and set(audit[name].split(", ")) <= allowed, (name, audit.get(name))
print(f"{len(names)} theorems use only standard axioms.")
PY
