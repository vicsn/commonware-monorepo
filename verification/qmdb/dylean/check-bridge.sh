#!/usr/bin/env bash
# Test the Rust specification against production, regenerate its Lean extraction, and check the
# DyLean proofs over it.
set -euo pipefail
cd "$(dirname "$0")"
here=$PWD
repo=$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")
dy=${DYLEAN:-"$(dirname "$repo")/dylean"}
cache="$repo/.verification-tools/qmdb"
toolchain=leanprover/lean4:v4.35.0
dy_pin=2254f7d1943acb33008e6018130aef34438dd6b2
rust_pin=5b7e44f63b39c29f7305de83ca9c1e22d167b554
hax=${HAX:-"$cache/qmdb-hax-tools/target/release/cargo-hax"}
export XDG_CACHE_HOME=${XDG_CACHE_HOME:-"$cache/modern-cache"}
src="$here/.lake/compat"
out="$here/.lake/bridge"
logs="$here/.lake/logs"
pkg="$here/rust/proofs/lean"
mkdir -p "$src" "$here/.lake/rust" "$out" "$logs"

# The production traversal at the pinned revision; rust/src/lib.rs includes it.
git -C "$repo" archive "$rust_pin" storage/src/merkle/proof/traversal.rs | tar xf - -C "$here/.lake/rust"

# The specification and the pinned traversal agree with this branch's production verifier.
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

# DyLean at its pin, patched for the extraction's Lean 4.35.
git -C "$dy" archive "$dy_pin" | tar xf - -C "$src"
patch -s -d "$src" -p1 < lean435.patch
(cd "$src" && lake +"$toolchain" build DY.EquationalTheory.Hash DY.EquationalTheory.Concat \
    DY.EquationalTheory.Literal DY.Actions.Network DY.Actions.ProtocolEvent DY.Meta) \
    > "$logs/dylean-build.log"

paths=$(cd "$pkg" && lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$src/.lake/build/lib/lean:$paths"
for mod in Model Binding DyTerms Reference Correspondence Protocol SecurityTheorems Scenarios \
    SanityChecks; do
    lean +"$toolchain" -o "$out/$mod.olean" "$mod.lean"
done | tee "$out/audit.log"
python3 - "$out/audit.log" <<'PY'
from pathlib import Path
import re, sys
allowed = {"propext", "Classical.choice", "Quot.sound"}
audit = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", Path(sys.argv[1]).read_text()))
names = [
    "Qmdb.fixed_root_binding", "Qmdb.inclusion_sound", "Qmdb.honest_opening",
    "Qmdb.Correspondence.tree_eq", "Qmdb.Correspondence.replay_eq",
    "Qmdb.Correspondence.verify_single_eq", "Qmdb.Correspondence.traverse_eq",
    "Qmdb.Correspondence.traversal_verify_eq", "Qmdb.Correspondence.root_eq",
    "Qmdb.Correspondence.client_step_eq", "Qmdb.Protocol.client_eq_reference",
    "Qmdb.Protocol.client_authentication", "Qmdb.traversal_matches_spec", "Qmdb.spec_root",
    "Qmdb.extracted_client_authentication", "Qmdb.Sanity.attempt_reachable",
]
for name in names:
    assert name in audit and set(audit[name].split(", ")) <= allowed, (name, audit.get(name))
print(f"{len(names)} theorems use only standard axioms.")
PY
lean +"$toolchain" --run Scenarios.lean
echo 'Client decisions match the expected verdicts.'
