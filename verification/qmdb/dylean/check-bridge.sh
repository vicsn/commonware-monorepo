#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
here=$PWD
repo=$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")
dy=${DYLEAN:-"$(dirname "$repo")/dylean"}
cache="$repo/.verification-tools/qmdb"
toolchain=leanprover/lean4:v4.35.0
dy_pin=2254f7d1943acb33008e6018130aef34438dd6b2
rust_pin=5b7e44f63b39c29f7305de83ca9c1e22d167b554
src="$here/.lake/compat"
rust="$here/.lake/rust"
out="$here/.lake/bridge"
mkdir -p "$src" "$rust" "$out"
git -C "$dy" archive "$dy_pin" | tar xf - -C "$src"
patch -s -d "$src" -p1 < lean435.patch
(cd "$src" && lake +"$toolchain" build DY.EquationalTheory.Hash DY.EquationalTheory.Concat \
    DY.EquationalTheory.Literal DY.Actions.Network DY.Actions.ProtocolEvent DY.Meta)
crate=verification/qmdb/general
git -C "$repo" archive "$rust_pin" storage/src/merkle/proof/traversal.rs "$crate" | tar xf - -C "$rust"
pkg="$rust/$crate/proofs/lean"
export XDG_CACHE_HOME=${XDG_CACHE_HOME:-"$cache/modern-cache"}
(cd "$rust/$crate" && "${HAX:-$cache/qmdb-hax-tools/target/release/cargo-hax}" hax into lean)
# Check the regenerated definitions against the pinned experiment before using them.
for f in "$pkg"/QmdbTraversal/Extraction/*.lean; do
    git show "$rust_pin:${f#"$rust/"}" | cmp - "$f"
done
deps="$repo/.worktrees/qmdb-hax-aeneas-lean/$crate/proofs/lean/.lake/packages"
mkdir -p "$pkg/.lake"
if [[ -d "$deps" && ! -e "$pkg/.lake/packages" ]]; then
    ln -s "$deps" "$pkg/.lake/packages"
fi
(cd "$pkg" && lake build QmdbTraversal.Extraction)
paths=$(cd "$pkg" && lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$src/.lake/build/lib/lean:$paths"
for mod in Model Binding Correspondence Protocol SecurityTheorems; do
    lean +"$toolchain" -o "$out/$mod.olean" "$mod.lean"
done | tee "$out/audit.log"
python3 - "$out/audit.log" <<'PY'
from pathlib import Path
import re, sys
allowed = {"propext", "Classical.choice", "Quot.sound"}
audit = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", Path(sys.argv[1]).read_text()))
for name in ["Qmdb.fixed_root_binding","Qmdb.inclusion_sound","Qmdb.honest_opening",
             "Qmdb.Bridge.replay_eq","Qmdb.Bridge.verify_iff","Qmdb.same_verifier","Qmdb.extracted_client_authentication"]:
    assert name in audit and set(audit[name].split(", ")) <= allowed, (name,audit)
PY
lean +"$toolchain" --run SanityChecks.lean
echo 'Reachable network/client scenarios passed.'
# The event-preservation proof must depend on actually checking the opening.
sed 's/guard (Verifier.verify h loc root item ws)/guard true/' Protocol.lean > "$out/UncheckedClient.lean"
if lean +"$toolchain" "$out/UncheckedClient.lean" > "$out/unchecked.log" 2>&1; then
    echo "Unchecked client unexpectedly passed" >&2
    exit 1
fi
grep -Eq 'failed|unsolved goals' "$out/unchecked.log"
echo 'Event invariant rejects the unchecked client.'
