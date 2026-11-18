#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
root=$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")
dy=${DYLEAN:-"$(dirname "$root")/dylean"}
lean_pin=leanprover/lean4:v4.35.0
dy_pin=2254f7d1943acb33008e6018130aef34438dd6b2
bls_pin=d1a5e7ca30d1cdc59be66356dbac7ccee070a892
# Use the same versioned compatibility patch as the QMDB Rust bridge.
compat="$PWD/../qmdb/dylean/.lake/compat"
mkdir -p "$compat" .lake
git -C "$dy" archive "$dy_pin" | tar xf - -C "$compat"
patch -s -d "$compat" -p1 < ../qmdb/dylean/lean435.patch
(cd "$compat" && lake +"$lean_pin" build DY.Actions.ProtocolEvent)
pkg="$PWD/.lake/$bls_pin/verification/bls/proofs/lean"
mkdir -p ".lake/$bls_pin"
git -C "$root" archive "$bls_pin" verification/bls/proofs/lean | tar xf - -C ".lake/$bls_pin"
mkdir -p "$pkg/.lake"
deps="$root/.worktrees/qmdb-hax-lean/verification/bls/proofs/lean/.lake/packages"
if [[ -d "$deps" && ! -e "$pkg/.lake/packages" ]]; then ln -s "$deps" "$pkg/.lake/packages"; fi
(cd "$pkg" && lake build BlsRouting.Examples)
paths=$(cd "$pkg" && lake env printenv LEAN_PATH)
export LEAN_PATH="$compat/.lake/build/lib/lean:$paths"
lean +"$lean_pin" -DwarningAsError=true Protocol.lean
