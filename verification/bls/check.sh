#!/usr/bin/env bash
# Check the BLS DyLean protocol against the exact hax BLS extraction pinned below, with the shared
# DyLean build.
set -euo pipefail
source "$(dirname "$0")/../toolchain.sh"
cd "$verification/bls"
bls_pin=d1a5e7ca30d1cdc59be66356dbac7ccee070a892
prepare_dylean
pkg="$PWD/.lake/$bls_pin/verification/bls/proofs/lean"
mkdir -p ".lake/$bls_pin"
git -C "$repo" archive "$bls_pin" verification/bls/proofs/lean | tar xf - -C ".lake/$bls_pin"
link_packages "$pkg" "$repo/.worktrees/qmdb-hax-lean/verification/bls/proofs/lean/.lake/packages"
(cd "$pkg" && lake build BlsRouting.Examples)
paths=$(cd "$pkg" && lake env printenv LEAN_PATH)
export LEAN_PATH="$verification/.lake/dylean/.lake/build/lib/lean:$paths"
lean +"$lean_toolchain" -DwarningAsError=true Protocol.lean
