#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
repo=$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")
dy=${DYLEAN:-"$(dirname "$repo")/dylean"}
pin=2254f7d1943acb33008e6018130aef34438dd6b2
test "$(git -C "$dy" rev-parse HEAD)" = "$pin"
git -C "$dy" diff --quiet HEAD --
(cd "$dy" && lake build DY.EquationalTheory.Hash DY.EquationalTheory.Concat DY.EquationalTheory.Literal)
mkdir -p .lake
export LEAN_PATH="$PWD/.lake:$dy/.lake/build/lib/lean"
lean -o .lake/Model.olean Model.lean
python3 validate.py
bash check-bridge.sh
