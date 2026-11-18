#!/usr/bin/env bash
# Check the pinned DyLean checkout, then run the bridge and the Rust mutation checks.
set -euo pipefail
cd "$(dirname "$0")"
repo=$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")
dy=${DYLEAN:-"$(dirname "$repo")/dylean"}
pin=2254f7d1943acb33008e6018130aef34438dd6b2
test "$(git -C "$dy" rev-parse HEAD)" = "$pin"
git -C "$dy" diff --quiet HEAD --
bash check-bridge.sh
python3 mutations.py
