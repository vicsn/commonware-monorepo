# Pins and setup shared by every symbolic verification check. Source this file.
#
# Keep the DyLean checkout beside the canonical monorepo (override with DYLEAN) and the managed
# hax CLI in .verification-tools (override with HAX).

verification=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
repo=$(dirname "$(git -C "$verification" rev-parse --path-format=absolute --git-common-dir)")
dy=${DYLEAN:-"$(dirname "$repo")/dylean"}
dy_pin=2254f7d1943acb33008e6018130aef34438dd6b2
lean_toolchain=leanprover/lean4:v4.35.0
cache="$repo/.verification-tools/qmdb"
hax=${HAX:-"$cache/qmdb-hax-tools/target/release/cargo-hax"}
export XDG_CACHE_HOME=${XDG_CACHE_HOME:-"$cache/modern-cache"}
logs="$verification/.lake/logs"
mkdir -p "$logs"

# DyLean at its pin, patched for the extraction's Lean 4.35 and to load beside Aeneas, in
# .lake/dylean. Every target builds against this one copy.
prepare_dylean() {
    local out="$verification/.lake/dylean"
    mkdir -p "$out"
    git -C "$dy" archive "$dy_pin" | tar xf - -C "$out"
    patch -s -d "$out" -p1 < "$verification/lean435.patch"
    (cd "$out" && lake +"$lean_toolchain" build DY.EquationalTheory.Hash \
        DY.EquationalTheory.Concat DY.EquationalTheory.Literal DY.Actions.Network \
        DY.Actions.ProtocolEvent DY.Meta) > "$logs/dylean-build.log"
}

# Optional: let the Lake package $1 reuse the dependency builds in $2 instead of building them.
link_packages() {
    mkdir -p "$1/.lake"
    if [[ -d "$2" && ! -e "$1/.lake/packages" ]]; then
        ln -s "$2" "$1/.lake/packages"
    fi
}
