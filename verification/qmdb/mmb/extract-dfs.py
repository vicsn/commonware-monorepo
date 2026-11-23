#!/usr/bin/env python3
"""Regenerate the specialized pinned Merkle DFS used by the Lean refinement proof."""

import argparse
from pathlib import Path
import subprocess
import tempfile

PIN = "789e9e5d47288b4138183e51f8d3cf1beedd8561"
HERE = Path(__file__).resolve().parent
VERIFICATION = HERE.parents[1]
ROOT = VERIFICATION.parent
TARGET = VERIFICATION / "lean/Qmdb/Mmb/Pinned.lean"


def subtree_source():
    proof = subprocess.check_output(
        ["git", "-C", ROOT, "show", f"{PIN}:storage/src/merkle/proof.rs"], text=True
    )
    begin = proof.index("    fn leaf_end(&self)")
    end = proof.index("    /// True if this subtree's leaves lie wholly inside", begin)
    guards = proof[begin:end].replace("<F>", "")
    begin = proof.index("    fn reconstruct_digest<D, H, E>(")
    method = proof[begin:proof.index("\n}", begin)]
    # The verifier always calls reconstruct_root_inner with collected=None. Remove that
    # parameter, its None reborrows and the unreachable recording branch before extraction.
    method = method.replace("        mut collected: Option<&mut Vec<(Position<F>, D)>>,\n", "")
    method = method.replace("            collected.as_deref_mut(),\n", "")
    branch = method.index("        if let Some(ref mut cd) = collected {")
    method = method[:branch] + method[method.index("        Ok(hasher.node_digest", branch):]
    # A subtree's symbolic name is (first leaf, height). The trace interpreter maps that
    # name to its MMB position. The split point and child heights are copied from children().
    begin = proof.index("        let child_height = self.height - 1;")
    split = proof[begin:proof.index("        (\n", begin)]
    children = """    fn children(&self) -> (Self, Self) {
""" + split + """        (
            Self { pos: (self.leaf_start, child_height), height: child_height, leaf_start: self.leaf_start },
            Self { pos: (mid, child_height), height: child_height, leaf_start: mid },
        )
    }
"""
    method = method.replace("<F>", "").replace("Hasher<F, Digest", "Hasher<Digest")
    return """#![allow(dead_code)]
use std::ops::Range;
type Location = u64;
type Position = (u64, u32);
struct Subtree { pos: Position, height: u32, leaf_start: Location }
trait Digest: Copy {}
trait Hasher { type Digest: Digest;
    fn leaf_digest(&self, pos: Position, data: &[u8]) -> Self::Digest;
    fn node_digest(&self, pos: Position, left: &Self::Digest, right: &Self::Digest) -> Self::Digest;
}
enum ReconstructionError { MissingDigests, MissingElements }
impl Subtree {
""" + guards + children + method + "\n}\n"



def graft_source():
    """Keep the source branches for the chunk count and for selecting the graft's hash inputs."""
    source = subprocess.check_output(
        ["git", "-C", ROOT, "show", f"{PIN}:storage/src/qmdb/current/grafting.rs"], text=True
    )
    start = source.index("    if ops_leaves < birth_chunk_0")
    end = source.index("\n}", start)
    count = source[start:end]
    start = source.index("                if chunk.iter().all(|&b| b == 0)")
    end = source.index("\n                }", source.index("self.hash(", start)) + len("\n                }")
    # Record the digest returned or the two inputs supplied to the hash callback.
    # Borrowing the op digest is transparent for this trace of the verifier.
    guard = source[start:end].replace(
        "\n                    ops_subtree_root\n", "\n                    Trace::Unwrapped(ops_subtree_root)\n"
    ).replace("self.hash(&[chunk, ops_subtree_root.as_ref()])", "Trace::Hash(chunk, ops_subtree_root)")
    family = subprocess.check_output(
        ["git", "-C", ROOT, "show", f"{PIN}:storage/src/merkle/mmb/mod.rs"], text=True
    )
    begin = family.index("        if height == 0", family.index("    fn peak_birth_size("))
    end = family.index("\n    }", begin)
    birth = family[begin:end].replace("*<Self as Graftable>::leftmost_leaf(pos, 0)", "first")
    birth = birth.replace("<Self as Graftable>::leftmost_leaf(pos, height)", "first")
    birth = birth.replace("*base.checked_add", "base.checked_add")
    return """
fn birth_size(first: u64, height: u32) -> u64 {
""" + birth + """
}
enum Trace<'a> { Unwrapped(&'a [u8]), Hash(&'a [u8], &'a [u8]) }
fn graft<'a>(chunk: &'a [u8], ops_subtree_root: &'a [u8]) -> Trace<'a> {
""" + guard + """
}
fn resolved(ops_leaves: u64, grafting_height: u32, birth_chunk_0: u64) -> u64 {
""" + count + """
}
"""

def extract(hax, tmp):
    (tmp / "src").mkdir()
    (tmp / "Cargo.toml").write_text(
        '[package]\nname = "pinned-dfs"\nversion = "0.0.0"\nedition = "2024"\n\n[workspace]\n'
    )
    (tmp / "hax.toml").write_bytes((VERIFICATION / "symbolic/hax.toml").read_bytes())
    (tmp / "src/lib.rs").write_text(subtree_source() + graft_source())
    subprocess.run([hax, "hax", "into", "lean"], cwd=tmp, check=True)
    extracted = tmp / "proofs/lean/PinnedDfs/Extraction"
    # Keep the two tiny generated modules in one Qmdb Lake target. Hax emits no model
    # for Option<&T>::copied(); shared references read as Lean values and T is Copy.
    types = (extracted / "Types.lean").read_text().replace(
        "public import PinnedDfs.Extraction.TypesExternal\n", ""
    ).replace(
        "@[expose] public section",
        "@[expose] public section\nset_option linter.missingDocs false",
    )
    namespace = "namespace pinned_dfs"
    types = types.replace(namespace, """/-- A checked shift returns None when the count reaches the machine word width. -/
def CoreModels.core.num.U64.checked_shl (word : Std.U64) (shift : Std.U32) :
    RustM (Option Std.U64) :=
  RustM.ok (if shift.val < 64 then some ⟨word.bv <<< shift.val⟩ else none)

/-- Reading a shared optional Copy value preserves its contents. -/
def CoreModels.core.option.OptionShared0T.copied {T : Type} (_ : core.marker.Copy T)
    (x : Option T) : RustM (Option T) := RustM.ok x

""" + namespace, 1)
    funs = (extracted / "Funs.lean").read_text()
    return types + "\n" + funs[funs.index(namespace):]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hax", required=True, type=Path)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as directory:
        out = extract(args.hax.resolve(), Path(directory))
    if args.write:
        TARGET.write_text(out)
    elif out != TARGET.read_text():
        raise SystemExit("Pinned DFS extraction differs; rerun with --write and inspect the diff.")


if __name__ == "__main__":
    main()
