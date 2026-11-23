#!/usr/bin/env python3
"""Extract the pinned Blueprint::split_proof_digests arithmetic and returned slice boundaries."""

import argparse
from pathlib import Path
import re
import subprocess
import tempfile

PIN = "789e9e5d47288b4138183e51f8d3cf1beedd8561"
HERE = Path(__file__).resolve().parent
VERIFICATION = HERE.parents[1]
ROOT = VERIFICATION.parent
TARGET = VERIFICATION / "lean/Qmdb/Mmb/PinnedLayout.lean"


def source():
    proof = subprocess.check_output(
        ["git", "-C", ROOT, "show", f"{PIN}:storage/src/merkle/proof.rs"], text=True
    )
    start = proof.index("    pub(crate) fn split_proof_digests")
    method = proof[start:proof.index("\n    }", start) + len("\n    }")]
    # The splitter only observes the lengths of these five lists. Represent the
    # returned borrows by their actual index or range; the proof checks their bounds.
    method = method.replace("split_proof_digests<'a, D>", "split_proof_digests")
    method = method.replace("digests: &'a [D]", "digests_len: usize")
    method = method.replace("ProofDigestLayout<'a, D>", "ProofDigestLayout")
    # Aeneas gives the discriminant instance a global name shared by both isolated extractions.
    method = method.replace("ReconstructionError", "LayoutError")
    method = method.replace("digests.len()", "digests_len")
    for field in ["fold_prefix", "suffix_peaks", "fetch_nodes", "prefix_active_peaks", "after_peaks"]:
        method = method.replace(f"!self.{field}.is_empty()", f"self.{field} != 0")
        method = method.replace(f"self.{field}.len()", f"self.{field}")
    method = re.sub(r'&digests\[([^\]]+)\]', r'\1', method)
    method = re.sub(r'\((self\.\w+ != 0)\)\.then\(\|\| (\w+)\)', r'if \1 { Some(\2) } else { None }', method)
    # Project each push in Blueprint::new to the identity of its destination vector.
    # Tempo fixes the bagging policy to BackwardFold. Keep the two original interval tests.
    start = proof.index("            if leaf_end <= range.start {")
    classify = proof[start:proof.index("            leaf_cursor = leaf_end;", start)]
    for field in ["fold_prefix", "prefix_active_peaks", "suffix_peaks", "after_peaks", "range_peaks"]:
        classify, num = re.subn(
            rf"{field}\.push\((?:Subtree \{{[^}}]*\}}|peak_pos)\);",
            "Group::" + field.title().replace("_", ""), classify
        )
        if num != 1:
            raise ValueError(f"unrecognized push to {field}")
    classify = classify.replace("bagging == Bagging::ForwardFold", "false")
    classify = classify.replace("bagging == Bagging::BackwardFold", "true")
    return """#![allow(dead_code)]
struct Blueprint { fold_prefix: usize, suffix_peaks: usize, fetch_nodes: usize, prefix_active_peaks: usize, after_peaks: usize }
enum LayoutError { MissingDigests, ExtraDigests }
struct ProofDigestLayout {
    fold_prefix: Option<usize>,
    prefix_active_peaks: std::ops::Range<usize>,
    after_peaks: std::ops::Range<usize>,
    suffix_acc: Option<usize>,
    siblings: std::ops::RangeFrom<usize>,
}
impl Blueprint {
""" + method + """
}
enum Group { FoldPrefix, PrefixActivePeaks, SuffixPeaks, AfterPeaks, RangePeaks }
fn classify_peak(leaf_start: u64, leaf_end: u64, range: std::ops::Range<u64>,
    peak_index: usize, inactive_peaks: usize) -> Group {
""" + classify + "}\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hax", required=True, type=Path)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as folder:
        tmp = Path(folder)
        (tmp / "src").mkdir()
        (tmp / "Cargo.toml").write_text('[package]\nname="pinned-layout"\nversion="0.0.0"\nedition="2024"\n[workspace]\n')
        (tmp / "hax.toml").write_bytes((VERIFICATION / "symbolic/hax.toml").read_bytes())
        (tmp / "src/lib.rs").write_text(source())
        subprocess.run([args.hax.resolve(), "hax", "into", "lean"], cwd=tmp, check=True)
        extraction = tmp / "proofs/lean/PinnedLayout/Extraction"
        types = (extraction / "Types.lean").read_text().replace(
            "@[expose] public section", "@[expose] public section\nset_option linter.missingDocs false"
        )
        funs = (extraction / "Funs.lean").read_text()
        output = types + "\n" + funs[funs.index("namespace pinned_layout"):]
    if args.write:
        TARGET.write_text(output)
    elif output != TARGET.read_text():
        raise SystemExit("Pinned layout extraction differs; run --write and review the result.")


if __name__ == "__main__":
    main()
