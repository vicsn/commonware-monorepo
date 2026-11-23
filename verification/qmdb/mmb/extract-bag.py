#!/usr/bin/env python3
"""Extract the pinned nonempty backward-bagging path, specializing iterator plumbing."""

import argparse
from pathlib import Path
import re
import subprocess
import tempfile

PIN = "789e9e5d47288b4138183e51f8d3cf1beedd8561"
VERIFY = Path(__file__).resolve().parents[2]
ROOT = VERIFY.parent
TARGET = VERIFY / "lean/Qmdb/Mmb/PinnedBag.lean"


def pinned(path):
    return subprocess.check_output(["git", "-C", ROOT, "show", f"{PIN}:{path}"], text=True)


def source():
    code = pinned("storage/src/merkle/hasher.rs")
    start = code.index("    fn root_with_folded_peaks")
    method = code[start:code.index("\n    }\n}", start)]
    # Aeneas cannot lower early returns inside iterator-for loops. Keep each fold
    # call and lower the loops to tail recursion over their count / next element.
    body = " ".join(method.split())
    pre = re.search(
        r"for _ in 0\.\.(.*?) \{ let peak = peak_digests\.next\(\)\?; "
        r"acc = self\.fold\(([^,]*), ([^)]*)\); \}", body
    )
    back = re.search(
        r"active_peaks\.push\(acc\); active_peaks\.extend\(peak_digests\.copied\(\)\); "
        r"let mut acc = \*active_peaks\.last\(\)\.unwrap\(\); "
        r"for peak in active_peaks\.iter\(\)\.rev\(\)\.skip\(1\) \{ "
        r"acc = self\.fold\(([^,]*), ([^)]*)\); \}", body
    )
    if not pre or not back:
        raise ValueError("unrecognized peak loops")
    # The digest API takes symbolic fields in the same order as the pinned hash calls.
    required = [
        "let Some(first) = peak_digests.next() else",
        "(inactive_peaks_to_fold == 0 && committed_inactive_peaks == 0) "
        ".then(|| self.digest(&(*leaves).to_be_bytes()))",
        "if committed_inactive_peaks == 0 { Some(self.hash(&[&(*leaves).to_be_bytes(), &folded_peaks]))",
        "else { Some(self.hash(&[ &(*leaves).to_be_bytes(), "
        "&(committed_inactive_peaks as u64).to_be_bytes(), &folded_peaks, ]))",
    ]
    if any(fragment not in body for fragment in required):
        raise ValueError("unrecognized root inputs")
    def args(match):
        return ", ".join("&" + arg.lstrip("&") for arg in match)
    prefix_call = args(pre.groups()[1:])
    backward_call = args(back.groups())
    proof = pinned("storage/src/merkle/proof.rs")
    start = proof.index("    const fn inactive_peaks_after_prefix_fold")
    adjust = proof[start:proof.index("\n    }", start) + 6]
    adjust = adjust.replace("(&self,", "(fold_prefix: usize,").replace(
        "self.fold_prefix.is_empty()", "fold_prefix == 0"
    ).replace("self.fold_prefix.len()", "fold_prefix")
    return f"""#![allow(dead_code)]
trait Hash {{
    type D: Copy;
    fn fold(&self, a: &Self::D, b: &Self::D) -> Self::D;
    fn root(&self, leaves:u64, inactive:Option<u64>, acc:Self::D) -> Self::D;
    fn empty(&self, leaves:u64) -> Self::D;
}}
trait Cursor<D> {{
    fn next(&mut self) -> Option<D>;
    fn reversed_with_head(self, head:D) -> Self;
}}
fn prefix<H:Hash,C:Cursor<H::D>>(hasher:&H, mut peaks:C, count:usize, acc:H::D) -> Option<(H::D,C)> {{
    if count==0 {{return Some((acc,peaks))}};
    let peak=peaks.next()?;
    let acc=hasher.fold({prefix_call});
    prefix(hasher,peaks,count-1,acc)
}}
fn backward<H:Hash,C:Cursor<H::D>>(hasher:&H, mut back:C, acc:H::D) -> H::D {{
    let Some(peak)=back.next() else {{ return acc; }};
    let acc=hasher.fold({backward_call});
    backward(hasher,back,acc)
}}
fn root<H:Hash,C:Cursor<H::D>>(hasher:&H, leaves:u64, inactive_peaks_to_fold:usize,
    committed_inactive_peaks:usize, mut peak_digests:C) -> Option<H::D> {{
    let Some(first) = peak_digests.next() else {{
        return if inactive_peaks_to_fold == 0 && committed_inactive_peaks == 0 {{
            Some(hasher.empty(leaves))
        }} else {{None}};
    }};
    let (acc,peaks)=prefix(hasher,peak_digests,{pre[1]},first)?;
    let mut back=peaks.reversed_with_head(acc);
    let acc=back.next()?;
    let acc=backward(hasher,back,acc);
    if committed_inactive_peaks == 0 {{Some(hasher.root(leaves,None,acc))}}
    else {{Some(hasher.root(leaves,Some(committed_inactive_peaks as u64),acc))}}
}}
""" + adjust + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hax", required=True, type=Path)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as folder:
        tmp = Path(folder)
        (tmp / "src").mkdir()
        (tmp / "Cargo.toml").write_text(
            '[package]\nname="pinned-bag"\nversion="0.0.0"\nedition="2024"\n[workspace]\n'
        )
        (tmp / "hax.toml").write_bytes((VERIFY / "symbolic/hax.toml").read_bytes())
        (tmp / "src/lib.rs").write_text(source())
        subprocess.run([args.hax.resolve(), "hax", "into", "lean"], cwd=tmp, check=True)
        extraction = tmp / "proofs/lean/PinnedBag/Extraction"
        types = (extraction / "Types.lean").read_text().replace(
            "@[expose] public section", "@[expose] public section\nset_option linter.missingDocs false"
        )
        funs = (extraction / "Funs.lean").read_text()
        output = types + "\n" + funs[funs.index("namespace pinned_bag"):]
    if args.write:
        TARGET.write_text(output)
    elif output != TARGET.read_text():
        raise SystemExit("Pinned peak bagging extraction differs; rerun with --write and review.")


if __name__ == "__main__":
    main()
