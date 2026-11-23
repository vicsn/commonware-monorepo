#!/usr/bin/env python3
"""Extract the pinned MMB peak iterator and physical child lookup."""
import argparse
import re
from pathlib import Path
import subprocess
import tempfile

PIN = "789e9e5d47288b4138183e51f8d3cf1beedd8561"
ROOT = Path(__file__).resolve().parents[3]
TARGET = ROOT / "verification/lean/Qmdb/Mmb/PinnedPeaks.lean"


def source(name):
    return subprocess.check_output(["git", "-C", ROOT, "show",
                                   f"{PIN}:storage/src/merkle/{name}.rs"], text=True)


def item(text, signature):
    """Read a Rust function or struct, including its balanced body."""
    start = text.index(signature)
    body = text.index("{", start)
    depth = 1
    for i in range(body + 1, len(text)):
        depth += (text[i] == "{") - (text[i] == "}")
        if depth == 0:
            return text[start:i + 1]
    raise ValueError(signature)


def rust():
    it = source("mmb/iterator")
    family = source("mmb/mod")
    # Split initialization at the successful conversion so both entry points can be checked.
    constructor = item(it, "pub fn new(size: Position)")
    split = 'let n = Location::try_from(size).expect("size is not a valid MMB size");'
    assert split in constructor
    init = constructor.replace("new(size: Position)", "new(n: Location)").replace(split, "")
    init_at = ("fn new_at(size: Position) -> Self {" + split.replace("Location::try_from", "count")
               + "Self::new(n)}")
    maximum = re.search(r"const MAX_NODES: Position = [^;]+;", family).group()
    guard = item(source("position"), "pub const fn is_valid(self)").replace(
        "is_valid(self)", "is_valid(pos: Position)").replace("self.0", "pos").replace("F::MAX_NODES", "MAX_NODES")
    # Erase the two error payloads: the constructor only uses expect, and the theorem
    # ranges over sizes accepted by both the bound check and the inverse conversion.
    count = item(source("location"), "fn try_from(pos: Position<F>)").replace(
        "try_from(pos: Position<F>) -> Result<Self, Self::Error>", "count(pos: Position) -> Option<Location>")
    count = count.replace("pos.is_valid()", "is_valid(pos)").replace(
        "Err(super::Error::PositionOverflow(pos))", "None").replace(
        "F::position_to_location(pos).ok_or(super::Error::NonLeaf(pos))", "position_to_location(pos)")
    step = item(it, "fn next(&mut self)").replace("Option<Self::Item>", "Option<(Position, u32)>")
    helpers = [item(it, name) for name in ["const fn peak_birth_leaf(", "fn birthed_node_pos(",
                                          "const fn child_leaves(", "fn parent_birth_leaf(",
                                          "fn children(pos: Position,"]]
    loc = item(family, "fn location_to_position(")
    inverse = item(family, "fn position_to_location(")
    # Location and Position are transparent u64 newtypes. Their +, -, and += use u64 arithmetic.
    code = ("#![allow(dead_code, unused_parens)]\ntype Location=u64;\ntype Position=u64;\n#[derive(Default)]\n"
            + item(it, "pub struct PeakIterator") + "\nimpl PeakIterator {\n" + init + "\n"
            + step + "\n" + init_at + "\n}\n" + "\n".join([*helpers, loc, inverse, maximum, guard, count]) + "\n")
    return (code.replace(".as_u64()", "").replace("Location::new(", "(")
            .replace("Position::new(", "(").replace("Family::location_to_position", "location_to_position")
            .replace("Family::position_to_location", "position_to_location"))


def generated(hax, tmp):
    (tmp / "src").mkdir()
    (tmp / "src/lib.rs").write_text(rust())
    (tmp / "Cargo.toml").write_text(
        '[package]\nname="pinned-peaks"\nversion="0.0.0"\nedition="2024"\n[workspace]\n')
    (tmp / "hax.toml").write_bytes((ROOT / "verification/symbolic/hax.toml").read_bytes())
    subprocess.run([hax, "hax", "into", "lean"], check=True, cwd=tmp)
    path = tmp / "proofs/lean/PinnedPeaks/Extraction"
    types = (path / "Types.lean").read_text().replace(
        "@[expose] public section",
        "@[expose] public section\nset_option linter.missingDocs false",
    )
    # The panic-format dependencies are unused in the extracted data structure and methods.
    types = types.replace("public import PinnedPeaks.Extraction.TypesExternal\n", "")
    funs = (path / "Funs.lean").read_text()
    return types + "\n" + funs[funs.index("namespace pinned_peaks"):]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hax", required=True, type=Path)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as temp:
        result = generated(args.hax.resolve(), Path(temp))
    if args.write:
        TARGET.write_text(result)
    elif result != TARGET.read_text():
        raise SystemExit("Pinned peak iterator extraction differs.")
