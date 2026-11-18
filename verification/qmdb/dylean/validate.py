"""Audit theorem dependencies and test the proof against type-correct changes."""
from pathlib import Path
import os
import re
import subprocess
import tempfile

root = Path.cwd()
proof = root / "Binding.lean"
result = subprocess.run(["lean", str(proof)], capture_output=True, text=True)
print(result.stdout + result.stderr, end="")
result.check_returncode()
for name in ("fixed_root_binding", "inclusion_sound", "honest_opening"):
    match = re.search(rf"'Qmdb\.{name}' depends on axioms: \[([^\]]*)\]", result.stdout)
    if not match or set(match[1].split(", ")) - {"propext", "Classical.choice", "Quot.sound"}:
        raise RuntimeError(f"Unverified dependencies for {name}")

source = (root / "Model.lean").read_text()
for old, new in [
    ("some (leaf p item, ws)", "some (leaf p ByteArray.empty, ws)"),
    ("if loc < start+2^h then", "if loc ≤ start+2^h then"),
]:
    assert source.count(old) == 1
    with tempfile.TemporaryDirectory() as tmp:
        cwd = Path(tmp).resolve()
        (cwd / "lean-toolchain").write_text((root / "lean-toolchain").read_text())
        env = dict(os.environ, LEAN_PATH=f"{cwd}:{os.environ['LEAN_PATH']}")
        (cwd / "Model.lean").write_text(source.replace(old, new))
        subprocess.run(["lean", "-o", "Model.olean", "Model.lean"], cwd=cwd, env=env, check=True)
        run = subprocess.run(["lean", str(proof)], cwd=cwd, env=env, capture_output=True, text=True)
        if run.returncode == 0 or not re.search(r"Binding\.lean:\d+:\d+: error:", run.stdout):
            raise RuntimeError(run.stdout + run.stderr)
        print(f"Proof rejects {new}")
