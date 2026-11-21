"""Mutate the Rust that hax extracts, re-extract it, and require the named proof modules to fail.

Usage: python3 mutate.py TABLE.toml

Run after check.sh, which prepares DyLean, the dependency builds and the proofs. Each mutation
builds in its own mirror of the repository under .lake/mutations: the crate in symbolic/, the
production files that it includes through `#[path]`, and the Lean package in lean/, sharing this
checkout's dependency builds and DyLean.
"""
import os
import re
import shutil
import subprocess
import sys
import tomllib
from pathlib import Path

here = Path(__file__).resolve().parent


def git(*args):
    return subprocess.check_output(["git", *args], cwd=here, text=True).strip()


top = Path(git("rev-parse", "--show-toplevel"))
repo = Path(git("rev-parse", "--path-format=absolute", "--git-common-dir")).parent
cache = repo / ".verification-tools" / "qmdb"
hax = os.environ.get("HAX", str(cache / "qmdb-hax-tools" / "target" / "release" / "cargo-hax"))
env = dict(os.environ, XDG_CACHE_HOME=os.environ.get("XDG_CACHE_HOME", str(cache / "modern-cache")))
crate = here / "symbolic"
proofs = here / "lean"
packages = (crate / "proofs" / "lean" / ".lake" / "packages").resolve()


def run(cmd, cwd):
    return subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)


def included():
    """Repository paths of the production files that the crate includes through `#[path]`."""
    found = []
    for source in (crate / "src").rglob("*.rs"):
        for path in re.findall(r'#\[path = "([^"]+)"\]', source.read_text()):
            found.append((source.parent / path).resolve().relative_to(top))
    return found


def mirror(root):
    """Copy the crate, its included production files and the proofs into `root`."""
    mirrored = root / crate.relative_to(top)
    shutil.copytree(crate / "src", mirrored / "src")
    for part in ["Cargo.lock", "hax.toml"]:
        shutil.copy(crate / part, mirrored / part)
    manifest = (crate / "Cargo.toml").read_text()
    (mirrored / "Cargo.toml").write_text(manifest.split("[dev-dependencies]")[0])
    for path in included():
        (root / path).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(top / path, root / path)
    lean = root / proofs.relative_to(top)
    shutil.copytree(proofs, lean, ignore=shutil.ignore_patterns(".lake"))
    (lean / ".lake").mkdir()
    (lean / ".lake" / "packages").symlink_to(packages)
    (root / here.relative_to(top) / ".lake").mkdir(parents=True)
    (root / here.relative_to(top) / ".lake" / "dylean").symlink_to(here / ".lake" / "dylean")
    return mirrored, lean


def main():
    table = tomllib.loads(Path(sys.argv[1]).read_text())
    base = here / ".lake" / "mutations"
    shutil.rmtree(base, ignore_errors=True)
    for mutation in table["mutation"]:
        name, fails = mutation["name"], mutation["fails"]
        fails = [fails] if isinstance(fails, str) else fails
        root = base / re.sub(r"\W+", "-", name)
        mirrored, lean = mirror(root)
        source = root / mutation["file"]
        text = source.read_text()
        assert text.count(mutation["original"]) == 1, (name, mutation["original"])
        source.write_text(text.replace(mutation["original"], mutation["mutated"]))

        extract = run([hax, "hax", "into", "lean"], mirrored)
        assert extract.returncode == 0, extract.stdout + extract.stderr
        pkg = mirrored / "proofs" / "lean"
        (pkg / ".lake").mkdir(exist_ok=True)
        (pkg / ".lake" / "packages").symlink_to(packages)
        shutil.copy(crate / "proofs" / "lean" / "lake-manifest.json", pkg)
        build = run(["lake", "build", "CommonwareSymbolic.Extraction"], pkg)
        assert build.returncode == 0, build.stdout + build.stderr

        result = run(["lake", "build"], lean)
        if result.returncode == 0:
            sys.exit(f"Mutation survived: {name}")
        failed = set(re.findall(r"✖ \[\d+/\d+\] Building (\S+)", result.stdout))
        assert failed == set(fails), (name, failed, result.stdout[-4000:])
        for module in fails:
            file = module.replace(".", "/") + ".lean"
            assert re.search(rf"error: {re.escape(file)}:\d+:\d+", result.stdout), result.stdout
        print(f"Proofs reject: {name} ({', '.join(fails)})")


if __name__ == "__main__":
    main()
