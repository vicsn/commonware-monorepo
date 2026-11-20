"""Mutate the extracted Rust, re-extract it, and require the Lean proofs to reject it.

Run after check-bridge.sh, which prepares the DyLean build and dependencies. Each mutation copies
the crate and the production files it includes into a tree that mirrors the repository.
"""
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

here = Path(__file__).resolve().parent
repo = Path(subprocess.check_output(
    ["git", "rev-parse", "--path-format=absolute", "--git-common-dir"], cwd=here, text=True
).strip()).parent
top = Path(subprocess.check_output(
    ["git", "rev-parse", "--show-toplevel"], cwd=here, text=True
).strip())
crate_path = here.relative_to(top) / "rust"
cache = repo / ".verification-tools" / "qmdb"
hax = os.environ.get("HAX", str(cache / "qmdb-hax-tools" / "target" / "release" / "cargo-hax"))
toolchain = "leanprover/lean4:v4.35.0"
env = dict(os.environ, XDG_CACHE_HOME=os.environ.get("XDG_CACHE_HOME", str(cache / "modern-cache")))
modules = ["Hashing", "Verifier", "DyTerms", "Symbolic", "Protocol"]

TERMS = "storage/src/merkle/hasher/terms.rs"
TRAVERSAL = "storage/src/merkle/proof/traversal.rs"
CLIENT = str(crate_path / "src" / "client.rs")

# (name, repository path, original, mutation, module whose proof must fail)
MUTATIONS = [
    ("leaf hash drops the element", TERMS,
     "terms.hash(&[Part::Bytes(&position.to_be_bytes()), Part::Bytes(element)])",
     "terms.hash(&[Part::Bytes(&position.to_be_bytes())])", "Verifier"),
    ("node hash drops the left child", TERMS,
     "Part::Digest(left),\n        Part::Digest(right),", "Part::Digest(right),", "Verifier"),
    ("root drops the peak", TERMS,
     "Part::Digest(folded),\n        ])\n    } else {", "])\n    } else {", "Verifier"),
    ("traversal treats a boundary subtree as inside", TRAVERSAL,
     "if start + width <= range_start || start >= range_end {",
     "if start + width < range_start || start >= range_end {", "Verifier"),
    ("traversal hashes the right child twice", TRAVERSAL,
     "Ok(backend.node(position, left, right))", "Ok(backend.node(position, right, right))",
     "Verifier"),
    ("verifier ignores unused siblings", CLIENT,
     "opening.cursor() == siblings.len()\n                && terms::root(",
     "terms::root(", "Verifier"),
    ("client skips verification", CLIENT,
     "if verify(terms, height, location, root, item, siblings) {", "if true {", "Symbolic"),
]


def run(cmd, cwd, **kw):
    return subprocess.run(cmd, cwd=cwd, env=kw.pop("env", env), capture_output=True, text=True, **kw)


def main():
    base = here / ".lake" / "mutations"
    shutil.rmtree(base, ignore_errors=True)
    deps = (here / "rust" / "proofs" / "lean" / ".lake" / "packages").resolve()
    dylean = here / ".lake" / "compat" / ".lake" / "build" / "lib" / "lean"
    for name, file, old, new, failing in MUTATIONS:
        root = base / re.sub(r"\W+", "-", name)
        crate = root / crate_path
        shutil.copytree(here / "rust" / "src", crate / "src")
        for part in ["Cargo.lock", "hax.toml"]:
            shutil.copy(here / "rust" / part, crate / part)
        manifest = (here / "rust" / "Cargo.toml").read_text()
        (crate / "Cargo.toml").write_text(manifest.split("[dev-dependencies]")[0])
        for included in [TERMS, TRAVERSAL]:
            (root / included).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(top / included, root / included)
        source = root / file
        text = source.read_text()
        assert text.count(old) == 1, (name, old)
        source.write_text(text.replace(old, new))

        extract = run([hax, "hax", "into", "lean"], crate)
        assert extract.returncode == 0, extract.stdout + extract.stderr
        pkg = crate / "proofs" / "lean"
        (pkg / ".lake").mkdir(exist_ok=True)
        (pkg / ".lake" / "packages").symlink_to(deps)
        shutil.copy(here / "rust" / "proofs" / "lean" / "lake-manifest.json", pkg)
        build = run(["lake", "build", "QmdbDylean.Extraction"], pkg)
        assert build.returncode == 0, build.stdout + build.stderr
        paths = run(["lake", "env", "printenv", "LEAN_PATH"], pkg).stdout.strip()
        out = root / "bridge"
        out.mkdir()
        lean_env = dict(env, LEAN_PATH=f"{out}:{dylean}:{paths}")
        for module in modules:
            result = run(["lean", f"+{toolchain}", "-o", str(out / f"{module}.olean"),
                          str(here / f"{module}.lean")], here, env=lean_env)
            if result.returncode != 0:
                assert module == failing, (name, module, result.stdout + result.stderr)
                assert re.search(rf"{module}\.lean:\d+:\d+: error", result.stdout), result.stdout
                print(f"Proofs reject: {name} ({module})")
                break
        else:
            sys.exit(f"Mutation survived: {name}")


if __name__ == "__main__":
    main()
