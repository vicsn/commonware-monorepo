"""Mutate the Rust specification, re-extract it, and require the Lean proofs to reject it.

Run after check-bridge.sh, which prepares the pinned traversal, DyLean build and dependencies.
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
cache = repo / ".verification-tools" / "qmdb"
hax = os.environ.get("HAX", str(cache / "qmdb-hax-tools" / "target" / "release" / "cargo-hax"))
toolchain = "leanprover/lean4:v4.35.0"
env = dict(os.environ, XDG_CACHE_HOME=os.environ.get("XDG_CACHE_HOME", str(cache / "modern-cache")))
modules = ["Model", "Binding", "DyTerms", "Reference", "Correspondence", "Protocol"]

# (name, file, original, mutation, module whose proof must fail)
MUTATIONS = [
    ("leaf drops the item", "spec.rs",
     "T::hash(T::concat(T::literal(&be64(position)), T::item(item)))",
     "T::hash(T::literal(&be64(position)))", "Correspondence"),
    ("root drops the family domain", "spec.rs",
     "pub const MMR_DOMAIN: u8 = 0;", "pub const MMR_DOMAIN: u8 = 1;", "Correspondence"),
    ("replay misroutes the midpoint", "spec.rs",
     "if location < start + half {", "if location <= start + half {", "Correspondence"),
    ("traversal ignores unused siblings", "adapter.rs",
     "Ok(peak) => opening.next == siblings.len() && spec::wrap::<T>(height, peak) == *root,",
     "Ok(peak) => spec::wrap::<T>(height, peak) == *root,", "Correspondence"),
    ("client skips verification", "client.rs",
     "if adapter::verify::<T>(height, location, &root, &item, siblings) {",
     "if true {", "Correspondence"),
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
        crate = root / "rust"
        shutil.copytree(here / "rust" / "src", crate / "src")
        for part in ["Cargo.lock", "hax.toml"]:
            shutil.copy(here / "rust" / part, crate / part)
        manifest = (here / "rust" / "Cargo.toml").read_text()
        (crate / "Cargo.toml").write_text(manifest.split("[dev-dependencies]")[0])
        traversal = Path("storage/src/merkle/proof/traversal.rs")
        (root / ".lake" / "rust" / traversal).parent.mkdir(parents=True)
        shutil.copy(here / ".lake" / "rust" / traversal, root / ".lake" / "rust" / traversal)
        source = crate / "src" / file
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
