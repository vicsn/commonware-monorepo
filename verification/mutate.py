"""Mutate the Rust that hax extracts, re-extract it, and require the named proof modules to fail.

Usage: python3 mutate.py [--jobs N|auto] TABLE.toml...

Run after check.sh, which prepares DyLean, the dependency builds and the proofs. Each mutation
builds in its own mirror of the repository under .lake/mutations: the crate in symbolic/, the
production files that it includes through `#[path]`, and the Lean package in lean/, sharing this
checkout's dependency builds and DyLean. A table names its `library`; a mutation builds only that
library and the modules it imports, and exactly the modules in its `fails` must fail. A mutation
that leaves the extraction unchanged survives without a Lean build.

The builds use Lake's artifact cache in .verification-tools/qmdb/lake-cache, so a repeated run
rebuilds little more than the modules that each mutation breaks. A mutation peaks at about 9 GB
with a cold cache and 2 GB with a warm one. `--jobs auto` budgets 10 GB per mutation and checks
as many at once as half of the memory available now holds, at most one per four cores.
"""
import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import tomllib
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

here = Path(__file__).resolve().parent


def git(*args):
    return subprocess.check_output(["git", *args], cwd=here, text=True).strip()


top = Path(git("rev-parse", "--show-toplevel"))
repo = Path(git("rev-parse", "--path-format=absolute", "--git-common-dir")).parent
cache = repo / ".verification-tools" / "qmdb"
hax = os.environ.get("HAX", str(cache / "qmdb-hax-tools" / "target" / "release" / "cargo-hax"))
# Lake's local artifact cache, in the tool cache, keeps every build output by the hash of its
# inputs.
# Mutations share the modules that a mutation leaves unchanged, and a later run reuses what an
# earlier run built for the same mutation. Lake caches only modules that build, so the modules
# that a mutation breaks are elaborated every time.
env = dict(
    os.environ,
    XDG_CACHE_HOME=os.environ.get("XDG_CACHE_HOME", str(cache / "modern-cache")),
    LAKE_ARTIFACT_CACHE="true",
    LAKE_CACHE_DIR=str(cache / "lake-cache"),
)
crate = here / "symbolic"
proofs = here / "lean"
packages = (crate / "proofs" / "lean" / ".lake" / "packages").resolve()


class Ran:
    """A finished command with its output, wall time in seconds and peak memory in bytes."""

    def __init__(self, returncode, stdout, stderr, seconds, peak):
        self.returncode, self.stdout, self.stderr = returncode, stdout, stderr
        self.seconds, self.peak = seconds, peak


def group_rss(pgid):
    """Resident memory, in bytes, of every process in the process group `pgid`."""
    out = subprocess.run(["ps", "-A", "-o", "pgid=,rss="], capture_output=True, text=True).stdout
    total = 0
    for line in out.splitlines():
        fields = line.split()
        if len(fields) == 2 and fields[0] == str(pgid):
            total += int(fields[1]) * 1024
    return total


def run(cmd, cwd):
    """Run `cmd` in its own process group, sampling the group's total resident memory."""
    start = time.monotonic()
    with tempfile.TemporaryFile("w+") as out, tempfile.TemporaryFile("w+") as err:
        proc = subprocess.Popen(
            cmd, cwd=cwd, env=env, stdout=out, stderr=err, text=True, start_new_session=True
        )
        peak = 0
        while proc.poll() is None:
            peak = max(peak, group_rss(proc.pid))
            time.sleep(0.5)
        out.seek(0)
        err.seek(0)
        return Ran(proc.returncode, out.read(), err.read(), time.monotonic() - start, peak)


def gb(n):
    return f"{n / 2**30:.1f} GB"


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


def tree(path):
    """The files under `path` and their contents."""
    return {p.relative_to(path): p.read_bytes() for p in sorted(path.rglob("*")) if p.is_file()}


def check(library, mutation, root):
    """Apply `mutation` in a mirror at `root` and build `library` on its extraction.

    Returns the line to print and the peak memory, or raises `Failure`.
    """
    name, fails = mutation["name"], mutation["fails"]
    fails = [fails] if isinstance(fails, str) else fails
    mirrored, lean = mirror(root)
    source = root / mutation["file"]
    text = source.read_text()
    if text.count(mutation["original"]) != 1:
        raise Failure(f"{name}: `original` does not occur exactly once in {mutation['file']}")
    source.write_text(text.replace(mutation["original"], mutation["mutated"]))

    extract = run([hax, "hax", "into", "lean"], mirrored)
    if extract.returncode != 0:
        raise Failure(f"{name}: extraction failed\n{extract.stdout}{extract.stderr}")
    pkg = mirrored / "proofs" / "lean"
    # A mutation that leaves the extraction unchanged survives whatever the proofs say.
    if tree(pkg / "CommonwareSymbolic") == tree(crate / "proofs" / "lean" / "CommonwareSymbolic"):
        raise Failure(f"Mutation survived, the extraction is unchanged: {name}")
    (pkg / ".lake").mkdir(exist_ok=True)
    (pkg / ".lake" / "packages").symlink_to(packages)
    shutil.copy(crate / "proofs" / "lean" / "lake-manifest.json", pkg)
    build = run(["lake", "build", "CommonwareSymbolic.Extraction"], pkg)
    if build.returncode != 0:
        raise Failure(f"{name}: the extraction does not build\n{build.stdout[-4000:]}")

    result = run(["lake", "build", library], lean)
    if result.returncode == 0:
        raise Failure(f"Mutation survived: {name}")
    failed = set(re.findall(r"✖ \[\d+/\d+\] Building (\S+)", result.stdout))
    if failed != set(fails):
        raise Failure(f"{name}: expected {sorted(fails)} to fail, got {sorted(failed)}\n"
                      f"{result.stdout[-4000:]}")
    for module in fails:
        file = module.replace(".", "/") + ".lean"
        if not re.search(rf"error: {re.escape(file)}:\d+:\d+", result.stdout):
            raise Failure(f"{name}: {module} fails without an error of its own\n"
                          f"{result.stdout[-4000:]}")
    peak = max(extract.peak, build.peak, result.peak)
    line = (f"Proofs reject: {name} ({', '.join(fails)}) [extract {extract.seconds:.0f}s, "
            f"extraction {build.seconds:.0f}s, lean {result.seconds:.0f}s, peak {gb(peak)}]")
    return line, peak


class Failure(Exception):
    """A mutation that the proofs do not reject as its table says."""


def available_memory():
    """Bytes of memory that macOS can hand out now: free, inactive and speculative pages."""
    out = subprocess.check_output(["vm_stat"], text=True)
    page = int(re.search(r"page size of (\d+) bytes", out).group(1))
    pages = 0
    for kind in ["free", "inactive", "speculative"]:
        pages += int(re.search(rf"Pages {kind}:\s+(\d+)", out).group(1))
    return pages * page


def jobs(value, count):
    """The number of mutations to check at once.

    `auto` budgets each mutation at the largest peak recorded, and at least `PEAK_FLOOR`, which a
    mutation reaches when the artifact cache is cold. It checks as many as half of the memory
    available now holds, and at most one for every four cores, since each build is itself
    parallel.
    """
    if value != "auto":
        return max(1, int(value))
    recorded = int(peak_record.read_text()) if peak_record.exists() else 0
    budget = max(recorded, PEAK_FLOOR)
    cores = int(subprocess.check_output(["sysctl", "-n", "hw.ncpu"], text=True))
    return max(1, min(count, available_memory() // 2 // budget, cores // 4))


peak_record = here / ".lake" / "logs" / "mutation-peak-rss"

# The largest peak of one mutation measured with a cold artifact cache, rounded up.
PEAK_FLOOR = 10 * 2**30


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("tables", nargs="+", type=Path)
    parser.add_argument("--jobs", default="1",
                        help="mutations to check at once, a number or `auto` (default 1)")
    args = parser.parse_args()

    work = []
    for path in args.tables:
        table = tomllib.loads(path.read_text())
        library = table["library"]
        for mutation in table["mutation"]:
            fails = mutation["fails"]
            for module in [fails] if isinstance(fails, str) else fails:
                if not module.startswith(library + "."):
                    sys.exit(f"{path}: {mutation['name']} names {module}, outside {library}")
            work.append((library, mutation))

    base = here / ".lake" / "mutations"
    shutil.rmtree(base, ignore_errors=True)
    count = jobs(args.jobs, len(work))
    print(f"Checking {len(work)} mutations, {count} at a time.", flush=True)
    worst, failures = 0, []
    with ThreadPoolExecutor(count) as pool:
        futures = [
            pool.submit(check, library, mutation,
                        base / re.sub(r"\W+", "-", f"{library} {mutation['name']}"))
            for library, mutation in work
        ]
        for future in futures:
            try:
                line, peak = future.result()
            except Failure as failure:
                failures.append(str(failure))
                print(failure, flush=True)
                continue
            worst = max(worst, peak)
            print(line, flush=True)
    # The largest peak seen bounds how many mutations `--jobs auto` checks at once. Each peak is
    # that mutation's own process group, and the record only grows.
    peak_record.parent.mkdir(parents=True, exist_ok=True)
    previous = int(peak_record.read_text()) if peak_record.exists() else 0
    peak_record.write_text(str(max(previous, worst)))
    if failures:
        sys.exit(f"{len(failures)} of {len(work)} mutations failed their check.")


if __name__ == "__main__":
    main()
