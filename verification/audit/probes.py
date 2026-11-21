#!/usr/bin/env python3
"""Run the probes of the first audit pass: mutations whose effect on the proofs is recorded.

Usage: python3 probes.py [TABLE.toml] [NAME-PREFIX ...]

Run after check.sh, which prepares DyLean, the dependency builds and the proofs. Like mutate.py,
each probe builds in its own mirror of the repository under verification/.lake/probes, so the
checkout is never edited. Unlike mutate.py, a probe may be expected to survive: `expect` is
"survives" or the list of proof modules that must stop building, and `message` is text that the
build output must then contain. A probe that edits Lean only is extracted again all the same, so
every probe runs the whole route. The build covers the Commonware, Leaf and Qmdb libraries.
"""

import re
import shutil
import sys
import tomllib
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.dont_write_bytecode = True
import mutate  # noqa: E402

TARGETS = ['Commonware', 'Leaf', 'Qmdb']
BASE = mutate.here / '.lake' / 'probes'


def edit(root, change, name):
    source = root / change['file']
    text = source.read_text()
    if 'append' in change:
        anchor = change['before']
        assert text.count(anchor) == 1, (name, anchor)
        text = text.replace(anchor, change['append'] + '\n' + anchor)
    else:
        assert text.count(change['original']) == 1, (name, change['original'])
        text = text.replace(change['original'], change['mutated'])
    source.write_text(text)


def run(probe):
    """The proof modules that stop building under `probe`, and the build output."""
    name = probe['name']
    root = BASE / re.sub(r'\W+', '-', name)
    mirrored, lean = mutate.mirror(root)
    for change in probe.get('edits', [probe]):
        edit(root, change, name)
    extract = mutate.run([mutate.hax, 'hax', 'into', 'lean'], mirrored)
    assert extract.returncode == 0, (name, extract.stdout + extract.stderr)
    pkg = mirrored / 'proofs' / 'lean'
    (pkg / '.lake').mkdir(exist_ok=True)
    (pkg / '.lake' / 'packages').symlink_to(mutate.packages)
    shutil.copy(mutate.crate / 'proofs' / 'lean' / 'lake-manifest.json', pkg)
    build = mutate.run(['lake', 'build', 'CommonwareSymbolic.Extraction'], pkg)
    assert build.returncode == 0, (name, build.stdout + build.stderr)
    result = mutate.run(['lake', 'build', *TARGETS], lean)
    failed = sorted(set(re.findall(r'✖ \[\d+/\d+\] Building (\S+)', result.stdout)))
    assert bool(failed) == (result.returncode != 0), (name, result.stdout[-2000:])
    return failed, result.stdout


def main():
    arguments = sys.argv[1:]
    table = HERE / 'probes.toml'
    if arguments and arguments[0].endswith('.toml'):
        table = Path(arguments.pop(0))
    probes = [probe for probe in tomllib.loads(table.read_text())['probe']
              if not arguments or probe['name'].startswith(tuple(arguments))]
    shutil.rmtree(BASE, ignore_errors=True)
    wrong = 0
    with ThreadPoolExecutor(max_workers=3) as pool:
        for probe, (failed, output) in zip(probes, pool.map(run, probes)):
            expected = probe['expect']
            found = 'survives' if not failed else failed
            verdict = 'survives' if not failed else 'breaks ' + ', '.join(failed)
            as_expected = found == expected and probe.get('message', '') in output
            wrong += not as_expected
            print(f'{"as recorded" if as_expected else "DIFFERS"}: {probe["name"]}: {verdict}',
                  flush=True)
    sys.exit(f'{wrong} of {len(probes)} probes differ from the record') if wrong else None


if __name__ == '__main__':
    main()
