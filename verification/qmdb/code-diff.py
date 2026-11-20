#!/usr/bin/env python3
"""Install/open report diff links on macOS; no background service required."""

import argparse
import hashlib
import html
import os
from pathlib import Path, PurePosixPath
import plistlib
import re
import shlex
import shutil
import subprocess
import sys
from urllib.parse import quote, unquote, urlsplit

ROOT = Path(__file__).resolve().parents[2]
STATE = ROOT / '.verification-tools/qmdb/code-diff'
APP = STATE / 'QMDB Code Diff.app'
SCHEME = 'qmdb-diff'
BASE = 'b45ef2d78ea7535d8a51588912ba1e13e461b146'
EXPERIMENTS = {
    'dylean': (ROOT, BASE),
}
CODE = Path('/Applications/Visual Studio Code.app/Contents/Resources/app/bin/code')
REGISTER = '/System/Library/Frameworks/CoreServices.framework/Frameworks/LaunchServices.framework/Support/lsregister'


def git(repo, *args):
    return subprocess.check_output(['git', '-C', str(repo), *args])


def comparison_base(experiment, relative):
    """Compare against the production baseline."""
    return EXPERIMENTS[experiment][1], relative


def resolve(uri):
    url = urlsplit(uri)
    if url.scheme != SCHEME or url.netloc not in EXPERIMENTS or url.query or url.fragment:
        raise ValueError('Invalid QMDB diff URL')
    relative = unquote(url.path.removeprefix('/'))
    parts = PurePosixPath(relative)
    if not relative or parts.is_absolute() or '..' in parts.parts:
        raise ValueError('Invalid source path')
    repo, revision = EXPERIMENTS[url.netloc]
    current = (repo / relative).resolve()
    if not current.is_relative_to(repo.resolve()) or not current.is_file():
        raise ValueError('Source must be an existing file inside the experiment checkout')
    # Only files explicitly linked from the report can be opened by the handler.
    report = (ROOT / 'qmdb-inclusion-proofs.html').read_text()
    if f'href="{html.escape(uri, quote=True)}"' not in report:
        raise ValueError('Diff is not linked from the QMDB report')
    revision, original = comparison_base(url.netloc, relative)
    commit = git(repo, 'rev-parse', '--verify', revision + '^{commit}').decode().strip()
    exists = git(repo, 'ls-tree', '-z', commit, '--', original)
    previous = git(repo, 'show', f'{commit}:{original}') if exists else b''
    key = hashlib.sha256((url.netloc + ':' + relative).encode()).hexdigest()[:16]
    baseline = STATE / 'baselines' / commit[:12] / key / current.name
    baseline.parent.mkdir(parents=True, exist_ok=True)
    if baseline.exists():
        baseline.chmod(0o600)
    baseline.write_bytes(previous)
    baseline.chmod(0o444)
    return baseline, current


def update_report():
    report = ROOT / 'qmdb-inclusion-proofs.html'
    source = report.read_text()
    # Reinstallation refreshes links without adding duplicates.
    source = re.sub(r' <a class="code-diff"[^>]*>Diff</a>', '', source)
    ordered = sorted(EXPERIMENTS.items(), key=lambda item: len(str(item[1][0])), reverse=True)
    def add(match):
        current = ROOT / unquote(html.unescape(match[1]))
        if current.suffix not in {'.rs', '.lean', '.py', '.sh', '.toml'}:
            return match[0]
        for name, (repo, revision) in ordered:
            if not current.is_relative_to(repo):
                continue
            relative = current.relative_to(repo).as_posix()
            revision, original = comparison_base(name, relative)
            exists = git(repo, 'ls-tree', '-z', revision, '--', original)
            previous = git(repo, 'show', f'{revision}:{original}') if exists else b''
            if exists and previous == current.read_bytes():
                return match[0]
            uri = f'{SCHEME}://{name}/' + quote(relative, safe='/')
            return match[0] + f' <a class="code-diff" href="{uri}" title="Compare documented baseline with working file in VS Code">Diff</a>'
        return match[0]
    source = re.sub(r'<a class="src" href="([^"]+)"[^>]*>.*?</a>', add, source)
    note = '<p class="muted" id="diff-help">Diff compares each experiment’s working file against the common original baseline <code>b45ef2d78</code>, including test changes in the same file. New files have an empty left pane. Install the local VS Code handler with <code>python3 verification/qmdb/code-diff.py --install</code>.</p>'
    source = re.sub(r'\n?<p class="muted" id="diff-help">.*?</p>', '', source)
    source = source.replace('<section id="changes"><h2>Production code changes</h2>', '<section id="changes"><h2>Production code changes</h2>\n' + note)
    report.write_text(source)


def install():
    if sys.platform != 'darwin' or not CODE.is_file():
        raise RuntimeError('Requires macOS with Visual Studio Code in /Applications')
    STATE.mkdir(parents=True, exist_ok=True)
    update_report()
    # The application dispatches only to this fixed script. URLs are shell-quoted
    # by AppleScript and validated above; none of their contents are shell code.
    command = shlex.join([sys.executable, str(Path(__file__).resolve()), '--open']) + ' '
    literal = '"' + command.replace('\\', '\\\\').replace('"', '\\"') + '"'
    script = STATE / 'handler.applescript'
    script.write_text('on «event GURLGURL» inputURL\n  do shell script ' + literal + ' & quoted form of inputURL\nend «event GURLGURL»\n')
    if APP.exists():
        shutil.rmtree(APP)
    subprocess.run(['osacompile', '-o', str(APP), str(script)], check=True)
    plist = APP / 'Contents/Info.plist'
    with plist.open('rb') as f:
        info = plistlib.load(f)
    info.update(CFBundleIdentifier='org.commonware.qmdb-code-diff', LSUIElement=True,
                CFBundleURLTypes=[{'CFBundleURLName': 'QMDB source diff', 'CFBundleURLSchemes': [SCHEME]}])
    with plist.open('wb') as f:
        plistlib.dump(info, f)
    subprocess.run(['codesign', '--force', '--sign', '-', str(APP)], check=True)
    subprocess.run([REGISTER, '-f', str(APP)], check=True)
    print(f'Installed {APP}; report Diff links refreshed.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--install', action='store_true')
    group.add_argument('--open', metavar='URL')
    group.add_argument('--check', metavar='URL', help='prepare and print diff files without launching VS Code')
    args = parser.parse_args()
    if args.install:
        install()
    else:
        previous, current = resolve(args.open or args.check)
        if args.check:
            print(previous)
            print(current)
        else:
            subprocess.run([str(CODE), '--diff', str(previous), str(current)], check=True,
                           env={k: v for k, v in os.environ.items() if k != 'ELECTRON_RUN_AS_NODE'})


if __name__ == '__main__':
    main()
