#!/usr/bin/env python3
"""Write a copy of the report whose links open GitHub at one revision.

The report links to files of its own checkout and to a local diff handler. A published copy has
no checkout, so this script rewrites every source link to the file on GitHub at `--rev` and every
diff link to GitHub's comparison of the production baseline with that revision. The copy has no
document wrapper: the page that hosts it supplies one.
"""

import argparse
import hashlib
import posixpath
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REPORT = ROOT / 'verification/hax-dylean.html'
REPOSITORY = 'vicsn/commonware-monorepo'
DIFF = 'qmdb-diff://dylean/'


class Mismatch(Exception):
    """The report does not have the shape this script rewrites."""


def require(condition, message):
    if not condition:
        raise Mismatch(message)


def attribute(tag, name):
    match = re.search(rf' {name}="([^"]*)"', tag)
    return match[1] if match else None


def one(pattern, page, what):
    matches = re.findall(pattern, page, flags=re.S)
    require(len(matches) == 1, f'expected one {what}, found {len(matches)}')
    return matches[0]


def source(tag, github, revision):
    """A link to a file of the checkout, as that file on GitHub."""
    path = posixpath.normpath(posixpath.join('verification', attribute(tag, 'href')))
    file = ROOT / path
    require(not path.startswith('..') and file.is_file(), f'source link to a missing file: {path}')
    anchor = ''
    line = attribute(tag, 'data-line')
    if line:
        require(int(line) <= len(file.read_text().split('\n')), f'{path} has no line {line}')
        anchor = f'#L{line}'
    return f'<a class="src" href="{github}/blob/{revision}/{path}{anchor}" title="Open on GitHub">'


def difference(tag, github, baseline, revision):
    """A link to the local diff handler, as the file's place in GitHub's comparison."""
    path = attribute(tag, 'href').removeprefix(DIFF)
    require((ROOT / path).is_file(), f'diff link to a missing file: {path}')
    # GitHub anchors each file of a comparison by the SHA-256 of its path.
    anchor = hashlib.sha256(path.encode()).hexdigest()
    return (f'<a class="code-diff" href="{github}/compare/{baseline}...{revision}#diff-{anchor}" '
            'title="Compare with the baseline on GitHub">')


def replace_element(page, tag, name, body):
    """Replace the content of the one element `tag` with id `name`."""
    pattern = rf'(<{tag}\b[^>]*\bid="{name}"[^>]*>).*?(</{tag}>)'
    require(len(re.findall(pattern, page, flags=re.S)) == 1, f'expected one #{name}')
    return re.sub(pattern, lambda match: match[1] + body + match[2], page, flags=re.S)


def convert(page, repository, revision):
    github = f'https://github.com/{repository}'
    baseline = one(r'Production baseline: <code>([0-9a-f]{40})</code>', page, 'production baseline')
    short = revision[:9]

    page = re.sub(r'<a class="src"[^>]*>', lambda match: source(match[0], github, revision), page)
    page = re.sub(r'<a class="code-diff"[^>]*>',
                  lambda match: difference(match[0], github, baseline, revision), page)
    page = replace_element(
        page, 'span', 'checkout',
        f' of <a href="{github}/tree/{revision}">{repository}</a>; this page links to revision '
        f'<code>{short}</code>')
    page = replace_element(
        page, 'p', 'diff-help',
        f'Diff opens GitHub’s comparison of the original baseline <code>{baseline[:9]}</code> with '
        f'revision <code>{short}</code>, at that file. It includes test changes in the same file.')
    page = replace_element(
        page, 'p', 'link-help',
        f'Source links open the file on GitHub at revision <code>{short}</code>.')

    head = one(r'<head>(.*?)</head>', page, 'head')
    title = one(r'<title>.*?</title>', head, 'title')
    style = one(r'<style>.*?</style>', head, 'style block')
    body = one(r'<body>(.*)</body>', page, 'body')
    copy = '\n'.join([title, '<meta name="claude:viewport-fit-sides" content="cover">', style,
                      body.strip()]) + '\n'
    for link in re.findall(r'href="([^"]*)"', copy):
        require(link.startswith(('#', 'https://')), f'link left unconverted: {link}')
    return copy


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--out', type=Path, required=True, help='where to write the copy')
    parser.add_argument('--rev', help='revision the links open (default: HEAD)')
    parser.add_argument('--repository', default=REPOSITORY,
                        help=f'GitHub repository that holds the revision (default: {REPOSITORY})')
    parser.add_argument('--report', type=Path, default=REPORT)
    args = parser.parse_args()
    revision = args.rev or subprocess.check_output(
        ['git', '-C', str(ROOT), 'rev-parse', 'HEAD'], text=True).strip()
    try:
        require(re.fullmatch(r'[0-9a-f]{40}', revision), '--rev must be a full commit hash')
        copy = convert(args.report.read_text(), args.repository, revision)
    except Mismatch as error:
        sys.exit(f'report-artifact: {error}')
    args.out.write_text(copy)
    print(f'Wrote {args.out} with links to {args.repository} at {revision[:9]}.')


if __name__ == '__main__':
    main()
