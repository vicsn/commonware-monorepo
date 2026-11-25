#!/usr/bin/env python3
"""Build the audit guide of the Merkle verification from the live sources.

`guide.html` holds the prose of the guide and `pairs.toml` says which code items face each other in
its side-by-side panels. Items are addressed by name, never by line number, so the panels follow
the code. This script resolves every item, renders the panels into the placeholders of the guide
and writes `verification/hax-dylean-audit.html`. A missing or ambiguous item, a quoted sentence
that its document no longer contains, or a stated fact that the sources no longer contain stops
the build. With `--check` it writes nothing and fails when the committed page is stale,
naming the panels that changed.

The declaration graph of the guide is drawn from `dag.json`, which is what Lean prints for
`Dag.lean`. With `--dag` this script runs Lean and stores that output; with `--dag --check` it
fails when the stored output is stale. Both need the Lean build of `verification/lean`.
"""

import argparse
import hashlib
import html
import json
import os
import re
import subprocess
import sys
import tomllib
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import dag as graph  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
VERIFICATION = ROOT / 'verification'
HERE = VERIFICATION / 'audit'
GUIDE = HERE / 'guide.html'
PAIRS = HERE / 'pairs.toml'
PAGE = VERIFICATION / 'hax-dylean-audit.html'
CRATE = VERIFICATION / 'symbolic'
EXTRACTION = CRATE / 'proofs/lean/CommonwareSymbolic'
GENERATED = [EXTRACTION / 'Extraction/Funs.lean', EXTRACTION / 'Extraction/Types.lean']
EXTERNAL = EXTRACTION / 'Assumptions/FunsExternal.lean'
DAG = HERE / 'dag.json'
DAG_LEAN = HERE / 'Dag.lean'
LEAN = VERIFICATION / 'lean'

KINDS = {
    'rust-rust': 'Rust ↔ Rust',
    'rust-generated': 'Rust ↔ generated Lean',
    'rust-trusted': 'Rust ↔ trusted Lean',
    'spec-generated': 'Lean definition ↔ generated Lean',
    'rust-model': 'Rust ↔ Lean model',
    'lean-lean': 'Lean ↔ Lean',
    'reading': 'Code ↔ how to read it',
}
STRENGTHS = {
    'proved': 'proved',
    'tested': 'tested',
    'trusted': 'trusted',
    'assumed': 'assumed',
    'none': 'no link',
    'shared': 'same code',
}
LEAN_KEYWORDS = 'def|theorem|lemma|structure|class|inductive|instance|abbrev|axiom|opaque'
LEAN_TRAILERS = ('where', 'termination_by', 'decreasing_by', 'partial_fixpoint', 'deriving')


class Mismatch(Exception):
    """The sources do not have the shape that the guide describes."""


def require(condition, message):
    if not condition:
        raise Mismatch(message)


def lines_of(path):
    return path.read_text().split('\n')


# Masking: replace comments and literals by spaces, keeping every line break and column.


def blank(text):
    return re.sub(r'[^\n]', ' ', text)


def mask_rust(text):
    pattern = re.compile(
        r'//[^\n]*'                     # line comment
        r'|/\*.*?\*/'                   # block comment
        r'|r(#*)".*?"\1'                # raw string
        r'|"(?:\\.|[^"\\])*"'           # string
        r"|'(?:\\.|[^'\\\n])'",         # char literal, not a lifetime
        re.S)
    return pattern.sub(lambda match: blank(match[0]), text)


def mask_lean(text):
    out, depth, index = [], 0, 0
    while index < len(text):
        pair = text[index:index + 2]
        if pair == '/-':
            depth += 1
            out.append('  ')
            index += 2
        elif pair == '-/' and depth:
            depth -= 1
            out.append('  ')
            index += 2
        elif depth:
            out.append('\n' if text[index] == '\n' else ' ')
            index += 1
        elif pair == '--':
            end = text.find('\n', index)
            end = len(text) if end < 0 else end
            out.append(' ' * (end - index))
            index = end
        elif text[index] == '"':
            end = index + 1
            while end < len(text) and text[end] != '"':
                end += 2 if text[end] == '\\' else 1
            out.append(blank(text[index:end + 1]))
            index = end + 1
        else:
            out.append(text[index])
            index += 1
    return ''.join(out)


# Rust items.

RUST_PREFIX = r'^\s*(?:pub(?:\([^)]*\))?\s+)?(?:(?:const|unsafe|async|default)\s+)*'


def rust_block_end(masked, start):
    """The last line of the item whose header starts on line `start` (0-based)."""
    depth = {'(': 0, '[': 0, '{': 0}
    closing = {')': '(', ']': '[', '}': '{'}
    opened = False
    for number in range(start, len(masked)):
        for char in masked[number]:
            if char in depth:
                depth[char] += 1
                opened = opened or char == '{'
            elif char in closing:
                depth[closing[char]] -= 1
                if char == '}' and opened and depth['{'] == 0:
                    return number
            elif char == ';' and not any(depth.values()):
                return number
    raise Mismatch(f'unterminated Rust item at line {start + 1}')


def rust_headers(masked, kind, name, scope):
    """Lines in `scope` that open the item `kind name` at item position."""
    first, last = scope
    if kind == 'impl':
        wanted = re.sub(r'\s+', ' ', name)
        found = []
        for number in range(first, last + 1):
            if re.match(r'^\s*(?:unsafe\s+)?impl\b', masked[number]):
                header = []
                for line in masked[number:last + 1]:
                    header.append(line)
                    if '{' in line:
                        break
                if wanted in re.sub(r'\s+', ' ', ' '.join(header)):
                    found.append(number)
        return found
    pattern = re.compile(RUST_PREFIX + rf'{kind}\s+{re.escape(name)}\b')
    if kind == 'const':
        pattern = re.compile(r'^\s*(?:pub(?:\([^)]*\))?\s+)?const\s+' + re.escape(name) + r'\b')
    return [number for number in range(first, last + 1) if pattern.match(masked[number])]


def rust_item(path, spec, within=None):
    lines = lines_of(path)
    masked = mask_rust('\n'.join(lines)).split('\n')
    kind, _, name = spec.partition(' ')
    require(kind in {'fn', 'const', 'trait', 'struct', 'enum', 'impl', 'type'} and name,
            f'{path.name}: cannot read the Rust item "{spec}"')
    scopes = [(0, len(lines) - 1)]
    if within:
        outer_kind, _, outer_name = within.partition(' ')
        require(outer_kind in {'impl', 'trait'}, f'"within" must name an impl or a trait: {within}')
        outers = rust_headers(masked, outer_kind, outer_name, scopes[0])
        require(outers, f'{path.name}: no block "{within}"')
        scopes = [(outer, rust_block_end(masked, outer)) for outer in outers]
    found = [number for scope in scopes for number in rust_headers(masked, kind, name, scope)
             if not (within and number == scope[0])]
    place = f'{path.name}: "{spec}"' + (f' within "{within}"' if within else '')
    require(len(found) == 1, f'{place} matches {len(found)} items, expected one')
    start, end = found[0], rust_block_end(masked, found[0])
    while start > 0 and re.match(r'\s*(///|//!|//|#\[)', lines[start - 1]):
        start -= 1
    return start, end


# Lean items.


def lean_item(path, name, statement=False, doc=True):
    lines = lines_of(path)
    masked = mask_lean('\n'.join(lines)).split('\n')
    header = re.compile(
        r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|public|noncomputable|unsafe|partial)\s+)*'
        rf'(?:{LEAN_KEYWORDS})\s+{re.escape(name)}(?![\w.\'!?])')
    found = [number for number, line in enumerate(masked) if header.match(line)]
    require(len(found) == 1, f'{path.name}: Lean item "{name}" matches {len(found)}, expected one')
    start = found[0]
    end = start
    for number in range(start + 1, len(masked)):
        line = masked[number]
        if line[:1].strip() and not line.startswith(LEAN_TRAILERS):
            break
        if line.strip():
            end = number
    if statement:
        end = lean_statement_end(masked, start, end, f'{path.name}: {name}')
    first = start
    while first > 0 and re.match(r'(omit\b.*\bin|@\[[^\]]*\])\s*$', lines[first - 1]):
        first -= 1
    if doc and first > 0 and lines[first - 1].rstrip().endswith('-/'):
        top = first - 1
        while top > 0 and not lines[top].startswith('/-'):
            top -= 1
        if lines[top].startswith('/--'):
            first = top
    return first, end


def lean_statement_end(masked, start, end, what):
    """The line that holds the `:=` which ends the statement, at bracket depth zero."""
    depth = 0
    for number in range(start, end + 1):
        line = masked[number]
        for column, char in enumerate(line):
            if char in '([{⟨':
                depth += 1
            elif char in ')]}⟩':
                depth -= 1
            elif char == ':' and line[column:column + 2] == ':=' and depth == 0:
                return number
    raise Mismatch(f'{what}: no `:=` ends the statement')


AUDIT_WIDTH = 80
# The groups of cited statements, in the order of the guide. The statements of the first group
# and the declarations they depend on follow the audit layout; the others are shown as written.
GROUPS = {
    'inclusion': 'Single-item inclusion',
    'reads': 'Ordered reads in the model',
    'rust': 'The model against extracted Rust',
}
RELATIONS = '=≤<>≥≠∈∧∨¬↔∀∃'


def signature_groups(masked, start, end):
    """The bracketed binders of the signature on lines `start` to `end`, each as (first line, last
    line, text), and the line of the colon that ends them."""
    groups, depth, opened, colon = [], 0, None, None
    for number in range(start, end + 1):
        line = masked[number]
        for column, char in enumerate(line):
            if char in '([{⟨':
                if depth == 0:
                    opened = (number, column)
                depth += 1
            elif char in ')]}⟩':
                depth -= 1
                if depth == 0:
                    text = '\n'.join(masked[opened[0]:number + 1])
                    groups.append((opened[0], number, masked[opened[0]][opened[1]:] if
                                   opened[0] == number else text))
            elif char == ':' and depth == 0 and line[column:column + 2] != ':=':
                return groups, number
    return groups, colon


def check_layout(path, name, first, last):
    """The layout of a declaration that auditors read: at most `AUDIT_WIDTH` columns, and when its
    signature takes several lines, the name alone on the first, every hypothesis and assumed
    instance alone on its lines, and the conclusion on lines of its own."""
    lines = lines_of(path)
    masked = mask_lean('\n'.join(lines)).split('\n')
    what = f'{path.name}: {name}'
    header = next(number for number in range(first, last + 1)
                  if re.match(rf'(?:@\[[^\]]*\]\s*)?(?:{LEAN_KEYWORDS})\b', masked[number]))
    try:
        stop = lean_statement_end(masked, header, last, what)
    except Mismatch:
        stop = None
    # A proof is not read, so the limit stops where the statement of a theorem does.
    read = stop if stop is not None and masked[header].startswith('theorem') else last
    for number in range(first, read + 1):
        require(len(lines[number]) <= AUDIT_WIDTH,
                f'{what}: line {number + 1} is over {AUDIT_WIDTH} columns')
    if stop is None:
        return
    if stop == header or re.search(r'\bwhere\s*$', masked[header]):
        return
    require(re.fullmatch(rf'(?:{LEAN_KEYWORDS})\s+\S+', masked[header].strip()),
            f'{what}: a signature of several lines starts with the name alone')
    groups, colon = signature_groups(masked, header + 1, stop)
    require(colon is not None, f'{what}: no colon ends the binders')
    require(masked[colon].rstrip().endswith(':'),
            f'{what}: the conclusion starts on a line of its own')
    for begin, finish, text in groups:
        hypothesis = text.startswith('[') or any(mark in text.split(':', 1)[-1]
                                                 for mark in RELATIONS)
        if not hypothesis:
            continue
        shared = [other for other in groups if other[:2] != (begin, finish)
                  and other[0] <= finish and other[1] >= begin]
        require(not shared, f'{what}: the hypothesis on line {begin + 1} shares its line')


def lean_context(path, start):
    """The `variable` lines in scope before line `start`, which a declaration silently uses."""
    lines = lines_of(path)
    masked = mask_lean('\n'.join(lines)).split('\n')
    seen = []
    for number in range(start):
        if masked[number].startswith('variable '):
            text = lines[number].strip()
            if text not in seen:
                seen.append(text)
    return seen


# Generated Lean and the Rust it was extracted from.


def generated_item(name):
    hits = []
    for path in GENERATED:
        try:
            hits.append((path, lean_item(path, name)))
        except Mismatch:
            continue
    require(len(hits) == 1, f'generated Lean item "{name}" found in {len(hits)} files')
    return hits[0]


def source_of(name):
    """The Rust file and lines that hax recorded for the generated item `name`."""
    path, (start, end) = generated_item(name)
    comment = '\n'.join(lines_of(path)[start:end + 1])
    match = re.search(r"Source: '([^']+)', lines (\d+):\d+-(\d+):\d+", comment)
    require(match, f'{name}: the generated item records no Rust source')
    rust = Path(os.path.normpath(CRATE / match[1]))
    require(rust.is_file(), f'{name}: recorded source {match[1]} is missing')
    lines = lines_of(rust)
    first, last = int(match[2]) - 1, int(match[3]) - 1
    while first > 0 and re.match(r'\s*(///|//|#\[)', lines[first - 1]):
        first -= 1
    return rust, (first, last)


# Snippets.


def excerpt(lines, span, item, what):
    """Narrow `span` to the lines from the anchor `from` through the anchor `through`."""
    start, end = span
    if 'from' in item:
        hits = [n for n in range(start, end + 1) if item['from'] in lines[n]]
        require(hits, f'{what}: no line contains {item["from"]!r}')
        start = hits[0]
    if 'through' in item:
        hits = [n for n in range(start, end + 1) if item['through'] in lines[n]]
        require(hits, f'{what}: no line after the start contains {item["through"]!r}')
        end = hits[0]
    return start, end


def resolve(item):
    """A snippet: its file, 0-based inclusive line span, language, label and context lines."""
    context = []
    if 'source_of' in item:
        path, span = source_of(item['source_of'])
        language, label = 'Rust', item.get('label', item['source_of'].replace('.', '::'))
    elif 'generated' in item:
        path, span = generated_item(item['generated'])
        language, label = 'Generated Lean', item.get('label', item['generated'])
    else:
        path = ROOT / item['file']
        require(path.is_file(), f'{item["file"]} is missing')
        if 'rust' in item:
            span = rust_item(path, item['rust'], item.get('within'))
            language, label = 'Rust', item.get('label', item['rust'])
        elif 'lean' in item:
            span = lean_item(path, item['lean'], item.get('statement', False),
                             item.get('doc', True))
            language, label = 'Lean', item.get('label', item['lean'])
            if graph.generated('.'.join(path.relative_to(LEAN).with_suffix('').parts)):
                language = 'Generated Lean'
            if item.get('context', True):
                context = lean_context(path, span[0])
        else:
            span = (0, len(lines_of(path)) - 1)
            require('from' in item, f'{item["file"]}: an item needs a name or a `from` anchor')
            language = {'.rs': 'Rust', '.lean': 'Lean', '.patch': 'Patch', '.sh': 'Shell',
                        '.toml': 'TOML', '.py': 'Python'}.get(path.suffix, 'Text')
            label = item.get('label', path.name)
    lines = lines_of(path)
    start, end = excerpt(lines, span, item, f'{path.name}: {item}')
    while end > start and not lines[end].strip():
        end -= 1
    return path, (start, end), language, label, context


def inline(text):
    """Escape prose from `pairs.toml`, with `code` in backticks."""
    return re.sub(r'`([^`]+)`', r'<code>\1</code>', html.escape(text, quote=False))


def source_link(path, span, text=None):
    href = os.path.relpath(path, VERIFICATION)
    shown = text or f'{"/".join(path.parts[-2:])}:{span[0] + 1}–{span[1] + 1}'
    return (f'<a class="src" href="{html.escape(href)}" data-line="{span[0] + 1}" '
            f'data-end="{span[1] + 1}" title="Open in VS Code">{html.escape(shown)}</a>')


def file_link(path, text):
    href = os.path.relpath(path, VERIFICATION)
    return (f'<a class="src" href="{html.escape(href)}" title="Open in VS Code">'
            f'{html.escape(text)}</a>')


def snippet(item):
    if 'prose' in item:
        points = ''.join(f'<li>{inline(point)}</li>' for point in item['prose'])
        return f'<ul class="reading">{points}</ul>'
    path, span, language, label, context = resolve(item)
    lines = lines_of(path)
    body = []
    for number in range(span[0], span[1] + 1):
        body.append(f'<span class="l"><span class="ln">{number + 1}</span>'
                    f'{html.escape(lines[number], quote=False)}</span>')
    scope = ''
    if context:
        scope = ('<div class="snip-scope">in scope: '
                 + ' · '.join(f'<code>{html.escape(line, quote=False)}</code>' for line in context)
                 + '</div>')
    part = ' (statement only)' if item.get('statement') else ''
    part = ' (excerpt)' if 'from' in item or 'through' in item else part
    return (f'<div class="snip"><div class="snip-head"><span class="lang">{language}</span> '
            f'<code>{html.escape(label, quote=False)}</code>{part} {source_link(path, span)}</div>'
            f'{scope}<pre><code>' + ''.join(body) + '</code></pre></div>')


def side(panel, name):
    heading = panel.get(f'{name}_label')
    head = f'<div class="side-label">{inline(heading)}</div>' if heading else ''
    return f'<div class="side">{head}' + ''.join(snippet(item) for item in panel[name]) + '</div>'


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()[:12]


def render_panel(panel):
    for key in ('id', 'title', 'kind', 'link', 'left', 'right'):
        require(key in panel, f'panel {panel.get("id", "?")}: missing "{key}"')
    require(panel['kind'] in KINDS, f'panel {panel["id"]}: unknown kind {panel["kind"]}')
    reading = panel['kind'] == 'reading'
    require(reading or panel.get('strength') in STRENGTHS,
            f'panel {panel["id"]}: unknown strength')
    chip = ''
    if 'strength' in panel:
        require(panel['strength'] in STRENGTHS, f'panel {panel["id"]}: unknown strength')
        chip = f'<span class="chip {panel["strength"]}">{STRENGTHS[panel["strength"]]}</span>'
    lead = 'How to read it.' if reading else 'What links them.'
    notes = ''
    if panel.get('notes'):
        notes = ('<ul class="pair-notes">'
                 + ''.join(f'<li>{inline(note)}</li>' for note in panel['notes']) + '</ul>')
    inner = (f'<figcaption class="pair-head"><span class="pair-title">{inline(panel["title"])}</span>'
             f'<span class="pair-kind">{KINDS[panel["kind"]]}</span>'
             f'{chip}</figcaption>'
             f'<div class="pair-grid">{side(panel, "left")}{side(panel, "right")}</div>'
             f'<p class="pair-link"><b>{lead}</b> {inline(panel["link"])}</p>{notes}')
    return (f'<figure class="pair" id="pair-{panel["id"]}" data-digest="{digest(inner)}">'
            f'{inner}</figure>')


# The claim tables: sentences of the READMEs beside the statements that back them.


def document_text(path):
    """The prose of a document on one line: a page without its tags, or a Markdown or Lean file
    without link targets and backticks."""
    text = path.read_text()
    if path.suffix == '.html':
        text = html.unescape(re.sub(r'<[^>]+>', '', text))
    else:
        text = re.sub(r'\[([^\]]+)\]\([^)]*\)', r'\1', text).replace('`', '')
    return re.sub(r'\s+', ' ', text)


def group_of(claim):
    group = claim.get('group', 'inclusion')
    require(group in GROUPS, f'unknown group of claims: {group}')
    return group


def render_claims(claims, group):
    """The claims of one group: each sentence, checked to occur in the document that makes it,
    beside the statements that back it."""
    rows = []
    for claim in claims:
        if group_of(claim) != group:
            continue
        require('source' in claim, f'a claim names no source: {claim["sentence"][:50]}…')
        source = ROOT / claim['source']
        require(source.is_file(), f'{claim["source"]} is missing')
        sentence = re.sub(r'\s+', ' ', claim['sentence'])
        require(sentence.replace('`', '') in document_text(source),
                f'{source.name} no longer says: {sentence[:70]}…')
        statements = ''.join(
            snippet({'file': backing['file'], 'lean': backing['lean'], 'statement': True,
                     'context': False, 'doc': False})
            for backing in claim['backed_by'])
        where = f'<div class="muted">{file_link(source, "/".join(source.parts[-2:]))}</div>'
        rows.append(f'<tr><td class="claim">“{inline(sentence)}”{where}</td><td>{statements}</td>'
                    f'<td>{inline(claim["reading"])}</td><td class="verdict"></td></tr>')
    require(rows, f'no claim in group {group}')
    inner = ''.join(rows)
    name = 'claims' if group == 'inclusion' else f'claims-{group}'
    return (f'<div class="table claims" id="{name}" data-digest="' + digest(inner) + '"><table>'
            '<thead><tr><th scope="col">The claim, and where it is made</th>'
            '<th scope="col">The Lean statement behind it</th>'
            '<th scope="col">Reading</th><th scope="col">Your verdict</th></tr></thead>'
            f'<tbody>{inner}</tbody></table></div>')


# The index of every extracted Merkle item.


def render_index(prefixes):
    rows = []
    for path in GENERATED:
        lines = lines_of(path)
        masked = mask_lean('\n'.join(lines)).split('\n')
        header = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:' + LEAN_KEYWORDS + r')\s+(\S+)')
        for number, line in enumerate(masked):
            match = header.match(line)
            if not match:
                continue
            name = match[1]
            try:
                rust, span = source_of(name)
            except Mismatch:
                continue
            shown = str(rust.relative_to(ROOT))
            if not any(shown.startswith(prefix) for prefix in prefixes):
                continue
            rows.append((shown, span[0], f'<tr><td><code>{html.escape(name)}</code></td>'
                         f'<td>{source_link(rust, span)}</td>'
                         f'<td>{source_link(path, (number, number), f"{path.name}:{number + 1}")}'
                         '</td></tr>'))
    require(rows, 'no extracted items found for the index')
    inner = ''.join(row for _, _, row in sorted(rows))
    return (f'<div class="table index" data-digest="{digest(inner)}"><table><thead><tr>'
            '<th scope="col">Generated definition</th><th scope="col">Rust source</th>'
            '<th scope="col">Generated Lean</th></tr></thead>'
            f'<tbody>{inner}</tbody></table></div>', len(rows))


# The declaration graph.


def chip(trust):
    return f'<span class="chip {trust}">{graph.TRUST[trust]}</span>'


def check_chains(page, nodes, members):
    """Each trust chain names the Lean files of its groups of statements: every file that holds
    one of the statements or a trusted declaration that one of them depends on. The box of a group
    of statements names every file that holds one of them."""
    figures = re.findall(r'<figure class="chain" data-groups="([\w ]+)">(.*?)</figure>', page,
                         flags=re.S)
    named = [group for groups, _ in figures for group in groups.split()]
    require(sorted(named) == sorted(GROUPS), f'the trust chains name the groups {named}')

    def files(text):
        return re.findall(r'<a class="src" href="(lean/[\w/]+\.lean)"', text)

    def where(keys):
        return {os.path.relpath(ROOT / nodes[key]['path'], VERIFICATION) for key in keys}

    for groups, figure in figures:
        cited = {key for group in groups.split() for key in members[group]}
        trusted = {key for key, node in nodes.items()
                   if node['trust'] == 'trusted' and cited & set(node['said_by'])}
        boxes = re.findall(r'<g data-files="(trusted|statements:\w+)">(.*?)</g>', figure,
                           flags=re.S)
        require(sum(len(files(body)) for _, body in boxes) == len(files(figure)),
                f'the trust chain of {groups} names a Lean file outside a box')
        shown, wanted = set(files(figure)), where(cited | trusted)
        require(shown == wanted, f'the trust chain of {groups} lacks {sorted(wanted - shown)} '
                f'and names {sorted(shown - wanted)}')
        statements = {kind.split(':')[1]: body for kind, body in boxes if kind != 'trusted'}
        require(sorted(statements) == sorted(groups.split()),
                f'the trust chain of {groups} has statement boxes for {sorted(statements)}')
        for group, body in statements.items():
            missing = where(members[group]) - set(files(body))
            require(not missing, f'the box of the {group} statements lacks {sorted(missing)}')


def render_dag(claims, page):
    """Every Lean declaration of the target with its trust type: two drawings and a table of all
    of them. Checks that the trust chains of `page` name the Lean files that the drawings make
    trusted."""
    nodes = graph.load(DAG.read_text(), lambda path, line: lines_of(ROOT / path)[line - 1])
    trusts = list(graph.TRUST)
    order = sorted(nodes, key=lambda key: (trusts.index(nodes[key]['trust']),
                                           nodes[key]['file'] or '', nodes[key]['line'] or 0))
    index = {key: number for number, key in enumerate(order)}
    cited = [key for key in order if nodes[key]['trust'] == 'statement']
    # Each cited statement backs the claims of one group, and each backing statement is cited.
    group = {}
    for claim in claims:
        for backing in claim['backed_by']:
            found = [key for key in cited if nodes[key]['path'] == backing['file']
                     and ('.' + nodes[key]['name']).endswith('.' + backing['lean'])]
            require(len(found) == 1, f'{backing["lean"]} of {backing["file"]} backs a claim and '
                    f'{len(found)} statements cited by Dag.lean match it')
            require(group.setdefault(found[0], group_of(claim)) == group_of(claim),
                    f'{backing["lean"]} backs claims of two groups')
    require(set(group) == set(cited), 'Dag.lean cites statements that back no claim: '
            f'{sorted(nodes[key]["name"] for key in set(cited) - set(group))}')
    members = {name: [key for key in cited if group[key] == name] for name in GROUPS}
    check_chains(page, nodes, members)
    strict = set(members['inclusion'])
    count = {trust: sum(node['trust'] == trust for node in nodes.values()) for trust in trusts}
    for key in order:
        node = nodes[key]
        audited = key in strict or strict & set(node['said_by'])
        if node['trust'] in ('statement', 'trusted') and node['kind'] != '#combine' and audited:
            path = ROOT / node['path']
            name = node['name'].rsplit('.', 1)[-1]
            first = node['line'] - 1
            masked = mask_lean(path.read_text()).split('\n')
            last = first
            started = False
            for number in range(first, len(masked)):
                line = masked[number]
                if started and line[:1].strip() and not line.startswith(LEAN_TRAILERS):
                    break
                if re.match(rf'(?:@\[[^\]]*\]\s*)?(?:{LEAN_KEYWORDS})\b', line):
                    started = True
                if line.strip() or not started:
                    last = number
            check_layout(path, name, first, last)

    def link(key):
        node = nodes[key]
        if key in graph.LIBRARIES:
            return f'{html.escape(key)} <span class="muted">({graph.LIBRARIES[key]})</span>'
        line = node['line'] - 1
        return source_link(ROOT / node['path'], (line, line), node['name'])

    drawings = [(graph.draw(nodes, index, True), f'every declaration ({len(nodes)})'),
                (graph.draw(nodes, index, False), 'definitions and cited statements')]
    options = ''.join(f'<option value="{number}">{html.escape(title)}</option>'
                      for number, (_, title) in enumerate(drawings))
    frames = ''.join(f'<div class="dag-frame"{" hidden" if number else ""}>{drawing}</div>'
                     for number, (drawing, _) in enumerate(drawings))
    legend = ''.join(f'<span>{chip(trust)} {count[trust]}</span>' for trust in trusts)
    data = [{'n': nodes[key]['name'], 't': graph.TRUST[nodes[key]['trust']],
             's': sorted(index[other] for other in nodes[key]['says']),
             'u': sorted(index[other] for other in nodes[key]['uses'])} for key in order]


    def short(key):
        return html.escape(nodes[key]['label']).replace('_', '_<wbr>').replace('.', '.<wbr>')

    def reach(key):
        node = nodes[key]
        if node['trust'] == 'statement':
            return 'It is one.'
        if not node['said_by']:
            return 'None.'
        if len(node['said_by']) == len(cited):
            return 'All.'
        parts = []
        for name, title in GROUPS.items():
            said = [other for other in members[name] if other in node['said_by']]
            if said and len(said) == len(members[name]):
                parts.append(f'{html.escape(title)}: all.')
            elif said:
                parts.append(f'{html.escape(title)}: '
                             + ', '.join(f'<code>{short(other)}</code>' for other in said) + '.')
        return ' '.join(parts)

    rows = ''.join(f'<tr data-i="{index[key]}"><td>{link(key)}</td>'
                   f'<td>{html.escape(nodes[key]["kind"])}</td><td>{chip(nodes[key]["trust"])}</td>'
                   f'<td>{reach(key)}</td></tr>' for key in order)
    inner = (
        f'<p>The target has {len(nodes)} declarations. {count["statement"]} are statements that '
        'this guide cites: '
        + ', '.join(f'{len(members[name])} for {html.escape(title[0].lower() + title[1:])}'
                    for name, title in GROUPS.items())
        + f'. What those statements say depends on {count["trusted"]} handwritten '
        f'declarations, on {count["generated"]} generated ones and on {count["assumed"]} '
        f'libraries. The other {count["checked"]} are lemmas and definitions that only proofs '
        'use: Lean checks them, and no cited statement depends on what they say.</p>'
        '<figure class="dag" id="dag-figure"><div class="dag-bar">'
        f'<label>Show <select id="dag-view">{options}</select></label>'
        '<label><input type="checkbox" id="dag-fit"> Fit to width</label>'
        f'<span class="dag-legend">{legend}</span></div>'
        f'<div class="dag-scroll">{frames}</div>'
        '<div class="dag-info" id="dag-info" aria-live="polite">Select a declaration to see what '
        'it depends on and what depends on it.</div>'
        '<figcaption>Read from left to right: a declaration depends on those to its left. A '
        'solid line means that a statement or the body of a definition mentions the other '
        'declaration, a dashed line that only a proof does. A line is left out when a longer '
        'path already implies it, and lines from the three libraries appear only for the '
        'selected declaration.</figcaption></figure>'
        f'<script type="application/json" id="dag-data">{json.dumps(data, separators=(",", ":"))}'
        '</script>'
        f'<details id="dag-all"><summary>All {len(nodes)} declarations</summary>'
        '<div class="table"><table><thead><tr><th scope="col">Declaration</th>'
        '<th scope="col">Kind</th><th scope="col">Trust type</th>'
        '<th scope="col">Cited statements that depend on what it says</th></tr></thead>'
        f'<tbody id="dag-rows">{rows}</tbody></table></div></details>')
    return f'<div id="dag" data-digest="{digest(inner)}">{inner}</div>'


def lean_dag():
    """What Lean prints for `Dag.lean` against the current build of the proofs."""
    result = subprocess.run(['lake', 'env', 'lean', str(DAG_LEAN)], cwd=LEAN, capture_output=True,
                            text=True)
    require(result.returncode == 0, 'Dag.lean failed; run verification/check.sh first:\n'
            + (result.stdout + result.stderr)[-2000:])
    return result.stdout


# Checks that no panel shows.


def check_facts(facts):
    for fact in facts:
        path = ROOT / fact['file']
        require(path.is_file(), f'{fact["file"]} is missing')
        text = re.sub(r'\s+', ' ', path.read_text())
        wanted = re.sub(r'\s+', ' ', fact['text'])
        require(wanted in text, f'{fact["file"]} no longer contains: {fact["text"]}')


def check_external():
    """The file of hand-filled external functions must declare nothing: hax never rewrites it, so
    the reproducibility check cannot notice an assumption added there."""
    masked = mask_lean(EXTERNAL.read_text())
    found = re.findall(rf'^(?:@\[[^\]]*\]\s*)?(?:{LEAN_KEYWORDS})\s+\S+', masked, flags=re.M)
    require(not found, f'{EXTERNAL.name} declares {found}')


def build():
    table = tomllib.loads(PAIRS.read_text())
    check_facts(table.get('fact', []))
    check_external()
    page = GUIDE.read_text()
    panels = {panel['id']: panel for panel in table['panel']}
    require(len(panels) == len(table['panel']), 'two panels share an id')
    used = re.findall(r'<!-- panel: ([\w-]+) -->', page)
    require(sorted(used) == sorted(panels), 'panels and placeholders differ: '
            f'{sorted(set(used) ^ set(panels))}')
    for name in used:
        page = page.replace(f'<!-- panel: {name} -->', render_panel(panels[name]))
    for group in GROUPS:
        mark = '<!-- claims -->' if group == 'inclusion' else f'<!-- claims: {group} -->'
        require(page.count(mark) == 1, f'the guide needs one placeholder {mark}')
        page = page.replace(mark, render_claims(table['claim'], group))
    require(page.count('<!-- index -->') == 1, 'the guide needs one index placeholder')
    index, count = render_index(table['index']['prefixes'])
    page = page.replace('<!-- index -->', index).replace('<!-- index-count -->', str(count))
    require(page.count('<!-- dag -->') == 1, 'the guide needs one graph placeholder')
    page = page.replace('<!-- dag -->', render_dag(table['claim'], page))
    require('<!-- ' not in page.replace('<!-- generated', ''), 'an unknown placeholder is left')
    note = ('<!-- generated by verification/audit/build.py from audit/guide.html and '
            'audit/pairs.toml; edit those, not this file -->\n')
    return page.replace('<main>', note + '<main>', 1)


def digests(page):
    return dict(re.findall(r'(?:id="([\w-]+)"|class="table index") data-digest="(\w+)"', page))


def refresh_dag(check):
    """Store what Lean prints for the declaration graph, or fail if the stored copy is stale."""
    printed = lean_dag()
    if not check:
        changed = not DAG.is_file() or DAG.read_text() != printed
        DAG.write_text(printed)
        print(f'{"Wrote" if changed else "Unchanged:"} {DAG.relative_to(ROOT)}.')
    elif not DAG.is_file() or DAG.read_text() != printed:
        sys.exit(f'audit guide: {DAG.name} is out of date; run {sys.argv[0]} --dag, then '
                 f'{sys.argv[0]}')
    else:
        print(f'{DAG.name} matches the Lean build.')


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--check', action='store_true',
                        help='exit 1 if the committed page differs instead of writing it')
    parser.add_argument('--dag', action='store_true',
                        help='refresh dag.json from Lean, or check it with --check, and stop')
    args = parser.parse_args()
    try:
        if args.dag:
            refresh_dag(args.check)
            if args.check:
                return
        page = build()
    except Mismatch as error:
        sys.exit(f'audit guide: {error}')
    if not args.check:
        changed = not PAGE.is_file() or PAGE.read_text() != page
        PAGE.write_text(page)
        print(f'{"Wrote" if changed else "Unchanged:"} {PAGE.relative_to(ROOT)}.')
        return
    if not PAGE.is_file():
        sys.exit(f'audit guide: {PAGE.name} is missing; run {sys.argv[0]}')
    committed = PAGE.read_text()
    if committed != page:
        old, new = digests(committed), digests(page)
        stale = sorted(str(name or 'index') for name in set(old) | set(new)
                       if old.get(name) != new.get(name))
        where = ', '.join(stale) if stale else 'the prose'
        sys.exit(f'audit guide: {PAGE.name} is out of date ({where}); run {sys.argv[0]}')
    print(f'{PAGE.name} matches the sources.')


if __name__ == '__main__':
    main()
