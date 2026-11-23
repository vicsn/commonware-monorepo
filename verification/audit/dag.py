"""Lay out and draw the declaration graph of the audit guide.

`Dag.lean` prints every Lean declaration of the QMDB target with what it mentions. This module
gives each one a trust type, lays the graph out in layers from left to right and draws it as SVG,
once with every lemma and once with definitions and cited statements only. It reads nothing but
that JSON and the first source line of each declaration, so the guide can be rebuilt and checked
without Lean.
"""

import html
import json
import re
from collections import defaultdict

# The libraries that the target rests on, and the assumption of the guide that covers each.
LIBRARIES = {'hax core models': 'A1', 'Aeneas library': 'A1', 'DyLean': 'A3'}
# Trust types in drawing order, with the phrase the guide uses for each.
TRUST = {
    'statement': 'cited statement',
    'trusted': 'trusted',
    'generated': 'generated',
    'assumed': 'assumed library',
    'checked': 'checked',
}
PITCH, HEIGHT, GAP, CHAR, LIMIT = 23, 18, 30, 6.35, 30


def source(file):
    """The repository path of the Lean file that holds module `file`."""
    stem = file.replace('.', '/') + '.lean'
    if file.startswith('CommonwareSymbolic.'):
        return 'verification/symbolic/proofs/lean/' + stem
    return 'verification/lean/' + stem


def shorten(name):
    """A declaration name without the prefixes that every name of its kind shares."""
    for prefix in ('Commonware.Symbolic.', 'Qmdb.', 'commonware_symbolic.'):
        if name.startswith(prefix):
            name = name[len(prefix):]
    # hax names a trait implementation after its type and the path of its trait.
    match = re.fullmatch(r'(.+)\.Insts\.([A-Za-z_0-9]+?)(\.\w+)?', name)
    if match:
        trait = re.sub(r'^(Commonware_symbolic|Core)', '', match[2])
        trait = re.sub(r'(?<=[a-z0-9])(?=[A-Z])', ' ', trait).split(' ')[-1]
        name = f'{match[1]}: {trait}{match[3] or ""}'
    return name


def load(text, first_line):
    """The graph: nodes with trust, label and direct dependencies. `first_line(path, line)` gives
    the text of a source line."""
    nodes = {raw['id']: dict(raw) for raw in json.loads(text)}
    for title in LIBRARIES:
        nodes[title] = {'id': title, 'file': None, 'line': None, 'names': [title],
                        'kinds': ['library'], 'cited': False, 'meaning': [], 'proof': []}
    for node in nodes.values():
        for dependency in node['meaning'] + node['proof']:
            assert dependency in nodes, (node['id'], dependency)
        node['kind'] = node['kinds'][0] if node['kinds'] else 'def'
        node['name'] = node['names'][0] if node['names'] else node['id']
        node['label'] = shorten(node['name'])
        if node['file']:
            node['path'] = source(node['file'])
            line = first_line(node['path'], node['line']).strip()
            combine = re.match(r'#combine (?:\+toplevel )?into (.+?) from', line)
            instance = re.match(r'instance\s*(?:\[[^\]]*\]\s*)*:\s*(.+?)(?:\s+where|\s*:=.*)?$', line)
            if combine:
                node['kind'], node['label'] = '#combine', '#combine ' + combine[1]
                node['name'] = node['label']
            elif instance and node['name'].rsplit('.', 1)[-1].startswith(('inst', 'wfInst')):
                node['kind'], node['label'] = 'instance', 'instance ' + instance[1]
                node['name'] = 'instance : ' + instance[1]
    # A lemma is only a step of a proof. Everything it mentions is a proof dependency, and a
    # definition that mentions it uses it as a proof term, which cannot change what the
    # definition says.
    for node in nodes.values():
        node['lemma'] = node['kind'] == 'theorem' and not node['cited']
    for node in nodes.values():
        mentions = set(node['meaning'])
        proofs = {key for key in mentions if nodes[key]['lemma']} | set(node['proof'])
        node['says'] = set() if node['lemma'] else mentions - proofs
        node['uses'] = mentions | proofs if node['lemma'] else proofs
        node['said_by'] = []
    # What the cited statements say: everything they reach without entering a proof.
    for statement in [key for key, node in nodes.items() if node['cited']]:
        seen, todo = set(), [statement]
        while todo:
            for dependency in nodes[todo.pop()]['says']:
                if dependency not in seen:
                    seen.add(dependency)
                    todo.append(dependency)
                    nodes[dependency]['said_by'].append(statement)
    for key, node in nodes.items():
        if key in LIBRARIES:
            node['trust'] = 'assumed'
        elif node['file'].startswith('CommonwareSymbolic.'):
            node['trust'] = 'generated'
        elif node['cited']:
            node['trust'] = 'statement'
        else:
            node['trust'] = 'trusted' if node['said_by'] else 'checked'
    return nodes


def reachable(graph):
    """For every node of an acyclic `graph` of dependency sets, everything it reaches."""
    memo = {}

    def reach(key):
        if key not in memo:
            memo[key] = set()
            for dependency in graph[key]:
                memo[key] |= {dependency} | reach(dependency)
        return memo[key]

    for key in graph:
        reach(key)
    return memo


def view(nodes, lemmas):
    """The nodes and reduced edges of one drawing. An edge is left out when a longer path already
    implies it: a `says` edge when other `says` edges do, a `uses` edge when any edges do."""
    shown = [key for key, node in nodes.items() if lemmas or not node['lemma']]
    inside = set(shown)
    says = {key: nodes[key]['says'] & inside for key in shown}
    both = {key: (nodes[key]['says'] | nodes[key]['uses']) & inside for key in shown}
    reach_says, reach_both = reachable(says), reachable(both)
    edges = []
    for key in shown:
        for dependency in says[key]:
            if not any(dependency in reach_says[other] for other in says[key] - {dependency}):
                edges.append((dependency, key, 'says'))
        for dependency in both[key] - says[key]:
            if not any(dependency in reach_both[other] for other in both[key] - {dependency}):
                edges.append((dependency, key, 'uses'))
    return shown, both, sorted(edges)


def spread(wanted, pitch):
    """Positions as close to `wanted` as their order and a minimal distance allow."""
    down = []
    for want in wanted:
        down.append(max(want, down[-1] + pitch) if down else want)
    up = []
    for want in reversed(wanted):
        up.append(min(want, up[-1] - pitch) if up else want)
    up.reverse()
    middle = [(low + high) / 2 for low, high in zip(down, up)]
    out = []
    for value in middle:
        out.append(max(value, out[-1] + pitch) if out else value)
    return out


def layout(nodes, shown, both):
    """Layers from left to right by longest path, ordered and placed to keep edges short."""
    rank = {}

    def depth(key):
        if key not in rank:
            rank[key] = 1 + max((depth(dependency) for dependency in both[key]), default=-1)
        return rank[key]

    users = defaultdict(set)
    for key in shown:
        depth(key)
        for dependency in both[key]:
            users[dependency].add(key)
    layers = defaultdict(list)
    for key in sorted(shown, key=lambda key: (nodes[key]['file'] or '', nodes[key]['line'] or 0)):
        layers[rank[key]].append(key)
    order = [layers[index] for index in sorted(layers)]
    y = {key: index * PITCH for layer in order for index, key in enumerate(layer)}
    for sweep in range(24):
        forward = sweep % 2 == 0
        for layer in (order if forward else reversed(order)):
            def wanted(key):
                near = both[key] if forward else users[key]
                return sum(y[other] for other in near) / len(near) if near else y[key]
            layer.sort(key=lambda key: (wanted(key), y[key]))
            for key, place in zip(layer, spread([wanted(key) for key in layer], PITCH)):
                y[key] = place
    top = min(y.values())
    x, left = {}, 0
    width = {key: min(len(nodes[key]['label']), LIMIT) * CHAR + 14 for key in shown}
    for layer in order:
        column = max(width[key] for key in layer)
        for key in layer:
            x[key] = left
        left += column + GAP
    place = {key: (x[key], y[key] - top + 6, width[key]) for key in shown}
    return place, left - GAP, max(y.values()) - top + HEIGHT + 12


def draw(nodes, index, lemmas):
    """One drawing as SVG. `index` numbers the nodes for the script of the page."""
    shown, both, edges = view(nodes, lemmas)
    place, width, height = layout(nodes, shown, both)
    parts = []
    for dependency, user, kind in edges:
        x1, y1, w1 = place[dependency]
        x2, y2, _ = place[user]
        x1, y1, y2 = x1 + w1, y1 + HEIGHT / 2, y2 + HEIGHT / 2
        bend = max(GAP * 0.6, (x2 - x1) * 0.45)
        if dependency in LIBRARIES:
            kind += ' lib'
        parts.append(f'<path class="e {kind}" data-a="{index[dependency]}" data-b="{index[user]}" '
                     f'd="M{x1:.0f} {y1:.1f}C{x1 + bend:.0f} {y1:.1f} {x2 - bend:.0f} {y2:.1f} '
                     f'{x2:.0f} {y2:.1f}"/>')
    for key in shown:
        node = nodes[key]
        left, top, wide = place[key]
        label = node['label']
        if len(label) > LIMIT:
            label = label[:LIMIT - 1] + '…'
        parts.append(f'<g class="n {node["trust"]}" data-i="{index[key]}">'
                     f'<title>{html.escape(node["name"])} · {TRUST[node["trust"]]}</title>'
                     f'<rect x="{left:.0f}" y="{top:.1f}" width="{wide:.0f}" height="{HEIGHT}" rx="4"/>'
                     f'<text x="{left + 7:.0f}" y="{top + 12.6:.1f}">{html.escape(label)}</text></g>')
    count = len(shown)
    title = (f'The declaration graph with every lemma: {count} declarations.' if lemmas else
             f'The declaration graph without lemmas: {count} definitions and cited statements.')
    return (f'<svg role="img" aria-label="{title} Each declaration depends on those to its left." '
            f'viewBox="0 0 {width:.0f} {height:.0f}" width="{width:.0f}" height="{height:.0f}">'
            + ''.join(parts) + '</svg>')
