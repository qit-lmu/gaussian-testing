"""Build the manuscript index for Git readers and for leanblueprint."""

import argparse
import hashlib
from html import unescape
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import NamedTuple
from urllib.parse import quote

ROOT = Path(__file__).resolve().parents[1]
MANUSCRIPT = Path('material/manuscript.tex')
BLUEPRINT = Path('blueprint/src/content.tex')
KINDS = 'theorem|lemma|corollary|proposition|definition|conjecture|remark'
STATUS = {'checked': 'Checked', 'partial': 'Partial coverage', 'open': 'Open'}


def read(path):
    return (ROOT / path).read_text(encoding='utf-8')


def uncomment(source):
    # An even number of backslashes before % ends in a row break, not \%.
    return re.sub(r'(?m)(?<!\\)((?:\\\\)*)%.*', r'\1', source)


def line_number(source, offset):
    return 1 + source.count('\n', 0, offset)


def numbered_results(source):
    """Use the manuscript's shared theorem counter, which resets each section."""
    events = re.compile(r'^\s*\\section\{|\\begin\{(' + KINDS + r')\}', re.M)
    section = serial = 0
    results = {}
    for match in events.finditer(source):
        kind = match.group(1)
        if kind is None:
            section += 1
            serial = 0
            continue
        serial += 1
        end = source.index('\\end{' + kind + '}', match.end())
        results[f'r{section}-{serial}'] = (f'{kind.title()} {section}.{serial}', match.start(), end)
    return results


def numbered_equations(source):
    """Read the manuscript's section-reset equation counter without running TeX.

    The supported numbered displays are ``equation`` and ``align``. In align,
    only outer row breaks advance the counter: rows inside split/aligned/matrix
    environments or braced arguments do not. Explicit counter changes, tags,
    and other numbering environments require a deliberate parser update.
    """
    source = uncomment(source)
    counter_setup = re.findall(r'\\numberwithin\s*\{(equation|section)\}\s*\{([^}]+)\}', source)
    if counter_setup != [('equation', 'section')]:
        raise ValueError('equation numbering requires exactly \\numberwithin{equation}{section}')
    unsupported = re.search(
        r'\\(?:tag\*?|appendix)\b|'
        r'\\(?:setcounter|addtocounter|stepcounter|refstepcounter|counterwithin\*?|counterwithout\*?)'
        r'\s*\{(?:equation|section)\}|'
        r'\\(?:renewcommand\*?|def)\s*\{?\\(?:theequation|thesection)\b', source)
    if unsupported:
        raise ValueError(f'unsupported equation numbering command at line '
                         f'{line_number(source, unsupported.start())}: {unsupported[0]}')
    begin = source.find(r'\begin{document}')
    end = source.find(r'\end{document}')
    if begin < 0 or end < begin:
        raise ValueError('equation numbering requires a complete document environment')
    body = source[begin + len(r'\begin{document}'):end]
    tokens = re.compile(
        r'\\begin\s*\{(?P<begin>[^}]+)\}|'
        r'\\end\s*\{(?P<end>[^}]+)\}|'
        r'(?P<section>\\section)(?P<star>\*)?\s*(?:\[[^\]]*\])?\s*(?=\{)|'
        r'\\label\s*\{(?P<label>[^}]+)\}|'
        r'(?P<row>\\\\\*?(?:\s*\[[^\]]*\])?)|'
        r'(?P<suppress>\\(?:notag|nonumber)\b)|'
        r'(?P<command>\\[A-Za-z]+|\\.)|(?P<brace>[{}])')
    unsupported_envs = {'gather', 'alignat', 'flalign', 'multline', 'eqnarray', 'subequations'}
    stack = []
    section = serial = braces = 0
    active = None
    equations = {}

    def finish_row():
        nonlocal serial
        if active['labels'] and (active['starred'] or active['suppressed']):
            raise ValueError(f'equation label on an unnumbered row: {active["labels"]}')
        # AMS align numbers even an empty row, including the one after a
        # trailing row break. Do not infer numbering from formula text.
        if not active['starred'] and not active['suppressed']:
            serial += 1
            for label in active['labels']:
                if label in equations:
                    raise ValueError(f'duplicate equation label: {label}')
                equations[label] = f'{section}.{serial}'
        active['labels'] = []
        active['suppressed'] = False

    for match in tokens.finditer(body):
        if env := match['begin']:
            base = env.removesuffix('*')
            if base in unsupported_envs:
                raise ValueError(f'unsupported equation numbering environment: {env}')
            if base in ('equation', 'align'):
                if active:
                    raise ValueError(f'nested numbered display environment: {env}')
                active = {'env': env, 'starred': env.endswith('*'), 'depth': braces,
                          'labels': [], 'suppressed': False}
            stack.append(env)
        elif env := match['end']:
            if not stack or stack.pop() != env:
                raise ValueError(f'unmatched environment while counting equations: {env}')
            if active and env == active['env']:
                finish_row()
                active = None
        elif match['section']:
            if active:
                raise ValueError('section command inside an equation')
            if not match['star']:
                section += 1
                serial = 0
        elif label := match['label']:
            if active:
                active['labels'].append(label)
        elif active and match['row'] and stack[-1] == active['env'] and braces == active['depth']:
            if active['env'].startswith('equation'):
                raise ValueError('outer row break in equation; use a nested split environment')
            finish_row()
        elif active and match['suppress']:
            if stack[-1] != active['env'] or braces != active['depth']:
                raise ValueError('nested equation-number suppression is not supported')
            active['suppressed'] = True
        elif match['brace']:
            braces += 1 if match['brace'] == '{' else -1
    if stack or active or braces:
        raise ValueError('unclosed environments or braces while counting equations')
    return equations


def validate_equation_references(records, equations, nodes, blueprint_source=None):
    """Check equation inventory, index titles, and explicit blueprint numbers."""
    indexed = {row.get('label') for row in records}
    if missing := equations.keys() - indexed:
        raise ValueError(f'numbered equations missing from manuscript index: {sorted(missing)}')
    numbers = {}
    for row in records:
        number = equations.get(row.get('label'))
        title_number = re.search(r'\(Eq\. (\d+\.\d+)\)$', row['title'])
        if number:
            if not title_number or title_number[1] != number:
                raise ValueError(f'{row["id"]}: title must end with (Eq. {number})')
            row['equation'] = numbers[row['id']] = number
        elif title_number or row.get('label', '').startswith('eq:'):
            raise ValueError(f'{row["id"]}: equation title requires a numbered equation label')
    refs = [(node.label, ref, display) for node in nodes for ref, display in node.refs]
    if blueprint_source is not None:
        refs = [(f'blueprint line {line_number(blueprint_source, match.start())}',
                 match[1], match[2]) for match in re.finditer(
                     r'\\(?:paperref|noderef|proofref)\{([^}]+)\}\{([^}]+)\}', blueprint_source)]
    for origin, ref, display in refs:
        displayed = re.findall(r'\b(?:Eq\.|Equation)\s*~?\s*\(?(\d+\.\d+)\)?',
                               display, re.I)
        for number in displayed:
            if numbers.get(ref) != number:
                raise ValueError(f'{origin}: {display} does not match the equation '
                                 f'anchored by {ref} ({numbers.get(ref, "not an equation")})')


def check_equations_aux(source, path):
    """Independently compare parsed numbers with an actual LaTeX compilation."""
    equations = numbered_equations(source)
    labels = {label: number for label, number in
              re.findall(r'\\newlabel\{([^}]+)\}\{\{([^}]+)\}', path.read_text())
              if not label.endswith('@cref')}
    for label, number in equations.items():
        if labels.get(label) != number:
            raise ValueError(f'{path}: {label} is {labels.get(label)!r}, expected {number}')
    if extra := {label for label in labels if label.startswith('eq:') and label not in equations}:
        raise ValueError(f'{path}: equation labels absent from the manuscript: {sorted(extra)}')
    print(f'Checked {len(equations)} equation labels against {path}.')


class Node(NamedTuple):
    label: str
    title: str
    refs: list
    primary: list
    line: int
    partial_proof: bool


def blueprint_nodes(source):
    nodes = []
    for match in re.finditer(r'\\begin\{(' + KINDS + r')\}\[([^\]]+)\]\\label\{([^}]+)\}(.*?)\\end\{\1\}', source, re.S):
        _, title, label, body = match.groups()
        citations = re.findall(r'\\(paperref|noderef|proofref)\{([^}]+)\}\{([^}]+)\}', body)
        primary = [(kind, item) for kind, item, _ in citations if kind != 'paperref']
        supporting = len(re.findall(r'\\supportingnode\b', body))
        if (bool(primary) + supporting) != 1:
            raise ValueError(f'{label}: identify the primary manuscript item(s) or mark it as supporting')
        partial_proof = len(re.findall(r'\\partialproof\b', body))
        if partial_proof > 1:
            raise ValueError(f'{label}: duplicate partial proof marker')
        if partial_proof and (re.search(r'\\(?:leanok|mathlibok)\b', body) or
                              re.search(r'\\leanproof\s*\{' + re.escape(label) + r'\}', source)):
            raise ValueError(f'{label}: a partial proof also has a completed Lean marker')
        refs = [(item, display) for _, item, display in citations]
        nodes.append(Node(label, title, refs, primary, line_number(source, match.start()), bool(partial_proof)))
    if not nodes or len({node.label for node in nodes}) != len(nodes):
        raise ValueError('missing or duplicate blueprint node labels')
    return nodes


def lean_locations():
    # Index source locations for links. The optional Lean check below verifies
    # actual availability of the qualified declarations through the public import.
    locations = {}
    decl = re.compile(r'^(?:@\[[^\]]+\]\s*)*(?:(?:protected|noncomputable|nonrec|unsafe)\s+)*(?:abbrev|def|inductive|structure|class|instance|lemma|theorem)\s+([\w.\'₀-₉]+)')
    block_comment = re.compile(r'/-|-/')
    for path in sorted((ROOT / 'GaussianTesting').rglob('*.lean')):
        stack = []
        depth = 0
        for num, raw in enumerate(path.read_text().splitlines(), 1):
            # Declarations start at column zero. Omit nested docstrings and comments.
            start = 0
            code = ''
            for token in block_comment.finditer(raw):
                if depth == 0:
                    code += raw[start:token.start()]
                depth += 1 if token.group() == '/-' else -1
                start = token.end()
            if depth == 0:
                code += raw[start:]
            if ns := re.match(r'^namespace\s+([\w.]+)', code):
                stack.append(ns[1])
            elif re.match(r'^(?:noncomputable )?section\b', code):
                stack.append('')
            elif re.match(r'^end(?:\s|$)', code) and stack:
                stack.pop()
            elif m := decl.match(code):
                name = '.'.join([n for n in stack if n] + [m[1]])
                locations[name] = (path.relative_to(ROOT).as_posix(), num)
    return locations


def blueprint_repository():
    repository = re.search(r'\\github\{([^}]+)\}', read('blueprint/src/web.tex'))
    if repository is None:
        raise ValueError('Blueprint web source must configure its GitHub repository')
    return repository[1].rstrip('/')


def lean_source_urls(names):
    """Resolve blueprint declarations to source at the checked-out commit."""
    revision = subprocess.check_output(
        ['git', 'rev-parse', '--verify', 'HEAD'], cwd=ROOT, text=True).strip()
    repository = blueprint_repository()
    locations = lean_locations()
    urls = {}
    for name in names:
        if name not in locations:
            raise ValueError(f'Blueprint declaration has no source location: {name}')
        path, line = locations[name]
        urls[name] = f'{repository}/blob/{revision}/{quote(path)}#L{line}'
    return urls


def theorem_owners(records, captions):
    """Each numbered manuscript theorem has one node, distinct from all other theorems."""
    owners = {row['title']: [] for row in records if row['title'].startswith('Theorem ')
              and re.fullmatch(r'r\d+-\d+', row['id'])}
    for label, citations in captions.items():
        for citation in citations:
            if citation.startswith('Proof of Theorem '):
                theorem = citation.removeprefix('Proof of ')
                raise ValueError(f'{label}: cite {theorem} in the text and give this supporting node its own caption')
            if citation in owners:
                owners[citation].append(label)
    for theorem, labels in owners.items():
        if len(labels) != 1:
            raise ValueError(f'{theorem}: expected one primary graph node, found {labels}')
    unique = {theorem: labels[0] for theorem, labels in owners.items()}
    if len(set(unique.values())) != len(unique):
        raise ValueError(f'distinct manuscript theorems share a graph node: {unique}')
    return unique


def load_map():
    records = json.loads(read('docs/manuscript-map.json'))
    source = uncomment(read(MANUSCRIPT))
    results = numbered_results(source)
    ids = {row['id'] for row in records}
    if len(ids) != len(records):
        raise ValueError('duplicate manuscript IDs')
    declared = {i for i in ids if re.fullmatch(r'r\d+-\d+', i)}
    if declared != results.keys():
        raise ValueError(f'numbered result inventory mismatch: {declared ^ results.keys()}')
    panels = re.findall(r'\\label\{(fig:test-[^}]+)\}', source)
    if len(panels) != 4:
        raise ValueError('review the Figure 1 inventory')
    panel_labels = dict(zip(('f1a', 'f1b', 'f1c', 'f1d'), panels))
    if not panel_labels.keys() <= ids:
        raise ValueError('missing Figure 1 panels')
    blueprint_source = uncomment(read(BLUEPRINT))
    nodes = blueprint_nodes(blueprint_source)
    validate_equation_references(records, numbered_equations(source), nodes, blueprint_source)
    titles = {r['id']: r['title'] for r in records}
    for node in nodes:
        for ref, display in node.refs:
            if ref not in titles:
                raise ValueError(f'{node.label}: unknown paper reference {ref}')
            if ref in results or ref in panel_labels:
                if display.replace('~', ' ') != titles[ref]:
                    raise ValueError(f'{node.label}: {display} should be {titles[ref]}')
    owners = theorem_owners(records, {
        n.label: [('Proof of ' if kind == 'proofref' else '') + titles[item] for kind, item in n.primary]
        for n in nodes})
    partial_nodes = {n.label for n in nodes if n.partial_proof}
    for row in records:
        if row['title'] in owners and (row['status'] == 'partial') != (owners[row['title']] in partial_nodes):
            raise ValueError(f"{row['title']}: partial proof marker and manuscript coverage disagree")

    lean = lean_locations()
    for row in records:
        id_ = row['id']
        if not re.fullmatch(r'[a-z0-9-]+', id_) or row['status'] not in STATUS:
            raise ValueError(f'invalid manuscript ID or coverage status: {id_}')
        if not all(row.get(f) for f in ('title', 'summary', 'scope')):
            raise ValueError(f'{id_}: missing description or coverage')
        if ('label' in row) == ('text' in row):
            raise ValueError(f'{id_}: expected exactly one source locator')
        needle = '\\label{' + row['label'] + '}' if 'label' in row else row['text']
        if source.count(needle) != 1:
            raise ValueError(f'{id_}: source locator must resolve exactly once: {needle}')
        offset = source.index(needle)
        if id_ in results:
            title, start, end = results[id_]
            if row['title'] != title or not start <= offset < end or not row.get('route'):
                raise ValueError(f'{id_}: expected a proof route and a locator inside {title}')
            offset = start
        if id_ in panel_labels:
            if row.get('label') != panel_labels[id_] or row['title'] != f'Figure 1({id_[-1]})':
                raise ValueError(f'{id_}: wrong panel order or locator')
            offset = source.rindex('\\begin{subfigure}', 0, offset)
        row['line'] = line_number(source, offset)
        sections = list(re.finditer(r'(?m)^\\section\{', source[:offset]))
        row['section'] = len(sections)
        row['subsection'] = len(re.findall(r'(?m)^\\subsection\{', source[sections[-1].end():offset]))
        row['nodes'] = [(n.label, n.title, n.line) for n in nodes if id_ in dict(n.refs)]
        if not row['nodes']:
            raise ValueError(f'{id_}: no blueprint component refers to this item')
        if row['title'] in owners:
            row['theorem_node'] = owners[row['title']]
        for name in row['lean']:
            if name not in lean:
                raise ValueError(f'{id_}: cannot locate public declaration {name}')
    return sorted(records, key=lambda r: r['line']), lean


def graph_annotations():
    """Primary citations and partial-proof markers displayed on graph nodes."""
    rows, _ = load_map()
    short = {}
    for row in rows:
        title = row['title']
        if re.fullmatch(r'r\d+-\d+|f1[a-d]', row['id']):
            citation = title
        elif 'equation' in row:
            citation = f'Eq. ({row["equation"]})'
        else:
            section = str(row['section'])
            if row['subsection']:
                section += f".{row['subsection']}"
            citation = f"§{section}, line {row['line']}"
        short[row['id']] = citation
    nodes = blueprint_nodes(uncomment(read(BLUEPRINT)))
    sections = {row['id']: row['section'] for row in rows}
    annotations = {}
    for node in nodes:
        if node.label.startswith('prelim:'):
            # Preliminaries cover a section; keep precise locations in the index.
            citations = [f'§{section}' for section in sorted(
                {sections[item] for _, item in node.primary})]
        else:
            citations = [('Proof of ' if kind == 'proofref' else '') + short[item]
                         for kind, item in node.primary]
        annotations[node.label] = (citations or ['Supporting result'], node.partial_proof)
    return annotations


SECTION_NAMES = ['Introduction', 'Preliminaries', 'Robustness', 'Kac walk', 'Fermions', 'Bosons']


def graph_sections():
    """Group by manuscript section, independently of the blueprint's chapters."""
    rows, _ = load_map()
    sections = {row['id']: row['section'] for row in rows}
    # Add a section here for any supporting node without a primary manuscript
    # item. The current preliminaries nodes cite their manuscript locations.
    supporting = {}
    result = {}
    for node in blueprint_nodes(uncomment(read(BLUEPRINT))):
        candidates = {sections[item] for _, item in node.primary}
        if not candidates and node.label in supporting:
            candidates = {supporting[node.label]}
        if len(candidates) != 1:
            raise ValueError(f'{node.label}: choose a manuscript section for graph layout')
        result[node.label] = candidates.pop()
    return result


def tex(text):
    escapes = {'\\': r'\textbackslash{}', '_': r'\_', '#': r'\#', '&': r'\&', '%': r'\%',
               '{': r'\{', '}': r'\}', '^': r'\textasciicircum{}', '~': r'\textasciitilde{}', '$': r'\$'}
    escapes.update((ch, r'\textsubscript{' + str(i) + '}') for i, ch in enumerate('₀₁₂₃₄₅₆₇₈₉'))
    return ''.join(escapes.get(ch, ch) for ch in text)


def index_files(records, lean):
    digest = hashlib.sha256((ROOT / MANUSCRIPT).read_bytes()).hexdigest()
    md = ['<!-- Generated by scripts/manuscript_map.py. Edit docs/manuscript-map.json. -->',
          '# Manuscript index', '',
          f'This index follows the [repository manuscript](../{MANUSCRIPT}). '
          'It includes every numbered result, Figure 1(a–d), and selected definitions, equations, '
          'and supporting claims. Coverage describes the **whole manuscript item**. A public Lean '
          'declaration can prove a component while a model identification or a broader statement is still open. '
          'Lean names below are in the GaussianTesting namespace.',
          '', f'<!-- manuscript sha256: {digest} -->', '', 'Jump to a numbered result:', '']
    for section in range(1, 7):
        links = [f"[{r['title']}](#{r['id']})" for r in records if r['id'].startswith(f'r{section}-')]
        if links:
            md.append(' · '.join(links) + '  ')
    bp = ['% Generated by scripts/manuscript_map.py. Edit docs/manuscript-map.json.',
          r'\chapter{Manuscript index}\label{sec:manuscript-index}',
          'Read this chapter in manuscript order. Each entry links the draft source and any corresponding '
          'Lean declarations. The coverage assessment refers to the full manuscript item. '
          'The component links lead to checked statements and their scope qualifications in this blueprint. '
          'For numbered results, the proof note compares the manuscript argument with the implemented route. '
          'Lean names are in the GaussianTesting namespace. Source links open line-numbered copies '
          'on the documentation site.', '']
    last = None
    for r in records:
        if r['section'] != last:
            last = r['section']
            heading = f"Manuscript section {last}. {SECTION_NAMES[last-1]}"
            md += ['', '## ' + heading]
            bp += ['\\section{' + heading + '}']
        status = STATUS[r['status']]
        line = r['line']
        md += ['', f'<a id="{r["id"]}"></a>', '', '### ' + r['title'], '',
               f"**{status}.** {r['summary']} [Manuscript, line {line}](../{MANUSCRIPT}#L{line})"
               + (f" (source anchor `{r['label']}`)" if 'label' in r else ''), '', r['scope']]
        bp += ['\\subsection{' + tex(r['title']) + '}\\label{paper:' + r['id'] + '}',
               r'\textbf{' + status + '.} ' + tex(r['summary']) + ' '
               + r'\bpsource{' + str(MANUSCRIPT) + '}{' + str(line) + '}{Manuscript, line ' + str(line) + '.}',
               '', tex(r['scope'])]
        if r.get('route'):
            md += ['', '**Proof route.** ' + r['route']]
            bp += ['', r'\textbf{Proof route.} ' + tex(r['route'])]
        if r['lean']:
            md_names, bp_names = [], []
            for name in r['lean']:
                file, n = lean[name]
                short = name.removeprefix('GaussianTesting.')
                md_names.append(f'[{short}](../{file}#L{n})')
                bp_names.append(r'\bpsource{' + file + '}{' + str(n) + r'}{\texttt{' + tex(short) + '}}')
            md += ['', '**Lean.** ' + ', '.join(md_names) + '.']
            bp += ['', r'\bpdecls{\textbf{Lean.} ' + ', '.join(bp_names) + '.}']
        groups = [('Blueprint', r['nodes'])]
        if 'theorem_node' in r:
            owner = r['theorem_node']
            groups = [('Theorem node', [node for node in r['nodes'] if node[0] == owner]),
                      ('Related blueprint entries', [node for node in r['nodes'] if node[0] != owner])]
        for heading, nodes in groups:
            if nodes:
                md_nodes = [f'[{title}](../{BLUEPRINT}#L{n})' for _, title, n in nodes]
                bp_nodes = [r'\bplink{' + label + '}{' + title + '}' for label, title, _ in nodes]
                md += ['', '**' + heading + '.** ' + ', '.join(md_nodes) + '.']
                bp += ['', r'\textbf{' + heading + '.} ' + ', '.join(bp_nodes) + '.']
        bp += ['']
    return {'docs/manuscript-index.md': '\n'.join(line.rstrip() for line in md) + '\n',
            'blueprint/src/manuscript-index.tex': '\n'.join(bp)}


def check_lean(records):
    names = sorted({n for r in records for n in r['lean']})
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / 'CheckManuscript.lean'
        path.write_text('import GaussianTesting\n' + ''.join('#check ' + n + '\n' for n in names))
        result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT, capture_output=True, text=True)
        if result.returncode:
            raise ValueError(result.stdout + result.stderr)
    print(f'Lean resolved all {len(names)} manuscript-linked declarations.')


def check_robustness_edges(dot):
    """The gradient inequality feeds Theorem 3.4, which implies Theorem 1.2."""
    gradient = 'lem:bound-gradient'
    sharp = 'thm:bound-fidelity-gradient-flow'
    intro = 'thm:gradient-flow-intro'
    # An edge can follow a closing subgraph brace, not only a semicolon.
    edges = set(re.findall(r'"([^"]+)"\s*->\s*"([^"]+)"', dot))
    for source, target in ((gradient, sharp), (sharp, intro)):
        if (source, target) not in edges:
            raise ValueError(f'rendered graph missing prerequisite edge: {source} -> {target}')
        if (target, source) in edges:
            raise ValueError(f'rendered graph also has reversed prerequisite: {target} -> {source}')


def dot_attributes(raw):
    """Read Graphviz attributes without treating commas inside labels as separators."""
    attrs = {}
    cursor = 0
    while cursor < len(raw):
        if raw[cursor].isspace() or raw[cursor] == ',':
            cursor += 1
            continue
        key = re.match(r'(\w+)\s*=\s*', raw[cursor:])
        if not key:
            raise ValueError(f'Cannot parse DOT attributes near {raw[cursor:cursor + 60]!r}')
        cursor += key.end()
        start = cursor
        if raw[cursor] == '"':
            cursor += 1
            start = cursor
            while cursor < len(raw) and raw[cursor] != '"':
                cursor += 2 if raw[cursor] == '\\' else 1
            value = raw[start:cursor]
            cursor += 1
        elif raw[cursor] == '<':
            depth = 1
            cursor += 1
            while cursor < len(raw) and depth:
                depth += (raw[cursor] == '<') - (raw[cursor] == '>')
                cursor += 1
            if depth:
                raise ValueError('Unterminated HTML label in DOT attributes')
            value = raw[start:cursor]
        else:
            while cursor < len(raw) and not raw[cursor].isspace() and raw[cursor] != ',':
                cursor += 1
            value = raw[start:cursor]
        if key[1] in attrs:
            raise ValueError(f'Duplicate DOT attribute {key[1]}')
        attrs[key[1]] = value
    return attrs


def check_compact_layout(dot, nodes):
    """Check the actual section boxes used by the fixed-position compact renderer."""
    clusters = re.findall(
        r'\bsubgraph\s+cluster_section_(\d+)\s*\{\s*graph\s*\[(.*?)\];', dot, re.S)
    boxes = {}
    for section, raw in clusters:
        section = int(section)
        if section in boxes:
            raise ValueError(f'Duplicate compact section cluster {section}')
        attrs = dot_attributes(raw)
        box = tuple(float(x) for x in attrs.get('bb', '').split(','))
        if len(box) != 4 or box[0] >= box[2] or box[1] >= box[3]:
            raise ValueError(f'Invalid compact section {section} bounding box: {box}')
        boxes[section] = box
    if boxes.keys() != {1, 3, 4, 5, 6}:
        raise ValueError(f'Unexpected compact section inventory: {boxes.keys()}')
    middle = (5, 4, 6)
    for section in middle:
        if boxes[3][1] <= boxes[section][3]:
            raise ValueError(f'Robustness must be above section {section}')
        if boxes[1][3] >= boxes[section][1]:
            raise ValueError(f'Introduction must be below section {section}')
    for left, right in zip(middle, middle[1:]):
        if boxes[left][2] >= boxes[right][0]:
            raise ValueError('Compact middle sections must run Fermions, Kac walk, Bosons')
    if max(boxes[s][3] for s in middle) - min(boxes[s][3] for s in middle) > 1:
        raise ValueError('Compact middle section headings must align')
    center = (boxes[5][0] + boxes[6][2]) / 2
    for section in (1, 3):
        if abs((boxes[section][0] + boxes[section][2]) / 2 - center) > 1:
            raise ValueError(f'Compact section {section} must be centered over the middle row')
    sections = graph_sections()
    for node, attrs in nodes.items():
        coords = tuple(float(x) for x in attrs.get('pos', '').rstrip('!').split(','))
        if len(coords) != 2:
            raise ValueError(f'{node}: missing compact node position')
        x, y = coords
        x0, y0, x1, y1 = boxes[sections[node]]
        if not (x0 <= x <= x1 and y0 <= y <= y1):
            raise ValueError(f'{node}: compact position is outside its manuscript section')
    main = 'thm:bound-fidelity-gradient-flow'
    main_x, main_y = map(float, nodes[main]['pos'].rstrip('!').split(','))
    if abs(main_x - center) > 1:
        raise ValueError('Theorem 3.4 must be centered at the bottom of Robustness')
    if any(float(nodes[node]['pos'].split(',')[1].rstrip('!')) <= main_y
           for node, section in sections.items() if section == 3 and node != main):
        raise ValueError('Theorem 3.4 must be below the other Robustness nodes')


def check_graph(dot, records, annotations):
    """Check the emitted DOT consumed by both the interactive graph and its static snapshot."""
    # Inspect the complete node inventory to catch extra rendered nodes as well as missing ones.
    nodes = re.findall(r'(?<=;)\s*(?:"([^"]+)"|([\w]+))\s*\[(.*?)\];', dot, re.S)
    rendered = {}
    for quoted, bare, attrs in nodes:
        if bare in ('graph', 'node', 'edge'):
            continue
        label = quoted or bare
        if label in rendered:
            raise ValueError(f'{label}: duplicate DOT node declaration')
        rendered[label] = dot_attributes(attrs)
    if rendered.keys() != annotations.keys():
        raise ValueError(f'rendered graph node inventory differs from source: {rendered.keys() ^ annotations.keys()}')

    captions = {}
    for label, attrs in rendered.items():
        raw = attrs.get('label', '')
        headings = re.findall(r'<B>(.*?)</B>', raw, re.S)
        captions[label] = [ref for heading in headings for ref in unescape(heading).split(' · ')]
        expected, partial_proof = annotations[label]
        if captions[label] != expected:
            raise ValueError(f'{label}: expected graph citations {expected}, got {captions[label]}')
        partial_fill = attrs.get('fillcolor', '').upper() == '#FFF1CF'
        partial_row = '<I>Partial proof</I>' in raw
        if partial_fill != partial_proof or partial_row != partial_proof:
            raise ValueError(f'{label}: partial-proof fill or text disagrees with source')
        if partial_proof and (attrs.get('color', '').upper() != '#895B12' or
                              'filled' not in attrs.get('style', '').split(',')):
            raise ValueError(f'{label}: partial proof must have amber border and fill')
    theorem_owners(records, captions)
    check_robustness_edges(dot)
    return rendered


def graph_semantics(dot, nodes):
    # The fixed layout supplies geometry, while labels, proof flags, shapes,
    # arrow directions, and dependency styles must agree with the wide graph.
    node_geometry = {'pos', 'pin', 'width', 'height'}
    semantic_nodes = {name: {k: v for k, v in attrs.items() if k not in node_geometry}
                      for name, attrs in nodes.items()}
    edges = {}
    for source, target, raw in re.findall(
            r'"([^"]+)"\s*->\s*"([^"]+)"\s*\[(.*?)\];', dot, re.S):
        if (source, target) in edges:
            raise ValueError(f'Duplicate dependency edge {source} -> {target}')
        attrs = dot_attributes(raw)
        if 'layout_only' in attrs or 'invis' in attrs.get('style', '').split(','):
            raise ValueError(f'Unexpected layout-only dependency {source} -> {target}')
        edges[source, target] = {k: v for k, v in attrs.items() if k != 'pos'}
    defaults = {}
    for kind in ('node', 'edge'):
        match = re.search(r'\b' + kind + r'\s*\[(.*?)\];', dot, re.S)
        defaults[kind] = dot_attributes(match[1]) if match else {}
    return semantic_nodes, edges, defaults


def check_html(records, lean):
    """Check both graph layouts and both directions of the emitted links."""
    web = ROOT / 'blueprint/web'
    repository = blueprint_repository()
    header_pages = sorted(web.glob('*.html')) + sorted((web / 'sources').rglob('*.html'))
    for path in header_pages:
        header = re.search(r'<header\b[^>]*>(.*?)</header>', path.read_text(), re.S)
        links = re.findall(r'<a class="repository-link" href="([^"]+)"[^>]*>GitHub</a>',
                           header[1] if header else '')
        if links != [repository]:
            raise ValueError(f'{path.relative_to(web)}: expected one GitHub repository link in header')
    annotations = graph_annotations()
    layouts = (
        ('dep_graph_document.html', 'dep_graph_wide.html', 'Wide layout'),
        ('dep_graph_wide.html', 'dep_graph_document.html', 'Compact layout'),
    )
    graph_data = []
    modal_targets = []
    for file, other, link_text in layouts:
        graph = (web / file).read_text()
        dot = graph.split('.renderDot(`', 1)[1].split('`)', 1)[0]
        nodes = check_graph(dot, records, annotations)
        header = re.search(r'<header\b[^>]*>(.*?)</header>', graph, re.S)
        switches = re.findall(
            r'<a class="graph-layout-switch" href="([^"]+)">([^<]+)</a>',
            header[1] if header else '')
        if switches != [(other, link_text)]:
            raise ValueError(f'{file}: missing reciprocal graph layout link in header')
        if file == 'dep_graph_document.html':
            if not re.search(r'\.engine\(["\']nop2["\']\)', graph):
                raise ValueError('Compact graph must use the fixed-position nop2 renderer')
            check_compact_layout(dot, nodes)
        graph_data.append(graph_semantics(dot, nodes))
        modal_targets.append({label: target for target, label in re.findall(
            r'class="latex_link" href="([^"#]+)#([^"]+)"', graph)})
    if graph_data[0] != graph_data[1]:
        raise ValueError('Compact and wide graphs differ in nodes, proof styles, or dependencies')
    if modal_targets[0] != modal_targets[1]:
        raise ValueError('Compact and wide graphs have different LaTeX modal links')
    pages = modal_targets[0]
    cache = {}

    def page(file):
        if file not in cache:
            cache[file] = (web / file).read_text()
        return cache[file]

    pairs = 0
    for r in records:
        target = 'paper:' + r['id']
        for i, (node, _, _) in enumerate(r['nodes']):
            origin = pages[node]
            # Exclude navigation and other theorem statements on the same page.
            body = page(origin).split(f'id="{node}"', 1)[1].split('class="thmwrapper', 1)[0]
            body = re.split(r'<div class="[^"]*_thmwrapper', body, maxsplit=1)[0]
            if annotations[node][1] and ('Partial proof.' not in body or '✓' in body):
                raise ValueError(f'{node}: rendered theorem must show its partial proof without a Lean checkmark')
            forward = re.search(r'href="([^"#]*)#' + re.escape(target) + '"', body)
            if not forward:
                raise ValueError(f'HTML link missing from {node} to {target}')
            dest = forward[1] or origin
            entry = re.search(r'<h2 id="' + re.escape(target) + r'">.*?</h2>(.*?)(?=<h[12]|</main>|$)',
                              page(dest), re.S)
            if not entry or f'href="{origin}#{node}"' not in entry[1]:
                raise ValueError(f'HTML anchor or return link missing from {target} to {node}')
            if i == 0:
                sources = [(MANUSCRIPT, r['line'])] + [lean[name] for name in r['lean']]
                for path, n in sources:
                    file = f'sources/{path}.html'
                    if f'"{file}#L{n}"' not in entry[1] or f'id="L{n}"' not in page(file):
                        raise ValueError(f'{target}: missing local source link to {path}:{n}')
            pairs += 1
    print(f'Checked both graph layouts and {pairs} bidirectional links in the rendered blueprint.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true', help='verify both generated files (default)')
    mode.add_argument('--write', action='store_true', help='refresh both generated files after review')
    mode.add_argument('--check-lean', action='store_true', help='also check all mapped Lean names after lake build')
    mode.add_argument('--check-html', action='store_true', help='also check two-way links after leanblueprint web')
    parser.add_argument('--check-equations-aux', type=Path, metavar='PATH',
                        help='also compare equation numbers with a compiled manuscript .aux file')
    args = parser.parse_args()
    if args.check_equations_aux:
        check_equations_aux(read(MANUSCRIPT), args.check_equations_aux)
    records, lean = load_map()
    for file, contents in index_files(records, lean).items():
        path = ROOT / file
        if args.write:
            path.write_text(contents, encoding='utf-8')
        elif not path.exists() or path.read_text(encoding='utf-8') != contents:
            raise ValueError(f'{file} is stale. Review the manuscript changes and run with --write.')
    if args.check_lean:
        check_lean(records)
    if args.check_html:
        check_html(records, lean)
    print(f'Validated {len(records)} manuscript entries.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError) as error:
        sys.exit(str(error))
