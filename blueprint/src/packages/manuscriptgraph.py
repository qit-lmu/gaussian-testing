"""Label blueprint graph nodes and group them by manuscript section."""

from functools import partial
from html import escape
from pathlib import Path
import re
from runpy import run_path
from textwrap import wrap

from plasTeX.PackageResource import PackagePreCleanupCB
from plastexdepgraph.Packages.depgraph import item_kind

from compactgraph import compact_layout


MAP_SCRIPT = Path(__file__).resolve().parents[3] / "scripts" / "manuscript_map.py"


def label_text(text):
    # Labels pass through Graphviz HTML and a JavaScript template literal.
    return escape(text).replace("\\", "&#92;").replace("$", "&#36;").replace("`", "&#96;")


def node_label(title, citations, partial_proof):
    if not citations:
        raise ValueError(f"Missing manuscript citation for graph node {title!r}")

    # Keep complete references together, with short ones sharing the same row.
    citation_rows = []
    for citation in citations:
        if citation_rows and len(citation_rows[-1]) + len(citation) + 3 <= 33:
            citation_rows[-1] += " · " + citation
        else:
            citation_rows.append(citation)
    rows = [f"<B>{label_text(row)}</B>" for row in citation_rows]

    # Figure titles already contain their citation. Display it once in bold.
    prefix = "Pending: " if title.startswith("Pending: ") else ""
    name = title.removeprefix(prefix)
    for citation in citations:
        name = name.removeprefix(citation + ", ")
    title_rows = wrap(prefix + name, width=28, break_long_words=False, break_on_hyphens=False)
    rows.extend(label_text(row) for row in title_rows)
    if partial_proof:
        rows.append("<I>Partial proof</I>")
    return "<" + "<BR/>".join(rows) + ">"


def labeled_dot(graph, to_dot, annotations, sections, section_names, shapes, *, compact=True):
    dot = to_dot(shapes)
    for node in graph.nodes:
        title = node.attributes["title"].textContent
        citations, partial_proof = annotations[node.id]
        attrs = dot.get_node(node.id).attr
        attrs["label"] = node_label(title, citations, partial_proof)
        if partial_proof:
            if node.userdata.get("leanok") or node.userdata.get("proved"):
                raise ValueError(f"{node.id}: a partial proof also has a completed Lean marker")
            attrs.update(color="#895B12", fillcolor="#FFF1CF", style="filled")
    # Clusters affect placement only: retain every dependency and each node's
    # existing proof-status colors.
    for section in sorted({sections[node.id] for node in graph.nodes}):
        members = [node for node in graph.nodes if sections[node.id] == section]
        member_ids = sorted(node.id for node in members)
        complete = all(
            not annotations[node.id][1] and (
                node.userdata.get("proved") or node.userdata.get("mathlibok") or
                (item_kind(node) == "definition" and node.userdata.get("leanok"))
            ) for node in members
        )
        # DOT has no separate outer cluster margin. Invisible wrappers add
        # eight points of clearance per side without inflating inner padding.
        outer = dot.add_subgraph(member_ids, name=f"cluster_spacing_{section}",
                                 style="invis", margin=8, label="")
        outer.add_subgraph(
            member_ids,
            name=f"cluster_section_{section}",
            label=f"§{section} · {section_names[section - 1]}",
            color="#B8C4D1", penwidth=1.8,
            fillcolor="#F2FAEF" if complete else "#F7F8FA",
            fontcolor="#475569", fontname="Helvetica", fontsize=18,
            style="rounded,filled", margin=20, labeljust="l", labelloc="t",
        )
    return compact_layout(dot, sections) if compact else dot


def write_graph_layouts(document):
    """Reuse the rendered graph page, including all theorem modals, in both layouts."""
    graphs = document.userdata["dep_graph"]["graphs"]
    if document not in graphs:
        return []
    compact_path = Path("dep_graph_document.html")
    wide_path = Path("dep_graph_wide.html")
    page = compact_path.read_text(encoding="utf-8")
    before_dot, dot_and_after = page.split(".renderDot(`", 1)
    _, after_dot = dot_and_after.split("`)", 1)
    shapes = document.userdata["dep_graph"].get("shapes", {"definition": "box"})
    for path, layout, target, other, compact, engine in (
        (compact_path, "compact", wide_path, "Wide", True, "nop2"),
        (wide_path, "wide", compact_path, "Compact", False, "dot"),
    ):
        # Graphviz may wrap long spline coordinates with a backslash-newline.
        # Remove that continuation before embedding DOT in a JS template literal.
        dot = graphs[document].to_dot(shapes, compact=compact).to_string()
        dot = dot.replace("\\\n", "").replace("\n", "")
        html = before_dot + f'.engine("{engine}").renderDot(`' + dot + "`)" + after_dot
        if html.count("<header>") != 1 or html.count("</header>") != 1:
            raise ValueError("Expected one dependency graph page header")
        html = html.replace("<header>", '<header class="graph-header">', 1)
        html = html.replace("</title>", f" — {layout} layout</title>", 1)
        html = html.replace(
            "</header>",
            f'<a class="graph-layout-switch" href="{target.name}">{other} layout</a>\n</header>',
            1,
        )
        path.write_text(html, encoding="utf-8")
    return [wide_path.name]


def write_repository_navigation(document):
    """Add the configured repository to each rendered page's main header."""
    repository = escape(document.userdata["project_github"], quote=True)
    link = (f'<a class="repository-link" href="{repository}" '
            'aria-label="GitHub repository">GitHub</a>')
    for path in Path.cwd().glob("*.html"):
        html = path.read_text(encoding="utf-8")
        header = re.search(r'(<body\b[^>]*>\s*<header\b[^>]*>)(.*?)(</header>)', html, re.S)
        if not header:
            raise ValueError(f"Expected a main header in {path.name}")
        body = header[2]
        if 'class="repository-link"' in body:
            continue
        switch = re.search(r'<a class="graph-layout-switch"[^>]*>.*?</a>', body, re.S)
        links = link
        if switch:
            body = body.replace(switch[0], "")
            links = switch[0] + "\n" + link
        navigation = f'<nav class="header-links" aria-label="Project links">{links}</nav>\n'
        html = html[:header.start()] + header[1] + body + navigation + header[3] + html[header.end():]
        path.write_text(html, encoding="utf-8")
    return []


def ProcessOptions(options, document):
    # Registered after depgraph's HTML callback: each build starts with its fresh
    # page, then adds navigation and the wide version without copying its template.
    document.addPackageResource([PackagePreCleanupCB(data=write_graph_layouts),
                                 PackagePreCleanupCB(data=write_repository_navigation)])

    def add_manuscript_labels():
        metadata = run_path(str(MAP_SCRIPT))
        annotations = metadata["graph_annotations"]()
        sections = metadata["graph_sections"]()
        for graph in document.userdata["dep_graph"]["graphs"].values():
            # plastexdepgraph 0.0.5 hardcodes its short labels. Keep its generated
            # graph and its Lean proof flags intact and set the presentation.
            graph.to_dot = partial(labeled_dot, graph, graph.to_dot, annotations,
                                   sections, metadata["SECTION_NAMES"])
        document.userdata["dep_graph"]["legend"].append(
            ("Pale amber background", "Lean proves components of the statement. The full manuscript proof remains open.")
        )
        document.userdata["dep_graph"]["legend"].extend([
            ("Faint green section background", "All proofs and definitions in this section group are formalized."),
            ("Faint gray section background", "Some proofs or definitions in this section group remain to be formalized."),
        ])

    # plastexdepgraph constructs the document graphs at priority 110.
    document.addPostParseCallbacks(120, add_manuscript_labels)

    def correct_statement_border():
        # leanblueprint labels this border with the proof fill color, but draws
        # it with the statement color. The two colors differ in our palette.
        graph = document.userdata["dep_graph"]
        for i, (_, description) in enumerate(graph["legend"]):
            if description == "the <em>statement</em> of this result is formalized":
                graph["legend"][i] = (f"{graph['colors']['stated'][1]} border", description)
                break

    # leanblueprint builds its legend at priority 150.
    document.addPostParseCallbacks(160, correct_statement_border)
