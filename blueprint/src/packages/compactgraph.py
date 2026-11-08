"""Pack manuscript sections without changing the proof dependency graph."""

import re

from pygraphviz import AGraph


def _node_attributes(node):
    attributes = dict(node.attr)
    # pygraphviz strips the outer delimiter when reading an HTML label.
    # Restore it when copying the node, so Graphviz measures the rendered text.
    if attributes.get("label", "").startswith("<"):
        attributes["label"] = "<" + attributes["label"] + ">"
    return attributes


def _translate_positions(text, dx, dy):
    """Translate Graphviz points, bounding boxes, and spline control points."""
    return re.sub(
        r"([es],)?(-?\d+(?:\.\d+)?),(-?\d+(?:\.\d+)?)",
        lambda match: (
            f"{match[1] or ''}{float(match[2]) + dx},{float(match[3]) + dy}"
        ),
        text,
    )


def compact_layout(dot, sections):
    """Lay out §3 above (§5, §4, §6), with §1 centered below them.

    Each section keeps its own DOT layout and internal edge splines. Packing
    those rectangles explicitly avoids global ranking constraints stretching
    a small section or moving a section into the wrong row. The ``nop2`` engine
    preserves this geometry and routes the remaining edges as smooth splines.
    """
    expected = {1, 3, 4, 5, 6}
    nodes = sorted(dot.nodes(), key=str)
    edges = sorted(dot.edges(), key=lambda edge: (str(edge[0]), str(edge[1])))
    present = {sections[str(node)] for node in nodes}
    if present != expected:
        raise ValueError(f"Compact layout expects sections {sorted(expected)}, got {sorted(present)}")
    if any(edge.attr.get("layout_only") == "true" for edge in edges):
        raise ValueError("Compact layout expects only proof dependency edges")

    section_data = {}
    for section in sorted(expected):
        outer = dot.get_subgraph(f"cluster_spacing_{section}")
        inner = outer.get_subgraph(f"cluster_section_{section}")
        names = [str(node) for node in nodes if sections[str(node)] == section]
        section_data[section] = outer, inner, names

    local = {}
    for section, (outer, inner, names) in section_data.items():
        graph = AGraph(directed=True, strict=True)
        # Leave room for neato's enlarged ellipse obstacles; tighter spacing
        # makes its spline router fall back to straight lines through nodes.
        # The larger horizontal spacing in Robustness gives it about two-thirds
        # of the middle row's width while its proof flows down to Theorem 3.4.
        graph.graph_attr.update(rankdir="TB", nodesep="1.85" if section == 3 else ".45",
                                ranksep=".45")
        graph.node_attr.update(dot.node_attr)
        graph.edge_attr.update(dot.edge_attr)
        for name in names:
            graph.add_node(name, **_node_attributes(dot.get_node(name)))
        members = set(names)
        for edge in edges:
            if str(edge[0]) in members and str(edge[1]) in members:
                graph.add_edge(*edge, **dict(edge.attr))
        wrapper = graph.add_subgraph(names, name=outer.name, **dict(outer.graph_attr))
        cluster = wrapper.add_subgraph(names, name=inner.name, **dict(inner.graph_attr))
        if section == 3:
            cluster.add_subgraph(["thm:bound-fidelity-gradient-flow"],
                                 name="layout_robustness_result", rank="sink")
        graph.layout(prog="dot")
        if section == 3:
            # Make the main result the centered endpoint of the section. Its
            # incoming curves are rerouted below after all positions are fixed.
            left, _, right, _ = map(float, cluster.graph_attr["bb"].split(","))
            main_result = graph.get_node("thm:bound-fidelity-gradient-flow")
            _, y = map(float, main_result.attr["pos"].split(","))
            main_result.attr["pos"] = f"{(left + right) / 2},{y}"
            for edge in graph.in_edges(main_result):
                edge.attr["pos"] = ""
        x0, y0, x1, y1 = map(float, graph.graph_attr["bb"].split(","))
        local[section] = graph, x1 - x0, y1 - y0

    gap = 50
    middle = (5, 4, 6)
    middle_width = sum(local[section][1] for section in middle) + 2 * gap
    width = max(local[3][1], middle_width, local[1][1])
    middle_height = max(local[section][2] for section in middle)
    middle_y = local[1][2] + gap
    top_y = middle_y + middle_height + gap
    origins = {
        1: ((width - local[1][1]) / 2, 0),
        3: ((width - local[3][1]) / 2, top_y),
    }
    x = (width - middle_width) / 2
    for section in middle:
        # Match the top edges while retaining each section's natural height.
        origins[section] = x, middle_y + middle_height - local[section][2]
        x += local[section][1] + gap

    result = AGraph(directed=True, strict=True)
    result.graph_attr.update(dot.graph_attr)
    result.node_attr.update(dot.node_attr)
    result.edge_attr.update(dot.edge_attr)
    for node in nodes:
        result.add_node(str(node), **_node_attributes(node))
    for edge in edges:
        result.add_edge(*edge, **dict(edge.attr))
    for section, (outer, inner, names) in section_data.items():
        graph, _, _ = local[section]
        dx, dy = origins[section]
        # nop2 supports flat clusters. Copy their already padded DOT boxes,
        # including heading positions, instead of using invisible wrapper nodes.
        cluster = result.add_subgraph(names, name=inner.name, **dict(inner.graph_attr))
        positioned = graph.get_subgraph(outer.name).get_subgraph(inner.name)
        for attribute in ("bb", "lp"):
            cluster.graph_attr[attribute] = _translate_positions(
                positioned.graph_attr[attribute], dx, dy
            )
        for node in graph.nodes():
            result.get_node(str(node)).attr.update(
                pos=_translate_positions(node.attr["pos"], dx, dy),
                pin="true", width=node.attr["width"], height=node.attr["height"],
            )
        for edge in graph.edges():
            result.get_edge(*edge).attr["pos"] = _translate_positions(edge.attr["pos"], dx, dy)

    # Internal splines are already present. Only cross-section dependencies
    # need routing. Smooth splines avoid both node text and right-angle bends.
    result.graph_attr.update(layout="nop2", overlap="true", splines="true")
    result.layout(prog="dot", args="-Knop2")
    return result
