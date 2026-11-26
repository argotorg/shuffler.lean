"""Parse generator graph data and unfold graphs for a terminal with shared-node links."""
from dataclasses import dataclass

from Coordinator.watch import bounded_json


@dataclass(frozen=True)
class Block:
    id: str
    offset: int | None
    kind: str
    calls: tuple[str, ...] = ()


@dataclass(frozen=True)
class Edge:
    source: str
    target: str
    label: str = ""


@dataclass(frozen=True)
class Function:
    id: str
    label: str
    callees: tuple[str, ...]
    blocks: tuple[Block, ...]
    edges: tuple[Edge, ...]
    error: str


@dataclass(frozen=True)
class Obligation:
    fn: str
    name: str
    deps: tuple[tuple[str, str], ...] = ()

    @property
    def id(self):
        return self.fn + "/" + self.name


@dataclass(frozen=True)
class Graph:
    functions: tuple[Function, ...]
    obligations: tuple[Obligation, ...] = ()

    def function(self, name):
        return next((f for f in self.functions if f.id == name), None)


def string(value):
    if not isinstance(value, str):
        raise ValueError("graph field must be text")
    return value


def array(value):
    if not isinstance(value, list) or len(value) > 10000:
        raise ValueError("graph field must be a bounded list")
    return value


def unique(names):
    if any(not n for n in names) or len(set(names)) != len(names):
        raise ValueError("graph identifiers must be nonempty and unique")


def parse_graph(value):
    if type(value["version"]) is not int or value["version"] != 1:
        raise ValueError("unknown graph version")
    functions = []
    for f in array(value["functions"]):
        blocks, edges = [], []
        for b in array(f["blocks"]):
            offset, kind = b["offset"], b["kind"]
            if offset is not None and (type(offset) is not int or offset < 0):
                raise ValueError("block offset must be nonnegative")
            if kind not in ("block", "branch", "call", "return", "trap"):
                raise ValueError("unknown block kind")
            blocks.append(Block(string(b["id"]), offset, kind, tuple(string(c) for c in array(b.get("calls", [])))))
        names = [b.id for b in blocks]
        unique(names)
        for e in array(f["edges"]):
            edge = Edge(string(e["from"]), string(e["to"]), string(e["label"]))
            if edge.source not in names or edge.target not in names:
                raise ValueError("CFG edge has no block")
            edges.append(edge)
        functions.append(Function(string(f["id"]), string(f["label"]),
                                  tuple(string(c) for c in array(f["callees"])),
                                  tuple(blocks), tuple(edges), string(f["error"])))
    unique([f.id for f in functions])
    return Graph(tuple(functions))


def read_graph(run):
    try:
        return parse_graph(bounded_json(run / "graph.json", 32 * 1024 * 1024))
    except (OSError, ValueError, TypeError, KeyError, AttributeError):
        return None


def parse_rows(value):
    """Parse one function's current generated rows, including rows added during search."""
    if type(value["version"]) is not int or value["version"] != 1:
        raise ValueError("unknown row graph version")
    fn = string(value["fn"])
    if not fn:
        raise ValueError("row function must be nonempty")
    rows = []
    for row in array(value["rows"]):
        deps = tuple(dict.fromkeys((string(d["fn"]), string(d["name"])) for d in array(row["deps"])))
        if any(not f or not n for f, n in deps):
            raise ValueError("row dependencies must have a function and name")
        rows.append(Obligation(fn, string(row["name"]), deps))
    unique([r.name for r in rows])
    return tuple(rows)


def read_rows(run):
    rows = []
    for path in sorted((run / "row-graphs").glob("*.json"))[:10000]:
        try:
            rows.extend(parse_rows(bounded_json(path, 4 * 1024 * 1024)))
        except (OSError, ValueError, TypeError, KeyError, AttributeError):
            continue
    return tuple(rows)


def merge_runtime(graph, inventory=(), journal=(), active=()):
    """Merge current dependencies, journal rows, and active jobs without changing the CFG."""
    functions = {f.id: f for f in graph.functions} if graph else {}
    rows = {(r.fn, r.name): r for r in graph.obligations} if graph else {}
    rows.update(((r.fn, r.name), r) for r in inventory)
    for fn, name in tuple(journal) + tuple(active):
        rows.setdefault((fn, name), Obligation(fn, name))
    for row in tuple(rows.values()):
        for fn, name in row.deps:
            rows.setdefault((fn, name), Obligation(fn, name))
    for fn, _ in rows:
        functions.setdefault(fn, Function(fn, fn, (), (), (), ""))
    return Graph(tuple(functions.values()), tuple(rows.values())) if functions or rows or graph else None


@dataclass(frozen=True)
class GraphRow:
    node: str
    prefix: str = ""
    edge: str = ""
    reference: str = ""


def outline(nodes, edges, roots=()):
    """Expand each node once. Keep each join and back edge as a selectable reference."""
    children = {n: [] for n in nodes}
    for edge in edges:
        children.setdefault(edge.source, []).append(edge)
        children.setdefault(edge.target, [])
    incoming = {e.target for e in edges}
    roots = roots or tuple(n for n in children if n not in incoming)
    rows, seen = [], set()
    for root in tuple(roots) + tuple(children):
        if root in seen:
            continue
        stack = [(root, (), "", frozenset())]
        while stack:
            node, guides, label, ancestors = stack.pop()
            prefix = "".join("   " if last else "│  " for last in guides[:-1])
            if guides:
                prefix += "└─ " if guides[-1] else "├─ "
            reference = "loop" if node in ancestors else "shared" if node in seen else ""
            rows.append(GraphRow(node, prefix, label, reference))
            if reference:
                continue
            seen.add(node)
            links = children[node]
            for i in range(len(links) - 1, -1, -1):
                edge = links[i]
                stack.append((edge.target, guides + (i == len(links) - 1,), edge.label, ancestors | {node}))
    return tuple(rows)


def call_rows(graph):
    if graph is None:
        return ()
    return outline(tuple(f.id for f in graph.functions),
                   tuple(Edge(f.id, c) for f in graph.functions for c in f.callees))


def cfg_rows(graph, name):
    fn = graph.function(name) if graph else None
    if fn is None:
        return ()
    names = tuple(b.id for b in fn.blocks)
    return outline(names, fn.edges, ("entry",) if "entry" in names else names[:1])


def row_rows(graph, name=""):
    if graph is None:
        return ()
    rows = tuple(r for r in graph.obligations if not name or r.fn == name)
    return outline(tuple(r.id for r in rows),
                   tuple(Edge(r.id, fn + "/" + dep) for r in rows for fn, dep in r.deps))
