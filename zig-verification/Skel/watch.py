#!/usr/bin/env python3
"""Read-only terminal dashboard for `skel full`. Uses the Python standard library."""
from __future__ import annotations

import argparse
from collections import Counter
import curses
from dataclasses import dataclass, field, replace
import locale
import math
import os
from pathlib import Path
import re
import sys

from Coordinator import prove_watch, watch
from Skel import watch_graph, watch_jobs

CHUNK = 8 * 1024 * 1024
LIMIT = 2 * 1024 * 1024


@dataclass(frozen=True)
class Row:
    fn: str
    name: str
    status: str
    rung: str = ""
    detail: str = ""
    model: str = ""
    cost_micro: int = 0

    @staticmethod
    def parse(value):
        if not isinstance(value, dict):
            raise ValueError("row must be an object")
        fn, name, status = value.get("fn"), value.get("name"), value.get("st")
        if not isinstance(fn, str) or not fn or not isinstance(name, str) or not name:
            raise ValueError("row needs a function and a name")
        if not isinstance(status, dict) or len(status) != 1:
            raise ValueError("row needs one status")
        kind, data = next(iter(status.items()))
        fields = {"closed": ("closed", "rung"), "open": ("open", "firstError"),
                  "notGenerated": ("not generated", "cause")}
        if kind not in fields or not isinstance(data, dict):
            raise ValueError("unknown row status")
        label, key = fields[kind]
        text = data.get(key)
        if not isinstance(text, str):
            raise ValueError("row status needs text")
        if kind == "closed" and data.get("how") not in ("tactics", "model", "prove", "replay"):
            raise ValueError("unknown row closure")
        model, cost = value.get("model", ""), value.get("costMicro", 0)
        if not isinstance(model, str) or type(cost) is not int or cost < 0:
            raise ValueError("invalid row model or cost")
        return Row(fn, name, label, text if kind == "closed" else "", text if kind != "closed" else "", model, cost)


@dataclass(frozen=True)
class Cursor:
    offset: int = 0
    tail: bytes = b""
    identity: tuple | None = None
    discard: bool = False


def advance(path, cursor):
    """Read complete lines only. Restart after replacement or truncation; bound line memory."""
    with path.open("rb") as source:
        stat = os.fstat(source.fileno())
        identity = stat.st_dev, stat.st_ino
        restarted = cursor.identity is not None and (identity != cursor.identity or stat.st_size < cursor.offset)
        if restarted:
            cursor = Cursor()
        source.seek(cursor.offset)
        chunk = source.read(CHUNK)
    parts = (cursor.tail + chunk).split(b"\n")
    tail = parts.pop()
    discard, skipped = cursor.discard, 0
    if discard and parts:
        parts.pop(0)
        discard = False
    lines = [p for p in parts if len(p) <= LIMIT]
    skipped += len(parts) - len(lines)
    if discard or len(tail) > LIMIT:
        skipped += not discard
        tail, discard = b"", True
    return (lines, Cursor(cursor.offset + len(chunk), tail, identity, discard), stat.st_mtime,
            cursor.offset + len(chunk) < stat.st_size, restarted, skipped)


@dataclass(frozen=True)
class Proof:
    path: Path
    fn: str
    name: str
    run: prove_watch.Run = prove_watch.Run()
    updated: float = 0
    outcome: str = ""
    result: str = ""
    detail: str = ""


def summary_result(summary, fn, name):
    """Old h1 records accept both proofs and disproofs. Match the checked target."""
    if not isinstance(summary, dict):
        return ""
    outcome, report = summary.get("outcome"), summary.get("report", "")
    if outcome != "accepted" or not isinstance(report, str) or not report.startswith("Accepted: "):
        return ""
    target = re.escape(fn + "." + name)
    pattern = r"(?:^|[ ,;])(?:[\w']+\.)*" + target + r" disproved(?:,|;|$)"
    return "disproof" if re.search(pattern, report) else ""


@dataclass(frozen=True)
class View:
    run: Path | None = None
    rows: dict = field(default_factory=dict)
    workers: tuple[Proof, ...] = ()
    skipped: int = 0
    behind: bool = False
    ledger: dict | None = None
    books: tuple = ()
    updated: float = 0
    feed: tuple[str, ...] = ()
    cap: float | None = None
    asks: tuple[watch_jobs.Ask, ...] = ()
    jobs: watch_jobs.Jobs = watch_jobs.Jobs()
    graph: watch_graph.Graph | None = None


def read_book(path):
    """Account totals include prior runs and live reservations, not just this campaign."""
    def amount(value):
        if type(value) not in (int, float):
            raise ValueError("account amount must be a number")
        number = float(value)
        if not math.isfinite(number) or number < 0:
            raise ValueError("account amount must be finite and nonnegative")
        return number

    try:
        data = watch.bounded_json(path, 32 * 1024 * 1024)
        spent = amount(data["spentUsd"])
        reservations = data.get("reservations")
        if reservations is None:
            reservations = []
        if not isinstance(reservations, list):
            raise ValueError("reservations must be a list")
        reserved = sum(amount(r["boundUsd"]) for r in reservations)
        if not math.isfinite(reserved):
            raise ValueError("invalid account totals")
        return (str(path), spent, reserved, "")
    except (OSError, ValueError, TypeError, KeyError, AttributeError, OverflowError) as error:
        return (str(path), 0, 0, watch.clean(error))


class Monitor:
    """Read journals and h1 events. Never write files, start tools, or call a model."""
    def __init__(self, run=None, root=Path("."), out=None, budgets=(), cap=None, proc_root=Path("/proc")):
        self.root = Path(root).resolve()
        self.run = self.path(run) if run is not None else None
        self.out = self.path(out) if out is not None else None
        self.budgets = tuple(dict.fromkeys(self.path(p).resolve() for p in budgets))
        self.cap = cap
        self.proc_root = proc_root
        self.cursor, self.log_cursor = Cursor(), Cursor()
        self.rows, self.proofs, self.cursors = {}, {}, {}
        self.skipped, self.updated = 0, 0
        self.feed = ()

    def path(self, path):
        path = Path(path)
        return path if path.is_absolute() else self.root / path

    def discover(self):
        if self.run is None:
            paths = [p for p in (self.root / ".skel/runs").glob("*-full*")
                     if p.is_dir() and re.fullmatch(r"\d{8}T\d{6}Z-full(?:-\d+)?", p.name)]
            self.run = max(paths, key=lambda p: (p.stat().st_mtime_ns, p.name), default=None)

    def read_rows(self):
        try:
            lines, cursor, updated, behind, restarted, skipped = advance(self.run / "rows.jsonl", self.cursor)
        except OSError:
            return False
        if restarted:
            self.rows = {}
        self.cursor, self.updated = cursor, max(self.updated, updated)
        self.skipped += skipped
        for line in lines:
            try:
                row = Row.parse(watch.load_json(line))
                self.rows[(row.fn, row.name)] = row
            except (ValueError, TypeError, KeyError):
                self.skipped += 1
        return behind

    def read_proofs(self):
        # Match exact frozen file names. Do not read their source or decode ambiguous underscores.
        frozen = {}
        for pattern in ("prove/*/**/*.lean",):
            for file in self.run.glob(pattern):
                fn = file.relative_to(self.run).parts[1]
                for name in (str(file), os.path.relpath(file, self.root)):
                    frozen[name.replace("/", "_")] = (fn, file.stem)
        behind = False
        for path in sorted((self.root / ".leantools/runs").glob("*")):
            match = re.fullmatch(prove_watch.STAMP + r"-(.+)", path.name)
            if not match or match[1] not in frozen or not path.is_dir():
                continue
            fn, name = frozen[match[1]]
            proof = self.proofs.get(path, Proof(path, fn, name))
            try:
                lines, cursor, updated, more, restarted, skipped = advance(
                    path / "events.jsonl", self.cursors.get(path, Cursor()))
            except OSError:
                continue
            self.cursors[path] = cursor
            self.skipped += skipped
            behind = behind or more
            run = prove_watch.Run() if restarted else proof.run
            for line in lines:
                try:
                    run = prove_watch.step(run, watch.load_json(line))
                except (ValueError, TypeError, KeyError, AttributeError):
                    self.skipped += 1
            outcome, result, detail = "", "", ""
            try:
                summary = watch.bounded_json(path / "summary.json", LIMIT)
                outcome = str(summary["outcome"])
                result = summary_result(summary, fn, name)
                if result == "disproof":
                    detail = f"{name}: disproved; the validator accepted a proof of the negation."
            except (OSError, ValueError, TypeError, KeyError):
                pass
            self.proofs[path] = replace(proof, run=run, updated=updated, outcome=outcome,
                                        result=result, detail=detail)
            self.updated = max(self.updated, updated)
        self.read_import_results()
        return behind

    def read_import_results(self):
        """Associate the campaign importer verdict with its exact h1 run directory."""
        known = {str(path.resolve()): path for path in self.proofs}
        for pattern in ("prove/*/**/invocations/*/result.json",):
            for path in self.run.glob(pattern):
                try:
                    record = watch.bounded_json(path, LIMIT)
                    result = record["result"]
                    if result["kind"] != "reply":
                        continue
                    reply = result["reply"]
                    directory = reply["runDir"]
                    if not isinstance(directory, str) or not directory:
                        continue
                    directory = self.path(directory).resolve()
                    key = known.get(str(directory))
                    if key is None:
                        continue
                    proof = self.proofs[key]
                    if record["row"] != proof.name or path.relative_to(self.run).parts[1] != proof.fn:
                        continue
                    kind = reply.get("result")
                    # Older campaign records retain the extraction reason but no typed result.
                    if kind is None and proof.result != "disproof" and proof.outcome == "accepted":
                        kind = "proof" if isinstance(reply.get("proof"), str) else "extraction-failure"
                    if kind not in ("proof", "disproof", "extraction-failure", "unfinished"):
                        continue
                    reason = reply.get("why", "")
                    if not isinstance(reason, str):
                        continue
                    self.proofs[key] = replace(proof, result=kind, detail=reason or proof.detail)
                except (OSError, ValueError, TypeError, KeyError, AttributeError):
                    continue

    def read_feed(self):
        try:
            lines, cursor, _, behind, restarted, skipped = advance(self.run / "rungs.log", self.log_cursor)
        except OSError:
            return False
        self.log_cursor = cursor
        self.skipped += skipped
        self.feed = (() if restarted else self.feed) + tuple(watch.clean(l.decode(errors="replace")) for l in lines[-8:])
        self.feed = self.feed[-8:]
        return behind

    def ledger(self):
        if self.out is None:
            return None
        try:
            path = self.out / "ledger.json"
            # An old report must not label a new campaign as complete.
            cutoff = max(self.run.stat().st_mtime, (self.run / "rows.jsonl").stat().st_mtime)
            if path.stat().st_mtime < cutoff:
                return None
            value = watch.bounded_json(path, 32 * 1024 * 1024)
            if not isinstance(value, dict) or not isinstance(value.get("obligations"), list):
                return None
            if not all(isinstance(row, dict) and all(isinstance(row.get(k), str) for k in
                       ("function", "name", "kind", "status")) for row in value["obligations"]):
                return None
            composition = value.get("composition")
            if not isinstance(composition, dict) or composition.get("state") not in ("proved", "blocked"):
                return None
            return value
        except (OSError, ValueError, TypeError):
            return None

    def refresh(self):
        self.discover()
        behind = False
        if self.run is not None:
            behind = self.read_rows()
            behind = self.read_proofs() or behind
            behind = self.read_feed() or behind
        jobs = watch_jobs.read_jobs(self.root, self.run, self.out, self.proc_root) if self.run else watch_jobs.Jobs()
        return View(self.run, dict(self.rows), tuple(self.proofs.values()), self.skipped, behind,
                    self.ledger() if self.run is not None else None,
                    tuple(read_book(p) for p in self.budgets), self.updated, self.feed, self.cap, jobs.asks, jobs,
                    watch_graph.merge_runtime(watch_graph.read_graph(self.run), watch_graph.read_rows(self.run),
                                              self.rows, tuple(jobs.proof_rows) + tuple((a.fn, a.name) for a in jobs.asks))
                    if self.run else None)


def proof_status(proof, jobs=watch_jobs.Jobs()):
    if proof.result == "disproof":
        return "disproved"
    if proof.result == "extraction-failure":
        return "import rejected"
    return proof.outcome or ("running" if (proof.fn, proof.name) in jobs.proof_rows else "no end record")


def visible_workers(view, active_only):
    return tuple(p for p in view.workers if not active_only or not p.outcome) + view.asks


def function_rows(view):
    names = sorted({r.fn for r in view.rows.values()} | {p.fn for p in view.workers} | {a.fn for a in view.asks}
                   | {f.id for f in (view.graph.functions if view.graph else ())})
    return [(fn, Counter(r.status for r in view.rows.values() if r.fn == fn)) for fn in names]


def table_slots(view, height):
    results = any(p.result in ("disproof", "extraction-failure") for p in view.workers)
    return max(1, height - 18 - bool(view.books) - bool(view.ledger) - results)


def header_lines(view, width):
    Line = watch.Line
    counts = Counter(r.status for r in view.rows.values())
    attempts = [a for p in view.workers for a in p.run.attempts]
    spent = sum(a.spent for a in attempts) / 1_000_000
    replies = sum(a.replies for a in attempts)
    prompt = sum(a.prompt for a in attempts)
    cached = sum(a.cached for a in attempts)
    lines = [Line("  KRAKEN / SKEL CAMPAIGN" + (" / CATCHING UP" if view.behind else ""), "title"),
             Line(f"  {view.run or 'Waiting for a full run directory'}", "muted"),
             Line(f"  ROW CHECKS  {counts['closed']} passed / {len(view.rows)} recorded"
                  f" | {counts['open']} open | {counts['not generated']} not generated", "accent"),
             Line(f"  H1  {len(view.workers)} runs | {replies} replies | ${spent:.3f} usage cost"
                  f" | cache {cached / prompt if prompt else 0:.0%}", "accent")]
    failures = Counter(p.result for p in view.workers)
    if failures['disproof'] or failures['extraction-failure']:
        lines.append(Line(f"  PROOF RESULTS  {failures['disproof']} disproved | "
                          f"{failures['extraction-failure']} import rejected", "warn"))
    if view.jobs.pid is not None:
        limit = f" / {view.jobs.limit} slots" if view.jobs.limit else ""
        lines.append(Line(f"  MODEL JOBS  {view.jobs.proofs} prove + {len(view.asks)} ask{limit} | pid {view.jobs.pid}", "accent"))
    else:
        lines.append(Line("  MODEL JOBS  local process state unavailable", "muted"))
    if view.books:
        valid = all(not error for _, _, _, error in view.books)
        total = sum(s for _, s, _, _ in view.books)
        reserved = sum(r for _, _, r, _ in view.books)
        if valid:
            cap = f" / ${view.cap:.2f} cap" if view.cap is not None else ""
            lines.append(Line(f"  ACCOUNTS  ${total:.3f} spent + ${reserved:.3f} reserved{cap} (includes prior runs)", "accent"))
        else:
            lines.append(Line("  ACCOUNTS  totals unavailable: cannot read all budget books", "warn"))
    if view.ledger:
        composition = view.ledger.get("composition", {}).get("state", "unknown")
        statements = [r for r in view.ledger["obligations"] if r.get("kind") == "statement"]
        lines.append(Line(f"  FINAL LEDGER  composition {composition} | "
                          f"{sum(s.get('status') == 'closed' for s in statements)} statements available", "good" if composition == "proved" else "warn"))
        final = Counter(r["status"] for r in view.ledger["obligations"] if r["kind"] != "statement")
        lines.append(Line(f"  FINAL ROWS  {final['closed']} closed | {final['open']} open | "
                          f"{final['callee open']} callee open | {final['not generated']} not generated", "accent"))
    else:
        lines.append(Line("  Row checks do not establish function composition. Final ledger is pending.", "muted"))
    try:
        load = " / ".join(f"{v:.1f}" for v in os.getloadavg())
        lines.append(Line(f"  Load 1/5/15 min: {load} | {os.cpu_count()} CPUs | last event {watch.age(view.updated)} ago", "muted"))
    except OSError:
        pass
    lines.append(Line("─" * max(0, width), "border"))
    return lines


def render(view, width, height, selected=0, offset=0, active_only=True, worker_view=False):
    """Render recorded progress; a quiet journal gives no evidence of process state."""
    Line = watch.Line
    lines = header_lines(view, width)
    lines += [Line("  MODEL WORKERS / " + ("PROOFS WITHOUT END RECORD + LIVE ASKS" if active_only else "ALL PROOFS + LIVE ASKS") if worker_view else
                   "  FUNCTIONS / ROW CHECKS RECEIVED", "accent"),
              Line("  FUNCTION / ROW                        KIND   RESULT           REPLIES    COST     TOOL" if worker_view else
                   "  FUNCTION                              PASSED    OPEN   NOT GENERATED", "muted")]
    items = visible_workers(view, active_only) if worker_view else function_rows(view)
    slots = table_slots(view, height)
    for i in range(offset, min(len(items), offset + slots)):
        marker = ">" if i == selected else " "
        if worker_view:
            proof = items[i]
            if isinstance(proof, watch_jobs.Ask):
                text = (f" {marker}{watch.fit(proof.fn + '/' + proof.name, 37)} ask    running          "
                        f"      —       —  {proof.kind} ({proof.elapsed:.0f}s)")
            else:
                a = proof.run.attempts[-1] if proof.run.attempts else None
                cost = sum(x.spent for x in proof.run.attempts) / 1_000_000
                text = (f" {marker}{watch.fit(proof.fn + '/' + proof.name, 37)} prove  {watch.fit(proof_status(proof, view.jobs), 16)} "
                        f"{a.replies if a else 0:>3}/{a.limit if a else 0:<3} ${cost:>6.3f}  {a.tool if a else ''}")
        else:
            fn, c = items[i]
            text = f" {marker}{watch.fit(fn, 37)} {c['closed']:>6} {c['open']:>7} {c['not generated']:>10}"
        lines.append(Line(text, "selected" if i == selected else "normal"))
    if not items:
        lines.append(Line("  Waiting for records.", "muted"))
    while len(lines) < height - 6:
        lines.append(Line(""))
    if items:
        item = items[min(max(0, selected), len(items) - 1)]
        if worker_view and isinstance(item, watch_jobs.Ask):
            lines.append(Line(f"  {item.model} | {item.kind} | pid {item.pid} | {item.elapsed:.0f}s", "accent"))
            detail = item.config + " | one model request; the harness checks its reply"
        elif worker_view:
            a = item.run.attempts[-1] if item.run.attempts else None
            lines.append(Line(f"  {a.model if a else ''} | iteration {a.iteration if a else 0} | {a.activity if a else 'waiting'}", "accent"))
            detail = item.detail or (a.detail if a else "") or str(item.path)
        else:
            fn = item[0]
            open_rows = [r for r in view.rows.values() if r.fn == fn and r.status != "closed"]
            disproved = [p for p in view.workers if p.fn == fn and p.result == "disproof"]
            detail = "\n".join(f"{p.name}: disproved; checked counterexample" for p in disproved[:2])
            fallback = (f"All recorded row checks for {fn} passed." if item[1] else
                        f"No row checks recorded for {fn}.")
            detail = detail or "\n".join(f"{r.name}: {r.detail}" for r in open_rows[:2]) or fallback
        lines.extend(Line("  " + line, "muted") for line in watch.clean(detail).splitlines()[:2])
    lines.append(Line("  " + (view.feed[-1] if view.feed else "No campaign process state is inferred from these records."), "muted"))
    lines.append(Line(f"  {view.skipped} skipped | q close | Tab functions/workers/deps/CFG | g deps | c CFG | j/k select | PgUp/PgDn | a all proofs", "footer"))
    return [Line(watch.fit(line.text, max(0, width)), line.style) for line in lines[:max(0, height)]]


def crop(text, start, width):
    """Pan by terminal columns, including wide and combining characters."""
    out, column = [], 0
    for char in watch.clean(text):
        size = watch.cell_width(char)
        if column >= start:
            out.append(char)
        elif column + size > start:
            out.append(" " * (column + size - start))
        column += size
    return watch.fit("".join(out), max(0, width))


def graph_items(view, state):
    if state.mode == "deps":
        return watch_graph.call_rows(view.graph)
    fn = state.fn or (view.graph.functions[0].id if view.graph and view.graph.functions else "")
    if state.mode == "rows":
        return watch_graph.row_rows(view.graph, fn)
    return watch_graph.cfg_rows(view.graph, fn)


def graph_status(view, fn, block="", name=""):
    names = (name,) if name else ("block." + block, "loop." + block) if block else ()
    live = any(a.fn == fn and (not names or a.name in names) for a in view.asks)
    live = live or any(f == fn and (not names or row in names) for f, row in view.jobs.proof_rows)
    if live:
        return "[*]", "accent"
    rows = [r for r in view.rows.values() if r.fn == fn and (not names or r.name in names)]
    if any(r.status != "closed" for r in rows):
        return "[!]", "warn"
    return ("[+]", "good") if rows else ("[ ]", "muted")


def render_graph(view, width, height, mode="deps", selected=0, offset=0, horizontal=0, fn=""):
    Line = watch.Line
    lines = header_lines(view, width)
    state = Navigation(mode=mode, fn=fn)
    items = graph_items(view, state)
    fn = fn or (view.graph.functions[0].id if view.graph and view.graph.functions else "")
    title = ("DEPENDENCIES / caller → callee" if mode == "deps" else
             f"PROOF DEPENDENCIES / {fn} / row → prerequisite" if mode == "rows" else f"CONTROL FLOW / {fn}")
    lines += [Line("  " + title, "accent"),
              Line("  [*] live model job  [+] recorded rows passed  [!] open rows  [ ] no row record  ↗ shared  ↶ loop", "muted")]
    slots = max(1, height - len(lines) - 6)
    for i in range(offset, min(len(items), offset + slots)):
        row = items[i]
        if mode == "rows":
            row_fn, _, row_name = row.node.partition("/")
            status, style = graph_status(view, row_fn, name=row_name)
        else:
            status, style = graph_status(view, row.node if mode == "deps" else fn, "" if mode == "deps" else row.node)
        edge = row.edge + " → " if row.edge else ""
        ref = " ↶ (loop)" if row.reference == "loop" else " ↗ (shared)" if row.reference else ""
        detail = ""
        if mode == "deps":
            counts = Counter(r.status for r in view.rows.values() if r.fn == row.node)
            if counts:
                detail = f"  {counts['closed']} passed / {counts['open']} open"
        elif mode == "cfg":
            function = view.graph.function(fn)
            block = next((b for b in function.blocks if b.id == row.node), None) if function else None
            if block:
                detail = f"  {block.kind}" + (f" +{block.offset}" if block.offset is not None else "")
                if block.calls:
                    detail = "  call " + ", ".join(block.calls) + (f" +{block.offset}" if block.offset is not None else "")
        body = row.prefix + edge + status + " " + row.node + ref + detail
        lines.append(Line(("> " if i == selected else "  ") + crop(body, horizontal, max(0, width - 2)),
                          "selected" if i == selected else style))
    if not items:
        function = view.graph.function(fn) if view.graph else None
        message = ("No proof rows are recorded for this function." if mode == "rows" else
                   function.error if function and function.error else "No graph data. Run: lake exe skel graph --out RUN/graph.json")
        lines.append(Line("  " + message, "warn"))
    while len(lines) < height - 6:
        lines.append(Line(""))
    if items:
        row = items[min(max(0, selected), len(items) - 1)]
        name = row.node if mode == "deps" else fn
        function = view.graph.function(name)
        if mode == "rows":
            row_fn, _, row_name = row.node.partition("/")
            obligation = next((o for o in view.graph.obligations if (o.fn, o.name) == (row_fn, row_name)), None)
            dependencies = [f"{f}/{n}" for f, n in obligation.deps] if obligation else []
            record = view.rows.get((row_fn, row_name))
            lines += [Line("  " + row.node + " needs: " + (", ".join(dependencies) or "none"), "accent"),
                      Line("  " + (record.detail if record and record.detail else "Only checked closed rows can close their dependent rows."), "muted")]
        elif mode == "deps":
            callers = [f.id for f in view.graph.functions if name in f.callees]
            lines += [Line("  " + name + " calls: " + (", ".join(function.callees) if function and function.callees else "none"), "accent"),
                      Line("  Called by: " + (", ".join(callers) or "none"), "muted")]
        else:
            outgoing = [f"{e.label + ': ' if e.label else ''}{e.target}" for e in function.edges if e.source == row.node] if function else []
            checks = [r for r in view.rows.values() if r.fn == fn and r.name in ("block." + row.node, "loop." + row.node)]
            lines += [Line(f"  {row.node} → " + ("; ".join(outgoing) or "no outgoing edge"), "accent"),
                      Line("  " + (checks[0].detail if checks and checks[0].detail else "Select a block to see its recorded checks."), "muted")]
    lines += [Line(f"  {len(items)} nodes/links | scroll {offset + 1 if items else 0} | horizontal {horizontal} | Proof rows and status update live.", "muted"),
              Line("  Tab views | o proof rows | Enter/c CFG | g/Backspace deps | [/] function | j/k select | PgUp/PgDn | h/l pan | q close", "footer")]
    return [Line(watch.fit(line.text, max(0, width)), line.style) for line in lines[:max(0, height)]]


MODES = ("functions", "workers", "deps", "cfg", "rows")


@dataclass(frozen=True)
class Navigation:
    mode: str = "functions"
    selected: int = 0
    offset: int = 0
    horizontal: int = 0
    fn: str = ""
    active_only: bool = True


def navigation_items(view, state):
    if state.mode in ("deps", "cfg", "rows"):
        return graph_items(view, state)
    return visible_workers(view, state.active_only) if state.mode == "workers" else function_rows(view)


def selected_function(view, state):
    items = navigation_items(view, state)
    if not items:
        return state.fn
    item = items[min(max(0, state.selected), len(items) - 1)]
    return (item.node if state.mode == "deps" else item.node.partition("/")[0] if state.mode == "rows" else
            state.fn if state.mode == "cfg" else item.fn if state.mode == "workers" else item[0])


def navigate(state, key, view, slots):
    items = navigation_items(view, state)
    name = selected_function(view, state)
    if key in ("tab", "deps", "cfg", "rows", "enter", "back"):
        mode = (MODES[(MODES.index(state.mode) + 1) % len(MODES)] if key == "tab" else
                "deps" if key in ("deps", "back") else "rows" if key == "rows" else "cfg")
        next_state = replace(state, mode=mode, fn=name, selected=0, offset=0, horizontal=0)
        if mode == "deps":
            rows = graph_items(view, next_state)
            next_state = replace(next_state, selected=next((i for i, r in enumerate(rows) if r.node == name), 0))
        return next_state
    if key in ("prev_fn", "next_fn") and view.graph and view.graph.functions:
        names = [f.id for f in view.graph.functions]
        index = names.index(state.fn) if state.fn in names else 0
        return replace(state, mode="rows" if state.mode == "rows" else "cfg",
                       fn=names[(index + (1 if key == "next_fn" else -1)) % len(names)], selected=0, offset=0)
    changes = {"down": 1, "up": -1, "page_down": slots, "page_up": -slots}
    if key in changes:
        return replace(state, selected=max(0, min(len(items) - 1, state.selected + changes[key])))
    if key in ("left", "right"):
        return replace(state, horizontal=max(0, state.horizontal + (12 if key == "right" else -12)))
    if key in ("home", "end"):
        return replace(state, selected=0 if key == "home" else max(0, len(items) - 1))
    if key == "all":
        return replace(state, active_only=not state.active_only, selected=0, offset=0)
    return state


def terminal(screen, monitor, interval, mode="functions", fn=""):
    curses.curs_set(0)
    screen.timeout(round(interval * 1000))
    styles = watch.make_styles()
    state = Navigation(mode=mode, fn=fn)
    while True:
        view = monitor.refresh()
        height, width = screen.getmaxyx()
        items = navigation_items(view, state)
        selected = max(0, min(state.selected, len(items) - 1))
        slots = table_slots(view, height)
        offset = max(0, min(state.offset, selected, len(items) - slots))
        if selected >= offset + slots:
            offset = selected - slots + 1
        state = replace(state, selected=selected, offset=offset)
        screen.erase()
        lines = (render_graph(view, width - 1, height, state.mode, selected, offset, state.horizontal, state.fn)
                 if state.mode in ("deps", "cfg", "rows") else
                 render(view, width - 1, height, selected, offset, state.active_only, state.mode == "workers"))
        for row, line in enumerate(lines):
            try:
                screen.addstr(row, 0, line.text, styles[line.style])
            except curses.error:
                pass
        screen.refresh()
        key = screen.getch()
        if key in (ord("q"), ord("Q"), 27):
            return
        keys = {curses.KEY_DOWN: "down", ord("j"): "down", curses.KEY_UP: "up", ord("k"): "up",
                curses.KEY_NPAGE: "page_down", curses.KEY_PPAGE: "page_up", 9: "tab",
                ord("g"): "deps", ord("c"): "cfg", ord("o"): "rows", 10: "enter", 13: "enter",
                curses.KEY_BACKSPACE: "back", 127: "back", ord("["): "prev_fn", ord("]"): "next_fn",
                ord("h"): "left", curses.KEY_LEFT: "left", ord("l"): "right", curses.KEY_RIGHT: "right",
                curses.KEY_HOME: "home", curses.KEY_END: "end", ord("a"): "all", ord("A"): "all"}
        state = navigate(state, keys.get(key, ""), view, slots)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("run", nargs="?", type=Path, help="run directory (default: newest local full run; stays on that run)")
    parser.add_argument("--out", type=Path, help="the matching skel --out directory, for the final ledger")
    parser.add_argument("--budget", action="append", type=Path, default=[], help="budget book; repeat for each account")
    parser.add_argument("--total-max-usd", type=float, help="display the shared account cap")
    parser.add_argument("--once", action="store_true", help="print one plain-text view")
    parser.add_argument("--workers", action="store_true", help="start with the model worker table (also with --once)")
    parser.add_argument("--view", choices=MODES, default="functions", help="start with functions, workers, deps, cfg or rows")
    parser.add_argument("--fn", default="", help="function shown in the CFG or proof-row view")
    parser.add_argument("--interval", type=float, default=1.0, help="refresh interval in seconds")
    args = parser.parse_args(argv)
    if not 0.1 <= args.interval <= 60:
        parser.error("--interval must be between 0.1 and 60 seconds")
    if args.total_max_usd is not None and not 0 < args.total_max_usd < float("inf"):
        parser.error("--total-max-usd must be finite and above zero")
    monitor = Monitor(args.run, out=args.out, budgets=args.budget, cap=args.total_max_usd)
    mode = "workers" if args.workers else args.view
    if args.once:
        view = monitor.refresh()
        while view.behind:
            view = monitor.refresh()
        items = navigation_items(view, Navigation(mode=mode, fn=args.fn))
        height = max(40, len(items) + 22)
        lines = (render_graph(view, 160, height, mode, fn=args.fn) if mode in ("deps", "cfg", "rows") else
                 render(view, 160, height, worker_view=mode == "workers"))
        print("\n".join(line.text.rstrip() for line in lines))
        return 0
    if not sys.stdin.isatty() or not sys.stdout.isatty():
        parser.error("use --once for plain text, or use an interactive terminal")
    locale.setlocale(locale.LC_ALL, "")
    try:
        curses.wrapper(terminal, monitor, args.interval, mode, args.fn)
    except KeyboardInterrupt:
        pass
    except curses.error as error:
        parser.exit(1, f"Terminal error: {error}. Use --once for plain text.\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
