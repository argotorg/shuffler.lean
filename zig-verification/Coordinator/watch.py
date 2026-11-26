#!/usr/bin/env python3
"""A read-only terminal view of coordinator run records. Uses the Python standard library."""
from __future__ import annotations

import argparse
from collections import deque
import curses
from dataclasses import dataclass, replace
from decimal import Decimal
import json
import locale
from pathlib import Path
import re
import sys
import time
import unicodedata

MAX_ARTIFACT = 256 * 1024
MAX_LINE = 2 * 1024 * 1024


def integer(text):
    if len(text) > 40000:
        raise ValueError("integer exceeds the display limit")
    return int(text) if len(text) < 4000 else int(Decimal(text))


def load_json(data):
    return json.loads(data, parse_int=integer)


def bounded_json(path, limit=MAX_ARTIFACT):
    with path.open("rb") as source:
        data = source.read(limit + 1)
    if len(data) > limit:
        raise ValueError("record exceeds the display limit")
    return load_json(data)


def clean(text):
    # Artifacts can contain terminal escapes. Only the dashboard controls the terminal.
    return "".join(c if c == "\n" or not unicodedata.category(c).startswith("C") else " "
                   for c in str(text)).replace("\t", " ")


def cell_width(text):
    return sum(0 if unicodedata.combining(c) else 2 if unicodedata.east_asian_width(c) in "WF" else 1
               for c in text)


def fit(text, width):
    text = clean(text).replace("\n", " ")
    out, used = [], 0
    for c in text:
        size = cell_width(c)
        if used + size > width:
            break
        out.append(c)
        used += size
    return "".join(out) + " " * max(0, width - used)


def certificate(number):
    if not isinstance(number, int) or number < 0 or number.bit_length() > 140000:
        return {}
    data = bytearray()
    try:
        while number:
            number, digit = divmod(number, 257)
            data.append(digit - 1)
        value = load_json(data)
        return value if isinstance(value, dict) else {}
    except (ValueError, TypeError, UnicodeError):
        return {}


def closed_goals(number):
    rules = certificate(number).get("rules", [])
    closed = set()
    for _ in rules:
        next_closed = closed | {r["target"] for r in rules if set(r["premises"]) <= closed}
        if next_closed == closed:
            break
        closed = next_closed
    return frozenset(closed)


def kind_name(kind):
    if isinstance(kind, dict) and "proof" in kind:
        return "proof", kind["proof"]["goal"]
    return ("plan" if kind == "coordinator" else "merge"), None


@dataclass(frozen=True)
class Worker:
    id: int
    role: str
    goal: int | None
    status: str = "queued"
    replies: int = 0
    limit: int = 0
    spent: int = 0
    prompt: int = 0
    cached: int = 0
    output: int = 0
    last_reply: float = 0
    tool: str = "—"
    activity: str = "waiting"
    tool_errors: int = 0
    detail: str = ""
    model: str = ""


@dataclass(frozen=True)
class Snapshot:
    run: str
    phase: str
    roots: tuple[tuple[int, str], ...]
    accepted: frozenset[int]
    published: frozenset[int]
    disproved: frozenset[int]
    workers: tuple[Worker, ...]
    spent: int
    budget: int
    committed: int
    replies: int
    cache_fraction: float
    pending_requests: int
    updated: float
    feed: tuple[str, ...]
    skipped: int
    behind: bool
    exit_code: int | None = None
    log: str = ""


class Monitor:
    """One local journal cursor; no writes, subprocesses, model calls, or proof-term reads."""
    def __init__(self, run):
        self.run = Path(run)
        self.reset()

    def reset(self):
        self.offset, self.tail, self.identity = 0, b"", None
        self.discard_line = False
        self.settings, self.names, self.roots = {}, {}, set()
        self.loaded = False
        self.workers, self.charges, self.usage, self.accounts = {}, {}, {}, {}
        self.checkpoint_jobs, self.pending_kind, self.account_owners = [], None, set()
        self.grants, self.accepted, self.disproved = set(), set(), set()
        self.published, self.revisions = frozenset(), {}
        self.phase, self.updated = "running", 0
        self.feed = deque(maxlen=12)
        self.skipped = 0

    def artifact(self, digest, limit=MAX_ARTIFACT):
        if not isinstance(digest, str) or not re.fullmatch("[0-9a-f]{64}", digest):
            self.skipped += 1
            return None
        try:
            return bounded_json(self.run / "artifacts" / digest, limit)
        except (OSError, ValueError):
            self.skipped += 1
            return None

    def registry(self, entries):
        for goal, entry in enumerate(entries):
            self.names[goal] = ", ".join(entry.get("names", [f"goal {goal}"]))
            if entry.get("root"):
                self.roots.add(goal)

    def update(self, job, **fields):
        if job in self.workers:
            self.workers[job] = replace(self.workers[job], **fields)

    def ensure_worker(self, job, kind=None):
        if job in self.workers:
            return
        if job < len(self.checkpoint_jobs):
            kind = self.checkpoint_jobs[job]["kind"]
        if kind is None:
            return
        role, goal = kind_name(kind)
        settings = dict(self.settings)
        if role != "proof":
            settings.update(self.settings.get("coordinator") or {})
        self.workers[job] = Worker(job, role, goal, limit=settings.get("turns", 0),
                                   model=settings.get("model", ""))

    def note(self, text):
        self.feed.append(clean(text).replace("\n", " ")[:500])

    def apply(self, event):
        kind = event.get("event")
        if kind == "model":
            value = event["input"]
            if not isinstance(value, dict):
                return
            if "start" in value:
                # A proposed model input can be a no-op. Wait for a reservation,
                # spawn, result, or checkpoint before displaying a real job.
                self.pending_kind = value["start"]["kind"]
            if "reserve" in value:
                r = value["reserve"]
                self.ensure_worker(r["owner"], self.pending_kind)
                if r["owner"] not in self.account_owners:
                    self.accounts[len(self.accounts)] = r["bound"]
                    self.account_owners.add(r["owner"])
            if "settle" in value:
                r = value["settle"]
                self.accounts[r["id"]] = r["amount"]
            if "timeout" in value:
                self.update(value["timeout"]["id"], status="timeout")
            if "stop" in value:
                self.phase = "stopping"
            if "deliver" in value and value["deliver"]["report"] == "failed":
                job = value["deliver"]["id"]
                if job in self.workers and self.workers[job].status not in ("plan saved", "failed"):
                    self.update(job, status="failed")
        elif kind == "spawn":
            job = event["job"]
            spec = self.artifact(event.get("spec"), MAX_LINE) if "spec" in event else None
            self.ensure_worker(job, spec["kind"] if spec else self.pending_kind)
            self.update(job, status="running")
        elif kind == "grant":
            self.grants.add((event["job"], event["request"]))
        elif kind == "charge":
            key = event["job"], event["request"]
            if key not in self.charges:
                self.charges[key] = event["charge"]
                w = self.workers.get(event["job"])
                if w:
                    self.update(w.id, spent=w.spent + event["charge"])
        elif kind == "worker":
            self.worker_event(event)
        elif kind == "result":
            r = event["result"]
            job, report = r["job"], r["report"]
            role, goal = kind_name(r["kind"])
            self.ensure_worker(job, r["kind"])
            if role == "proof" and isinstance(report, dict) and "artifact" in report:
                self.accepted.add(goal)
                number = r.get("receipt", {}).get("revision", {}).get("source", 0)
                if certificate(number).get("finalDisproof"):
                    self.disproved.add(goal)
                self.note(f"Accepted {self.names.get(goal, f'goal {goal}')} · worker #{job}")
                status = "accepted"
            else:
                status = "plan saved" if role == "plan" else "checked"
                self.note(f"Worker #{job}: {status}")
            self.update(job, status=status, detail=clean(r.get("memory", ""))[:4000], tool="finish")
        elif kind == "revision":
            receipt = event["receipt"]
            self.registry(receipt.get("registry", []))
            self.revisions[event["commit"]] = closed_goals(receipt["revision"]["source"])
        elif kind == "published":
            self.published = self.revisions.get(event["commit"], self.published)
            self.note(f"Published revision {event['commit'][:8]}")
        elif kind in ("rejected-result", "protocol-error", "launch-failed", "infrastructure-error"):
            reason = clean(event.get("reason", kind))[:2000]
            self.note(f"{kind}: {reason}")
            self.update(event.get("job"), status="failed", detail=reason)

    def worker_event(self, event):
        a = self.artifact(event["artifact"])
        job = event["job"]
        if not isinstance(a, dict) or job not in self.workers:
            return
        w = self.workers[job]
        if w.status == "queued":
            self.update(job, status="running")
            w = self.workers[job]
        kind = a.get("event")
        if kind == "usage":
            key = job, a["request"]
            if key in self.usage:
                return
            self.usage[key] = (a.get("prompt", 0), a.get("cached", 0))
            stamp = (self.run / "artifacts" / event["artifact"]).stat().st_mtime
            self.update(job, replies=w.replies + 1, prompt=w.prompt + a.get("prompt", 0),
                        cached=w.cached + a.get("cached", 0), output=w.output + a.get("completion", 0),
                        last_reply=stamp, activity="reply received")
        elif kind == "reserve":
            self.update(job, activity="model request")
        elif kind == "tool":
            reply = a.get("reply", {})
            result = reply.get("result", {})
            detail = reply.get("error") or (result.get("diagnostics", "") if isinstance(result, dict) else result)
            failed = reply.get("ok") is False
            self.update(job, tool=a.get("name", "tool") + (" !" if failed else ""),
                        tool_errors=w.tool_errors + int(failed), detail=clean(detail or "")[:4000],
                        activity="tool feedback")
        elif kind == "failed":
            self.update(job, status="failed", detail=clean(a.get("reason", "Worker failed"))[:4000])
            self.note(f"Worker #{job} failed: {a.get('reason', '')}")
        elif kind == "exit" and w.status in ("queued", "running"):
            self.update(job, status="exited", tool=f"exit {a.get('code', '?')}")

    def refresh(self):
        checkpoint = {}
        try:
            checkpoint = bounded_json(self.run / "checkpoint.json", MAX_LINE)
            self.checkpoint_jobs = checkpoint.get("state", {}).get("jobs", [])
        except (OSError, ValueError, KeyError, TypeError):
            pass
        if not self.loaded:
            try:
                ref = bounded_json(self.run / "manifest.json")
                manifest = self.artifact(ref, MAX_LINE)
                if manifest:
                    self.settings = manifest["settings"]
                    self.registry(manifest["initial"]["registry"])
                    self.published = closed_goals(manifest["initial"]["revision"]["source"])
                    self.loaded = True
            except (OSError, ValueError, KeyError, TypeError):
                pass
        behind = False
        try:
            path = self.run / "events.jsonl"
            stat = path.stat()
            identity = stat.st_dev, stat.st_ino
            if self.identity is not None and (identity != self.identity or stat.st_size < self.offset):
                self.reset()
                return self.refresh()
            self.identity, self.updated = identity, stat.st_mtime
            with path.open("rb") as source:
                source.seek(self.offset)
                chunk = source.read(MAX_LINE)
            self.offset += len(chunk)
            behind = self.offset < stat.st_size
            data = self.tail + chunk
            parts = data.split(b"\n")
            self.tail = parts.pop()
            for line in parts:
                if self.discard_line or len(line) > MAX_LINE:
                    self.discard_line = False
                    self.skipped += 1
                    continue
                try:
                    self.apply(load_json(line)["payload"])
                except (ValueError, KeyError, TypeError, AttributeError, OSError):
                    self.skipped += 1
            if len(self.tail) > MAX_LINE:
                self.tail, self.discard_line = b"", True
        except OSError:
            pass
        try:
            phase = checkpoint["state"]["phase"]
            if isinstance(phase, dict) and "done" in phase:
                self.phase = phase["done"]["reason"]
        except (OSError, ValueError, KeyError, TypeError):
            pass
        exit_code, log = None, ""
        try:
            result = bounded_json(self.run / "launcher-result.json")
            if type(result.get("exitCode")) is int:
                exit_code, log = result["exitCode"], clean(result.get("log", ""))
                if exit_code == 0 and self.phase in ("running", "stopping"):
                    self.phase = "complete"
                elif exit_code == 1 and self.phase not in ("exhausted", "cancelled"):
                    self.phase = "stopped"
                elif exit_code not in (0, 1):
                    self.phase = "infrastructure error"
        except (OSError, ValueError, KeyError, TypeError, AttributeError):
            pass
        for job in range(len(self.checkpoint_jobs)):
            self.ensure_worker(job)
        prompt = sum(p for p, _ in self.usage.values())
        workers = tuple(replace(w, status="stopped") if self.phase not in ("running", "stopping")
                        and w.status in ("queued", "running") else w for w in self.workers.values())
        return Snapshot(str(self.run), self.phase, tuple(sorted((g, self.names[g]) for g in self.roots)),
                        frozenset(self.accepted & self.roots), self.published & self.roots, frozenset(self.disproved),
                        workers, sum(self.charges.values()), self.settings.get("budget", 0),
                        sum(self.accounts.values()), len(self.usage),
                        sum(c for _, c in self.usage.values()) / prompt if prompt else 0,
                        len(self.grants - self.charges.keys()), self.updated, tuple(self.feed), self.skipped, behind,
                        exit_code, log)


@dataclass(frozen=True)
class Line:
    text: str
    style: str = "normal"


def money(value):
    return f"${value / 1000000:,.3f}"


def age(stamp):
    if not stamp:
        return "—"
    seconds = max(0, int(time.time() - stamp))
    return f"{seconds}s" if seconds < 60 else f"{seconds // 60}m" if seconds < 3600 else f"{seconds // 3600}h"


def visible_workers(view, active_only):
    return tuple(w for w in view.workers if not active_only or w.status in ("queued", "running"))


def render(view, width, height, selected=0, offset=0, active_only=False, worker_view=False):
    width, height = max(0, width), max(0, height)
    if width < 60 or height < 18:
        texts = [Line(" KRAKEN / PROOF WATCH" + (f" / FINAL {view.phase.upper()}" if view.exit_code is not None else ""), "title"),
                 Line(" Resize the terminal to at least 60 × 18.", "warn"),
                 Line(f" {len(view.accepted)} accepted · {len(view.published & {g for g, _ in view.roots})} published · {money(view.spent)}")]
        return [Line(fit(line.text, width), line.style) for line in texts[:height]]
    roots = {g for g, _ in view.roots}
    accepted = (view.accepted | view.published) & roots
    published = view.published & roots
    active = sum(w.status in ("queued", "running") for w in view.workers)
    live = "CATCHING UP" if view.behind else view.phase.upper()
    if view.exit_code is not None and not view.behind:
        live = "FINAL · " + live
    if view.phase == "running" and view.updated and time.time() - view.updated > 60:
        live += " · QUIET"
    lines = [Line(f"  ◈ KRAKEN  /  PROOF WATCH                         {live}", "title"),
             Line(f"  {view.run}  ·  journal {age(view.updated)} ago", "muted"),
             Line("─" * width, "border")]
    if width >= 105:
        third = (width - 4) // 3
        labels = [f"PROOFS   {len(accepted)} / {len(roots)} accepted",
                  f"SPENT    {money(view.spent)} / {money(view.budget)}",
                  f"ACTIVITY {active} active · {view.replies} replies"]
        lines += [Line("  " + " │ ".join(fit(s, third - 2) for s in labels), "accent"),
                  Line("  " + " │ ".join(fit(s, third - 2) for s in [
                      f"{len(published)} published · {len(roots - accepted)} open",
                      f"Committed {money(view.committed)}",
                      f"Cache {view.cache_fraction:.0%} · {view.pending_requests} requests pending"]), "muted")]
    else:
        lines += [Line(f"  PROOFS {len(accepted)}/{len(roots)} accepted · {len(published)} published   {money(view.spent)} spent", "accent"),
                  Line(f"  {active} active · {view.replies} replies · cache {view.cache_fraction:.0%} · cap {money(view.budget)}", "muted")]
    bar = " ".join("◆" if g in published else "◇" if g in accepted else "·" for g, _ in view.roots)
    lines += [Line(f"  {bar}    ◆ published   ◇ accepted", "good"),
              Line("─" * width, "border"), Line("  PROOF OVERVIEW", "accent")]
    if worker_view:
        lines.pop()
    compact_roots = height < 34 and width >= 76 and len(view.roots) > 6
    max_roots = 0 if worker_view else len(view.roots) if compact_roots else min(len(view.roots), max(2, height // 3 - 2))
    root_cells = []
    for goal, name in view.roots[:max_roots]:
        jobs = [w for w in view.workers if w.goal == goal]
        working = any(w.status in ("queued", "running") for w in jobs)
        status = "published" if goal in published else "accepted" if goal in accepted else "working" if working else "open"
        if goal in view.disproved:
            status = "disproved"
        style = "good" if goal in accepted else "normal" if working else "muted"
        if compact_roots:
            root_cells.append(f"{fit(name, (width - 6) // 2 - 12)} {fit(status.upper(), 10)}")
        else:
            lines.append(Line(f"  {fit(name, max(16, width - 52))} {fit(status.upper(), 10)}"
                              f" {len(jobs):>2} jobs  {sum(w.replies for w in jobs):>3} replies  {money(sum(w.spent for w in jobs)):>8}", style))
    if compact_roots:
        for index in range(0, len(root_cells), 2):
            lines.append(Line("  " + " │ ".join(root_cells[index:index + 2])))
    if len(view.roots) > max_roots and not worker_view:
        lines.append(Line(f"  + {len(view.roots) - max_roots} more roots (enlarge the terminal)", "muted"))
    lines += [Line("─" * width, "border"),
              Line("  WORKERS  /  " + ("ACTIVE" if active_only else "ALL ATTEMPTS") + "    ↑↓ select · a filter", "accent")]
    wide = width >= 105
    lines.append(Line("  JOB  TARGET                   STATUS        REPLIES     SPENT   CACHE   REPLY AGE  LAST TOOL" if wide else
                      "  JOB  TARGET             STATUS       REPLIES    SPENT", "muted"))
    workers = visible_workers(view, active_only)
    slots = max(1, height - len(lines) - 8)
    for index in range(offset, min(len(workers), offset + slots)):
        w = workers[index]
        name = dict(view.roots).get(w.goal, f"helper {w.goal}") if w.role == "proof" else w.role.upper()
        if wide:
            text = (f" {'›' if index == selected else ' '} {w.id:>2}  {fit(name, 23)} {fit(w.status, 12)}"
                    f" {w.replies:>3}/{w.limit:<3} {money(w.spent):>9} {w.cached / w.prompt if w.prompt else 0:>6.0%}"
                    f" {age(w.last_reply):>9}  {w.tool}")
        else:
            text = (f" {'›' if index == selected else ' '} {w.id:>2}  {fit(name, 18)} {fit(w.status, 12)}"
                    f" {w.replies:>3}/{w.limit:<3} {money(w.spent):>9}")
        style = "selected" if index == selected else "bad" if w.status in ("failed", "timeout") else "good" if w.status == "accepted" else "normal"
        lines.append(Line(text, style))
    if not workers:
        lines.append(Line("  No workers in this view.", "muted"))
    while len(lines) < height - 7:
        lines.append(Line(""))
    if workers:
        w = workers[min(selected, len(workers) - 1)]
        lines.append(Line(f"  #{w.id} · {w.model} · {w.activity} · {w.output:,} output tokens · {w.tool_errors} tool errors", "accent"))
        detail = clean(w.detail).splitlines() or ["Waiting for recorded tool feedback."]
        lines += [Line("  " + row, "warn" if w.tool_errors and "!" in w.tool else "muted") for row in detail[:2]]
    message = (f"Run ended (exit {view.exit_code}) · log: {view.log}" if view.exit_code is not None
               else view.feed[-1] if view.feed else "Waiting for an accepted result.")
    lines += [Line("─" * width, "border"), Line("  " + message, "muted")]
    warning = f"{view.skipped} skipped · " if view.skipped else ""
    close = "q close" if view.exit_code is not None else "q quit"
    lines.append(Line("  " + warning + close + " · ↑↓ / j k select · Tab overview/workers · a active/all", "footer"))
    return [Line(fit(line.text, width), line.style) for line in lines[:height]]


def make_styles():
    """The curses attributes of each style name. Call it after `curses.initscr`."""
    curses.start_color()
    curses.use_default_colors()
    palette = {"normal": (252, -1), "muted": (244, -1), "title": (231, 24),
               "accent": (80, -1), "good": (114, -1), "warn": (215, -1),
               "bad": (203, -1), "border": (238, -1), "selected": (231, 24), "footer": (110, -1)}
    styles = {}
    for pair, (name, (fg, bg)) in enumerate(palette.items(), 1):
        if curses.COLORS >= 256:
            curses.init_pair(pair, fg, bg)
        else:
            curses.init_pair(pair, curses.COLOR_CYAN if name in ("accent", "title") else curses.COLOR_WHITE, -1)
        styles[name] = curses.color_pair(pair) | (curses.A_BOLD if name in ("title", "accent", "selected") else 0)
    return styles


def terminal(screen, monitor, interval):
    curses.curs_set(0)
    screen.timeout(int(interval * 1000))
    styles = make_styles()
    selected, offset, active_only, worker_view = 0, 0, True, False
    final_shown = False
    while True:
        view = monitor.refresh()
        if not final_shown and (view.exit_code is not None or view.phase not in ("running", "stopping")):
            active_only, selected, offset, final_shown = False, 0, 0, True
        height, width = screen.getmaxyx()
        workers = visible_workers(view, active_only)
        selected = max(0, min(selected, len(workers) - 1))
        # Keep selection in view even as workers finish or the terminal changes size.
        root_lines = ((len(view.roots) + 1) // 2 if height < 34 and width - 1 >= 76 and len(view.roots) > 6
                      else min(len(view.roots), max(2, height // 3 - 2)))
        slots = max(1, height - 18 if worker_view else height - root_lines - 19)
        offset = max(0, min(offset, selected))
        if selected >= offset + slots:
            offset = selected - slots + 1
        screen.erase()
        for row, line in enumerate(render(view, width - 1, height, selected, offset, active_only, worker_view)):
            try:
                screen.addstr(row, 0, line.text, styles[line.style])
            except curses.error:
                pass
        screen.refresh()
        key = screen.getch()
        if key in (ord("q"), ord("Q"), 27):
            return
        if key in (curses.KEY_DOWN, ord("j")):
            selected += 1
        elif key in (curses.KEY_UP, ord("k")):
            selected -= 1
        elif key == curses.KEY_NPAGE:
            selected += slots
        elif key == curses.KEY_PPAGE:
            selected -= slots
        elif key in (ord("a"), ord("A")):
            active_only, selected, offset = not active_only, 0, 0
        elif key == 9:
            worker_view, offset = not worker_view, 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("run", nargs="?", type=Path, help="run directory (default: latest local run)")
    parser.add_argument("--once", action="store_true", help="print one plain-text overview")
    parser.add_argument("--wait", action="store_true", help="wait for the launcher to create run records")
    parser.add_argument("--interval", type=float, default=1.0, help="refresh interval in seconds (default: 1)")
    args = parser.parse_args(argv)
    if not 0.1 <= args.interval <= 60:
        parser.error("--interval must be between 0.1 and 60 seconds")
    run = args.run
    if run is None:
        root = Path(__file__).resolve().parents[1]
        runs = list((root / ".coordinator").glob("*/runs/*/events.jsonl"))
        if not runs:
            parser.error("no local runs found; give a run directory")
        run = max(runs, key=lambda p: p.stat().st_mtime).parent
    if not args.wait and not (run / "manifest.json").is_file():
        parser.error(f"not a run directory: {run}")
    monitor = Monitor(run)
    if args.once:
        view = monitor.refresh()
        while view.behind:
            view = monitor.refresh()
        for line in render(view, 120, max(42, len(view.workers) + len(view.roots) + 22)):
            print(line.text.rstrip())
        return 0
    if not sys.stdin.isatty() or not sys.stdout.isatty():
        parser.error("an interactive terminal is required; use --once for plain text")
    locale.setlocale(locale.LC_ALL, "")
    try:
        curses.wrapper(terminal, monitor, args.interval)
    except KeyboardInterrupt:
        pass
    except curses.error as error:
        parser.exit(1, f"Terminal error: {error}. Use --once for plain text.\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
