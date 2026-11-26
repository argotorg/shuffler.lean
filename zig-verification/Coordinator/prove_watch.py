#!/usr/bin/env python3
"""A read-only view of a batch of `leantools prove` runs, on the screen of watch.py.

The batch log (written by prove-exprint.sh) has these lines:

    batch start <epoch>     the start of the batch
    file <path>             a working file of the batch
    [<path>] <text>         a line that `leantools prove <path>` printed
    exit <path> <code>      the exit status of `leantools prove <path>`
    batch end <epoch>       no run of the batch is in progress

The record of a file is the newest directory `<runs>/<time>-<path with _ for />` whose
`events.jsonl` changed at or after the start of the batch. A row of the worker table is one
iteration of the harness; its number is the iteration. REPLY AGE is the age of the last event.
"""
from __future__ import annotations

import argparse
import curses
from dataclasses import dataclass, field, replace
import json
import locale
import os
from pathlib import Path
import re
import sys
import time

from Coordinator import watch

CHUNK = 8 * 1024 * 1024
STAMP = r"\d{4}-\d\d-\d\dT\d\d-\d\d-\d\d\.\d+"


@dataclass(frozen=True)
class Batch:
    start: int = 0
    files: tuple[str, ...] = ()
    exits: dict[str, int] = field(default_factory=dict)
    output: dict[str, tuple[str, ...]] = field(default_factory=dict)
    ended: bool = False
    skipped: int = 0


def parse_log(text):
    batch = Batch()
    for line in text.splitlines():
        words = line.split(" ")
        output = re.fullmatch(r"\[(.*?)\] ?(.*)", line)
        if words[:2] == ["batch", "start"] and len(words) == 3 and words[2].isdecimal():
            batch = replace(batch, start=int(words[2]))
        elif words[0] == "file" and len(words) == 2 and words[1]:
            batch = replace(batch, files=batch.files + (words[1],))
        elif output and output[1] in batch.files:
            lines = batch.output.get(output[1], ()) + (output[2],)
            batch = replace(batch, output={**batch.output, output[1]: lines})
        elif words[0] == "exit" and len(words) == 3 and words[1] in batch.files and words[2].isdecimal():
            batch = replace(batch, exits={**batch.exits, words[1]: int(words[2])})
        elif words[:2] == ["batch", "end"] and len(words) == 3 and words[2].isdecimal():
            batch = replace(batch, ended=True)
        else:
            batch = replace(batch, skipped=batch.skipped + 1)
    return batch


def names(files):
    """The files without `.lean` and without the directory that all of them share."""
    if not files:
        return ()
    shared = os.path.commonpath([os.path.dirname(f) for f in files])
    return tuple(os.path.relpath(f, shared or ".").removesuffix(".lean") for f in files)


@dataclass(frozen=True)
class Price:
    """USD for each million tokens, which is micro-USD for each token."""
    input: float = 0
    cached: float = 0
    output: float = 0

    def cost(self, event):
        prompt, cached = event["prompt_tokens"], event["cached_tokens"]
        return (prompt - cached) * self.input + cached * self.cached + event["completion_tokens"] * self.output


def price(value, default):
    value = value if isinstance(value, dict) else {}
    return Price(value.get("input", default.input), value.get("cachedInput", default.cached),
                 value.get("output", default.output))


@dataclass(frozen=True)
class Attempt:
    """One iteration of the harness. `spent` is in micro-USD; `verdict` is the result of its submission."""
    iteration: int
    limit: int
    replies: int = 0
    prompt: int = 0
    cached: int = 0
    output: int = 0
    spent: float = 0
    tool: str = "—"
    tool_errors: int = 0
    detail: str = ""
    activity: str = "model request"
    model: str = ""
    verdict: bool | None = None


@dataclass(frozen=True)
class Run:
    prover: Price = Price()
    reflection: Price = Price()
    budget: float = 20
    attempts: tuple[Attempt, ...] = ()
    last: str = ""


def step(run, event):
    """The run after one line of `events.jsonl`."""
    kind = event["event"]
    if kind == "run-start":
        config = event["config"]
        prover = price(config.get("price"), Price())
        reflection = config.get("reflection")
        return replace(run, prover=prover, budget=config.get("budgetUsd", run.budget), last=kind,
                       reflection=price(reflection.get("price") if isinstance(reflection, dict) else None, prover))
    if kind == "iteration":
        return replace(run, attempts=run.attempts + (Attempt(event["iteration"], event["turns"]),), last=kind)
    if not run.attempts:
        raise ValueError("event before the first iteration")
    a = run.attempts[-1]
    if kind in ("reply", "reflection"):
        rate = run.prover if kind == "reply" else run.reflection
        a = replace(a, replies=a.replies + (kind == "reply"), prompt=a.prompt + event["prompt_tokens"],
                    cached=a.cached + event["cached_tokens"], output=a.output + event["completion_tokens"],
                    spent=a.spent + rate.cost(event), model=str(event["model"]),
                    activity="reply received" if kind == "reply" else "reflection received")
    elif kind == "tool-reply":
        a = replace(a, tool=event["name"], detail=watch.clean(event["text"])[:4000], activity="tool feedback")
    elif kind == "tool":
        failed = event["ok"] is not True
        a = replace(a, tool=event["name"] + (" !" if failed else ""), tool_errors=a.tool_errors + failed)
    elif kind == "submit":
        a = replace(a, verdict=event["accepted"] is True, detail=watch.clean(event["report"])[:4000])
    elif kind == "request-attempt":
        if event["status"] != 200:
            a = replace(a, activity=f"{event['operation']} request, attempt {event['attempt']}: status {event['status']}")
    elif kind == "reflection-failed":
        a = replace(a, activity="reflection failed")
    elif kind == "context-limit":
        a = replace(a, activity="context limit: " + watch.clean(event["reason"]))
    else:
        raise ValueError("unknown event")
    return replace(run, attempts=run.attempts[:-1] + (a,), last=kind)


def record(runs, file, start):
    """The newest run directory of `file` with events at or after `start`."""
    name = re.compile(STAMP + "-" + re.escape(file.replace("/", "_")))
    try:
        found = [d for d in sorted(runs.iterdir())
                 if name.fullmatch(d.name) and (d / "events.jsonl").stat().st_mtime >= start]
    except OSError:
        return None
    return found[-1] if found else None


@dataclass(frozen=True)
class Reading:
    """What the monitor knows of the record of one file."""
    path: Path
    run: Run = Run()
    updated: float = 0
    outcome: str = ""
    report: str = ""


def file_workers(goal, reading, done, code, output):
    """The rows of one file. `done`: `leantools prove` ended or the batch ended."""
    tail = "\n".join(output[-2:])
    if reading is None or not reading.run.attempts:
        status = "queued" if not done else "stopped" if code is None else "failed"
        return (watch.Worker(1, "proof", goal, status=status, detail=tail),)
    rows = []
    for a in reading.run.attempts:
        live = a.verdict is None and a is reading.run.attempts[-1]
        status = ("accepted" if a.verdict else "rejected" if a.verdict is False
                  else "running" if not done else reading.outcome or "stopped")
        rows.append(watch.Worker(a.iteration, "proof", goal, status=status, replies=a.replies, limit=a.limit,
                                 spent=round(a.spent), prompt=a.prompt, cached=a.cached, output=a.output,
                                 last_reply=reading.updated if live and not done else 0, tool=a.tool,
                                 activity=a.activity, tool_errors=a.tool_errors, model=a.model,
                                 detail=reading.report or a.detail or tail if live and done else a.detail))
    return tuple(rows)


def file_notes(name, reading, code, output):
    notes = []
    if reading is not None:
        notes.append(f"{name}: run record {reading.path}")
        for a in reading.run.attempts:
            notes.append(f"{name}: iteration {a.iteration} starts (limit {a.limit} replies)")
            if a.verdict is not None:
                notes.append(f"{name}: iteration {a.iteration} {'accepted' if a.verdict else 'rejected'}"
                             f" after {a.replies} replies")
    if code is not None:
        outcome = reading.outcome if reading is not None else ""
        reason = reading.report.strip().split("\n")[0] if outcome == "failed" else "" if outcome else "".join(output[-1:])
        notes.append(" · ".join(part for part in (f"{name}: exit {code}", outcome, reason) if part))
    return notes


class Monitor:
    """Cursors into the batch log and the run records; no writes, subprocesses, or model calls."""
    def __init__(self, log, runs=None):
        self.log = Path(log)
        self.runs = Path(runs) if runs else self.log.resolve().parent / ".leantools" / "runs"
        self.start = None
        self.reset()

    def reset(self):
        self.readings, self.offsets, self.tails = {}, {}, {}
        self.skipped = 0
        self.notes = []

    def read(self, file, path):
        """Moves the cursor of `file` by at most CHUNK bytes; true when more bytes remain."""
        if file not in self.readings or self.readings[file].path != path:
            self.readings[file], self.offsets[file], self.tails[file] = Reading(path), 0, b""
        reading = self.readings[file]
        events = path / "events.jsonl"
        with events.open("rb") as source:
            source.seek(self.offsets[file])
            chunk = source.read(CHUNK)
            stat = os.fstat(source.fileno())
        self.offsets[file] += len(chunk)
        lines = (self.tails[file] + chunk).split(b"\n")
        self.tails[file] = lines.pop()
        run = reading.run
        for line in lines:
            try:
                run = step(run, json.loads(line))
            except (ValueError, KeyError, TypeError, AttributeError):
                self.skipped += 1
        outcome, report = "", ""
        try:
            summary = watch.bounded_json(path / "summary.json", watch.MAX_LINE)
            outcome, report = str(summary["outcome"]), watch.clean(summary["report"])[:4000]
        except (OSError, ValueError, KeyError, TypeError):
            pass
        self.readings[file] = replace(reading, run=run, updated=stat.st_mtime, outcome=outcome, report=report)
        return self.offsets[file] < stat.st_size

    def refresh(self):
        text, updated = "", 0
        try:
            with self.log.open("rb") as source:
                text = source.read(watch.MAX_LINE).decode(errors="replace")
                updated = os.fstat(source.fileno()).st_mtime
        except OSError:
            pass
        batch = parse_log(text)
        if batch.start != self.start:  # the launcher writes the log from the start for each batch
            self.start = batch.start
            self.reset()
        shown = names(batch.files)
        behind = False
        workers, notes, accepted, live = [], [], set(), 0
        for goal, file in enumerate(batch.files):
            path = record(self.runs, file, batch.start)
            try:
                behind = (path is not None and self.read(file, path)) or behind
            except OSError:
                pass
            reading = self.readings.get(file) if path is not None else None
            code, output = batch.exits.get(file), batch.output.get(file, ())
            done = batch.ended or code is not None
            rows = file_workers(goal, reading, done, code, output)
            workers += rows
            notes += file_notes(shown[goal], reading, code, output)
            if any(w.status == "accepted" for w in rows):
                accepted.add(goal)
            if reading is not None:
                updated = max(updated, reading.updated)
                live += not done and reading.run.last not in ("", "reply", "tool-reply")
        if batch.ended:
            notes.append(f"batch end: {len(accepted)} of {len(batch.files)} accepted")
        seen = set(self.notes)
        self.notes += [watch.clean(note).replace("\n", " ")[:500] for note in notes if note not in seen]
        current = [self.readings[f] for f in batch.files if f in self.readings]
        prompt = sum(a.prompt for r in current for a in r.run.attempts)
        code = max((batch.exits.get(f, 1) for f in batch.files), default=0) if batch.ended else None
        spent = sum(w.spent for w in workers)
        return watch.Snapshot(
            str(self.log), "running" if code is None else "complete" if code == 0 else "stopped",
            tuple(enumerate(shown)), frozenset(accepted), frozenset(), frozenset(), tuple(workers), spent,
            round(sum(r.run.budget for r in current) * 1_000_000), spent, sum(w.replies for w in workers),
            sum(a.cached for r in current for a in r.run.attempts) / prompt if prompt else 0, live, updated,
            tuple(self.notes[-12:]), self.skipped + batch.skipped, behind, code, str(self.log) if code is not None else "")


def totals(view):
    active = sum(w.status in ("queued", "running") for w in view.workers)
    return (f"{len(view.accepted)}/{len(view.roots)} accepted · {active} active · {view.replies} replies"
            f" · {watch.money(view.spent)}")


def follow(monitor, write, interval=1.0, heartbeat=60.0, sleep=time.sleep, now=time.monotonic):
    """Writes each note once and the totals each `heartbeat` seconds; gives the exit status of the batch."""
    written, beat = 0, now()
    while True:
        view = monitor.refresh()
        for note in monitor.notes[written:]:
            write(note)
        written = len(monitor.notes)
        if view.behind:
            continue
        if view.exit_code is not None:
            return view.exit_code
        if now() - beat >= heartbeat:
            write(totals(view))
            beat = now()
        sleep(interval)


def overview(view):
    return [line.text.rstrip() for line in watch.render(view, 120, max(42, len(view.workers) + len(view.roots) + 22))]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("log", type=Path, help="the batch log")
    parser.add_argument("--runs", type=Path, help="the run records (default: .leantools/runs next to the log)")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--plain", action="store_true", help="print lines until the batch ends, then one overview")
    mode.add_argument("--once", action="store_true", help="print one overview")
    parser.add_argument("--interval", type=float, default=1.0, help="refresh interval in seconds (default: 1)")
    args = parser.parse_args(argv)
    if not 0.1 <= args.interval <= 60:
        parser.error("--interval must be between 0.1 and 60 seconds")
    monitor = Monitor(args.log, args.runs)
    if args.plain or args.once:
        if args.plain:
            try:
                follow(monitor, lambda text: print(time.strftime("%H:%M:%S"), text, flush=True), args.interval)
            except KeyboardInterrupt:
                return 130
        view = monitor.refresh()
        while view.behind:
            view = monitor.refresh()
        print("\n".join(overview(view)), flush=True)
        return view.exit_code or 0
    if not sys.stdin.isatty() or not sys.stdout.isatty():
        parser.error("an interactive terminal is required; use --plain or --once for plain text")
    locale.setlocale(locale.LC_ALL, "")
    try:
        curses.wrapper(watch.terminal, monitor, args.interval)
    except KeyboardInterrupt:
        pass
    except curses.error as error:
        parser.exit(1, f"Terminal error: {error}. Use --plain for plain text.\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
