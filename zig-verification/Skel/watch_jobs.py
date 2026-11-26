"""Read local campaign processes. Do not infer live jobs from unfinished records."""
from dataclasses import dataclass
import os
from pathlib import Path
import re

from Coordinator.watch import bounded_json


@dataclass(frozen=True)
class Ask:
    pid: int
    fn: str
    name: str
    model: str
    kind: str
    config: str
    elapsed: float


@dataclass(frozen=True)
class Jobs:
    pid: int | None = None
    limit: int | None = None
    procs: int | None = None
    proofs: int = 0
    asks: tuple[Ask, ...] = ()
    proof_rows: tuple[tuple[str, str], ...] = ()


@dataclass(frozen=True)
class Process:
    pid: int
    parent: int
    args: tuple[str, ...]
    cwd: Path
    start: int


def small_text(path, limit=2 * 1024 * 1024):
    with path.open("rb") as source:
        data = source.read(limit + 1)
    if len(data) > limit:
        raise ValueError("process input exceeds display limit")
    return data.decode()


def process(path):
    try:
        # comm is parenthesized; it can contain spaces and parentheses.
        fields = small_text(path / "stat", 8192).rsplit(")", 1)[1].split()
        if fields[0] in ("Z", "X"):
            return None
        args = tuple(small_text(path / "cmdline", 65536).rstrip("\0").split("\0"))
        return Process(int(path.name), int(fields[1]), args, (path / "cwd").resolve(strict=True), int(fields[19]))
    except (OSError, ValueError, IndexError, UnicodeError):
        return None


def option(args, key):
    try:
        return args[args.index(key) + 1]
    except (ValueError, IndexError):
        return None


def positive(text):
    return int(text) if text and text.isdecimal() and 0 < int(text) < 10**9 else None


def relative(cwd, text):
    path = Path(text)
    return (path if path.is_absolute() else cwd / path).resolve()


def command(p, name, action):
    return len(p.args) >= 2 and Path(p.args[0]).name == name and p.args[1] == action


def prompt_label(text):
    """Read explicit program-counter names and the loop slot; keep ambiguity visible."""
    entries = set(re.findall(r"\bSysV\.Entry\s+\S+\s+\S+\s+\S+\s+[\w.]+\.([A-Za-z_]\w*)PC\b", text))
    pcs = set(re.findall(r"\b[\w.]+\.([A-Za-z_]\w*)PC\b", text))
    for lo, hi in re.findall(r"ExecRange\s+\S+\s+(\S+)\s+(\S+)", text):
        for bound in (lo, hi):
            match = re.search(r"\.([A-Za-z_]\w*)PC$", bound)
            if match:
                pcs.discard(match[1])
    names = entries or pcs
    fn = next(iter(names)) if len(names) == 1 else "unknown"
    slot = text.partition("## Slot statement\n")[2].partition("\n## ")[0]
    match = re.search(r"blocksP?\.Returns\s+\S+\s+\.(\w+)", slot)
    loop = text.startswith("You propose loop triples")
    return fn, "loop." + match[1] if loop and match else "proposal", "loop proposal" if loop else "proposal"


def ask_of(p, uptime, ticks):
    config = option(p.args, "--config") or ""
    model, text = "", ""
    try:
        value = bounded_json(relative(p.cwd, config))
        model = value.get("model", "")
        if not isinstance(model, str):
            model = ""
    except (OSError, ValueError, TypeError, AttributeError):
        pass
    try:
        text = small_text(relative(p.cwd, p.args[-1]))
    except (OSError, ValueError, UnicodeError):
        pass
    fn, name, kind = prompt_label(text)
    return Ask(p.pid, fn, name, model, kind, config, max(0, uptime - p.start / ticks))


def read_jobs(root, run, out=None, proc_root=Path("/proc")):
    """Require one matching skel process in this checkout. Never read its environment."""
    root, run, proc_root = Path(root).resolve(), Path(run).resolve(), Path(proc_root)
    try:
        processes = tuple(p for path in proc_root.iterdir() if path.name.isdecimal()
                          if (p := process(path)) is not None)
    except OSError:
        return Jobs()
    try:
        metadata = bounded_json(run / "campaign.json")
        owner, target_out = metadata["pid"], metadata["out"]
        if type(owner) is not int or not isinstance(target_out, str):
            owner, target_out = None, None
    except (OSError, ValueError, TypeError, KeyError):
        owner, target_out = None, None
    campaigns = []
    for p in processes:
        if p.cwd != root or not command(p, "skel", "full"):
            continue
        target = option(p.args, "--out")
        matches_out = out is not None and target and relative(p.cwd, target) == Path(out).resolve()
        matches_owner = p.pid == owner and target_out and (target is None or relative(p.cwd, target) == relative(root, target_out))
        matches_child = any(c.parent == p.pid and command(c, "leantools", "prove")
                            and len(c.args) > 2 and relative(c.cwd, c.args[2]).is_relative_to(run / "prove")
                            for c in processes)
        if matches_out or (out is None and (matches_child or matches_owner)):
            campaigns.append(p)
    if len(campaigns) != 1:
        return Jobs()
    campaign = campaigns[0]
    children = tuple(p for p in processes if p.parent == campaign.pid)
    try:
        uptime = float(small_text(proc_root / "uptime", 1024).split()[0])
        ticks = os.sysconf("SC_CLK_TCK")
    except (OSError, ValueError, IndexError):
        uptime, ticks = 0, 100
    proofs = tuple(p for p in children if command(p, "leantools", "prove"))
    proof_rows = []
    for p in proofs:
        if len(p.args) > 2:
            path = relative(p.cwd, p.args[2])
            if path.is_relative_to(run / "prove"):
                parts = path.relative_to(run / "prove").parts
                if len(parts) >= 2:
                    proof_rows.append((parts[0], path.stem))
    return Jobs(campaign.pid, positive(option(campaign.args, "--ask-parallel")),
                positive(option(campaign.args, "--procs")),
                len(proofs),
                tuple(ask_of(p, uptime, ticks) for p in children if command(p, "leantools", "ask")), tuple(proof_rows))
