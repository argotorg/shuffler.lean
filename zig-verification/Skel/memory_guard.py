"""Limit project Lean workers, without stopping model calls or changing budgets.

Run with ``--once`` to report a decision without sending signals or writing state.
The live guard sends TERM to one worker at a time, then KILL after the grace time.
It tracks the campaign by PID and Linux start time and reads the current daemon
metadata each cycle, so a daemon restart does not leave its new workers unguarded.
"""
import argparse
from dataclasses import dataclass, field
import errno
import fcntl
import json
import os
from pathlib import Path
import signal
import time


GIB = 1024 ** 3


@dataclass(frozen=True, order=True)
class Identity:
    pid: int
    start: int


@dataclass(frozen=True)
class Process:
    identity: Identity
    parent: int
    name: str
    cwd: Path
    rss: int
    args: tuple[str, ...] = field(default=(), repr=False)


@dataclass(frozen=True)
class Limits:
    rss_cap: int = 8 * GIB
    floor: int = 20 * GIB
    recovery: int = 24 * GIB


@dataclass(frozen=True)
class Decision:
    pressure: bool
    victim: Process | None = None
    reason: str | None = None


def small_bytes(path, limit):
    with path.open("rb") as source:
        data = source.read(limit + 1)
    if len(data) > limit:
        raise ValueError("process data exceeds limit")
    return data


def read_process(path, page_size=None):
    """Read a stable process snapshot. Never read its environment."""
    try:
        stat = small_bytes(path / "stat", 8192)
        fields = stat.rsplit(b")", 1)[1].split()
        if fields[0] in (b"Z", b"X", b"x"):
            return None
        args = tuple(os.fsdecode(x) for x in small_bytes(path / "cmdline", 65536).split(b"\0") if x)
        if not args:
            return None
        # Linux appends this suffix while a process runs a replaced executable.
        name = Path(os.readlink(path / "exe").removesuffix(" (deleted)")).name
        cwd = (path / "cwd").resolve(strict=True)
        # Re-read stat after the other files, to reject an exit or PID reuse.
        after = small_bytes(path / "stat", 8192).rsplit(b")", 1)[1].split()
        if fields[19] != after[19] or after[0] in (b"Z", b"X", b"x"):
            return None
        return Process(Identity(int(path.name), int(after[19])), int(after[1]),
                       name, cwd, max(0, int(after[21])) *
                       (page_size if page_size is not None else os.sysconf("SC_PAGE_SIZE")), args)
    except (OSError, ValueError, IndexError):
        return None


def read_processes(proc_root=Path("/proc")):
    try:
        return tuple(p for path in proc_root.iterdir() if path.name.isdecimal()
                     if (p := read_process(path)) is not None)
    except OSError:
        return ()


def read_available(proc_root=Path("/proc")):
    try:
        for line in small_bytes(proc_root / "meminfo", 65536).splitlines():
            fields = line.split()
            if len(fields) == 3 and fields[0] == b"MemAvailable:" and fields[2] == b"kB":
                value = int(fields[1])
                return value * 1024 if value >= 0 else None
    except (OSError, ValueError):
        pass
    return None


def command(p, name, action):
    return p.name == name and len(p.args) > 1 and p.args[1] == action


def daemon_identity(root, processes):
    """A metadata PID alone does not identify a daemon."""
    try:
        value = json.loads(small_bytes(root / ".leantools/daemon.json", 65536))
        pid = value["pid"]
        if type(pid) is not int:
            return None
        p = next((p for p in processes if p.identity.pid == pid), None)
        if p is not None and p.cwd == root and command(p, "leantools", "daemon"):
            if "--root" in p.args:
                index = p.args.index("--root")
                if index + 1 == len(p.args) or (root / p.args[index + 1]).resolve() != root:
                    return None
            return p.identity
    except (OSError, ValueError, KeyError, TypeError):
        pass
    return None


def elaborator(p):
    return ((p.name == "lean" and "--server" not in p.args) or
            p.name == "lean-worker" or command(p, "leantools", "validate"))


def eligible_processes(processes, root, roots):
    """Require both an exact checkout and an unbroken, age-consistent ancestry."""
    by_pid = {p.identity.pid: p for p in processes}
    roots = frozenset(roots)

    def descendant(p):
        seen = set()
        while p.identity.pid not in seen:
            if p.identity in roots:
                return True
            seen.add(p.identity.pid)
            parent = by_pid.get(p.parent)
            if parent is None or parent.identity.start > p.identity.start:
                return False
            p = parent
        return False

    return tuple(p for p in processes if p.cwd == root and elaborator(p) and descendant(p))


def select_victim(processes, root, roots, available, limits=Limits(), pressure=False,
                  attempted=frozenset()):
    """Pure pressure hysteresis and largest-worker selection."""
    pressure = (available is not None and
                (available < limits.floor or (pressure and available < limits.recovery)))
    workers = tuple(p for p in eligible_processes(processes, root, roots)
                    if p.identity not in attempted)
    largest = max(workers, key=lambda p: (p.rss, p.identity), default=None)
    if largest is not None:
        if largest.rss > limits.rss_cap:
            return Decision(pressure, largest, "rss-cap")
        if pressure:
            return Decision(pressure, largest, "available-floor")
    return Decision(pressure)


def signal_process(identity, sig, proc_root=Path("/proc"), root=None):
    """Use a pidfd when Linux supplies it, and check start time before every signal.

    Older kernels require a final /proc identity check followed by kill(2).
    With pidfds, an exit or PID reuse cannot redirect a signal to another process.
    """
    fd = None
    try:
        if hasattr(os, "pidfd_open") and hasattr(signal, "pidfd_send_signal"):
            try:
                fd = os.pidfd_open(identity.pid)
            except OSError as error:
                if error.errno not in (errno.ENOSYS, errno.EINVAL):
                    raise
        p = read_process(proc_root / str(identity.pid))
        if p is None or p.identity != identity:
            return "gone"
        if root is not None and (p.cwd != root or not elaborator(p)):
            return "out-of-scope"
        if fd is None:
            os.kill(identity.pid, sig)
        else:
            signal.pidfd_send_signal(fd, sig)
        return "sent"
    except ProcessLookupError:
        return "gone"
    except OSError:
        return "denied"
    finally:
        if fd is not None:
            os.close(fd)


def decision_record(decision, available):
    record = {"pressure": decision.pressure, "availableBytes": available,
              "reason": decision.reason}
    if decision.victim is not None:
        p = decision.victim
        record.update(pid=p.identity.pid, start=p.identity.start, rssBytes=p.rss)
    return record


def parser():
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--root", type=Path, default=Path.cwd())
    result.add_argument("--campaign", type=int, help="Stop when this skel full process ends")
    result.add_argument("--log", type=Path, help="Append JSONL here; state is PATH.state.json")
    result.add_argument("--rss-gib", type=float, default=8)
    result.add_argument("--floor-gib", type=float, default=20)
    result.add_argument("--recovery-gib", type=float, default=24)
    result.add_argument("--interval", type=float, default=0.25)
    result.add_argument("--grace", type=float, default=0.5)
    result.add_argument("--once", action="store_true", help="Report one snapshot; never send signals")
    result.add_argument("--proc-root", type=Path, default=Path("/proc"), help=argparse.SUPPRESS)
    return result


def main(argv=None):
    cli = parser()
    args = cli.parse_args(argv)
    if not (0 < args.rss_gib < float("inf") and 0 < args.floor_gib <= args.recovery_gib < float("inf")
            and 0 < args.interval <= 60 and 0 <= args.grace <= 60):
        cli.error("limits must be finite and positive; recovery must be at least the floor")
    root = args.root.resolve(strict=True)
    limits = Limits(int(args.rss_gib * GIB), int(args.floor_gib * GIB), int(args.recovery_gib * GIB))
    processes = read_processes(args.proc_root)
    campaign = None
    if args.campaign is not None:
        p = next((p for p in processes if p.identity.pid == args.campaign), None)
        if p is None or p.cwd != root or not command(p, "skel", "full"):
            cli.error("campaign must be a live skel full process in this checkout")
        campaign = p.identity
    if args.once:
        daemon = daemon_identity(root, processes)
        available = read_available(args.proc_root)
        roots = tuple(i for i in (campaign, daemon) if i is not None)
        print(json.dumps({"event": "snapshot", **decision_record(
            select_victim(processes, root, roots, available, limits), available)}))
        return 0
    if args.proc_root != Path("/proc"):
        cli.error("live process control requires /proc")
    log = args.log or root / ".skel/memory-guard.jsonl"
    log.parent.mkdir(parents=True, exist_ok=True)
    state = Path(str(log) + ".state.json")
    # Hold this descriptor until exit. A second supervisor cannot use the same log.
    with Path(str(log) + ".lock").open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            cli.error("another memory guard holds this log lock")
        own = read_process(Path("/proc") / str(os.getpid()))
        metadata = {"pid": os.getpid(), "start": own.identity.start if own else None,
                    "root": str(root), "campaign": campaign.pid if campaign else None,
                    "campaignStart": campaign.start if campaign else None}
        stopping = False

        def stop(_sig, _frame):
            nonlocal stopping
            stopping = True

        old_handlers = {sig: signal.signal(sig, stop) for sig in (signal.SIGTERM, signal.SIGINT)}
        with log.open("a", buffering=1) as output:
            def emit(event, **data):
                output.write(json.dumps({"time": time.time(), "event": event, **data}) + "\n")

            def save_state(status):
                temporary = Path(str(state) + f".{os.getpid()}.tmp")
                temporary.write_text(json.dumps({**metadata, "state": status}) + "\n")
                temporary.replace(state)

            attempted = frozenset()
            pending = None
            pressure = False
            save_state("running")
            emit("start", **metadata, rssCapBytes=limits.rss_cap, floorBytes=limits.floor,
                 recoveryBytes=limits.recovery, interval=args.interval, grace=args.grace)
            try:
                while not stopping:
                    processes = read_processes(args.proc_root)
                    identities = frozenset(p.identity for p in processes)
                    if campaign is not None and campaign not in identities:
                        break
                    daemon = daemon_identity(root, processes)
                    roots = tuple(i for i in (campaign, daemon) if i is not None)
                    available = read_available(args.proc_root)
                    decision = select_victim(processes, root, roots, available, limits, pressure, attempted)
                    pressure = decision.pressure
                    if pending is not None:
                        identity, deadline, record = pending
                        if identity not in identities:
                            emit("worker-ended", **record)
                            pending = None
                        elif time.monotonic() >= deadline:
                            # Revalidate scope before escalation, as well as identity in signal_process.
                            eligible = {p.identity for p in eligible_processes(processes, root, roots)}
                            result = signal_process(identity, signal.SIGKILL, root=root) if identity in eligible else "out-of-scope"
                            emit("kill", **record, result=result)
                            pending = None
                    elif decision.victim is not None:
                        identity = decision.victim.identity
                        record = decision_record(decision, available)
                        result = signal_process(identity, signal.SIGTERM, root=root)
                        attempted = attempted | {identity}
                        emit("term", **record, result=result)
                        if result == "sent":
                            pending = (identity, time.monotonic() + args.grace, record)
                    time.sleep(args.interval)
            finally:
                emit("stop", **metadata)
                save_state("stopped")
                for sig, handler in old_handlers.items():
                    signal.signal(sig, handler)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
