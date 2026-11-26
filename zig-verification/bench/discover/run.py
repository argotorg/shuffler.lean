"""The evaluation runner of the invariant discovery (docs/research/invariant-discovery-design-20261119.md, 4.3; task D14).

    bench/discover/run.sh [--set dev|heldout] [--solver] [--dry-run] [--allow-heldout] [--out FILE]

For each site of the set in bench/discover/config.json it runs `skel <args> --discover [--solver]` and writes one JSON line
to FILE (default .skel/discover-eval/<UTC time>.jsonl; the file is replaced). With --dry-run it runs nothing: each line has
the site, the mode and the command, and null for each measured value.

The keys of a line:
  set, site, mode (discover | discover+solver), version (git describe), cmd (the command), status, found,
  inv_atoms, measure_parts, rounds, asks, ms, cost_usd, false_rejected.
status is dry, found, not-found, error (the command failed, timed out, or left no ledger) or no-command (the config has no
command for the site). found is true when each ledger of the run is closed. The numbers are read from the ledgers
`discover-*.json` of the run directory that skel prints (`run directory: DIR`), summed over the ledgers:
  inv_atoms      the atoms of the closed quad (the best quad of an open run, 0 for none);
  measure_parts  the components of its measure (a tuple `(a, b)` has two);
  rounds, asks   the rounds of the ledgers, and the rounds in which the model was asked;
  ms             the wall time of the command; cost_usd the change of `spentUsd` in the budget file (null with no file);
  false_rejected the candidates that the filters rejected, by filter: real, cti and unknown (the verdict of a candidate),
                 houdini_drop (the atoms that the Houdini loop dropped), goal (the goals that a state refutes), and total.
  sites          when the run directory has discover-summary.json (the command `skel discover`, task DISC-WIRE): for
                 each loop site its fn, head, form, status (closed, open or error), rung and error. found is then true
                 when the summary has a site and each site is closed; a site with an error has no ledger.

The held-out set needs --allow-heldout (the evaluation agent, task D15). SKEL_CMD sets the skel command (a shell line), and
BUDGET_FILE the budget file. Exit 0 when the lines are written (a failed site is a line), 2 for a bad argument or config.
"""
import glob
import json
import os
import re
import shlex
import subprocess
import sys
import time


def die(msg):
    print(f"run.py: {msg}", file=sys.stderr)
    sys.exit(2)


def parse(argv):
    o = {"set": "dev", "solver": False, "dry": False, "allow_heldout": False, "out": None}
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--solver":
            o["solver"] = True
        elif a == "--dry-run":
            o["dry"] = True
        elif a == "--allow-heldout":
            o["allow_heldout"] = True
        elif a in ("--set", "--out") and i + 1 < len(argv):
            o["set" if a == "--set" else "out"] = argv[i + 1]
            i += 1
        else:
            die(f"bad argument: {a}")
        i += 1
    return o


def version():
    try:
        r = subprocess.run(["git", "describe", "--always", "--dirty"], capture_output=True, text=True, timeout=30)
        return r.stdout.strip() if r.returncode == 0 and r.stdout.strip() else "unknown"
    except (OSError, subprocess.SubprocessError):
        return "unknown"


def spent(path):
    try:
        with open(path) as f:
            return float(json.load(f)["spentUsd"])
    except (OSError, ValueError, KeyError, TypeError):
        return None


def parts(measure):
    """The components of a measure text: a tuple `(a, b)` has the commas at depth 1."""
    if not measure.startswith("("):
        return 1
    depth, commas = 0, 0
    for c in measure:
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == "," and depth == 1:
            commas += 1
    return commas + 1


def metrics(ledgers):
    """The metrics of the ledgers of a run (the ledger format of Skel/Discover/Ladder.lean)."""
    m = {"inv_atoms": 0, "measure_parts": 0, "rounds": 0, "asks": 0,
         "false_rejected": {"real": 0, "cti": 0, "unknown": 0, "houdini_drop": 0, "goal": 0}}
    for l in ledgers:
        q = l.get("quad")
        if q:
            m["inv_atoms"] += len(q.get("inv", []))
            m["measure_parts"] += parts(q.get("measure", ""))
        rs = l.get("rounds", [])
        m["rounds"] += len(rs)
        for r in rs:
            m["asks"] += 1 if r.get("asked") else 0
            for c in r.get("candidates", []):
                for k in ("real", "cti", "unknown"):
                    if c.get("verdict", "").startswith(k):
                        m["false_rejected"][k] += 1
                m["false_rejected"]["houdini_drop"] += len(c.get("dropped", []))
            m["false_rejected"]["goal"] += sum(1 for g in r.get("goals", []) if str(g[1]).startswith("refuted"))
    m["false_rejected"]["total"] = sum(m["false_rejected"].values())
    return m


SUMMARY = "discover-summary.json"
SITE_KEYS = ("fn", "head", "form", "status", "rung", "error")


def read_summary(path):
    """The sites of the summary file of `skel discover`, or None when there is no readable summary."""
    try:
        with open(path) as f:
            sites = json.load(f)["sites"]
        return sites if isinstance(sites, list) else None
    except (OSError, ValueError, KeyError, TypeError):
        return None


def line(base, **kw):
    out = dict(base)
    out.update(kw)
    return out


def run_site(base, cmd, limit, budget):
    before = spent(budget)
    t0 = time.monotonic()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=limit)
        code, out = r.returncode, r.stdout
    except subprocess.TimeoutExpired:
        code, out = None, ""
    except OSError:
        code, out = 127, ""
    ms = int((time.monotonic() - t0) * 1000)
    after = spent(budget)
    cost = None if before is None or after is None else round(after - before, 6)
    m = re.search(r"^run directory: (.+)$", out, re.M)
    ledgers = []
    summary = None
    if m:
        d = m.group(1).strip()
        for p in sorted(glob.glob(os.path.join(d, "discover-*.json"))):
            if os.path.basename(p) == SUMMARY:
                continue
            try:
                with open(p) as f:
                    ledgers.append(json.load(f))
            except (OSError, ValueError):
                pass
        summary = read_summary(os.path.join(d, SUMMARY))
    if code != 0 or (not ledgers and summary is None):
        return line(base, status="error", found=False, ms=ms, cost_usd=cost, rounds=0, asks=0, inv_atoms=0,
                    measure_parts=0, false_rejected=None)
    if summary is None:
        found = all(l.get("status") == "closed" for l in ledgers)
        extra = {}
    else:
        found = bool(summary) and all(s.get("status") == "closed" for s in summary)
        extra = {"sites": [{k: s.get(k) for k in SITE_KEYS} for s in summary]}
    return line(base, status="found" if found else "not-found", found=found, ms=ms, cost_usd=cost, **metrics(ledgers),
                **extra)


def main(argv):
    o = parse(argv)
    here = os.path.dirname(os.path.abspath(__file__))
    try:
        with open(os.path.join(here, "config.json")) as f:
            cfg = json.load(f)
        sites = cfg["sets"][o["set"]]["sites"]
    except (OSError, ValueError, KeyError):
        die(f"no config or no set {o['set']}")
    if o["set"] == "heldout" and not o["allow_heldout"]:
        die("the held-out set needs --allow-heldout")
    skel = shlex.split(os.environ["SKEL_CMD"]) if os.environ.get("SKEL_CMD") else cfg["skel"]
    budget = os.environ.get("BUDGET_FILE", cfg["budget"])
    mode = "discover+solver" if o["solver"] else "discover"
    flags = [cfg["discoverFlag"]] + ([cfg["solverFlag"]] if o["solver"] else [])
    ver = version()
    out = o["out"] or os.path.join(".skel", "discover-eval", time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()) + ".jsonl")
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    nulls = {k: None for k in ("found", "inv_atoms", "measure_parts", "rounds", "asks", "ms", "cost_usd", "false_rejected",
                               "sites")}
    with open(out, "w") as f:
        for s in sites:
            args = s["args"]
            cmd = None if args is None else skel + args + flags
            base = {"set": o["set"], "site": s["site"], "mode": mode, "version": ver, "cmd": cmd, "status": None, **nulls}
            if o["dry"]:
                row = line(base, status="dry")
            elif cmd is None:
                row = line(base, status="no-command")
            else:
                row = run_site(base, cmd, cfg["limitSeconds"], budget)
            f.write(json.dumps(row) + "\n")
            f.flush()
    print(f"wrote {len(sites)} lines to {out}")


main(sys.argv[1:])
