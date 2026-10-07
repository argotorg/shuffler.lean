#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check MSan detection, replay saved inputs, and run guided mutations."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys


def run(build, name, arguments, environment, expected=0):
    for attempt in range(1, 11):
        index = attempt
        log = build / f"{name}.attempt-{index}.log"
        while log.exists():
            index += 1
            log = build / f"{name}.attempt-{index}.log"
        print(f"{name}: {len(arguments)} command arguments; log {log}", flush=True)
        with log.open("w") as output:
            result = subprocess.run(arguments, env=environment, stdout=output, stderr=subprocess.STDOUT)
        text = log.read_text()
        startup_failure = (
            text.startswith('MemorySanitizer: CHECK failed: msan_linux.cpp:193 "((personality(')
            and "ADDR_NO_RANDOMIZE" in text and "<empty stack>" in text
            and len(text.splitlines()) <= 4)
        with (build / "commands.jsonl").open("a") as commands:
            commands.write(json.dumps({"phase": name, "arguments": arguments,
                                       "exit": result.returncode, "log": str(log),
                                       "pre_main_mapping_failure": startup_failure}) + "\n")
        if startup_failure:
            print(f"{name}: MSan failed before main; retry {attempt}/10; log retained", flush=True)
            continue
        shutil.copyfile(log, build / (name + ".log"))
        if result.returncode != expected:
            raise RuntimeError(f"{name}: exit {result.returncode}, expected {expected}; see {log}")
        return text
    raise RuntimeError(f"{name}: MSan could not initialize after 10 attempts")


def main(arguments):
    if len(arguments) not in (0, 1, 2):
        raise ValueError("usage: run-msan.py [BUILD_DIRECTORY [FUZZ_SECONDS]]")
    root = Path(__file__).resolve().parent.parent
    build = Path(arguments[0]).resolve() if arguments else root / "build/msan"
    seconds = int(arguments[1]) if len(arguments) == 2 else 60
    if seconds <= 0:
        raise ValueError("FUZZ_SECONDS must be positive")
    environment = dict(os.environ)
    # Frame-pointer unwinding avoids recursion through the instrumented unwinder.
    # These options change diagnostics only. All MSan checks remain enabled.
    environment["MSAN_OPTIONS"] = (
        "halt_on_error=1:exit_code=86:symbolize=1:"
        "fast_unwind_on_malloc=1:fast_unwind_on_fatal=1")
    symbolizer = shutil.which("llvm-symbolizer")
    if symbolizer is None:
        raise ValueError("llvm-symbolizer is required; use tests/msan-shell.nix")
    environment["MSAN_SYMBOLIZER_PATH"] = symbolizer
    probe = str(build / "msan-probe")
    detection = run(build, "probe", [probe], environment, expected=86)
    if "WARNING: MemorySanitizer: use-of-uninitialized-value" not in detection:
        raise RuntimeError("the probe failed without the required uninitialized-read report")
    run(build, "probe-initialized", [probe, "initialized"], environment)

    sources = {"libfuzzer": root / "build/guided/corpus",
               "afl": root / "build/afl/findings/default/queue"}
    manifest = []
    corpus = build / "corpus"
    corpus.mkdir(exist_ok=True)
    for label, directory in sources.items():
        files = sorted(path for path in directory.iterdir() if path.is_file() and not path.name.startswith("."))
        if not files:
            raise ValueError(f"saved {label} corpus is empty: {directory}")
        snapshot = build / ("replay-" + label)
        snapshot.mkdir(exist_ok=True)
        for index, source in enumerate(files):
            data = source.read_bytes()
            digest = hashlib.sha256(data).hexdigest()
            destination = snapshot / f"{index:05d}-{digest}"
            destination.write_bytes(data)
            (corpus / digest).write_bytes(data)
            manifest.append({"source": str(source), "snapshot": str(destination),
                             "sha256": digest, "size": len(data), "corpus": label})
    (build / "replay-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    target = str(build / "permute-msan")
    for label in sources:
        files = [entry["snapshot"] for entry in manifest if entry["corpus"] == label]
        # Explicit files run once each, even if their coverage is redundant.
        run(build, "replay-" + label, [target, "-runs=1", *files], environment)
        print(f"replayed {label}: {len(files)} saved files", flush=True)
    artifacts = build / "artifacts"
    artifacts.mkdir(exist_ok=True)
    output = run(build, "fuzz", [target, str(corpus), "-max_len=8195", "-timeout=10",
                                "-rss_limit_mb=2048", "-print_final_stats=1", "-seed=73419",
                                f"-max_total_time={seconds}",
                                f"-artifact_prefix={artifacts}/"], environment)
    print("\n".join(output.splitlines()[-15:]))


if __name__ == "__main__":
    try:
        main(sys.argv[1:])
    except (OSError, ValueError, RuntimeError) as error:
        sys.exit(f"MSan check: {error}")
