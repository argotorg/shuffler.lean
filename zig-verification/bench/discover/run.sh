#!/usr/bin/env bash
# The evaluation runner of the invariant discovery (task D14): bench/discover/run.py with python3 -I.
# Run it from the repository root in the dev shell (lake on PATH), for example:
#   nix develop -c bench/discover/run.sh --dry-run
#   nix develop -c bench/discover/run.sh --set dev --out /tmp/dev.jsonl [--solver]
exec python3 -I "$(dirname "$0")/run.py" "$@"
