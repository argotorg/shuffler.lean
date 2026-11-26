#!/usr/bin/env sh
# Run after `lake build leantools tests`, from pkgs/leantools. Uses the production modules.
set -eu
fixture=$(mktemp -d)
trap 'rm -rf "$fixture"' EXIT HUP INT TERM
cat > "$fixture/lakefile.lean" <<'EOF'
import Lake
open Lake DSL
package runtimeFixture
EOF
lake env lean --run Test/Runtime.lean "$fixture"
python3 Test/daemon_parallel.py
