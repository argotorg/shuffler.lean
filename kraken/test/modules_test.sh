#!/usr/bin/env bash
# Check the public proof boundary and reject imports that bypass it.
set -euo pipefail
dir=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$dir/.." && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

lean_file() {
  (cd "$root" && LEAN_NUM_THREADS=1 nice lake env lean -E warning "$1")
}

cat > "$tmp/Public.lean" <<'EOF'
module
import PlanBridge.Final
import Lean

example : PlanBridge.AssemblyContract PlanBridge.InputOk PlanBridge.ResultOk :=
  PlanBridge.plan_correct

example : PlanBridge.AssemblyBinaryContract PlanBridge.InputOk PlanBridge.ResultOk :=
  PlanBridge.plan_binary_correct

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  for n in [`List.allSome, `Mem, `Shuffler.Planner.run, `PlanBridge.plannerRun_corr] do
    if env.contains n then throwError "implementation declaration is public: {n}"
EOF
lean_file "$tmp/Public.lean"

cat > "$tmp/Mixed.lean" <<'EOF'
module
import all PlanBridge.Assembly
import all PlanBridge.Model
EOF
if lean_file "$tmp/Mixed.lean" > "$tmp/mixed.out" 2>&1; then
  echo 'modules_test: mixed implementation imports passed' >&2
  exit 1
fi
if ! grep -q "already contains 'List.allSome'" "$tmp/mixed.out"; then
  cat "$tmp/mixed.out" >&2
  exit 1
fi

cat > "$tmp/Legacy.lean" <<'EOF'
import PlanBridge.Final
EOF
if lean_file "$tmp/Legacy.lean" > "$tmp/legacy.out" 2>&1; then
  echo 'modules_test: legacy import passed' >&2
  exit 1
fi
if ! grep -q "already contains 'List.allSome'" "$tmp/legacy.out"; then
  cat "$tmp/legacy.out" >&2
  exit 1
fi

echo 'modules_test: public composition passes; mixed and legacy imports are rejected'
