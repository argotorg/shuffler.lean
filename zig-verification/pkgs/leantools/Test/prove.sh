#!/usr/bin/env bash
# End-to-end test of `leantools prove` with a scripted model (Test/mock_http.py) and the real tools,
# run from the root of a project that builds Kraken (this repository):
#   nix develop .#leantools -c pkgs/leantools/Test/prove.sh
set -u
lt=${LEANTOOLS:-pkgs/leantools/.lake/build/bin/leantools}
here=$(dirname "$0")
fails=0
dir=.leantools/test
mkdir -p "$dir"
expect() {
  local name=$1 want=$2 got=$3
  if [[ "$got" == *"$want"* ]]; then echo "ok   $name"
  else echo "FAIL $name: want '$want' in:"; echo "$got" | head -20 | sed 's/^/     /'; fails=$((fails + 1)); fi
}
fixture() {
  rm -rf ".leantools/orig/$1"
  cat > "$1" <<'EOF'
import Kraken.StateCfg
import Kraken.FunSpec
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open scoped Program.WP

set_option experimental.vcgen true

def touch : Program := parse("
touch:
  ret
")

theorem touch_go [Host] [FunDecls] [Embeds touch] (c : MachineData) (ra : Int64) :
    ⦃ fun s₀ => s₀ = c.push64 ra ⦄ touch ⦃ fun _ _ => False; fun a t => a = ra ∧ t.regs.rsp = c.regs.rsp ⦄ := by
  vcgen [touch]
    invariants
    · fun {s₀} l s' => match l with
        | "touch" => s' = s₀
        | _ => False
    · fun _ _ => 0
    with skip
  case vc1 => sorry
  case vc2 => sorry
  case vc3 => sorry
EOF
}
# run SCRIPT FILE [PRIMER] [BUDGET]: run the real CLI against the local model.
run() {
  local script=$1 file=$2 primer=${3:-$dir/primer.md} budget=${4:-20}
  : > "$dir/mock.log"
  MOCK_SCRIPT=$script MOCK_LOG=$dir/mock.log python3 "$here/mock_http.py" > "$dir/mock.port" &
  local mock=$!
  for _ in $(seq 50); do [ -s "$dir/mock.port" ] && break; sleep 0.1; done
  cat > "$dir/prove.json" <<EOF
{ "baseUrl": "http://test-user:URL-SECRET@127.0.0.1:$(cat "$dir/mock.port")/v1/script", "model": "mock", "apiKeyEnv": "MOCK_KEY",
  "turns": 5, "maxIterations": 3, "budgetUsd": $budget, "price": {"input": 1, "cachedInput": 0.1, "output": 10},
  "extra": {"model": "mock-effective", "max_tokens": 2048, "reasoning_effort": "high", "headers": {"Authorization": "CONFIG-SECRET"}},
  "primer": "$primer" }
EOF
  MOCK_KEY=sk-mock "$lt" prove "$file" --config "$dir/prove.json" 2>&1
  kill $mock
}
edit='{"role": "assistant", "content": "", "tool_calls": [{"id": "e1", "type": "function", "function": {"name": "edit_working_file", "arguments": "{\"old_string\": \"    with skip\\n  case vc1 => sorry\\n  case vc2 => sorry\\n  case vc3 => sorry\", \"new_string\": \"    with kfinish\"}"}}]}'
submit='{"role": "assistant", "content": "", "tool_calls": [{"id": "s1", "type": "function", "function": {"name": "submit_working_file", "arguments": "{\"reasoning\": \"kfinish closes the VCs\"}"}}]}'
# a reply with a call of a tool without a file parameter (grep), then the edit
grepedit=${edit/'"tool_calls": ['/'"tool_calls": [{"id": "g1", "type": "function", "function": {"name": "grep", "arguments": "{\"pattern\": \"def MachineData.push64\", \"fixed\": true, \"path\": \".kraken/Kraken/X64/WP/Spec.lean\"}"}}, '}

if [[ ${LEANTOOLS_KEEP_DAEMON:-0} != 1 ]]; then "$lt" stop >/dev/null; fi
echo "PRIMER-MARKER" > "$dir/primer.md"
# A: one iteration
fixture "$dir/ProveA.lean"
echo "[$grepedit, $submit]" > "$dir/scriptA.json"
out=$(run "$dir/scriptA.json" "$dir/ProveA.lean")
expect "A: accepted" "accepted after 1 iterations, 2 turns" "$out"
expect "A: report" "Accepted: touch_go proved" "$out"
expect "A: the model got the tools without file" '"name":"edit_working_file"' "$(head -1 "$dir/mock.log")"
[[ $(head -1 "$dir/mock.log") != *'"file":{'* ]] && echo "ok   A: no file parameter" || { echo "FAIL A: no file parameter"; fails=$((fails + 1)); }
expect "A: the primer is in the system prompt" "# Project background\\n\\nPRIMER-MARKER" "$(head -1 "$dir/mock.log")"
expect "A: the first message has the initial feedback" '<initial-feedback>\n' "$(head -1 "$dir/mock.log")"
expect "A: the initial feedback has the goals" '3 `sorry`, with the goal at each' "$(head -1 "$dir/mock.log")"
expect "A: the edit's check reached the model" "No errors." "$(sed -n 2p "$dir/mock.log")"
[[ $(sed -n 2p "$dir/mock.log") =~ X64/WP/Spec\.lean:[0-9]+:def\ MachineData\.push64 ]] && echo "ok   A: grep without file reached the model" || { echo "FAIL A: grep without file reached the model"; fails=$((fails + 1)); }
[[ $(sed -n 2p "$dir/mock.log") != *'unknown argument'* ]] && echo "ok   A: no unknown argument" || { echo "FAIL A: no unknown argument"; fails=$((fails + 1)); }
rundir=$(ls -dt .leantools/runs/*ProveA.lean | head -1)
expect "A: summary" '"outcome": "accepted"' "$(cat "$rundir/summary.json")"
expect "A: cost" '"cost_usd": 0.00' "$(cat "$rundir/summary.json")"
expect "A: events" '"event":"submit"' "$(cat "$rundir/events.jsonl")"
if python3 - "$rundir" "$dir/prove.json" "$dir/primer.md" "$dir/mock.log" <<'PY'
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

run, config, primer, requests = map(Path, sys.argv[1:])
events_text = (run / "events.jsonl").read_text()
events = [json.loads(line) for line in events_text.splitlines()]
start = next(e for e in events if e["event"] == "run-start")
summary = json.loads((run / "summary.json").read_text())
request = json.loads(requests.read_text().splitlines()[0])
for key in ("source_sha256", "config_sha256", "prompt_sha256", "reflection_prompt_sha256",
            "primer_sha256", "tools_sha256"):
    assert re.fullmatch("[0-9a-f]{64}", start[key]), (key, start[key])
    assert summary[key] == start[key], key
assert start["source_commit"] == summary["source_commit"]
assert start["source_dependencies"] == summary["source_dependencies"]
kraken = next(dep for dep in start["source_dependencies"] if dep["name"] == "Kraken")
assert kraken["dir"] == ".kraken"
top = subprocess.check_output(["git", "-C", ".kraken", "rev-parse", "--show-toplevel"], text=True).strip()
own_git = Path(top).resolve() == Path(".kraken").resolve()
assert kraken["status"] == ("git" if own_git else "tree")
assert re.fullmatch("[0-9a-f]{64}", kraken["source_sha256"])
assert start["config_sha256"] == hashlib.sha256(config.read_bytes()).hexdigest()
assert start["primer_sha256"] == hashlib.sha256(primer.read_bytes()).hexdigest()
assert start["prompt_sha256"] == hashlib.sha256(request["messages"][0]["content"].encode()).hexdigest()
assert start["config"]["extra"]["reasoning_effort"] == "high"
assert start["config"]["extra"]["headers"] == "[redacted]"
assert start["config"]["baseUrl"] == "[redacted]"
assert all(secret not in events_text for secret in ("CONFIG-SECRET", "URL-SECRET", "sk-mock"))
assert request["model"] == "mock-effective" and summary["model"] == "mock-effective"
assert all(e["model"] == "mock-effective" for e in events if e["event"] == "reply")
attempts = [e for e in events if e["event"] == "request-attempt"]
assert len(attempts) == 2
assert all(e["status"] == 200 and e["attempt"] == 1 and e["elapsed_ms"] >= 0 for e in attempts)
assert all(e["operation"] == "prover" and e["model"] == "mock-effective" for e in attempts)
PY
then echo "ok   A: run identity, attempts, and redaction"
else echo "FAIL A: run identity, attempts, and redaction"; fails=$((fails + 1)); fi
# B: a rejected submission, a reflection, a second iteration
fixture "$dir/ProveB.lean"
reflection='{"role": "assistant", "content": "LESSONS-MARKER: You submitted with sorry."}'
echo "[$submit, $reflection, $edit, $submit]" > "$dir/scriptB.json"
out=$(run "$dir/scriptB.json" "$dir/ProveB.lean")
expect "B: accepted" "accepted after 2 iterations, 3 turns" "$out"
second=$(sed -n 3p "$dir/mock.log")
expect "B: iteration 2 gets the lessons" "LESSONS-MARKER" "$second"
expect "B: iteration 2 gets the code" "<code>" "$second"
expect "B: iteration 2 gets the feedback" "Not accepted: the file must have no errors and no" "$second"
expect "B: the reflection got the transcript" "<transcript>" "$(sed -n 2p "$dir/mock.log")"
rundir=$(ls -dt .leantools/runs/*ProveB.lean | head -1)
if python3 - "$rundir" <<'PY'
import json
from pathlib import Path
import sys

run = Path(sys.argv[1])
events = [json.loads(line) for line in (run / "events.jsonl").read_text().splitlines()]
summary = json.loads((run / "summary.json").read_text())
completions = [e for e in events if e["event"] in ("reply", "reflection")]
reflections = [e for e in completions if e["event"] == "reflection"]
assert len(reflections) == 1 and reflections[0]["used"] is True
assert reflections[0]["model"] == "mock-effective" and reflections[0]["finish_reason"] == "stop"
for key in ("prompt_tokens", "cached_tokens", "completion_tokens"):
    assert summary[key] == sum(e[key] for e in completions), key
assert summary["prompt_tokens"] == 4000
assert abs(summary["cost_usd"] - 0.00512) < 1e-10
assert len([e for e in events if e["event"] == "request-attempt"]) == 4
PY
then echo "ok   B: reflection accounting"
else echo "FAIL B: reflection accounting"; fails=$((fails + 1)); fi
# D: malformed calls in output-limited replies do not reach the tools.
fixture "$dir/ProveD.lean"
python3 - "$dir/scriptD.json" "$edit" "$submit" <<'PY'
import json
from pathlib import Path
import sys

partial = {"choices": [{"finish_reason": "length", "message": {
    "role": "assistant", "content": "cut", "tool_calls": [{"function": {"name": "edit_working_file"}}]}}],
    "usage": {"prompt_tokens": 7, "completion_tokens": 3}}
Path(sys.argv[1]).write_text(json.dumps([partial, partial, json.loads(sys.argv[2]), json.loads(sys.argv[3])]))
PY
out=$(run "$dir/scriptD.json" "$dir/ProveD.lean")
expect "D: length recovery" "accepted after 1 iterations, 4 turns" "$out"
expect "D: request after length" "output limit" "$(sed -n 2p "$dir/mock.log")"
# a missing primer file stops the run before a model call
fixture "$dir/ProveC.lean"
out=$(run "$dir/scriptA.json" "$dir/ProveC.lean" "$dir/no-such-primer.md"; echo "exit $?")
expect "C: missing primer" "no primer file" "$out"
[ -s "$dir/mock.log" ] && { echo "FAIL C: no model call"; fails=$((fails + 1)); } || echo "ok   C: no model call"
# A positive budget below the first request bound must refuse before HTTP.
fixture "$dir/ProveBudget.lean"
out=$(run "$dir/scriptA.json" "$dir/ProveBudget.lean" "$dir/primer.md" 0.000001)
expect "budget: refused before request" "request bound" "$out"
[ -s "$dir/mock.log" ] && { echo "FAIL budget: no model call"; fails=$((fails + 1)); } || echo "ok   budget: no model call"
if [[ ${LEANTOOLS_KEEP_DAEMON:-0} != 1 ]]; then "$lt" stop >/dev/null; fi
echo "$fails failures"
exit $((fails > 0))
