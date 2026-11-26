#!/usr/bin/env bash
# End-to-end test of `leantools ask` as a process, with the `ask` endpoint of Test/mock_http.py:
# exit statuses, stdout, the budget file, two processes at the same time. It needs only the built
# binary, python3 and curl: run it from pkgs/leantools after `lake build`:
#   LEANTOOLS=.lake/build/bin/leantools Test/ask.sh
set -u
lt=${LEANTOOLS:-.lake/build/bin/leantools}
lt=$(realpath "$lt")
here=$(realpath "$(dirname "$0")")
fails=0
dir=$(mktemp -d)
trap 'kill $mock 2>/dev/null; rm -rf "$dir"' EXIT
python3 "$here/mock_http.py" > "$dir/port" &
mock=$!
for _ in $(seq 50); do [ -s "$dir/port" ] && break; sleep 0.1; done
base=http://127.0.0.1:$(cat "$dir/port")
export LEANTOOLS_ROOT=$dir
export ASK_KEY=sk-ask-secret

ok() { echo "ok   $1"; }
bad() { echo "FAIL $1: $2"; fails=$((fails + 1)); }
eq() { [[ "$2" == "$3" ]] && ok "$1" || bad "$1" "got '$2', want '$3'"; }
requests() { curl -s "$base/count/$1"; }
# config KEY USAGE/FINISH RETRIES [DELAY]
config() {
  cat > "$dir/config.json" <<EOT
{ "baseUrl": "$base/v1/ask/$1/$2/${4:-0}", "model": "m1", "apiKeyEnv": "ASK_KEY", "maxTokens": 100,
  "maxRetries": $3, "timeoutSeconds": 10, "price": {"input": 1, "cachedInput": 0.5, "output": 2},
  "extra": {"headers": {"Authorization": "CONFIG-SECRET"}} }
EOT
}
budget() { printf '{"note": "n", "budgetUsd": %s, "spentUsd": %s, "runs": []}\n' "$1" "$2" > "$dir/budget.json"; }
# field EXPR: a python expression on the parsed budget file b
field() { python3 -I -c "import json; b=json.load(open('$dir/budget.json')); print($1)"; }
printf hello > "$dir/prompt.txt"
ask() { "$lt" ask --config "$dir/config.json" --budget "$dir/budget.json" --max-usd "$1" "${@:2}"; }

# a call
config k1 10/4/20/stop 0; budget 10.00 0.5
out=$(ask 1 "$dir/prompt.txt" 2>"$dir/err"); st=$?
eq "ok: status" $st 0
eq "ok: stdout is the reply" "$out" "1:hello"
eq "ok: spentUsd" "$(field "b['spentUsd']")" 0.500048
eq "ok: one entry" "$(field "len(b['runs'])")" 1
eq "ok: one request" "$(requests k1)" 1
if grep -rq "sk-ask-secret\|CONFIG-SECRET" "$dir/.leantools" "$dir/budget.json"; then bad "ok: no credential in the record" "found"; else ok "ok: no credential in the record"; fi

# the prompt on stdin
out=$(echo "from stdin" | ask 1 - 2>/dev/null)
eq "stdin: the reply" "$out" "1:from stdin"

# a refusal: no request, exit 1, the file is unchanged
config k2 10/4/20/stop 0; budget 0.0002 0
cp "$dir/budget.json" "$dir/before.json"
out=$(ask 1 "$dir/prompt.txt" 2>"$dir/err"); st=$?
eq "refused: status" $st 1
eq "refused: nothing on stdout" "$out" ""
if grep -q "0.000221" "$dir/err"; then ok "refused: the message has the bound"; else bad "refused: the message" "$(cat "$dir/err")"; fi
eq "refused: no request" "$(requests k2)" 0
if cmp -s "$dir/before.json" "$dir/budget.json"; then ok "refused: the file is unchanged"; else bad "refused: the file is unchanged" changed; fi

# --max-usd below the bound
budget 10 0
out=$(ask 0.0001 "$dir/prompt.txt" 2>/dev/null); st=$?
eq "max-usd below the bound: status" $st 1
eq "max-usd below the bound: no request" "$(requests k2)" 0

# a broken budget file and a missing key: status 2, no request
echo "not json" > "$dir/budget.json"
ask 1 "$dir/prompt.txt" >/dev/null 2>"$dir/err"; st=$?
eq "broken budget: status" $st 2
if grep -q "budget.json" "$dir/err"; then ok "broken budget: names the file"; else bad "broken budget: names the file" "$(cat "$dir/err")"; fi
budget 10 0
unset ASK_KEY
ask 1 "$dir/prompt.txt" >/dev/null 2>"$dir/err"; st=$?
eq "no key: status" $st 2
eq "no key: no request" "$(requests k2)" 0
export ASK_KEY=sk-ask-secret

# a usage error
"$lt" ask --config "$dir/config.json" > /dev/null 2>"$dir/err"; st=$?
eq "usage error: status" $st 2

# --dry-run: status 0, no request, no key, no change
config k3 10/4/20/stop 0; budget 10 0.5
cp "$dir/budget.json" "$dir/before.json"
out=$(ask 1 --dry-run "$dir/prompt.txt" 2>&1); st=$?
eq "dry-run: status" $st 0
eq "dry-run: no request" "$(requests k3)" 0
if [[ "$out" == *'"max_tokens": 100'* && "$out" == *"cost_bound_usd: 0.000221"* ]]; then ok "dry-run: body and bound"; else bad "dry-run: body and bound" "$out"; fi
if [[ "$out" != *sk-ask-secret* && "$out" != *CONFIG-SECRET* ]]; then ok "dry-run: no credential"; else bad "dry-run: no credential" "$out"; fi
if cmp -s "$dir/before.json" "$dir/budget.json"; then ok "dry-run: the file is unchanged"; else bad "dry-run: the file is unchanged" changed; fi

# a failed request: status 1, no text, an entry with cost 0
config k4 0/0/0/fail 1; budget 10 0.5
out=$(ask 1 "$dir/prompt.txt" 2>/dev/null); st=$?
eq "failed request: status" $st 1
eq "failed request: no text" "$out" ""
eq "failed request: spentUsd" "$(field "b['spentUsd']")" 0.5
eq "failed request: one entry" "$(field "len(b['runs'])")" 1

# a reply cut by max_tokens: status 3, the text, the cost
config k5 10/4/20/length 0; budget 10 0
out=$(ask 1 "$dir/prompt.txt" 2>/dev/null); st=$?
eq "length: status" $st 3
eq "length: the text" "$out" "1:hello"
eq "length: spentUsd" "$(field "b['spentUsd']")" 4.8e-05

# a reply with finish_reason=error: status 1, the cost is recorded
config k5e 10/4/20/error 0; budget 10 0
out=$(ask 1 "$dir/prompt.txt" 2>/dev/null); st=$?
eq "error finish: status" $st 1
eq "error finish: spentUsd" "$(field "b['spentUsd']")" 4.8e-05

# two processes at the same time: both entries are present
config k6 10/4/20/stop 0 300; budget 10 0
ask 1 "$dir/prompt.txt" > "$dir/o1" 2>/dev/null & p1=$!
ask 1 "$dir/prompt.txt" > "$dir/o2" 2>/dev/null & p2=$!
wait $p1; s1=$?; wait $p2; s2=$?
eq "concurrent: statuses" "$s1 $s2" "0 0"
eq "concurrent: both entries" "$(field "len(b['runs'])")" 2
eq "concurrent: spentUsd" "$(field "b['spentUsd']")" 9.6e-05
eq "concurrent: requests" "$(requests k6)" 2

# two processes at the same time with budget for one
config k7 10/4/20/stop 0 300; budget 0.00025 0
ask 1 "$dir/prompt.txt" > "$dir/o1" 2>/dev/null & p1=$!
ask 1 "$dir/prompt.txt" > "$dir/o2" 2>/dev/null & p2=$!
wait $p1; s1=$?; wait $p2; s2=$?
eq "concurrent, budget for one: statuses" "$(printf '%s\n' $s1 $s2 | sort | tr '\n' ' ')" "0 1 "
eq "concurrent, budget for one: one entry" "$(field "len(b['runs'])")" 1
eq "concurrent, budget for one: one request" "$(requests k7)" 1

echo "$fails failures"
exit $((fails > 0))
