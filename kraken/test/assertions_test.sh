#!/usr/bin/env bash
# Test assertion failures in child processes, using the production implementation.
set -euo pipefail
dir=$(cd "$(dirname "$0")/.." && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

build=${1:-$dir/../build}
bin=$build/kraken/c
cmake -S "$dir/.." -B "$build" -G Ninja -DBUILD_TESTING=ON >/dev/null
cmake --build "$build" --target shuffler_harness_process_test shuffler_assertion_test \
	shuffler_bbu_harness shuffler_pop_harness shuffler_surplus_harness shuffler_lowest_harness >/dev/null
"$bin/harness_process_test" 2> "$tmp/helper-err"
printf 'invalid: child process failed\n' > "$tmp/helper-want"
cmp "$tmp/helper-want" "$tmp/helper-err"
echo "ok C process helper: keeps return values, exit status and buffer writes"

"$bin/shuffler_assertion_test" success
"$bin/shuffler_assertion_test" assembly-success

fails=0
for name in empty-stack duplicate-spill nonvariable-spill unavailable-target \
	assembly-empty-stack assembly-duplicate-spill assembly-nonvariable-spill assembly-unavailable-target; do
	status=0
	"$bin/shuffler_assertion_test" "$name" > "$tmp/out" 2> "$tmp/err" || status=$?
	if [ "$status" -ne 1 ] || [ -s "$tmp/out" ] || [ -s "$tmp/err" ]; then
		echo "FAIL $name: expected exit status 1 and no output; got $status" >&2
		cat "$tmp/out" "$tmp/err" >&2
		fails=$((fails + 1))
	else
		echo "ok $name: exit status 1"
	fi
done

# An assertion must not prevent the differential harness from reading later cases.
cat > "$tmp/bbu-cases" <<'EOF'
0 1 2 0
0 0 0
0 1 3 0
EOF
cat > "$tmp/bbu-want" <<'EOF'
assertion
ok |
ok p 3 | 3
EOF
"$bin/bbu_harness" run < "$tmp/bbu-cases" > "$tmp/bbu-got"
cmp "$tmp/bbu-want" "$tmp/bbu-got"
echo "ok bbu harness: reads cases after exit(1)"

cat > "$tmp/pop-cases" <<'EOF'
pop;;;;;1
pop;;;;;0
bad
pop;;;;;0
EOF
cat > "$tmp/pop-want" <<'EOF'
err
ok;;;;;0
bad input
ok;;;;;0
EOF
"$bin/pop_harness" < "$tmp/pop-cases" > "$tmp/pop-got"
cmp "$tmp/pop-want" "$tmp/pop-got"
echo "ok pop harness: reads cases after exit(1)"

for name in surplus lowest; do
	printf '%s;;;;\nbad\n%s;;;;\n' "$name" "$name" > "$tmp/cases"
	printf 'ok;;;\nbad input\nok;;;\n' > "$tmp/want"
	"$bin/${name}_harness" < "$tmp/cases" > "$tmp/got"
	cmp "$tmp/want" "$tmp/got"
	echo "ok $name harness: reads each case"
done
[ "$fails" -eq 0 ]
