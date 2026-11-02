#!/usr/bin/env bash
# Check assembly generation, dependencies, and compiler failures in a separate build tree.
set -euo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
tmp=$(mktemp -d)
proof_asm="$root/build/kraken/c/build_bottom_up.S"
cleanup() {
	if [ -f "$tmp/proof-assembly.S" ]; then cp "$tmp/proof-assembly.S" "$proof_asm"; fi
	rm -rf "$tmp"
}
trap cleanup EXIT

mkdir -p "$tmp/src/kraken/c"
cp "$root/CMakeLists.txt" "$tmp/src/"
cp "$root/kraken/c/CMakeLists.txt" "$root/kraken/c/labels.awk" "$tmp/src/kraken/c/"
cp -R "$root/kraken/c/shuffler" "$tmp/src/kraken/c/"
cp "$root/kraken/c/generate_assembly.sh" "$tmp/src/kraken/c/"

export ASSEMBLY_TEST_CXX=${SHUFFLER_ASM_CXX:-g++}
export ASSEMBLY_TEST_LOG="$tmp/compilations"
cat > "$tmp/cxx" <<'EOF'
#!/usr/bin/env bash
for arg in "$@"; do
	if [ "$arg" = -S ]; then printf 'compile\n' >> "$ASSEMBLY_TEST_LOG"; fi
done
exec "$ASSEMBLY_TEST_CXX" "$@"
EOF
chmod +x "$tmp/cxx"
cmake -S "$tmp/src" -B "$tmp/build" -G Ninja -DBUILD_TESTING=OFF \
	-DSHUFFLER_ASM_CXX="$tmp/cxx" > "$tmp/configure.log"
build() { cmake --build "$tmp/build" --target shuffler_assembly > "$tmp/build.log" 2>&1; }
asm="$tmp/build/kraken/c/build_bottom_up.S"

build || { cat "$tmp/build.log" >&2; exit 1; }
[ -s "$asm" ]
grep -q '^plan:$' "$asm"
grep -Eq 'call[[:space:]]+exit' "$asm"
[ "$(wc -l < "$ASSEMBLY_TEST_LOG")" -eq 1 ]
build
[ "$(wc -l < "$ASSEMBLY_TEST_LOG")" -eq 1 ]
echo 'ok assembly build: generates the program and skips unchanged inputs'

rm "$asm"
build
[ -s "$asm" ]
[ "$(wc -l < "$ASSEMBLY_TEST_LOG")" -eq 2 ]
echo 'ok assembly build: restores a missing output'

printf '\n#error assembly_dependency_test\n' >> "$tmp/src/kraken/c/shuffler/Stack.h"
if build; then echo 'FAIL assembly build: accepts a source error' >&2; exit 1; fi
grep -q assembly_dependency_test "$tmp/build.log"
[ "$(wc -l < "$ASSEMBLY_TEST_LOG")" -eq 3 ]
echo 'ok assembly build: checks header changes and reports compiler errors'

cp "$root/kraken/c/shuffler/Stack.h" "$tmp/src/kraken/c/shuffler/Stack.h"
build
[ -s "$asm" ]
[ "$(wc -l < "$ASSEMBLY_TEST_LOG")" -eq 4 ]
echo 'ok assembly build: succeeds after the source error is removed'

rm "$asm"
export ASSEMBLY_TEST_CXX=false
if build; then echo 'FAIL assembly build: accepts a failed compiler' >&2; exit 1; fi
[ ! -e "$asm" ]
echo 'ok assembly build: compiler failure leaves no assembly output'

printf '#!/usr/bin/env bash\nprintf "0.0.0\\n"\n' > "$tmp/other-version"
chmod +x "$tmp/other-version"
export ASSEMBLY_TEST_CXX="$tmp/other-version"
if build; then echo 'FAIL assembly build: accepts a different compiler version' >&2; exit 1; fi
grep -q 'requires GCC 15.3.0' "$tmp/build.log"
[ ! -e "$asm" ]
echo 'ok assembly build: rejects a different compiler version'

# Use the production Lake dependency, including when proof objects already exist.
rm -f "$proof_asm"
(cd "$root" && LEAN_NUM_THREADS=1 nice lake build BbuKraken.AsmTest) > "$tmp/proof.log" 2>&1 \
	|| { cat "$tmp/proof.log" >&2; exit 1; }
[ -s "$proof_asm" ]
echo 'ok proof build: generates a missing assembly input before checking proofs'

cp "$proof_asm" "$tmp/proof-assembly.S"
printf '\n\tassembly_trace_failure\n' >> "$proof_asm"
if (cd "$root" && LEAN_NUM_THREADS=1 nice lake build BbuKraken.AsmTest) \
	> "$tmp/trace-failure.log" 2>&1; then
	echo 'FAIL proof build: accepts changed invalid assembly with cached proofs' >&2
	exit 1
fi
grep -q 'unsupported instruction: assembly_trace_failure' "$tmp/trace-failure.log"
cp "$tmp/proof-assembly.S" "$proof_asm"
rm "$tmp/proof-assembly.S"
(cd "$root" && LEAN_NUM_THREADS=1 nice lake build BbuKraken.AsmTest) > "$tmp/proof.log" 2>&1 \
	|| { cat "$tmp/proof.log" >&2; exit 1; }
echo 'ok proof build: changed assembly invalidates cached proofs'

mkdir "$tmp/fail-bin"
cat > "$tmp/fail-bin/cmake" <<'EOF'
#!/usr/bin/env bash
echo assembly_build_failure >&2
exit 42
EOF
chmod +x "$tmp/fail-bin/cmake"
if (cd "$root" && PATH="$tmp/fail-bin:$PATH" LEAN_NUM_THREADS=1 nice lake build BbuKraken.AsmTest) \
	> "$tmp/failure.log" 2>&1; then
	echo 'FAIL proof build: accepts a failed assembly build' >&2
	exit 1
fi
grep -q assembly_build_failure "$tmp/failure.log"
echo 'ok proof build: a generation failure stops a build with cached proofs'
