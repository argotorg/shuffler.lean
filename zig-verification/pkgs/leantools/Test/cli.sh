#!/usr/bin/env bash
# End-to-end test of the leantools CLI and daemon, run from the root of a project that builds
# Kraken (this repository):  nix develop -c pkgs/leantools/Test/cli.sh
set -u
fails=0
dir=.leantools/test
mkdir -p "$dir"
f=$dir/Cli.lean

# expect NAME TEXT CMD...: the output of CMD contains TEXT
expect() {
  local name=$1 want=$2; shift 2
  local out; out=$("$@" 2>&1)
  if [[ "$out" == *"$want"* ]]; then echo "ok   $name"
  else echo "FAIL $name: want '$want' in:"; echo "$out" | head -20 | sed 's/^/     /'; fails=$((fails + 1)); fi
}

# expect_line NAME ERE CMD...: a line of the output of CMD matches the extended regex ERE
expect_line() {
  local name=$1 want=$2; shift 2
  local out; out=$("$@" 2>&1)
  if grep -qE -- "$want" <<<"$out"; then echo "ok   $name"
  else echo "FAIL $name: want a line that matches '$want' in:"; echo "$out" | head -20 | sed 's/^/     /'; fails=$((fails + 1)); fi
}

# expect_all NAME ERE CMD...: CMD prints at least one line, and each line matches the extended regex ERE
expect_all() {
  local name=$1 want=$2; shift 2
  local out; out=$("$@" 2>&1)
  if [[ -n "$out" ]] && ! grep -qvE -- "$want" <<<"$out"; then echo "ok   $name"
  else echo "FAIL $name: want each line to match '$want'; these do not:"; grep -vE -- "$want" <<<"$out" | head -20 | sed 's/^/     /'; fails=$((fails + 1)); fi
}

# expect_fail NAME TEXT CMD...: CMD fails and its output contains TEXT
expect_fail() {
  local name=$1 want=$2; shift 2
  local out st; out=$("$@" 2>&1); st=$?
  if [[ $st -ne 0 && "$out" == *"$want"* ]]; then echo "ok   $name"
  else echo "FAIL $name: want a failure with '$want' (exit status $st) in:"; echo "$out" | head -20 | sed 's/^/     /'; fails=$((fails + 1)); fi
}

leantools stop >/dev/null
rm -rf .leantools/orig/"$f"
cat > "$f" <<'EOF'
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
  case vc3 => exact foo
EOF

expect "tools lists 18" "fuzz" leantools tools
[[ $(leantools tools | grep -c '^[a-z_]*: ') == 18 ]] && echo "ok   18 tools" || { echo "FAIL 18 tools"; fails=$((fails + 1)); }
expect "view" $'1\timport Kraken.StateCfg' leantools view_working_file --file "$f"
expect "view limit" "[lines 3-27 not shown: view from offset 3]" leantools view_working_file --file "$f" --limit 2
expect "view original" "Unknown identifier \`foo\`" leantools view_original_file --file "$f"
expect "diagnostics" "27:21: error: Unknown identifier \`foo\`" leantools lean_diagnostic_messages --file "$f"
out=$(leantools edit_working_file --file "$f" --old_string "exact foo" --new_string "sorry")
expect "edit: errors gone" "No errors." echo "$out"
expect "edit: three sorry" "3 \`sorry\`, with the goal at each" echo "$out"
expect "edit: goals at sorry" "⊢ t✝ = c.push64 ra" echo "$out"
expect "edit: same text" "No edit: the new text is the same as the old" leantools edit_working_file --file "$f" --old_string "case vc2 =>  sorry" --new_string "case vc2 => sorry"
expect "edit: no match" "No edit: old_string is not in the file" leantools edit_working_file --file "$f" --old_string "no such text" --new_string "x"
expect "edit: ambiguous" "matches 3 places" leantools edit_working_file --file "$f" --old_string "=> sorry" --new_string "=> rfl"
expect "goal of a line" "⊢ t✝ = c.push64 ra" leantools lean_goal --file "$f" --line 25
expect "goal at a column" "⊢" leantools lean_goal --file "$f" --line 25 --column 15
expect "term goal" "Program" leantools lean_term_goal --file "$f" --line 11 --column 24
expect "hover" "MachineData" leantools lean_hover_info --file "$f" --line 17 --column 25
expect "declaration" "def MachineData.push64" leantools lean_declaration_file --file "$f" --line 17 --column 25
expect "references" "references" leantools lean_references --file "$f" --line 11 --column 6
expect "outline" "touch_go" leantools lean_file_outline --file "$f"
expect "scratch" "MachineData.push64" leantools lean_run_scratch_code --file "$f" --code "#check @MachineData.push64"
expect "scratch error line" "1:8: error" leantools lean_run_scratch_code --file "$f" --code "#check nosuchname"
expect "loogle" "Mem.loadInt_storeInt" leantools lean_loogle --query "Mem.loadInt (Mem.storeInt _ _ _ _) _ _"
expect "loogle error" "unknown identifier" leantools lean_loogle --query "Mem.NoSuchThing"
# the grep checks want a line that starts with the path, so a match in this file does not count
expect_line "grep: .kraken, fixed" '^\.kraken/Kraken/X64/WP/Spec\.lean:[0-9]+:def MachineData\.push64' leantools grep --pattern "def MachineData.push64" --fixed true
expect_line "grep: .kraken, regex" '^\.kraken/Kraken/X64/WP/Spec\.lean:[0-9]+:.*theorem mov_reg32_mem' leantools grep --pattern 'theorem mov_reg32_m[e]m'
expect_line "grep: Lean sources" '^/.*/src/lean/Init/Prelude\.lean:[0-9]+:class inductive Nonempty' leantools grep --pattern "class inductive Nonempty" --fixed true
expect_line "grep: no match" '^No matches\.$' leantools grep --pattern 'no[_]such[_]text'
# grep with path: one file or one directory, of the project or of the Lean sources; the same
# rules as view_file
spec=.kraken/Kraken/X64/WP/Spec.lean
expect_all "grep path: one file" '^\.kraken/Kraken/X64/WP/Spec\.lean:[0-9]+:' leantools grep --pattern "MachineData" --fixed true --path "$spec"
expect_line "grep path: one file, the match" '^\.kraken/Kraken/X64/WP/Spec\.lean:[0-9]+:def MachineData\.push64' leantools grep --pattern "def MachineData.push64" --fixed true --path "$spec"
expect_all "grep path: a directory" '^(\.kraken/Kraken/X64/|Matching files: \.kraken/Kraken/X64/|\[[0-9]+ more (lines|characters) not shown\]$)' leantools grep --pattern "theorem" --path .kraken/Kraken/X64
expect_line "grep path: capped result lists files" '^Matching files: \.kraken/Kraken/X64/' leantools grep --pattern "theorem" --path .kraken/Kraken/X64
expect_line "grep path: a directory, the match" '^\.kraken/Kraken/X64/WP/Spec\.lean:[0-9]+:def MachineData\.push64' leantools grep --pattern "def MachineData.push64" --fixed true --path .kraken/Kraken
expect_all "grep path: not elsewhere (only a note where it is)" '^No matches in \.kraken/Kraken\. Elsewhere: .*Init/Prelude\.lean \([0-9]+ lines?\)' leantools grep --pattern "class inductive Nonempty" --fixed true --path .kraken/Kraken
init=$(leantools grep --pattern "class inductive Nonempty" --fixed true | grep -m1 '^/' | cut -d: -f1)
init=${init%/Init/*}/Init
expect_all "grep path: a directory of the Lean sources" '^/.*/src/lean/Init/' leantools grep --pattern "class inductive Nonempty" --fixed true --path "$init"
expect_fail "grep path: .leantools" "not shown" leantools grep --pattern "port" --path .leantools
expect_fail "grep path: daemon.json" "not shown" leantools grep --pattern "token" --path .leantools/daemon.json
expect_fail "grep path: .git" "not shown" leantools grep --pattern "core" --path .git
expect_fail "grep path: /etc" "outside the project and the Lean sources" leantools grep --pattern "root" --path /etc
expect_fail "grep path: dot dot" "outside the project and the Lean sources" leantools grep --pattern "root" --path ../../../../../../../../../../../../etc
# the deny list of leantools.json (the hand proofs of the shuffler fuel): not shown, left out of a search
expect_fail "view_file: a denied file" "deny list" leantools view_file --path Lift/Shuffler/Fuel.lean
expect_fail "grep path: a denied file" "deny list" leantools grep --pattern "theorem" --path Lift/Shuffler/Fuel.lean
expect_fail "view_working_file: a denied file" "deny list" leantools view_working_file --file Lift/Shuffler/Fuel.lean
expect_line "grep: a search of the project says that denied files are left out" '^\[some files are left out of this search' leantools grep --pattern "no[_]such[_]text"
expect_fail "grep path: missing" "does not exist" leantools grep --pattern "x" --path .kraken/NoSuchDir
# unknown arguments are errors that name them and the parameters
expect_fail "unknown argument: grep" 'unknown argument "paht" for grep; its parameters are pattern, path, glob, context, fixed' leantools grep --pattern x --paht .kraken
expect_fail "unknown argument: view_working_file" 'unknown argument "line" for view_working_file; its parameters are file, offset, limit' leantools view_working_file --file "$f" --line 3
expect_fail "unknown arguments: lean_loogle" 'unknown arguments "file", "path" for lean_loogle; its parameters are query, num_results' leantools lean_loogle --query "Mem.loadInt" --path x --file y
# view_file: files of the project (.kraken included) and of the Lean sources, as grep prints them
mm=.kraken/Kraken/X64/Examples/WP/Memmove.lean
expect "view_file: .kraken, offset, limit" \
  $'11\tpublic import Kraken.StateCfg\n12\tpublic import Kraken.SeparationMem\n'"[lines 13-$(wc -l < "$mm") not shown: view from offset 13]" \
  leantools view_file --path "$mm" --offset 11 --limit 2
expect_line "view_file: .kraken, from offset" $'^11\t' leantools view_file --path "$mm" --offset 11 --limit 2
src=$(leantools grep --pattern "class inductive Nonempty" --fixed true | grep -m1 '^/' | cut -d: -f1)
expect "view_file: Lean source as grep prints it" "class inductive Nonempty" leantools view_file --path "$src"
expect "view_file: project file" $'1\tmodule' leantools view_file --path VerifiedNix.lean
[ -e ".leantools/orig/VerifiedNix.lean" ] && { echo "FAIL view_file: no original"; fails=$((fails + 1)); } || echo "ok   view_file: no original"
expect "view_file: absolute path in the project" $'1\tmodule' leantools view_file --path "$PWD/VerifiedNix.lean"
# the state and build directories are not shown: the daemon token, the other working files, git
plain=$dir/Plain.lean
printf 'theorem plain : True := trivial\n' > "$plain"
expect "view_file: daemon.json" "not shown" leantools view_file --path .leantools/daemon.json
expect "view_file: another working file" "not shown" leantools view_file --path "$plain"
expect "view_file: .git" "not shown" leantools view_file --path .git/config
expect "view_file: /etc/passwd" "outside the project and the Lean sources" leantools view_file --path /etc/passwd
expect "view_file: dot dot" "outside the project and the Lean sources" leantools view_file --path ../../../../../../../../../../../../etc/passwd
ln -sfn /etc "$dir/etc-link"
expect "view_file: symlink out" "outside the project and the Lean sources" leantools view_file --path "$dir/etc-link/passwd"
expect_fail "grep path: symlink out" "outside the project and the Lean sources" leantools grep --pattern "root" --path "$dir/etc-link"
expect "view_file: missing" "does not exist" leantools view_file --path "$dir/NoSuchFile.lean"
expect "view_file: directory" "is a directory" leantools view_file --path .kraken
expect "view_file: path required" "path is required" leantools view_file
expect "history" "1 back: 1 errors" leantools history_working_file --file "$f"
expect "undo too far" "No undo" leantools undo_edit_working_file --file "$f" --steps 9
expect "undo" "Unknown identifier \`foo\`" leantools undo_edit_working_file --file "$f" --steps 1
expect "submit with errors" "Not accepted: the file must have no errors and no" leantools submit_working_file --file "$f" --reasoning "test"
expect "proof complete" "No \`sorry\`." leantools edit_working_file --file "$f" --old_string $'    with skip\n  case vc1 => sorry\n  case vc2 => sorry\n  case vc3 => exact foo' --new_string "    with kfinish"
expect "submit accepted" "Accepted: touch_go proved" leantools submit_working_file --file "$f" --reasoning "kfinish closes all VCs"
leantools edit_working_file --file "$f" --old_string "t.regs.rsp = c.regs.rsp ⦄" --new_string "True ⦄" >/dev/null
expect "submit changed statement" "touch_go: the type differs" leantools submit_working_file --file "$f" --reasoning "test"
# a removed original is frozen again from the current file, also while the daemon runs
rm -rf ".leantools/orig/$f"
expect "removed original: frozen again" "True ⦄" leantools view_original_file --file "$f"
[ -e ".leantools/orig/$f" ] && echo "ok   removed original: on disk again" || { echo "FAIL removed original: on disk again"; fails=$((fails + 1)); }
expect "outside the project" "outside the project" leantools view_working_file --file /etc/passwd
expect "dot dot" "is not allowed" leantools view_working_file --file ../x.lean
expect "unknown tool" "unknown tool" leantools no_such_tool
# fuzz: #fuzz commands after the working file, with the fuzz module; the file does not change
fz=$dir/FuzzCli.lean
cat > "$fz" <<'EOF'
import Kraken.StateCfg
import Kraken.X64.Parser

open Kraken.X64.Parser

def inc2 : Program := parse("
inc2:
  addq $2, %rax
  ret
")

theorem later : True := by
  sorry
EOF
fuzzcmd() {
  printf '#fuzz inc2 args (c : MachineData) (ra : Int64) with\n  (gen := do return (← Fuzz.stack (← Fuzz.machine), Fuzz.ret))\n  (start := c.push64 ra)\n  (invariant := fun {s₀} l s'"'"' => match l with | "inc2" => s'"'"' = s₀ | _ => False)\n  (variant := fun _ _ => 0)\n  (post := fun a t => a = ra ∧ t.regs.rax = c.regs.rax + %s)\n  (runs := 20)' "$1"
}
before=$(cat "$fz")
expect "fuzz: a correct spec" "20 samples (0 skipped by pre), 20 label visits: no check failed." leantools fuzz --file "$fz" --code "$(fuzzcmd 2)"
expect "fuzz: a wrong postcondition" "postcondition, conjunct 2, false at the exit" leantools fuzz --file "$fz" --code "$(fuzzcmd 1)"
out=$(leantools fuzz --file "$fz" --code "$(fuzzcmd 2)" 2>&1)
[[ "$out" != *"sorry"* ]] && echo "ok   fuzz: not the working file's messages" || { echo "FAIL fuzz: not the working file's messages"; fails=$((fails + 1)); }
[[ "$(cat "$fz")" == "$before" ]] && echo "ok   fuzz: the working file is unchanged" || { echo "FAIL fuzz: the working file is unchanged"; fails=$((fails + 1)); }
expect "fuzz: an error in the code" "1:7: error" leantools fuzz --file "$fz" --code "#fuzz nosuchprog args with (gen := pure ()) (start := default) (invariant := fun _ _ => True) (variant := fun _ _ => 0)"
# the fuzz test of `vcgen` (VerifiedNix.Fuzz): its `fuzz:` message is in the reports of edits,
# undos and submissions
fv=$dir/FuzzVcgen.lean
rm -rf .leantools/orig/"$fv"
cat > "$fv" <<'EOF'
import VerifiedNix.X64Specs

open Kraken.X64.Parser
open Std.WP
open scoped Program.WP

set_option experimental.vcgen true

def cnt : Program := parse("
cnt:
  xorq %rax, %rax
  testq %rdi, %rdi
  je .Ldone
.Lnext:
  addq $1, %rax
  cmpq %rax, %rdi
  jne .Lnext
.Ldone:
  ret
")

theorem cnt_spec [Host] [FunDecls] (c : MachineData) (ra : Int64) (n : Nat) (hn : c.regs.rdi.toNat = n) :
    ⦃ fun s₀ => s₀ = c.push64 ra ⦄ cnt
    ⦃ fun _ _ => False; fun a t => a = ra ∧ t.regs.rax = c.regs.rdi ∧ t.regs.rsp = c.regs.rsp ⦄ := by
  sorry
EOF
cntproof() {
  printf '  vcgen [cnt]\n    invariants\n    · fun {s₀} l s'"'"' => match l with\n      | "cnt" => s'"'"' = s₀\n'
  printf '      | ".Lnext" => s'"'"'.regs.rax.toNat %s < n ∧ s'"'"'.regs.rdi = c.regs.rdi ∧ s'"'"'.regs.rsp = s₀.regs.rsp ∧ s'"'"'.dmem = s₀.dmem\n' "$1"
  printf '      | ".Ldone" => s'"'"'.regs.rax = c.regs.rdi ∧ s'"'"'.regs.rsp = s₀.regs.rsp ∧ s'"'"'.dmem = s₀.dmem\n      | _ => False\n'
  printf '    · fun l s'"'"' => match l with\n      | "cnt" => n\n      | ".Lnext" => n - s'"'"'.regs.rax.toNat\n      | _ => 0\n    with kfinish'
}
leantools view_original_file --file "$fv" >/dev/null
fuzzline='^25:3: info: fuzz: 200 samples \(0 skipped by pre\), [0-9]+ label visits: 1 failures$'
out=$(leantools edit_working_file --file "$fv" --old_string "  sorry" --new_string "$(cntproof "+ 1")" 2>&1)
grep -qE "$fuzzline" <<<"$out" && grep -qE "^sample [0-9]+: invariant at .Lnext, conjunct 1, false at a visit: s'.regs.rax.toNat \+ 1 < n$" <<<"$out" \
  && echo "ok   vcgen fuzz: the edit reply" || { echo "FAIL vcgen fuzz: the edit reply:"; echo "$out" | head -12 | sed 's/^/     /'; fails=$((fails + 1)); }
out=$(leantools edit_working_file --file "$fv" --old_string "s'.regs.rax.toNat + 1 < n" --new_string "s'.regs.rax.toNat < n" 2>&1)
[[ "$out" == *"No errors."* && "$out" != *"fuzz:"* ]] && echo "ok   vcgen fuzz: a correct invariant, no message" \
  || { echo "FAIL vcgen fuzz: a correct invariant, no message:"; echo "$out" | head -8 | sed 's/^/     /'; fails=$((fails + 1)); }
expect_line "vcgen fuzz: the undo reply" "$fuzzline" leantools undo_edit_working_file --file "$fv"
expect_line "vcgen fuzz: the submission reply" "$fuzzline" leantools submit_working_file --file "$fv" --reasoning "test"
# an edit that raises maxHeartbeats above the limit is refused, and the file does not change
before=$(cat "$fz")
expect "heartbeats: refused" "No edit: it sets maxHeartbeats to 4000000; the limit here is 400000" leantools edit_working_file --file "$fz" --old_string "theorem later" --new_string $'set_option maxHeartbeats 4000000 in\ntheorem later'
expect "heartbeats: 0 refused" "No edit: it sets maxHeartbeats to 0" leantools edit_working_file --file "$fz" --old_string "theorem later" --new_string $'set_option maxHeartbeats 0 in\ntheorem later'
[[ "$(cat "$fz")" == "$before" ]] && echo "ok   heartbeats: the file is unchanged" || { echo "FAIL heartbeats: the file is unchanged"; fails=$((fails + 1)); }
expect "heartbeats: below the limit" "1 \`sorry\`" leantools edit_working_file --file "$fz" --old_string "theorem later" --new_string $'set_option maxHeartbeats 300000 in\ntheorem later'
# an unknown name: the reply names declarations with the same last part (from loogle)
fh=$dir/Hint.lean
rm -rf .leantools/orig/"$fh"
printf 'import Kraken.StateCfg\n\ntheorem t (s : MachineData) : ¬ s.StackBelow s := by\n  sorry\n' > "$fh"
leantools view_original_file --file "$fh" >/dev/null
expect "unknown name: the declaration" "declarations with this last part: Program.WP.MachineData.not_stackBelow_self" \
  leantools edit_working_file --file "$fh" --old_string "  sorry" --new_string "  exact MachineData.not_stackBelow_self s"
expect "unknown name: a local name has no hint" "Unknown identifier \`hzz\`" \
  leantools edit_working_file --file "$fh" --old_string "exact MachineData.not_stackBelow_self s" --new_string "exact hzz"
out=$(leantools view_working_file --file "$fh" 2>&1); out=$(leantools edit_working_file --file "$fh" --old_string "exact hzz" --new_string "exact hzz2" 2>&1)
[[ "$out" != *"declarations with this last part"* ]] && echo "ok   unknown name: no hint for a local name" || { echo "FAIL unknown name: no hint for a local name"; fails=$((fails + 1)); }
# grep with path and no match: the reply names the other files where the pattern occurs
out=$(leantools grep --pattern "push64_stackBelow" --fixed true --path .kraken 2>&1)
[[ "$out" == "No matches in .kraken. Elsewhere: "* && "$out" == *"VerifiedNix/X64Specs.lean ("*" lines)"* && "$out" != *"./"* ]] \
  && echo "ok   grep path: no match, elsewhere" || { echo "FAIL grep path: no match, elsewhere:"; echo "$out" | head -3 | sed 's/^/     /'; fails=$((fails + 1)); }
expect_line "grep path: no match anywhere" '^No matches\.$' leantools grep --pattern 'no[_]such[_]text' --path .kraken
# a goal of the last check report is one line in the next report; a submission shows each goal
fs=$dir/Seen.lean
rm -rf .leantools/orig/"$fs"
printf 'import Kraken.StateCfg\n\ntheorem a : 1 = 1 := by\n  sorry\n\ntheorem b : 2 = 2 := by\n  sorry\n' > "$fs"
leantools view_original_file --file "$fs" >/dev/null
expect "seen: the first edit shows each goal" "⊢ 2 = 2" leantools edit_working_file --file "$fs" --old_string "1 = 1" --new_string "3 = 3"
out=$(leantools edit_working_file --file "$fs" --old_string "3 = 3" --new_string "4 = 4" 2>&1)
[[ "$out" == *"⊢ 4 = 4"* && "$out" != *"⊢ 2 = 2"* && "$out" == *"--- sorry at 7:3: the goal is unchanged since the last check of this file"* ]] \
  && echo "ok   seen: the next edit shows only the new goal" || { echo "FAIL seen: the next edit shows only the new goal:"; echo "$out" | head -8 | sed 's/^/     /'; fails=$((fails + 1)); }
expect "seen: an undo shows the goal of the version before" "⊢ 3 = 3" leantools undo_edit_working_file --file "$fs"
expect_fail "seen: a submission shows each goal" "⊢ 2 = 2" leantools submit_working_file --file "$fs" --reasoning "x"
# a check that does not end in `checkSeconds` (5 here) stops at once: the edit is undone, the Lean
# worker of the file ends (the elaboration does not go on), and the next edit has a normal check
cp leantools.json "$dir/leantools.json.bak"
trap 'cp "$dir/leantools.json.bak" leantools.json' EXIT
sed 's/ *}$/, "checkSeconds": 5 }/' "$dir/leantools.json.bak" > leantools.json
leantools stop >/dev/null
ft=$dir/Slow.lean
rm -rf .leantools/orig/"$ft"
printf 'import Kraken.StateCfg\n\ntheorem t : True := by\n  sorry\n' > "$ft"
expect "timeout: a fast check" "1 \`sorry\`" leantools view_original_file --file "$ft"
slow_workers() { pgrep -f "^[^ ]*/lean --worker file://.*/Slow\.lean"; }
# the CPU ticks (1/100 s) of the workers of Slow.lean in 3 s
slow_cpu() {
  local a=0 b=0 p
  for p in $(slow_workers); do a=$((a + $(awk '{print $14 + $15}' /proc/$p/stat 2>/dev/null || echo 0))); done
  sleep 3
  for p in $(slow_workers); do b=$((b + $(awk '{print $14 + $15}' /proc/$p/stat 2>/dev/null || echo 0))); done
  echo $((b - a))
}
w1=$(slow_workers)
[[ -n "$w1" ]] && echo "ok   timeout: the worker" || { echo "FAIL timeout: the worker"; fails=$((fails + 1)); }
t0=$SECONDS
expect "timeout: undone" "did not end in 5 s" leantools edit_working_file --file "$ft" --old_string "theorem t" \
  --new_string $'#eval Id.run do\n  let mut x := 0\n  for i in [0:2000000000] do x := x + i\n  return x\n\ntheorem t'
(( SECONDS - t0 < 40 )) && echo "ok   timeout: at once ($((SECONDS - t0)) s)" || { echo "FAIL timeout: at once ($((SECONDS - t0)) s)"; fails=$((fails + 1)); }
for _ in $(seq 50); do st=$(ps -o stat= -p "$w1" 2>/dev/null); [[ -z "$st" || "$st" == Z* ]] && break; sleep 0.1; done
[[ -z "$st" || "$st" == Z* ]] && echo "ok   timeout: the worker has ended" || { echo "FAIL timeout: the worker has ended ($st)"; fails=$((fails + 1)); }
ticks=$(slow_cpu)
(( ticks < 100 )) && echo "ok   timeout: no elaboration goes on ($ticks ticks in 3 s)" || { echo "FAIL timeout: no elaboration goes on ($ticks ticks in 3 s)"; fails=$((fails + 1)); }
[[ "$(cat "$ft")" == *"theorem t : True"* && "$(cat "$ft")" != *"#eval"* ]] && echo "ok   timeout: the file is the old one" || { echo "FAIL timeout: the file is the old one"; fails=$((fails + 1)); }
expect "timeout: the next edit" "1 \`sorry\`" leantools edit_working_file --file "$ft" --old_string "True" --new_string "1 = 1"
cp "$dir/leantools.json.bak" leantools.json
leantools stop >/dev/null
# `stop` returns when the daemon has ended, so a call right after it goes to a new daemon
old=$(grep -o '"pid":[0-9]*' .leantools/daemon.json | cut -d: -f2)
leantools stop >/dev/null
for _ in $(seq 50); do st=$(ps -o stat= -p "$old" 2>/dev/null); [[ -z "$st" || "$st" == Z* ]] && break; sleep 0.1; done
[[ -z "$st" || "$st" == Z* ]] && echo "ok   stop: the daemon has ended" || { echo "FAIL stop: the daemon has ended ($st)"; fails=$((fails + 1)); }
[ -e .leantools/daemon.json ] && { echo "FAIL stop: daemon.json removed"; fails=$((fails + 1)); } || echo "ok   stop: daemon.json removed"
out=$(leantools view_original_file --file "$f" 2>&1)
[[ "$out" == *"Check of the original:"* && "$out" != *"the Lean server stopped"* ]] && echo "ok   a call after stop" \
  || { echo "FAIL a call after stop:"; echo "$out" | tail -3 | sed 's/^/     /'; fails=$((fails + 1)); }
leantools stop >/dev/null
echo "$fails failures"
exit $((fails > 0))
