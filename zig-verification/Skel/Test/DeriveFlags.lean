import Lift.P1.Command
import Lift.P1.Execution
import Lift.Level2.Code
import Skel.Gen.Derive.Blocks
import Skel.Gen.Generate
import Skel.Gen.Derived.Level2z
import Skel.Gen.Derived.Pilot

/-! The kept flags of the derived blocks (task L2-FLAGS). The module is checked by `lake build Skel.Test.DeriveFlags`:
each `#eval` throws when a check fails.

* **Synthetic functions.** `zfn`: the branch of the second block reads `zf` of the `cmpq` of the entry block, so the entry
  block keeps `zf` with the value `rdi = rsi`. `zfinc`: an `incq` after the `cmpq` sets `zf` again, so the kept value is
  that of the `incq` (`rcx + 1 = 0`), not that of the compare. `cfin`: the entry block reads `cf` of the caller: no block
  keeps it, and the derivation refuses the block.
* **l2zFlags.** The entry block keeps `cf` and `zf` of `cmpq %rsi, %rdi`; LBB16_3 derives.
* **No change elsewhere.** Each derived block of level2z and of the pilot but the entry of `l2zFlags` has no kept flag. -/

open Lean Meta Elab Term Skel.Gen Skel.Gen.Derive

namespace DeriveFlagsCode

def program : Program := level2Program(r#"
.Lau.zfn:
zfn:
 cmpq %rsi, %rdi
 jmp .LBB0_1
.LBB0_1:
 je .LBB0_2
 movq %rdi, %rax
 retq
.LBB0_2:
 movq %rsi, %rax
 retq
.Lfunc_end0:
.Lau.zfinc:
zfinc:
 cmpq %rsi, %rdi
 incq %rcx
 jmp .LBB1_1
.LBB1_1:
 je .LBB1_2
 movq %rdi, %rax
 retq
.LBB1_2:
 movq %rsi, %rax
 retq
.Lfunc_end1:
.Lau.cfin:
cfin:
 jb .LBB2_1
 movq %rdi, %rax
 retq
.LBB2_1:
 movq %rsi, %rax
 retq
.Lfunc_end2:
"#)

def sizes : List Nat := program.map fun d => match d with | .label _ => 0 | _ => 4

def code : _root_.Executable := ⟨1048576, program.zipWith (fun d n => ⟨d, n⟩) sizes⟩

end DeriveFlagsCode

#lift_exact DeriveFlagsCode.code as DeriveFlagsCode.L1

#derive_blocks DeriveFlagsCode.derived DeriveFlagsCode.L1.step DeriveFlagsCode.code ["zfn", "zfinc", "cfin"]

namespace DeriveFlagsTests

def check (ok : Bool) (what : String) : TermElabM Unit := unless ok do throwError "FAIL: {what}"

/-- The part of the block at `off` of `fn` in `d`. -/
def partAt (d : Derived) (fn : String) (off : Nat) : Except String Part := do
  let some parts := d.lookup fn | throw s!"{fn}: no function"
  let some r := parts.lookup off | throw s!"{fn}: no block at {off}"
  r.mapError fun e => s!"{fn} o{off}: {repr e}"

/-- The text of the kept flags of a part. -/
def flagsShow (p : Part) : List (String × String) := p.flags.map fun (f, c) => (f.name, c.show)

/-- The offsets of the blocks of `fn`. -/
def offsets (d : Derived) (fn : String) : List Nat := ((d.lookup fn).getD []).map (·.1)

#eval show TermElabM Unit from do
  let d := DeriveFlagsCode.derived
  -- zfn: the entry keeps zf of the compare; the next block branches on the flag of its start and keeps no flag
  let [o0, o1, _, _] := offsets d "zfn" | throwError "zfn: {offsets d "zfn"} blocks"
  match partAt d "zfn" o0, partAt d "zfn" o1 with
  | .ok e, .ok n =>
    check (flagsShow e == [("zf", "(Reg64.rdi = Reg64.rsi)")]) s!"zfn entry keeps zf = (rdi = rsi): {flagsShow e}"
    check (flagsShow n == []) s!"zfn LBB0_1 keeps no flag: {flagsShow n}"
    match n.term with
    | .branch (.flag .zf) _ _ => pure ()
    | .branch c _ _ => throwError "zfn LBB0_1: the branch reads {c.show}, not the flag zf of its start"
    | _ => throwError "zfn LBB0_1: no branch"
  | e, n => throwError "zfn: {repr (e.toOption.isSome, n.toOption.isSome)} {match e with | .error m => m | _ => ""} {match n with | .error m => m | _ => ""}"
  -- zfinc: the last flag writer before the exit is `incq %rcx`: zf is that of the `incq`, cf is not live
  match partAt d "zfinc" 0 with
  | .ok e =>
    check (flagsShow e == [("zf", "(Reg64.rcx + 1 = 0)")] || (flagsShow e).map (·.1) == ["zf"] && !((flagsShow e).any (·.2 == "(Reg64.rdi = Reg64.rsi)")))
      s!"zfinc entry keeps zf of the incq, not of the compare: {flagsShow e}"
    check ((flagsShow e).all (·.2 != "(Reg64.rdi = Reg64.rsi)")) s!"zfinc: zf is not the compare: {flagsShow e}"
  | .error m => throwError "zfinc: {m}"
  -- cfin: the entry reads cf of the caller: refused
  match partAt d "cfin" 0 with
  | .error m => check ((m.splitOn "no block keeps the flags").length > 1) s!"cfin: the refusal names the cause: {m}"
  | .ok p => throwError "cfin: the entry derives with a flag input of the caller: {flagsShow p}"

#eval show TermElabM Unit from do
  -- l2zFlags: the entry keeps cf and zf of `cmpq %rsi, %rdi`; LBB16_3 (offset 8) derives and keeps no flag
  match partAt Skel.Gen.Derived.level2z "l2zFlags" 0, partAt Skel.Gen.Derived.level2z "l2zFlags" 8 with
  | .ok e, .ok b =>
    check (flagsShow e == [("cf", "¬(Reg64.rsi ≤ Reg64.rdi)"), ("zf", "(Reg64.rdi = Reg64.rsi)")])
      s!"l2zFlags entry keeps cf, zf: {flagsShow e}"
    check (flagsShow b == []) s!"l2zFlags LBB16_3 keeps no flag: {flagsShow b}"
  | .error m, _ | _, .error m => throwError "l2zFlags: {m}"

#eval show TermElabM Unit from do
  -- no other block of level2z and of the pilot keeps a flag
  let ds : List (String × Derived) := [("level2z", Skel.Gen.Derived.level2z), ("pilot", Skel.Gen.Derived.pilot)]
  let parts : List (String × String × Nat × Part) := ds.flatMap fun (name, d) =>
    d.flatMap fun (fn, ps) => ps.filterMap fun (off, r) => r.toOption.map fun p => (name, fn, off, p)
  let n := parts.length
  let bad := parts.filter fun (_, fn, off, p) => !(fn == "l2zFlags" && off == 0) && !p.flags.isEmpty
  check bad.isEmpty s!"blocks that keep a flag: {bad.map fun (name, fn, off, p) => (name, fn, off, flagsShow p)}"
  check (n > 100) s!"{n} derived blocks"
  logInfo m!"{n} derived blocks: only the entry of l2zFlags keeps a flag"

end DeriveFlagsTests
