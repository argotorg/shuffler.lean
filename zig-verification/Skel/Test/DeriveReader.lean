import Lift.P1.Command
import Lift.P1.Execution
import Lift.Level2.Code
import Skel.Gen.Derive.Blocks
import Skel.Test.DeriveReadForms

/-! The reader rules of task READER (W12 of `docs/design/llm-rungs-20261120.md`; the causes D1 to D3 of
`docs/research/shuffler-census-23-20261119.md`, section 4). The module is checked by `lake build Skel.Test.DeriveReader`:
each `#eval` throws when a check fails. No `set_option` changes a limit.

* **D1.** Two zero tests in one condition: `a = 0 ∧ b = 0` (`setne; sete; orb; je`, and `notq; orq; cmove`) is
  `a ||| b = 0`; the implication `a = 0 → ¬ b = 0` (the same with `jne`) is `¬ (a ||| b = 0)`.
* **D2.** The zero flag of a `from_result` that `simp` did not reduce (a load, a `push` or a `pop` between the compare and
  the jump): `(from_result r f).zf` is `r = 0`.
* **D3.** An operand of a borrow that is not one cast: the narrow literal borrow of a 32-bit `lea` (`(C + (S % 2^32) % 2^64)
  % M = S % M - K`), the 64-bit borrow of a sum (`addq; cmpq; jbe`: `(↑(2^64 - a) + S) % 2^64 = S % 2^64 - ↑a`), and the
  cast of a `Nat` mask (`andq` with a literal, then `cmpq $1; sbb`: `↑(K &&& x.toNat)`).

Each rule has a synthetic function (derived, read, and compared with the raw terms on random states) and small terms
(compared with the raw proposition on the edge states of `rax`, `rbx`), and negative cases that the reader still refuses. -/

open Lean Meta Elab Term Skel.Gen Skel.Gen.Derive DeriveSiteTests DeriveRunTests DeriveWalkTests DeriveReadTests
  DeriveReadFormsTests

namespace DeriveReaderCode

def program : Program := level2Program(r#"
.Lrd.d1je:
d1je:
 testq %rdi, %rdi
 setne %al
 testq %rsi, %rsi
 sete %cl
 orb %al, %cl
 je .Lt_d1je
 xorl %edx, %edx
 retq
.Lt_d1je:
 movl $1, %edx
 retq
.Lfunc_end0:
.Lrd.d1jne:
d1jne:
 testq %rdi, %rdi
 setne %al
 testq %rsi, %rsi
 sete %cl
 orb %al, %cl
 jne .Lt_d1jne
 xorl %edx, %edx
 retq
.Lt_d1jne:
 movl $1, %edx
 retq
.Lfunc_end1:
.Lrd.d1cmov:
d1cmov:
 notq %rax
 orq %rcx, %rax
 cmoveq %rdx, %r12
 retq
.Lfunc_end2:
.Lrd.d2load:
d2load:
 cmpb %bl, %al
 movq 8(%rdi), %rsi
 jne .Lt_d2load
 xorl %edx, %edx
 retq
.Lt_d2load:
 movl $1, %edx
 retq
.Lfunc_end3:
.Lrd.d2push:
d2push:
 testb %al, %al
 pushq $3
 popq %rcx
 cmovel %edx, %ecx
 retq
.Lfunc_end4:
.Lrd.d3lea:
d3lea:
 leal -1(%rsi), %eax
 cmpb $2, %al
 jb .Lt_d3lea
 xorl %edx, %edx
 retq
.Lt_d3lea:
 movl $1, %edx
 retq
.Lfunc_end5:
.Lrd.d3add:
d3add:
 addq %rdx, %rcx
 cmpq %rsi, %rcx
 jbe .Lt_d3add
 xorl %edx, %edx
 retq
.Lt_d3add:
 movl $1, %edx
 retq
.Lfunc_end6:
.Lrd.d3and:
d3and:
 movabsq $280375465082880, %rax
 andq %rsi, %rax
 cmpq $1, %rax
 jb .Lt_d3and
 xorl %edx, %edx
 retq
.Lt_d3and:
 movl $1, %edx
 retq
.Lfunc_end7:
"#)

def sizes : List Nat := program.map fun d => match d with | .label _ => 0 | _ => 4

def code : _root_.Executable := ⟨1048576, program.zipWith (fun d n => ⟨d, n⟩) sizes⟩

def fns : List String := ["d1je", "d1jne", "d1cmov", "d2load", "d2push", "d3lea", "d3add", "d3and"]

end DeriveReaderCode

#lift_exact DeriveReaderCode.code as DeriveReaderCode.L1

#derive_blocks DeriveReaderCode.derived DeriveReaderCode.L1.step DeriveReaderCode.code
  ["d1je", "d1jne", "d1cmov", "d2load", "d2push", "d3lea", "d3add", "d3and"]

namespace DeriveReaderTests

/-- The part of the first block of the function `fn`. -/
def rdPart (fn : String) : Except String Part := do
  let some parts := DeriveReaderCode.derived.lookup fn | throw s!"{fn}: no function"
  let some r := parts.lookup 0 | throw s!"{fn}: no block at 0"
  r.mapError fun e => s!"{fn}: {repr e}"

/-- The condition of the branch of the first block of `fn`, as text. -/
def rdCond (fn : String) : Except String String := do
  match (← rdPart fn).term with
  | .branch c _ _ => pure c.show
  | _ => throw s!"{fn}: no branch"

/-- The value of the register `r` in the first block of `fn`, as text. -/
def rdReg (fn : String) (r : Reg64) : Except String String := do
  pure (regVal (← rdPart fn).regs r).show

end DeriveReaderTests

open DeriveReaderTests

/-! ## The synthetic functions: each entry block derives with the condition or value of its rule -/

#eval show TermElabM Unit from do
  let items : List (String × Except String String × String) := [
    -- D1: `setne; sete; orb; je` is the zero test of the `orb` of the two `setcc` bytes
    ("d1je", rdCond "d1je", "(((setcc (Reg64.rsi = 0)) ||| (setcc ¬(Reg64.rdi = 0))) = 0)"),
    -- D1: with `jne`, the negation
    ("d1jne", rdCond "d1jne", "¬(((setcc (Reg64.rsi = 0)) ||| (setcc ¬(Reg64.rdi = 0))) = 0)"),
    -- D1: `notq; orq; cmove`
    ("d1cmov r12", rdReg "d1cmov" .r12, "(if (((~~~Reg64.rax) ||| Reg64.rcx) = 0) then Reg64.rdx else Reg64.r12)"),
    -- D2: the zero flag of `cmpb` after a load
    ("d2load", rdCond "d2load", "¬((zext8 Reg64.rax) = (zext8 Reg64.rbx))"),
    -- D2: the zero flag of `testb` after `push; pop` (the `pop` is a load)
    ("d2push rcx", rdReg "d2push" .rcx, "(if ((zext8 Reg64.rax) = 0) then zext32 Reg64.rdx else zext32 load0)"),
    -- D3: the borrow of `cmpb $2` of a 32-bit `lea` (no borrow: the fall-through target first)
    ("d3lea", rdCond "d3lea", "(2 ≤ (zext8 (Reg64.rsi + 18446744073709551615)))"),
    -- D3: the borrow of `cmpq` of a sum
    ("d3add", rdCond "d3add", "((Reg64.rdx + Reg64.rcx) ≤ Reg64.rsi)"),
    -- D3: the borrow of `cmpq $1` of a masked value (`andq` with a literal)
    ("d3and", rdCond "d3and", "(1 ≤ (280375465082880 &&& Reg64.rsi))")]
  let bad := items.filterMap fun (what, got, want) => match got with
    | .ok s => if s == want then none else some s!"{what}: {s}, expected {want}"
    | .error e => some s!"{what}: {e}"
  check bad.isEmpty s!"the conditions and values of the rules: {bad}"

#eval show TermElabM Unit from do
  -- each block of the synthetic functions derives
  for fn in DeriveReaderCode.fns do
    let some parts := DeriveReaderCode.derived.lookup fn | throwError "{fn}: no function"
    for (o, r) in parts do
      if let .error e := r then throwError "check failed: {fn} o{o} does not derive: {repr e}"

#eval show TermElabM Unit from do
  -- the read values of all blocks against the raw terms on random states
  let bases := DeriveReaderCode.fns.map fun fn => (fn, ((labelAddr DeriveReaderCode.code fn).getD 0))
  let ws ← walkAll ``DeriveReaderCode.L1.step `DeriveReaderCode.m1 (specsOf DeriveReaderCode.code bases)
  let (blocks, nitems, compared, skipped, bad) ← meaning bases ws 300
  logInfo m!"reader rules: {blocks} blocks, {nitems} items, {compared} values compared, not compiled {skipped}, {bad.length} different {bad.take 3}"
  -- `d2push` entry is not compiled (`compileRaw` gives none: a raw term has a free variable that is not the start or a load
  -- value); `d2load` checks the rule D2
  check (blocks + 1 == ws.length && blocks ≥ 7 && skipped == ["d2push entry"])
    s!"reader rules: {blocks} of {ws.length} blocks read and compiled, not compiled {skipped}"
  check bad.isEmpty s!"reader rules: the raw terms and the read values differ: {bad.take 3}"
  -- and on the edge pairs of `rax`, `rbx`
  let (compared, bad) ← blockEdges (ws.filter fun (s, _) => name s != "d2push entry") bases 300
  check (compared > 0 && bad.isEmpty) s!"reader rules: the raw terms and the read values differ at the edges: {bad.take 3}"

/-! ## Small terms: the read condition against the raw proposition, and the refused forms -/

#eval show TermElabM Unit from do
  let rc (stx : TermElabM Syntax) := do readBody readCond (← elabE stx)
  -- D1
  check (isCond (← rc `(fun d : MachineData => d.regs.rax = 0 ∧ d.regs.rbx = 0)) (.eq (.or (r .rax) (r .rbx)) (n 0)))
    "a = 0 ∧ b = 0 is a ||| b = 0"
  check (isCond (← rc `(fun d : MachineData => d.regs.rax = 0 → ¬ d.regs.rbx = 0))
    (.not (.eq (.or (r .rax) (r .rbx)) (n 0)))) "a = 0 → ¬ b = 0 is ¬ (a ||| b = 0)"
  for (what, stx) in [("a = 0 ∧ b = 0", `(fun d : MachineData => d.regs.rax = 0 ∧ d.regs.rbx = 0)),
      ("a = 0 → ¬ b = 0", `(fun d : MachineData => d.regs.rax = 0 → ¬ d.regs.rbx = 0))] do
    let (k, first) ← condDiffs stx
    check (k == 0) s!"{what} differs from the raw term on {k} states, first {first}"
  -- D1, refused: a test that is not a zero test, an implication whose conclusion is not a negated zero test, a dependent `∀`
  check (isErr (← rc `(fun d : MachineData => d.regs.rax = 0 ∧ d.regs.rbx = 1)) (· == .unsupported ``And))
    "a = 0 ∧ b = 1 is refused"
  check (isErr (← rc `(fun d : MachineData => d.regs.rax = 0 → d.regs.rbx = 0)) (· == .unsupported `other))
    "a = 0 → b = 0 is refused"
  check (isErr (← rc `(fun d : MachineData => d.regs.rax ≤ d.regs.rbx → ¬ d.regs.rcx = 0)) (· == .unsupported `other))
    "a ≤ b → ¬ c = 0 is refused"
  check (isErr (← rc `(fun d : MachineData => ∀ x : UInt64, x = d.regs.rax)) (· == .unsupported `other))
    "a dependent ∀ is refused"

#eval show TermElabM Unit from do
  let rc (stx : TermElabM Syntax) := do readBody readCond (← elabE stx)
  -- D2
  let zf := `(fun d : MachineData =>
    (StatusFlags.from_result (d.regs.rax.toBitVec - d.regs.rbx.toBitVec) ⟨false, false, false⟩).zf = true)
  check (isCond (← rc zf) (.eq (r .rax) (r .rbx))) "the zf of from_result (a - b) is a = b"
  let (k, first) ← condDiffs zf
  check (k == 0) s!"the zf of from_result differs from the raw term on {k} states, first {first}"
  -- D2, refused: the sign flag of a from_result
  check (isErr (← rc `(fun d : MachineData =>
      (StatusFlags.from_result d.regs.rax.toBitVec ⟨false, false, false⟩).sf = true)) (· == .unsupported ``StatusFlags.sf))
    "the sf of from_result is refused"

#eval show TermElabM Unit from do
  let rc (stx : TermElabM Syntax) := do readBody readCond (← elabE stx)
  -- D3: the narrow literal borrow of a 32-bit sum
  let lea := `(fun d : MachineData =>
    ((2 : Int) + ((d.regs.rax.toNat : Int) + 18446744073709551615) % 4294967296 % 18446744073709551616) % 256 =
      ((d.regs.rax.toNat : Int) + 18446744073709551615) % 256 - 254)
  check (isCond (← rc lea) (.ule (n 254) (.zext .b8 (.add (r .rax) (n 18446744073709551615)))))
    "the borrow of cmpb $-2 of a lea"
  let (k, first) ← condDiffs lea
  check (k == 0) s!"the narrow borrow of a sum differs from the raw term on {k} states, first {first}"
  -- D3: the 64-bit borrow of a sum
  let add := `(fun d : MachineData =>
    (((18446744073709551616 - d.regs.rax.toNat : Nat) : Int) + ((d.regs.rbx.toNat : Int) + (d.regs.rcx.toNat : Int))) %
        18446744073709551616 =
      ((d.regs.rbx.toNat : Int) + (d.regs.rcx.toNat : Int)) % 18446744073709551616 - (d.regs.rax.toNat : Int))
  check (isCond (← rc add) (.ule (r .rax) (.add (r .rbx) (r .rcx)))) "the borrow of a sum"
  let (k, first) ← condDiffs add
  check (k == 0) s!"the borrow of a sum differs from the raw term on {k} states, first {first}"
  -- D3, refused: the two sums differ; the right side has no `% 2^64` (the sum can pass 2^64); a literal subtracted
  check (isErr (← rc `(fun d : MachineData =>
      ((2 : Int) + ((d.regs.rax.toNat : Int) + 18446744073709551615) % 4294967296 % 18446744073709551616) % 256 =
        ((d.regs.rbx.toNat : Int) + 18446744073709551615) % 256 - 254)) (· == .unsupported ``Int))
    "a narrow borrow of two different sums is refused"
  check (isErr (← rc `(fun d : MachineData =>
      (((18446744073709551616 - d.regs.rax.toNat : Nat) : Int) + ((d.regs.rbx.toNat : Int) + (d.regs.rcx.toNat : Int))) %
          18446744073709551616 =
        ((d.regs.rbx.toNat : Int) + (d.regs.rcx.toNat : Int)) - (d.regs.rax.toNat : Int))) (· == .unsupported ``Int))
    "a 64-bit borrow of a sum with no modulus on the right is refused"
  -- D3: the borrow of a `Nat` mask
  let mask := `(fun d : MachineData =>
    ((18446744073709551615 : Int) + ((280375465082880 &&& d.regs.rax.toNat : Nat) : Int)) % 18446744073709551616 =
      ((280375465082880 &&& d.regs.rax.toNat : Nat) : Int) - 1)
  check (isCond (← rc mask) (.ule (n 1) (.and (n 280375465082880) (r .rax)))) "the borrow of a mask"
  let (k, first) ← condDiffs mask
  check (k == 0) s!"the borrow of a mask differs from the raw term on {k} states, first {first}"
  -- D3, refused: a `Nat` sum in the cast; a literal of 2^64 in the mask
  check (isErr (← rc `(fun d : MachineData =>
      ((18446744073709551615 : Int) + ((d.regs.rbx.toNat + d.regs.rax.toNat : Nat) : Int)) % 18446744073709551616 =
        ((d.regs.rbx.toNat + d.regs.rax.toNat : Nat) : Int) - 1)) (· == .unsupported ``Int))
    "the borrow of a Nat sum is refused"
  check (isErr (← rc `(fun d : MachineData =>
      ((18446744073709551615 : Int) + ((18446744073709551616 &&& d.regs.rax.toNat : Nat) : Int)) % 18446744073709551616 =
        ((18446744073709551616 &&& d.regs.rax.toNat : Nat) : Int) - 1)) (· == .unsupported ``Int))
    "a mask literal of 2^64 is refused"
  check (isErr (← rc `(fun d : MachineData =>
      ((2 : Int) + ((d.regs.rax.toNat : Int) - 1) % 4294967296 % 18446744073709551616) % 256 =
        ((d.regs.rax.toNat : Int) - 1) % 256 - 254)) (· == .unsupported ``Int))
    "a narrow borrow of a difference of Int is refused"
