import Kraken.StateCfg
import Kraken.X64.Parser
import VerifiedNix.X64Specs
import VerifiedNix.Fuzz

/-! Tests of `#fuzz` (VerifiedNix/Fuzz.lean): each check finds the error it is made for, and a
correct invariant and spec give no failure. -/

open Kraken.X64.Parser

set_option linter.unusedVariables false

def sum8 : Program := parse("
sum8:
  xorq %rax, %rax
  testq %rsi, %rsi
  je .Lend
  xorq %rcx, %rcx
.Lnext:
  addq (%rdi,%rcx,8), %rax
  addq $1, %rcx
  cmpq %rcx, %rsi
  jne .Lnext
.Lend:
  ret
")

/-- The sum of the first `k` words at `a`. -/
def sumWords (m : Mem 64) (a : BitVec 64) : Nat → BitVec 64
  | 0 => 0
  | k + 1 => sumWords m a k + BitVec.ofInt 64 (m.loadInt (a + 8#64 * BitVec.ofNat 64 k) 8).get!

-- a correct invariant, variant and postcondition
/--
info: 200 samples (0 skipped by pre), 1278 label visits: no check failed.
-/
#guard_msgs in
#fuzz sum8 args (c : MachineData) (ra : Int64) (n : Nat) with
  (gen := do
    let n ← Fuzz.nat 10
    let c ← Fuzz.stack (← Fuzz.machine)
    let c ← Fuzz.buffer c .rdi (← Fuzz.bytes (8 * n))
    return (Fuzz.setReg c .rsi n, Fuzz.ret, n))
  (pre := c.regs.rsi.toNat = n ∧ Mem.Mapped [(c.regs.rdi.toBitVec, 8 * n)] c.dmem)
  (start := c.push64 ra)
  (invariant := fun {s₀} l s' => match l with
    | "sum8" => s' = s₀
    | ".Lnext" => s'.regs.rcx.toNat < n ∧ s'.regs.rsi = c.regs.rsi ∧ s'.regs.rdi = c.regs.rdi
        ∧ s'.regs.rsp = s₀.regs.rsp ∧ s'.regs.rax.toBitVec = sumWords c.dmem c.regs.rdi.toBitVec s'.regs.rcx.toNat
        ∧ Mem.WritesOnly [(c.regs.rsp.toBitVec - 8#64, 8)] c.dmem s'.dmem
    | ".Lend" => s'.regs.rax.toBitVec = sumWords c.dmem c.regs.rdi.toBitVec n
    | _ => False)
  (variant := fun l s' => match l with
    | "sum8" => n
    | ".Lnext" => n - s'.regs.rcx.toNat
    | _ => 0)
  (post := fun a t => a = ra ∧ t.regs.rsp = c.regs.rsp
    ∧ t.regs.rax.toBitVec = sumWords c.dmem c.regs.rdi.toBitVec n)

-- two wrong ones: a WritesOnly that leaves out the return slot, and a variant that the entry edge
-- does not respect
/--
info: 200 samples (0 skipped by pre), 1512 label visits: 2 failures
sample 1: invariant at .Lnext, conjunct 2, false at a visit: Mem.WritesOnly [] c.dmem s'.dmem
  state: rax=0 rbx=8334473010281426407 rcx=0 rdx=2195868541721285004 rsi=4 rdi=273678336 rsp=2147352568 r8=12617472984780539247 r9=2182016956446853147
sample 1: variant does not decrease from sum8 (0) to .Lnext (4)
-/
#guard_msgs in
#fuzz sum8 args (c : MachineData) (ra : Int64) (n : Nat) with
  (gen := do
    let n ← Fuzz.range 1 10
    let c ← Fuzz.stack (← Fuzz.machine)
    let c ← Fuzz.buffer c .rdi (← Fuzz.bytes (8 * n))
    return (Fuzz.setReg c .rsi n, Fuzz.ret, n))
  (start := c.push64 ra)
  (invariant := fun {s₀} l s' => match l with
    | "sum8" => s' = s₀
    | ".Lnext" => s'.regs.rcx.toNat < n ∧ Mem.WritesOnly [] c.dmem s'.dmem
    | ".Lend" => True
    | _ => False)
  (variant := fun _ s' => n - s'.regs.rcx.toNat)

def inc2 : Program := parse("
inc2:
  addq $2, %rax
  ret
")

-- a wrong postcondition
/--
info: 20 samples (0 skipped by pre), 20 label visits: 1 failures
sample 1: postcondition, conjunct 2, false at the exit to 795741901218840576: t.regs.rax = c.regs.rax + 1
  state: rax=18329534712202620151 rbx=3441359099766425339 rcx=12754697793273094231 rdx=8661515466582073216 rsi=16499090405550790134 rdi=197649356997426491 rsp=2147352576 r8=14288940661897737496 r9=3890071160368634674
-/
#guard_msgs in
#fuzz inc2 args (c : MachineData) (ra : Int64) with
  (gen := do return (← Fuzz.stack (← Fuzz.machine), Fuzz.ret))
  (start := c.push64 ra)
  (invariant := fun {s₀} l s' => match l with | "inc2" => s' = s₀ | _ => False)
  (variant := fun _ _ => 0)
  (post := fun a t => a = ra ∧ t.regs.rax = c.regs.rax + 1)
  (runs := 20)

def store : Program := parse("
store:
  movb %al, 3(%rdx)
  ret
")

-- the destination is not mapped: a fault
/--
info: 20 samples (0 skipped by pre), 20 label visits: 1 failures
sample 1: the run faults: store at the unmapped address 8661515466582073219
-/
#guard_msgs in
#fuzz store args (c : MachineData) (ra : Int64) with
  (gen := do return (← Fuzz.stack (← Fuzz.machine), Fuzz.ret))
  (start := c.push64 ra)
  (invariant := fun {s₀} l s' => match l with | "store" => s' = s₀ | _ => False)
  (variant := fun _ _ => 0)
  (runs := 20)

-- pre rejects half of the samples
/--
info: 20 samples (24 skipped by pre), 20 label visits: no check failed.
-/
#guard_msgs in
#fuzz inc2 args (c : MachineData) (ra : Int64) (n : Nat) with
  (gen := do return (← Fuzz.stack (← Fuzz.machine), Fuzz.ret, ← Fuzz.nat 2))
  (pre := n = 0)
  (start := c.push64 ra)
  (invariant := fun {s₀} l s' => match l with | "inc2" => s' = s₀ | _ => False)
  (variant := fun _ _ => 0)
  (runs := 20)

def spin : Program := parse("
spin:
  jmp spin
")

-- a loop without end
/--
info: 2 samples (0 skipped by pre), 2000 label visits: 2 failures
sample 1: variant does not decrease from spin (0) to spin (0)
sample 1: the run did not end within 1000 steps
-/
#guard_msgs in
#fuzz spin args (c : MachineData) (ra : Int64) with
  (gen := do return (← Fuzz.stack (← Fuzz.machine), Fuzz.ret))
  (start := c.push64 ra)
  (invariant := fun {s₀} l s' => True)
  (variant := fun _ _ => 0)
  (runs := 2) (fuel := 1000)

def dbl : Program := parse("
dbl:
  add %rdi, %rdi
  mov %rdi, %rax
  ret
")

def quad : Program := parse("
quad:
  call dbl
  mov %rax, %rdi
  call dbl
  ret
") ++ dbl

-- a callee inside the program: its label is not a visit of the caller's fragment
/--
info: 20 samples (0 skipped by pre), 20 label visits: no check failed.
-/
#guard_msgs in
#fuzz quad args (c : MachineData) (ra : Int64) with
  (gen := do return (← Fuzz.stack (← Fuzz.machine), Fuzz.ret))
  (start := c.push64 ra)
  (invariant := fun {s₀} l s' => match l with | "quad" => s' = s₀ | _ => False)
  (variant := fun _ _ => 0)
  (post := fun a t => a = ra ∧ t.regs.rax = c.regs.rdi + c.regs.rdi + (c.regs.rdi + c.regs.rdi))
  (runs := 20)

/-! ## `gen` and `pre` from the binders

Without `gen`, `#fuzz` makes the samples from the types of the binders and from the hypothesis
binders; `pre` is the conjunction of the hypotheses. -/

-- the generator of the machine: a buffer for each register with a block, the bytes of each
-- `Contains` written into it, and the registers of the equations set
#guard
  let c := (Fuzz.state [(.rdi, 0, 16), (.rdi, 8, 16)] [(.rdi, 4, [1, 2, 3]), (.rbx, 0, [9])] [(.rsi, 7)]).run' (mkStdGen 0)
  decide (Mem.Mapped [(c.regs.rdi.toBitVec, 24), (c.regs.rbx.toBitVec, 1), (c.regs.rsp.toBitVec - 512#64, 576)] c.dmem)
    && decide (Mem.Contains c.dmem (c.regs.rdi.toBitVec + 4#64) [1, 2, 3])
    && decide (Mem.Contains c.dmem c.regs.rbx.toBitVec [9])
    && c.regs.rsi.toNat == 7
    && decide (Mem.Blocks.Disjoint [(c.regs.rdi.toBitVec, 24)] [(c.regs.rbx.toBitVec, 1), (c.regs.rsp.toBitVec - 512#64, 576)])
-- the buffer is no longer than its blocks and bytes
#guard
  let c := (Fuzz.state [(.rdi, 0, 16)] [] []).run' (mkStdGen 0)
  !decide (Mem.Mapped [(c.regs.rdi.toBitVec, 17)] c.dmem)
-- without blocks, the registers keep their random values and no buffer is mapped
#guard
  let c := (Fuzz.state [] [] [(.rax, 3)]).run' (mkStdGen 0)
  c.regs.rax.toNat == 3 && c.dmem.size == 576

-- a correct invariant, variant and postcondition
/--
info: 200 samples (0 skipped by pre), 1278 label visits: no check failed.
-/
#guard_msgs in
#fuzz sum8 args (c : MachineData) (ra : Int64) (n : Nat) (hn : c.regs.rsi.toNat = n)
    (hm : Mem.Mapped [(c.regs.rdi.toBitVec, 8 * n)] c.dmem) with
  (start := c.push64 ra)
  (invariant := fun {s₀} l s' => match l with
    | "sum8" => s' = s₀
    | ".Lnext" => s'.regs.rcx.toNat < n ∧ s'.regs.rsi = c.regs.rsi ∧ s'.regs.rdi = c.regs.rdi
        ∧ s'.regs.rsp = s₀.regs.rsp ∧ s'.regs.rax.toBitVec = sumWords c.dmem c.regs.rdi.toBitVec s'.regs.rcx.toNat
        ∧ Mem.WritesOnly [(c.regs.rsp.toBitVec - 8#64, 8)] c.dmem s'.dmem
    | ".Lend" => s'.regs.rax.toBitVec = sumWords c.dmem c.regs.rdi.toBitVec n
    | _ => False)
  (variant := fun l s' => match l with
    | "sum8" => n
    | ".Lnext" => n - s'.regs.rcx.toNat
    | _ => 0)
  (post := fun a t => a = ra ∧ t.regs.rsp = c.regs.rsp
    ∧ t.regs.rax.toBitVec = sumWords c.dmem c.regs.rdi.toBitVec n)

-- a wrong invariant (the return slot is left out of WritesOnly) and a variant that grows on the
-- edge from the entry into the loop
/--
info: 200 samples (0 skipped by pre), 1278 label visits: 2 failures
sample 1: invariant at .Lnext, conjunct 2, false at a visit: Mem.WritesOnly [] c.dmem s'.dmem
  state: rax=0 rbx=8334473010281426407 rcx=0 rdx=2195868541721285004 rsi=3 rdi=273678336 rsp=2147352568 r8=12617472984780539247 r9=2182016956446853147
sample 1: variant does not decrease from sum8 (0) to .Lnext (3)
-/
#guard_msgs in
#fuzz sum8 args (c : MachineData) (ra : Int64) (n : Nat) (hn : c.regs.rsi.toNat = n)
    (hm : Mem.Mapped [(c.regs.rdi.toBitVec, 8 * n)] c.dmem) with
  (start := c.push64 ra)
  (invariant := fun {s₀} l s' => match l with
    | "sum8" => s' = s₀
    | ".Lnext" => s'.regs.rcx.toNat < n ∧ Mem.WritesOnly [] c.dmem s'.dmem
    | ".Lend" => True
    | _ => False)
  (variant := fun _ s' => n - s'.regs.rcx.toNat)

-- a wrong postcondition
/--
info: 200 samples (0 skipped by pre), 200 label visits: 1 failures
sample 1: postcondition, conjunct 2, false at the exit to 795741901218840576: t.regs.rax = c.regs.rax + 1
  state: rax=18329534712202620151 rbx=3441359099766425339 rcx=12754697793273094231 rdx=8661515466582073216 rsi=16499090405550790134 rdi=197649356997426491 rsp=2147352576 r8=14288940661897737496 r9=3890071160368634674
-/
#guard_msgs in
#fuzz inc2 args (c : MachineData) (ra : Int64) with
  (start := c.push64 ra)
  (invariant := fun {s₀} l s' => match l with | "inc2" => s' = s₀ | _ => False)
  (variant := fun _ _ => 0)
  (post := fun a t => a = ra ∧ t.regs.rax = c.regs.rax + 1)

def bsum : Program := parse("
bsum:
  xorq %rax, %rax
  xorq %rcx, %rcx
  testq %rdx, %rdx
  je .Ldone
.Lloop:
  movzbl (%rsi,%rcx), %r8d
  addq %r8, %rax
  addq $1, %rcx
  cmpq %rcx, %rdx
  jne .Lloop
.Ldone:
  ret
")

/-- The sum of the first `k` bytes. -/
def byteSum (bs : List UInt8) (k : Nat) : Nat := ((bs.take k).map (·.toNat)).sum

-- bytes at a register and their length in another: `Contains` and an equation of the length
/--
info: 200 samples (0 skipped by pre), 1628 label visits: no check failed.
-/
#guard_msgs in
#fuzz bsum args (c : MachineData) (ra : Int64) (bs : List UInt8) (hl : bs.length = c.regs.rdx.toNat)
    (hc : Mem.Contains c.dmem c.regs.rsi.toBitVec bs) with
  (start := c.push64 ra)
  (invariant := fun {s₀} l s' => match l with
    | "bsum" => s' = s₀
    | ".Lloop" => s'.regs.rcx.toNat < bs.length ∧ s'.regs.rax.toNat = byteSum bs s'.regs.rcx.toNat
    | ".Ldone" => s'.regs.rax.toNat = byteSum bs bs.length
    | _ => False)
  (variant := fun l s' => match l with
    | "bsum" => bs.length + 1
    | ".Lloop" => bs.length - s'.regs.rcx.toNat
    | _ => 0)
  (post := fun a t => a = ra ∧ t.regs.rax.toNat = byteSum bs bs.length)

-- the same with a wrong invariant: the sum includes the byte at `rcx`
/--
info: 200 samples (0 skipped by pre), 1628 label visits: 1 failures
sample 3: invariant at .Lloop, conjunct 2, false at a visit: s'.regs.rax.toNat = byteSum bs (s'.regs.rcx.toNat + 1)
  state: rax=0 rbx=17649662430383804098 rcx=0 rdx=8 rsi=272629760 rdi=11819994351422223841 rsp=2147352568 r8=17606155342222300928 r9=4763097786025821624
-/
#guard_msgs in
#fuzz bsum args (c : MachineData) (ra : Int64) (bs : List UInt8) (hl : bs.length = c.regs.rdx.toNat)
    (hc : Mem.Contains c.dmem c.regs.rsi.toBitVec bs) with
  (start := c.push64 ra)
  (invariant := fun {s₀} l s' => match l with
    | "bsum" => s' = s₀
    | ".Lloop" => s'.regs.rcx.toNat < bs.length ∧ s'.regs.rax.toNat = byteSum bs (s'.regs.rcx.toNat + 1)
    | ".Ldone" => True
    | _ => False)
  (variant := fun l s' => match l with
    | "bsum" => bs.length + 1
    | ".Lloop" => bs.length - s'.regs.rcx.toNat
    | _ => 0)

-- a hypothesis that is not decidable: no test
/--
info: not run: the hypothesis h is not decidable: ∀ (x : Nat), x + 1 ≠ 0
-/
#guard_msgs in
#fuzz inc2 args (c : MachineData) (ra : Int64) (h : ∀ x : Nat, x + 1 ≠ 0) with
  (start := c.push64 ra)
  (invariant := fun {s₀} l s' => match l with | "inc2" => s' = s₀ | _ => False)
  (variant := fun _ _ => 0)

-- a binder without a generator: no test
/--
info: not run: no generator for s : String
-/
#guard_msgs in
#fuzz inc2 args (c : MachineData) (ra : Int64) (s : String) with
  (start := c.push64 ra)
  (invariant := fun {s₀} l s' => match l with | "inc2" => s' = s₀ | _ => False)
  (variant := fun _ _ => 0)

-- hypotheses that no sample satisfies
/--
info: 0 samples (4000 skipped by pre), 0 label visits: no sample satisfied pre.
-/
#guard_msgs in
#fuzz inc2 args (c : MachineData) (ra : Int64) (h₁ : c.regs.rax.toNat = 5) (h₂ : c.regs.rax.toNat = 6) with
  (start := c.push64 ra)
  (invariant := fun {s₀} l s' => match l with | "inc2" => s' = s₀ | _ => False)
  (variant := fun _ _ => 0)

-- `pre` without `gen`: the hypotheses and `pre`
/--
info: 20 samples (65 skipped by pre), 20 label visits: no check failed.
-/
#guard_msgs in
#fuzz inc2 args (c : MachineData) (ra : Int64) (n : Nat) (h : n < 5) with
  (pre := n % 2 = 0)
  (start := c.push64 ra)
  (invariant := fun {s₀} l s' => match l with | "inc2" => s' = s₀ ∧ n < 5 ∧ n % 2 = 0 | _ => False)
  (variant := fun _ _ => 0)
  (runs := 20)

def ld8 : Program := parse("
ld8:
  movq 8(%rdi), %rax
  addq %rsi, %rax
  addq %rdx, %rax
  ret
")

-- the other spellings: `get64` and an offset in a block, equations of a `UInt64` and of a
-- `BitVec 64`, and a block of the stack (mapped by `Fuzz.stack`): no sample is skipped
/--
info: 200 samples (0 skipped by pre), 200 label visits: no check failed.
-/
#guard_msgs in
#fuzz ld8 args (c : MachineData) (ra : Int64) (hm : Mem.Mapped [(c.regs.get64 .rdi + 8#64, 8)] c.dmem)
    (hs : c.regs.rsi = 5) (hd : c.regs.rdx.toBitVec = 3#64)
    (hr : Mem.Mapped [(c.regs.rsp.toBitVec - 8#64, 8)] c.dmem) with
  (start := c.push64 ra)
  (invariant := fun {s₀} l s' => match l with | "ld8" => s' = s₀ | _ => False)
  (variant := fun _ _ => 0)
  (post := fun a t => a = ra
    ∧ t.regs.rax.toBitVec = BitVec.ofInt 64 (c.dmem.loadInt (c.regs.rdi.toBitVec + 8#64) 8).get! + 5#64 + 3#64)

-- a block below its register is not in the vocabulary: no buffer, and `pre` skips each sample
/--
info: 0 samples (4000 skipped by pre), 0 label visits: no sample satisfied pre.
-/
#guard_msgs in
#fuzz ld8 args (c : MachineData) (ra : Int64) (hm : Mem.Mapped [(c.regs.rdi.toBitVec - 8#64, 16)] c.dmem) with
  (start := c.push64 ra)
  (invariant := fun {s₀} l s' => match l with | "ld8" => s' = s₀ | _ => False)
  (variant := fun _ _ => 0)

/-! ## Inside `vcgen`

When `vcgen … invariants · I · V` leaves VCs open on a program with a back edge, a fuzz test of
`I` and `V` runs from the goal and the hypotheses, and its result is one message at `vcgen`. The
VCs and errors are those of `vcgen` alone (`set_option fuzz.vcgen false`). -/

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

-- a back edge: a jump to a label at or before the jump
#guard Fuzz.hasBackEdge sum8 && Fuzz.hasBackEdge spin && Fuzz.hasBackEdge cnt
#guard !Fuzz.hasBackEdge inc2 && !Fuzz.hasBackEdge quad && !Fuzz.hasBackEdge store

def fwd : Program := parse("
fwd:
  testq %rax, %rax
  je .Lout
  addq $1, %rax
.Lout:
  ret
")

#guard !Fuzz.hasBackEdge fwd

def callg : Program := parse("
callg:
  call g
  ret
")

-- a call of a label that is not in the program
#guard Fuzz.callsOutside callg && !Fuzz.callsOutside quad && !Fuzz.callsOutside sum8

-- a correct invariant: all VCs closed, no test
#guard_msgs in
theorem cnt_ok [Host] [FunDecls] (c : MachineData) (ra : Int64) (n : Nat) (hn : c.regs.rdi.toNat = n) :
    ⦃ fun s₀ => s₀ = c.push64 ra ⦄ cnt
    ⦃ fun _ _ => False; fun a t => a = ra ∧ t.regs.rax = c.regs.rdi ∧ t.regs.rsp = c.regs.rsp ⦄ := by
  vcgen [cnt]
    invariants
    · fun {s₀} l s' => match l with
      | "cnt" => s' = s₀
      | ".Lnext" => s'.regs.rax.toNat < n ∧ s'.regs.rdi = c.regs.rdi ∧ s'.regs.rsp = s₀.regs.rsp ∧ s'.dmem = s₀.dmem
      | ".Ldone" => s'.regs.rax = c.regs.rdi ∧ s'.regs.rsp = s₀.regs.rsp ∧ s'.dmem = s₀.dmem
      | _ => False
    · fun l s' => match l with
      | "cnt" => n
      | ".Lnext" => n - s'.regs.rax.toNat
      | _ => 0
    with kfinish

-- a wrong invariant (`rax + 1 < n` is false at the first visit for `n = 1`), without the test: the
-- errors of `vcgen`
/--
error: `finish` has failed, use `+verbose` to obtain diagnostic information
---
error: `finish` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
set_option fuzz.vcgen false in
theorem cnt_wrong_alone [Host] [FunDecls] (c : MachineData) (ra : Int64) (n : Nat) (hn : c.regs.rdi.toNat = n) :
    ⦃ fun s₀ => s₀ = c.push64 ra ⦄ cnt
    ⦃ fun _ _ => False; fun a t => a = ra ∧ t.regs.rax = c.regs.rdi ∧ t.regs.rsp = c.regs.rsp ⦄ := by
  vcgen [cnt]
    invariants
    · fun {s₀} l s' => match l with
      | "cnt" => s' = s₀
      | ".Lnext" => s'.regs.rax.toNat + 1 < n ∧ s'.regs.rdi = c.regs.rdi ∧ s'.regs.rsp = s₀.regs.rsp ∧ s'.dmem = s₀.dmem
      | ".Ldone" => s'.regs.rax = c.regs.rdi ∧ s'.regs.rsp = s₀.regs.rsp ∧ s'.dmem = s₀.dmem
      | _ => False
    · fun l s' => match l with
      | "cnt" => n
      | ".Lnext" => n - s'.regs.rax.toNat
      | _ => 0
    with kfinish

-- the same with the test: the same errors, and the failure (a new run: the trace says so)
/--
error: `finish` has failed, use `+verbose` to obtain diagnostic information
---
error: `finish` has failed, use `+verbose` to obtain diagnostic information
---
info: fuzz: 200 samples (0 skipped by pre), 1322 label visits: 1 failures
sample 1: invariant at .Lnext, conjunct 1, false at a visit: s'.regs.rax.toNat + 1 < n
  state: rax=2 rbx=8334473010281426407 rcx=12176710773263963476 rdx=2195868541721285004 rsi=4998282481800353753 rdi=3 rsp=2147352568 r8=12617472984780539247 r9=2182016956446853147
---
trace: [Fuzz] a new run
-/
#guard_msgs in
set_option trace.Fuzz true in
example [Host] [FunDecls] (c : MachineData) (ra : Int64) (n : Nat) (hn : c.regs.rdi.toNat = n) :
    ⦃ fun s₀ => s₀ = c.push64 ra ⦄ cnt
    ⦃ fun _ _ => False; fun a t => a = ra ∧ t.regs.rax = c.regs.rdi ∧ t.regs.rsp = c.regs.rsp ⦄ := by
  vcgen [cnt]
    invariants
    · fun {s₀} l s' => match l with
      | "cnt" => s' = s₀
      | ".Lnext" => s'.regs.rax.toNat + 1 < n ∧ s'.regs.rdi = c.regs.rdi ∧ s'.regs.rsp = s₀.regs.rsp ∧ s'.dmem = s₀.dmem
      | ".Ldone" => s'.regs.rax = c.regs.rdi ∧ s'.regs.rsp = s₀.regs.rsp ∧ s'.dmem = s₀.dmem
      | _ => False
    · fun l s' => match l with
      | "cnt" => n
      | ".Lnext" => n - s'.regs.rax.toNat
      | _ => 0
    with kfinish

-- the same declaration again (an `example` again, as a new elaboration of a proof): the result of
-- the cache, no new run. (The cache key is the term of the test, with the names of the `match`
-- functions of the invariants, which contain the name of the declaration.)
/--
error: `finish` has failed, use `+verbose` to obtain diagnostic information
---
error: `finish` has failed, use `+verbose` to obtain diagnostic information
---
info: fuzz: 200 samples (0 skipped by pre), 1322 label visits: 1 failures
sample 1: invariant at .Lnext, conjunct 1, false at a visit: s'.regs.rax.toNat + 1 < n
  state: rax=2 rbx=8334473010281426407 rcx=12176710773263963476 rdx=2195868541721285004 rsi=4998282481800353753 rdi=3 rsp=2147352568 r8=12617472984780539247 r9=2182016956446853147
-/
#guard_msgs in
set_option trace.Fuzz true in
example [Host] [FunDecls] (c : MachineData) (ra : Int64) (n : Nat) (hn : c.regs.rdi.toNat = n) :
    ⦃ fun s₀ => s₀ = c.push64 ra ⦄ cnt
    ⦃ fun _ _ => False; fun a t => a = ra ∧ t.regs.rax = c.regs.rdi ∧ t.regs.rsp = c.regs.rsp ⦄ := by
  vcgen [cnt]
    invariants
    · fun {s₀} l s' => match l with
      | "cnt" => s' = s₀
      | ".Lnext" => s'.regs.rax.toNat + 1 < n ∧ s'.regs.rdi = c.regs.rdi ∧ s'.regs.rsp = s₀.regs.rsp ∧ s'.dmem = s₀.dmem
      | ".Ldone" => s'.regs.rax = c.regs.rdi ∧ s'.regs.rsp = s₀.regs.rsp ∧ s'.dmem = s₀.dmem
      | _ => False
    · fun l s' => match l with
      | "cnt" => n
      | ".Lnext" => n - s'.regs.rax.toNat
      | _ => 0
    with kfinish

-- a wrong variant (it grows on the edge from the entry into the loop), with `try kfinish`: the
-- VCs are open goals, no error
/--
info: fuzz: 200 samples (0 skipped by pre), 1322 label visits: 1 failures
sample 1: variant does not decrease from cnt (0) to .Lnext (3)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
theorem cnt_var [Host] [FunDecls] (c : MachineData) (ra : Int64) (n : Nat) (hn : c.regs.rdi.toNat = n) :
    ⦃ fun s₀ => s₀ = c.push64 ra ⦄ cnt
    ⦃ fun _ _ => False; fun a t => a = ra ∧ t.regs.rax = c.regs.rdi ∧ t.regs.rsp = c.regs.rsp ⦄ := by
  vcgen [cnt]
    invariants
    · fun {s₀} l s' => match l with
      | "cnt" => s' = s₀
      | ".Lnext" => s'.regs.rax.toNat < n ∧ s'.regs.rdi = c.regs.rdi ∧ s'.regs.rsp = s₀.regs.rsp ∧ s'.dmem = s₀.dmem
      | ".Ldone" => s'.regs.rax = c.regs.rdi ∧ s'.regs.rsp = s₀.regs.rsp ∧ s'.dmem = s₀.dmem
      | _ => False
    · fun l s' => match l with
      | ".Lnext" => n - s'.regs.rax.toNat
      | _ => 0
    with try kfinish
  all_goals sorry

-- a hypothesis that is not decidable: not run
/--
error: `finish` has failed, use `+verbose` to obtain diagnostic information
---
error: `finish` has failed, use `+verbose` to obtain diagnostic information
---
info: fuzz: not run: the hypothesis hg is not decidable: ∀ (x : Nat), x + 1 ≠ 0
-/
#guard_msgs in
theorem cnt_undecidable [Host] [FunDecls] (c : MachineData) (ra : Int64) (n : Nat) (hn : c.regs.rdi.toNat = n)
    (hg : ∀ x : Nat, x + 1 ≠ 0) :
    ⦃ fun s₀ => s₀ = c.push64 ra ⦄ cnt
    ⦃ fun _ _ => False; fun a t => a = ra ∧ t.regs.rax = c.regs.rdi ∧ t.regs.rsp = c.regs.rsp ⦄ := by
  vcgen [cnt]
    invariants
    · fun {s₀} l s' => match l with
      | "cnt" => s' = s₀
      | ".Lnext" => s'.regs.rax.toNat + 1 < n ∧ s'.regs.rdi = c.regs.rdi ∧ s'.regs.rsp = s₀.regs.rsp ∧ s'.dmem = s₀.dmem
      | ".Ldone" => s'.regs.rax = c.regs.rdi ∧ s'.regs.rsp = s₀.regs.rsp ∧ s'.dmem = s₀.dmem
      | _ => False
    · fun l s' => match l with
      | "cnt" => n
      | ".Lnext" => n - s'.regs.rax.toNat
      | _ => 0
    with kfinish

-- no back edge: no test
/--
error: `finish` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
theorem inc2_wrong [Host] [FunDecls] (c : MachineData) (ra : Int64) :
    ⦃ fun s₀ => s₀ = c.push64 ra ⦄ inc2 ⦃ fun _ _ => False; fun a t => a = ra ∧ t.regs.rax = c.regs.rax + 1 ⦄ := by
  vcgen [inc2]
    invariants
    · fun {s₀} l s' => match l with | "inc2" => s' = s₀ | _ => False
    · fun _ _ => 0
    with kfinish

def cntf : Program := parse("
cntf:
  xorq %rax, %rax
.Lnext:
  addq $1, %rax
  cmpq %rax, %rdi
  jne .Lnext
")

-- `#fuzz` checks `post` at the exits only: these runs fall through the end of the program
/--
info: 200 samples (18 skipped by pre), 1213 label visits: no check failed.
-/
#guard_msgs in
#fuzz cntf args (s : MachineData) (n : Nat) (hn : s.regs.rdi.toNat = n) (h0 : 0 < n) with
  (start := s)
  (invariant := fun {s₀} l s' => match l with
    | "cntf" => s' = s₀
    | ".Lnext" => s'.regs.rax.toNat < n ∧ s'.regs.rdi = s.regs.rdi
    | _ => False)
  (variant := fun l s' => match l with
    | "cntf" => n
    | ".Lnext" => n - s'.regs.rax.toNat
    | _ => 0)
  (post := fun _ _ => False)

-- `WP.wp` with a run that falls through the end: an invariant that is true but too weak (no `rsp`
-- for the jump) leaves a VC; the test finds no failure, and checks the end against `Q`, not `E`
/--
error: `finish` has failed, use `+verbose` to obtain diagnostic information
---
info: fuzz: 200 samples (18 skipped by pre), 1213 label visits: no check failed.
-/
#guard_msgs in
theorem cntf_weak [Host] [FunDecls] (s : MachineData) (n : Nat) (hn : s.regs.rdi.toNat = n) (h0 : 0 < n) :
    WP.wp cntf (fun _ t => t.regs.rax = s.regs.rdi) (fun _ _ => False) s := by
  vcgen [cntf]
    invariants
    · fun {s₀} l s' => match l with
      | "cntf" => s' = s₀
      | ".Lnext" => s'.regs.rax.toNat < n ∧ s'.regs.rdi = s.regs.rdi
      | _ => False
    · fun l s' => match l with
      | "cntf" => n
      | ".Lnext" => n - s'.regs.rax.toNat
      | _ => 0
    with kfinish

-- a wrong fall-through condition `Q`
/--
error: `finish` has failed, use `+verbose` to obtain diagnostic information
---
info: fuzz: 200 samples (18 skipped by pre), 1213 label visits: 1 failures
sample 1: fall-through condition, conjunct 1, false at the end of the program: t.regs.rax = s.regs.rdi + 1
  state: rax=3 rbx=8334473010281426407 rcx=12176710773263963476 rdx=2195868541721285004 rsi=4998282481800353753 rdi=3 rsp=2147352576 r8=12617472984780539247 r9=2182016956446853147
-/
#guard_msgs in
theorem cntf_q [Host] [FunDecls] (s : MachineData) (n : Nat) (hn : s.regs.rdi.toNat = n) (h0 : 0 < n) :
    WP.wp cntf (fun _ t => t.regs.rax = s.regs.rdi + 1) (fun _ _ => False) s := by
  vcgen [cntf]
    invariants
    · fun {s₀} l s' => match l with
      | "cntf" => s' = s₀
      | ".Lnext" => s'.regs.rax.toNat < n ∧ s'.regs.rdi = s.regs.rdi ∧ s'.regs.rsp = s.regs.rsp
      | _ => False
    · fun l s' => match l with
      | "cntf" => n
      | ".Lnext" => n - s'.regs.rax.toNat
      | _ => 0
    with kfinish

-- a precondition without `s₀ = …`: not run
/--
error: `finish` has failed, use `+verbose` to obtain diagnostic information
---
error: `finish` has failed, use `+verbose` to obtain diagnostic information
---
error: `finish` has failed, use `+verbose` to obtain diagnostic information
---
error: `finish` has failed, use `+verbose` to obtain diagnostic information
---
error: `finish` has failed, use `+verbose` to obtain diagnostic information
---
info: fuzz: not run: the precondition does not fix the start state (no conjunct `s₀ = …`)
-/
#guard_msgs in
theorem cnt_nostart [Host] [FunDecls] (n : Nat) :
    ⦃ fun s₀ => s₀.regs.rdi.toNat = n ⦄ cnt ⦃ fun _ _ => False; fun _ t => t.regs.rax.toNat = n ⦄ := by
  vcgen [cnt]
    invariants
    · fun {s₀} l s' => match l with
      | "cnt" => s' = s₀
      | ".Lnext" => s'.regs.rax.toNat + 1 < n
      | ".Ldone" => s'.regs.rax.toNat = n
      | _ => False
    · fun l s' => match l with
      | "cnt" => n
      | ".Lnext" => n - s'.regs.rax.toNat
      | _ => 0
    with kfinish


-- Named predicates use their executable components, without a classical decision.
def FuzzSmall (n : Nat) : Prop := n < 4
def FuzzNested (n : Nat) : Prop := FuzzSmall n ∧ (FuzzSmall (n + 1) ∨ ¬ FuzzSmall n)
def FuzzEquivalent (n : Nat) : Prop := FuzzSmall n ↔ n < 4
def FuzzImplies (n : Nat) : Prop := FuzzSmall n → n < 5
def FuzzMemory (m : Mem 64) (a : BitVec 64) : Prop := Mem.Mapped [(a, 1)] m
opaque FuzzOpaque (n : Nat) : Prop := n < 4
def FuzzDeep (n : Nat) : Nat → Prop
  | 0 => FuzzSmall n
  | depth + 1 => FuzzDeep n depth

def FuzzRecursive : Nat → Prop
  | 0 => True
  | n + 1 => FuzzRecursive n

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  withLocalDeclD `n (mkConst ``Nat) fun n => do
    for pred in [``FuzzSmall, ``FuzzNested, ``FuzzEquivalent, ``FuzzImplies] do
      let .ok e ← (Fuzz.decideOr "predicate" (mkApp (mkConst pred) n)).run
        | throwError "no decision for {pred}"
      for i in [0:7] do
        let e ← mkLambdaFVars #[n] e
        let actual ← unsafe evalExpr Bool (mkConst ``Bool) (mkApp e (mkNatLit i))
        let expected := if pred == ``FuzzSmall then i < 4
          else if pred == ``FuzzNested then i < 4 && (i + 1 < 4 || !(i < 4)) else true
        unless actual == expected do throwError "wrong decision for {pred} at {i}"
    for pred in [``FuzzOpaque, ``FuzzRecursive] do
      let p := mkApp (mkConst pred) n
      let .error reason ← (Fuzz.decideOr "predicate" p).run
        | throwError "unexpected decision for {pred}"
      unless reason == s!"predicate is not decidable: {← ppExpr p}" do
        throwError "changed reason: {reason}"
    let deep := mkApp2 (mkConst ``FuzzDeep) n (mkNatLit 100)
    let .error reason ← (Fuzz.decideOr "predicate" deep).run
      | throwError "the unfolding limit was not applied"
    unless reason == s!"predicate is not decidable: {← ppExpr deep}" do
      throwError "changed bounded-search reason: {reason}"
    let predTy ← mkArrow (mkConst ``Nat) (mkSort 0)
    withLetDecl `LocalPred predTy (mkConst ``FuzzSmall) fun localPred => do
      let p := mkApp localPred n
      let .ok _ ← (Fuzz.closedOver "predicate" #[n] p).run
        | throwError "a local let is not closed"
      let .ok e ← (Fuzz.decideOr "predicate" p).run
        | throwError "no decision for a local let"
      unless !(← mkLambdaFVars #[n] e).hasFVar do
        throwError "a decision still contains a local let"
    withLocalDeclD `Helper predTy fun helper => do
      let .error reason ← (Fuzz.closedOver "predicate" #[n] (mkApp helper n)).run
        | throwError "a local constant passed the closure check"
      unless reason == "predicate depends on Helper : Nat → Prop" do
        throwError "changed dependency reason: {reason}"
    withLocalDeclD `m (mkApp (mkConst ``Mem) (mkNatLit 64)) fun m =>
      withLocalDeclD `a (mkApp (mkConst ``BitVec) (mkNatLit 64)) fun a => do
        let .ok _ ← (Fuzz.decideOr "memory predicate" (mkApp2 (mkConst ``FuzzMemory) m a)).run
          | throwError "no decision for memory predicate"

-- A let used by each executable component is expanded before the closure check.
/-- info: 10 samples (0 skipped by pre), 10 label visits: no check failed. -/
#guard_msgs in
#fuzz inc2 args (c : MachineData) (ra : Int64) with
  (gen := let g := Fuzz.stack; do return (← g (← Fuzz.machine), Fuzz.ret))
  (pre := let P := FuzzSmall; P 0)
  (start := let s := c.push64 ra; s)
  (invariant := let P := FuzzSmall; fun _ _ => P 0)
  (variant := let v := 0; fun _ _ => v)
  (post := let P := FuzzSmall; fun _ _ => P 0)
  (runs := 10)

-- Ordinary tactic syntax forwards the Kraken options and lemma parameters.
example : True := by kfinish
example (n : Nat) (h : n = 0) : n = 0 := by kfinish only
example : (1 : Nat) + 1 = 2 := by kfinish
example : True := by kfinish (clean := true)
example (n : Nat) (h : n = 0) : FuzzSmall n := by kfinish [FuzzSmall]
example (n : Nat) (h : n = 0) : FuzzSmall n := by kfinish (clean := true) only [FuzzSmall]
example : True := by
  fail_if_success (have : (0 : Nat) = 1 := by kfinish)
  trivial

-- Manual proof steps use names assigned by tactics.
example : ∀ n : Nat, n = n := by
  intro
  expose_names
  rfl
example : ∀ n : Nat, n = n := by
  intro
  rename_i n
  rfl

example (s t : MachineData) (h : t.regs.rsp = s.regs.rsp) : t.StackAtOrBelow s := by
  change ¬ s.regs.rsp.toBitVec.SerialLt t.regs.rsp.toBitVec
  rw [h]
  exact BitVec.not_serialLt_self _
example (s : MachineData) (ra : Int64) : (s.push64 ra).regs.rdi = s.regs.rdi := by
  simp [MachineData.regs_push64]
