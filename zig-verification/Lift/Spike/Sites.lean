module

public import Lift.Sem.Model
public import Lift.Sem.SysV
public import Lift.P2.Total.Primitive

@[expose] public section

/-! Helpers for the proof of one instruction step with `Handled`, shared by the toys. -/

namespace Lift.Spike.Sites

open Lift.P2.Total Lift.Sem

/-- One step to a known state: if each result of the step is `.next t`, go on from `t`. -/
theorem Reaches.of_next {step : MachineState → Effects} {policy : CpuPolicy}
    {Q : MachineState → Prop} {s : MachineState} (t : MachineState)
    (h : ∀ r, Handled policy id s.data.dmem (step s) r ↔ r = .next t)
    (k : Reaches step policy Q t) : Reaches step policy Q s :=
  .of_step fun r hr => ⟨t, (h r).mp hr, k⟩

/-- The execute check of an instruction `p` in the code range. -/
theorem exec_iff {M : Type} {policy : CpuPolicy} {lo hi : Int64} (h : SysV.ExecRange policy lo hi)
    (visible : DataMem → M) (prior : DataMem) (p : Std.Rco Int64) (k : Unit → Effects)
    (result : StepResult M) (hp : lo ≤ p.lower ∧ p.lower < p.upper ∧ p.upper ≤ hi) :
    Handled policy visible prior (.require_exec_access p k) result ↔
      Handled policy visible prior (k ()) result :=
  Handled.exec_iff _ _ _ _ _ _ (h _ _ hp.1 hp.2.1 hp.2.2)

/-- A load that `readRam` permits and that reads `v`. -/
theorem load_iff {M : Type} {policy : CpuPolicy} (visible : DataMem → M) (d : MachineData)
    (a : BitVec 64) (w : Width) (k : w.type → MachineData → Effects) (result : StepResult M)
    {v : w.type} (hread : readRam policy d.dmem a w = .ok v) :
    Handled policy visible d.dmem (d.load a w k) result ↔
      Handled policy visible d.dmem (k v d) result := by
  rw [readRam_correct, hread]

/-- The effect of `retq` after its execute check. -/
def retq (d : MachineData) : Effects :=
  d.load d.regs.rsp.toBitVec .W64 fun ra s =>
    .done ⟨{ s with regs := { s.regs with rsp := d.regs.rsp + 8 } }, Int64.ofBitVec ra⟩

/-- `retq` with a readable return word `ra`. -/
theorem retq_iff {policy : CpuPolicy} (d : MachineData) (ra : Int64)
    (hread : readRam policy d.dmem d.regs.rsp.toBitVec .W64 = .ok ra.toBitVec)
    (result : StepResult DataMem) :
    Handled policy id d.dmem (retq d) result ↔
      result = .next ⟨{ d with regs := { d.regs with rsp := d.regs.rsp + 8 } }, ra⟩ := by
  rw [retq, load_iff _ _ _ _ _ _ hread, Handled.done_iff, Int64.ofBitVec_toBitVec]

/-- At the entry, the return word is readable and is the return address. -/
theorem readRet {policy : CpuPolicy} {lo hi entry ra : Int64} {s : MachineState}
    (h : SysV.Entry policy lo hi entry s) (hra : SysV.retAddr s = some ra) :
    readRam policy s.data.dmem s.data.regs.rsp.toBitVec .W64 = .ok ra.toBitVec := by
  unfold SysV.retAddr at hra
  cases hl : Mem.loadInt s.data.dmem s.data.regs.rsp.toBitVec 8 with
  | none => simp [hl] at hra
  | some v =>
    simp only [hl, Option.map_some, Option.some.injEq] at hra
    subst hra
    simp [readRam, h.retRead, Width.bytes, hl]

/-! ## Helpers for the block lemmas of `Lift/Spike/Sites/` -/

/-- One step to a state that a choice `a` gives (an `undefined` value of the step): go on from
each `t a`. -/
theorem Reaches.of_choice {step : MachineState → Effects} {policy : CpuPolicy}
    {Q : MachineState → Prop} {s : MachineState} {A : Type} (t : A → MachineState)
    (h : ∀ r, Handled policy id s.data.dmem (step s) r ↔ ∃ a, r = .next (t a))
    (k : ∀ a, Reaches step policy Q (t a)) : Reaches step policy Q s :=
  .of_step fun r hr => by
    obtain ⟨a, e⟩ := (h r).mp hr
    exact ⟨t a, e, k a⟩

/-- Chain block lemmas: a block lemma with `Reaches … Q` as its postcondition. -/
theorem Reaches.join {step : MachineState → Effects} {policy : CpuPolicy}
    {Q : MachineState → Prop} {s : MachineState}
    (h : Reaches step policy (Reaches step policy Q) s) : Reaches step policy Q s :=
  h.seq fun _ k => k

/-- Backward use: `Reaches` at `s`, where `Q` is false, gives `Reaches` at each next state. -/
theorem Reaches.next_of {step : MachineState → Effects} {policy : CpuPolicy}
    {Q : MachineState → Prop} {s : MachineState} (hr : Reaches step policy Q s) (hq : ¬ Q s)
    (t : MachineState) (ht : Handled policy id s.data.dmem (step s) (.next t)) :
    Reaches step policy Q t := by
  cases hr with
  | done h => exact absurd h hq
  | step _ next => exact next t ht

/-- A step of `s` that can fail, where `Q` is false: no `Reaches` from `s`. -/
theorem Reaches.not_of_failure {step : MachineState → Effects} {policy : CpuPolicy}
    {Q : MachineState → Prop} {s : MachineState} (hq : ¬ Q s) (reason : Failure) (m : DataMem)
    (hf : Handled policy id s.data.dmem (step s) (.failure reason m)) :
    ¬ Reaches step policy Q s := by
  intro hr
  cases hr with
  | done h => exact hq h
  | step fails _ =>
    obtain ⟨_, e⟩ := fails _ hf
    cases e

/-- A store that `writeRam` permits and that gives the memory `m`. -/
theorem store_iff {M : Type} {policy : CpuPolicy} (visible : DataMem → M) (d : MachineData)
    (a : BitVec 64) (w : Width) (v : w.type) (k : MachineData → Effects) (result : StepResult M)
    {m : DataMem} (hwrite : writeRam policy d.dmem a w v = .ok m) :
    Handled policy visible d.dmem (d.store a v k) result ↔
      Handled policy visible d.dmem (k { d with dmem := m }) result := by
  rw [writeRam_correct, hwrite]

/-- A read that a disjoint store does not change. -/
theorem readRam_of_writeRam {policy : CpuPolicy} {m m' : DataMem} {a b : BitVec 64} {w w' : Width}
    {v : w.type} {u : w'.type} (hwrite : writeRam policy m a w v = .ok m')
    (hsep : ByteDisjoint a w.bytes b w'.bytes) (hread : readRam policy m b w' = .ok u) :
    readRam policy m' b w' = .ok u := by
  unfold readRam at hread ⊢
  rw [writeRam_preserves_load policy m m' a b w w'.bytes v hsep hwrite]
  cases hp : policy.permits (.read b w') <;> simp only [hp] at hread ⊢
  · cases hread
  · cases hl : Mem.loadInt m b w'.bytes <;> simp only [hl] at hread ⊢
    · cases hread
    · exact hread

/-- The flags of `shrq $1` on `x`, with `af` undefined. -/
def shrFlags (x : UInt64) (af : Bool) : StatusFlags :=
  StatusFlags.from_result (x.toBitVec >>> 1) { cf := x.toBitVec.getLsbD 0, af := af, of := x.toBitVec.msb }

/-- The flags of `xorl %r, %r` (the result `0`), with `af` undefined. -/
def zeroFlags (af : Bool) : StatusFlags :=
  StatusFlags.from_result 0#32 { cf := false, af := af, of := false }

/-- The flags of `cmpq %y, %x` and of `subq %y, %x` (the result `x - y`). -/
def subFlags (x y : UInt64) : StatusFlags :=
  StatusFlags.from_result (x.toBitVec - y.toBitVec)
    { cf := (x.toBitVec - y.toBitVec).unsigned != x.toBitVec.unsigned - y.toBitVec.unsigned,
      af := ((x.toBitVec - y.toBitVec).take 4).unsigned !=
        (x.toBitVec.take 4).unsigned - (y.toBitVec.take 4).unsigned,
      of := (x.toBitVec - y.toBitVec).signed != x.toBitVec.signed - y.toBitVec.signed }

/-- The flags of `addq` (the result `x + y`). -/
def addFlags (x y : UInt64) : StatusFlags :=
  StatusFlags.from_result (x.toBitVec + y.toBitVec)
    { cf := (x.toBitVec + y.toBitVec).unsigned != x.toBitVec.unsigned + y.toBitVec.unsigned,
      af := ((x.toBitVec + y.toBitVec).take 4).unsigned !=
        (x.toBitVec.take 4).unsigned + (y.toBitVec.take 4).unsigned,
      of := (x.toBitVec + y.toBitVec).signed != x.toBitVec.signed + y.toBitVec.signed }

/-- The flags of `incq` on `x`; `cf` does not change. -/
def incFlags (x : UInt64) (cf : Bool) : StatusFlags :=
  StatusFlags.from_result (x.toBitVec + 1#64)
    { cf := cf,
      af := ((x.toBitVec + 1#64).take 4).unsigned != (x.toBitVec.take 4).unsigned + 1,
      of := (x.toBitVec + 1#64).signed != x.toBitVec.signed + 1 }

/-- `je` after `cmpq %y, %x` jumps if and only if `x = y`. -/
theorem subFlags_zf (x y : UInt64) : (subFlags x y).zf = decide (x = y) := by
  simp only [subFlags, StatusFlags.from_result, BitVec.zero]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, ← UInt64.toBitVec_inj]
  exact Lean.Grind.AddCommGroup.sub_eq_zero_iff

/-- After `cmpq %y, %x`, the condition `be` (`cf ∨ zf`) is the unsigned `x ≤ y`. -/
theorem subFlags_be (x y : UInt64) :
    ((subFlags x y).cf = true ∨ (subFlags x y).zf = true) ↔ x ≤ y := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  simp only [subFlags, StatusFlags.from_result, BitVec.unsigned, bne_iff_ne, ne_eq, beq_iff_eq,
    UInt64.le_iff_toNat_le, BitVec.toNat_sub, BitVec.zero, ← BitVec.toNat_inj,
    UInt64.toNat_toBitVec, BitVec.toNat_ofNatLT]
  omega

/-- `Decompiles` for a step function with `L1Spec` is `Decompiles` for the Kraken step. -/
theorem decompiles_l1Spec_iff {A R : Type} (asm : _root_.Executable) (step : MachineState → Effects)
    (spec : Lift.P1.L1Spec asm step) (M : Model A R) :
    Decompiles step M ↔ Decompiles (fun s => asm.step s .done) M := by
  rw [Lift.P1.L1Spec.step_eq asm step spec]

end Lift.Spike.Sites
