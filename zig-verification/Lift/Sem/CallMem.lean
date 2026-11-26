module

public import Lift.Sem.Model
public import Lift.P2.Total.Memory

@[expose] public section

/-! A callee with memory in its result, at L2 (PIL-CALL).

The caller passes its memory to the callee (`Decompiles.call`: the callee `rep` has the machine
memory at the call) and goes on with the memory of the callee result. The caller's stack words
(its saved registers, its return word) are in that memory. The callee model says nothing of them,
so the caller uses the callee model restricted to the results that keep these bytes
(`Model.restrict` with `Kept`). The restriction is also in `post`, so the caller has it at the
return of the callee. `Decompiles.restrict` gives `Decompiles` of the restricted model from
`Decompiles` of the callee. A callee that writes the kept bytes has no result in the restricted
model: the caller model then has no return through that call. -/

namespace Lift.Sem

open Lift.P2.Total

/-- The memory `m'` has the bytes of `m` at the `n` addresses from `lo`. -/
def Kept (lo : BitVec 64) (n : Nat) (m m' : DataMem) : Prop :=
  ∀ i, i < n → m'.get? (lo + BitVec.ofNat 64 i) = m.get? (lo + BitVec.ofNat 64 i)

/-- The model `M` with only the results that satisfy `P`; `post` has `P` too. -/
def Model.restrict {A R : Type} (M : Model A R) (P : A → R → Prop) : Model A R where
  rep := M.rep
  returns a r := M.returns a r ∧ P a r
  post a r s t := M.post a r s t ∧ P a r

theorem Decompiles.restrict {A R : Type} {step : MachineState → Effects} {M : Model A R}
    (h : Decompiles step M) (P : A → R → Prop) : Decompiles step (M.restrict P) :=
  fun policy a r s hrep hret => (h policy a r s hrep hret.1).mono fun _ ht => ⟨ht, hret.2⟩

/-- A read of 8 kept bytes gives the same word. -/
theorem Kept.readRam {policy : CpuPolicy} {lo a : BitVec 64} {n k : Nat} {m m' : DataMem} {v : BitVec 64}
    (h : Kept lo n m m') (hk : k + 8 ≤ n) (ha : a = lo + BitVec.ofNat 64 k)
    (hr : Lift.P2.Total.readRam policy m a .W64 = .ok v) : Lift.P2.Total.readRam policy m' a .W64 = .ok v := by
  subst ha
  unfold Lift.P2.Total.readRam at hr ⊢
  have e : Mem.loadInt m' (lo + BitVec.ofNat 64 k) Width.W64.bytes = Mem.loadInt m (lo + BitVec.ofNat 64 k) Width.W64.bytes := by
    apply Mem.loadInt_congr
    intro i hi
    have hi8 : i < 8 := hi
    have e2 : lo + BitVec.ofNat 64 k + BitVec.ofNat 64 i = lo + BitVec.ofNat 64 (k + i) := by
      rw [BitVec.add_assoc, BitVec.ofNat_add]
    rw [e2]
    exact h (k + i) (by omega)
  rw [e]
  cases hp : policy.permits (.read (lo + BitVec.ofNat 64 k) .W64) <;> simp only [hp] at hr ⊢
  · cases hr
  · cases hl : Mem.loadInt m (lo + BitVec.ofNat 64 k) Width.W64.bytes <;> simp only [hl] at hr ⊢
    · cases hr
    · exact hr

end Lift.Sem
