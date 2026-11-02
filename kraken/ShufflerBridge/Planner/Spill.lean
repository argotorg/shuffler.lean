module

public import ShufflerBridge.Planner.MapR
import all ShufflerBridge.Planner.MapR
public import ShufflerBridge.Planner.Emission
import all ShufflerBridge.Planner.Emission

@[expose] public section

/-!
The flat spill bytes and the PR31 spill set of the planner.

The PR31 spill set of the bytes `sp` is `spilledVariables (listEnv n t sp) src`: the ids of the
variables of the source and the target whose byte is not 0. `SlotsOk` holds for the source and
target slots: they are canonical, their kind is a kind of the C++, and two variable slots with
one payload are equal. Then `Flat.spillAdd` is `SpillSet.add` (`add_corr`), and
`Flat.spillIsSpilled` is `SpillSet.is_spilled` (`isSpilled_corr`).
-/

namespace ShufflerBridge.Planner

open Shuffler ShufflerBridge.Emission
open FlatShuffler.Flat (isVariable spillIsSpilled spillAdd setByte listEnv)

-- The source and target slots `L`.
structure SlotsOk (L : List FlatShuffler.StackSlot) : Prop where
  canon : ∀ v ∈ L, StackSlotHasCanonicalEncoding v
  kind : ∀ v ∈ L, v.kind.toNat < 4
  inj : ∀ v ∈ L, ∀ w ∈ L, isVariable v = true → isVariable w = true → v.payload = w.payload →
    v = w

theorem decode_var {v : FlatShuffler.StackSlot} (hk : v.kind.toNat < 4) (i : VarId) :
    decodeStackSlot v = .Var i ↔ isVariable v = true ∧ i = ⟨stackSlotIdentity v⟩ := by
  have hiv : isVariable v = true ↔ v.kind = 0 ∧ v.valueOpcode ≠ 0 := by
    simp [isVariable, FlatShuffler.isLiteralValue, FlatShuffler.Value, FlatShuffler.Const]
  rw [hiv, decodeStackSlot]
  by_cases h0 : v.kind = FlatShuffler.Junk
  · rw [ite_eq_left h0]
    constructor
    · intro h; cases h
    · rintro ⟨⟨h, -⟩, -⟩; rw [h] at h0; exact absurd h0 (by decide)
  rw [ite_eq_right h0]
  by_cases h1 : v.valueOpcode = FlatShuffler.Const ∨ v.kind = FlatShuffler.FunctionCallReturnLabel
  · rw [ite_eq_left h1]
    constructor
    · intro h; cases h
    · rintro ⟨⟨h, ho⟩, -⟩
      rcases h1 with h1 | h1
      · exact absurd h1 ho
      · rw [h] at h1; exact absurd h1 (by decide)
  rw [ite_eq_right h1]
  by_cases h2 : v.kind = FlatShuffler.FunctionReturnLabel
  · rw [ite_eq_left h2]
    constructor
    · intro h; cases h
    · rintro ⟨⟨h, -⟩, -⟩; rw [h] at h2; exact absurd h2 (by decide)
  rw [ite_eq_right h2]
  have hk0 : v.kind = 0 := by
    rw [not_or] at h1
    have := h1.2
    simp only [FlatShuffler.Junk, FlatShuffler.FunctionCallReturnLabel, FlatShuffler.FunctionReturnLabel] at h0 h2 this
    bv_omega
  have ho : v.valueOpcode ≠ 0 := fun h => h1 (.inl h)
  constructor
  · intro h; cases h; exact ⟨⟨hk0, ho⟩, rfl⟩
  · rintro ⟨-, rfl⟩; rfl

theorem isSpilled_listEnv (n : Nat) (t : Vector FlatShuffler.StackSlot FlatShuffler.MAX_N)
    (sp : BitVec 32 → BitVec 8) (x : FlatShuffler.StackSlot) :
    FlatShuffler.isSpilled (listEnv n t sp) x = spillIsSpilled sp x := by
  simp only [FlatShuffler.isSpilled, spillIsSpilled, isVariable, listEnv, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]
  congr 1

theorem mem_spillSet {e : FlatShuffler.Env} {src : Stack} {i : Nat} :
    VarId.mk i ∈ spilledVariables e src ↔
      i < 2 ^ 48 ∧ FlatShuffler.isSpilled e (stackSlotFromIdentity i) = true ∧ Value.Var ⟨i⟩ ∈ src ++ decodedTargetStack e := by
  simp [spilledVariables, Finset.mem_image, Finset.mem_filter, Finset.mem_range]

section
variable {S : List FlatShuffler.StackSlot} {n : Nat} {t : Vector FlatShuffler.StackSlot FlatShuffler.MAX_N}

-- The PR31 spill set of the bytes `sp`.
abbrev pSpills (S : List FlatShuffler.StackSlot) (n : Nat) (t : Vector FlatShuffler.StackSlot FlatShuffler.MAX_N)
    (sp : BitVec 32 → BitVec 8) : SpillSet :=
  spilledVariables (listEnv n t sp) (S.map decodeStackSlot)

theorem src_tgt (sp : BitVec 32 → BitVec 8) :
    S.map decodeStackSlot ++ decodedTargetStack (listEnv n t sp) = (S ++ t.toList.take n).map decodeStackSlot := by
  simp [decodedTargetStack, listEnv]

-- A variable of the source or the target is in the spill set if and only if its byte is not 0.
theorem mem_pSpills (ok : SlotsOk (S ++ t.toList.take n)) (sp : BitVec 32 → BitVec 8)
    {i : Nat} :
    VarId.mk i ∈ pSpills S n t sp ↔
      ∃ v ∈ S ++ t.toList.take n, isVariable v = true ∧ i = stackSlotIdentity v ∧ sp v.payload ≠ 0 := by
  rw [mem_spillSet, src_tgt, List.mem_map]
  constructor
  · rintro ⟨-, hs, v, hv, hd⟩
    obtain ⟨hvar, hi⟩ := (decode_var (ok.kind v hv) _).mp hd
    simp only [VarId.mk.injEq] at hi
    subst hi
    rw [ofNumber_number, isSpilled_listEnv] at hs
    simp only [spillIsSpilled, hvar, Bool.true_and, bne_iff_ne, ne_eq] at hs
    exact ⟨v, hv, hvar, rfl, hs⟩
  · rintro ⟨v, hv, hvar, rfl, hs⟩
    refine ⟨number_lt v, ?_, v, hv, (decode_var (ok.kind v hv) _).mpr ⟨hvar, rfl⟩⟩
    rw [ofNumber_number, isSpilled_listEnv]
    simpa [spillIsSpilled, hvar] using hs

-- `spillIsSpilled` of a source or target slot is `SpillSet.is_spilled`.
theorem isSpilled_corr (sp : BitVec 32 → BitVec 8)
    {x : FlatShuffler.StackSlot} (hx : x ∈ S ++ t.toList.take n) :
    spillIsSpilled sp x = true ↔ (pSpills S n t sp).is_spilled (decodeStackSlot x) := by
  rw [← isSpilled_listEnv n t sp, isSpilled_iff]
  rw [src_tgt]
  exact List.mem_map_of_mem hx

-- A result of `spillAdd` and a result of `SpillSet.add`: both are done with the spill set of
-- the bytes, or both fail.
def SpCorr (S : List FlatShuffler.StackSlot) (n : Nat) (t : Vector FlatShuffler.StackSlot FlatShuffler.MAX_N) :
    FlatShuffler.Flat.Status × (BitVec 32 → BitVec 8) → Except ShuffleErr SpillSet → Prop
  | (.done, sp), .ok s => s = pSpills S n t sp
  | (.assertionFailed, _), .error _ => True
  | _, _ => False

-- The spill set after `m_spilled[p] = 1` for a variable `x` of the source or the target.
theorem pSpills_setByte (ok : SlotsOk (S ++ t.toList.take n)) (sp : BitVec 32 → BitVec 8)
    {x : FlatShuffler.StackSlot} (hxl : x ∈ S ++ t.toList.take n) (hv : isVariable x = true) :
    pSpills S n t (setByte sp x.payload 1) = insert ⟨stackSlotIdentity x⟩ (pSpills S n t sp) := by
  ext ⟨i⟩
  rw [Finset.mem_insert, mem_pSpills ok, mem_pSpills ok, VarId.mk.injEq]
  constructor
  · rintro ⟨v, hvl, hvv, rfl, hs⟩
    unfold setByte at hs
    split at hs
    · left
      rw [ok.inj v hvl x hxl hvv hv (by assumption)]
    · exact .inr ⟨v, hvl, hvv, rfl, hs⟩
  · rintro (rfl | ⟨v, hvl, hvv, rfl, hs⟩)
    · exact ⟨x, hxl, hv, rfl, by simp [setByte]⟩
    · refine ⟨v, hvl, hvv, rfl, ?_⟩
      unfold setByte
      split
      · simp
      · exact hs

theorem number_inj {v w : FlatShuffler.StackSlot} (h : stackSlotIdentity v = stackSlotIdentity w) : v = w := by
  have h1 := congrArg stackSlotFromIdentity h
  rwa [ofNumber_number, ofNumber_number] at h1

theorem add_corr (ok : SlotsOk (S ++ t.toList.take n)) (sp : BitVec 32 → BitVec 8)
    {x : FlatShuffler.StackSlot} (hx : x ∈ S) :
    SpCorr S n t (spillAdd sp x) ((pSpills S n t sp).add (decodeStackSlot x)) := by
  have hxl : x ∈ S ++ t.toList.take n := List.mem_append_left _ hx
  have hk := ok.kind x hxl
  cases hv : isVariable x
  · have hf : spillAdd sp x = (.assertionFailed, sp) := by
      unfold spillAdd; rw [ite_eq_left (by rw [hv]; rfl)]
    rw [hf]
    have hnv : ∀ i, decodeStackSlot x ≠ .Var i := fun i h => by
      have := ((decode_var hk i).mp h).1
      rw [hv] at this; cases this
    revert hnv
    cases decodeStackSlot x with
    | Var i => intro h; exact (h i rfl).elim
    | _ => intro _; exact True.intro
  · have hd : decodeStackSlot x = .Var ⟨stackSlotIdentity x⟩ := (decode_var hk _).mpr ⟨hv, rfl⟩
    rw [hd]
    by_cases hz : sp x.payload = 0
    · have hm : VarId.mk (stackSlotIdentity x) ∉ pSpills S n t sp := by
        rw [mem_pSpills ok]
        rintro ⟨v, hvl, hvv, hi, hs⟩
        rw [← number_inj hi] at hs
        exact hs hz
      have hf : spillAdd sp x = (.done, setByte sp x.payload 1) := by
        unfold spillAdd
        rw [ite_eq_right (by rw [hv]; decide), ite_eq_right (by rw [hz]; decide)]
      rw [hf]
      show SpCorr S n t _ (requires _ _ >>= fun _ => pure _)
      rw [requires_of_true _ hm, except_ok_bind]
      exact (pSpills_setByte ok sp hxl hv).symm
    · have hm : VarId.mk (stackSlotIdentity x) ∈ pSpills S n t sp :=
        (mem_pSpills ok sp).mpr ⟨x, hxl, hv, rfl, hz⟩
      have hf : spillAdd sp x = (.assertionFailed, sp) := by
        unfold spillAdd
        rw [ite_eq_right (by rw [hv]; decide), ite_eq_left (by simpa using hz)]
      rw [hf]
      show SpCorr S n t _ (requires _ _ >>= fun _ => pure _)
      rw [requires_of_false _ (not_not.mpr hm)]
      trivial

end

end ShufflerBridge.Planner
