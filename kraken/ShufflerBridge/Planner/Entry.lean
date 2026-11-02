module

public import ShufflerBridge.Planner.Run
import all ShufflerBridge.Planner.Run
public import ShufflerBridge.Planner.Loops
import all ShufflerBridge.Planner.Loops

@[expose] public section

/-!
The flat `plannerRun` and PR31 `Planner.run` (`plannerRun_corr`).
-/

namespace ShufflerBridge.Planner

open Shuffler Shuffler.Planner ShufflerBridge.Emission
open FlatShuffler.Flat (get put optOf NONE ofNat_succ)

/-! ## The check of the target slots -/

theorem mem_take_iff {α : Type} [Inhabited α] (v : Vector α FlatShuffler.maxStackSize) {k : Nat}
    (hk : k ≤ FlatShuffler.maxStackSize) (x : α) :
    x ∈ v.toList.take k ↔ ∃ i, i < k ∧ get v (.ofNat 64 i) = x := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [List.length_take, Vector.length_toList] at hi
    exact ⟨i, by omega, by rw [FlatShuffler.Flat.get_ofNat v (by omega)]; simp⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by simp; omega, by rw [FlatShuffler.Flat.get_ofNat v (by omega)]; simp⟩

theorem containsFrom_iff (stack : Vector FlatShuffler.StackSlot FlatShuffler.maxStackSize) {size : FlatShuffler.Word}
    (hs : size.toNat ≤ FlatShuffler.maxStackSize) (slot : FlatShuffler.StackSlot) :
    ∀ j k, k + j = size.toNat →
      (FlatShuffler.Flat.containsFrom stack size slot (.ofNat 64 k) = true ↔
        ∃ i, k ≤ i ∧ i < size.toNat ∧ get stack (.ofNat 64 i) = slot) := by
  intro j
  induction j with
  | zero =>
    intro k hk
    rw [FlatShuffler.Flat.containsFrom, dite_eq_right (by rw [FlatShuffler.Flat.ofNat_lt_iff (by omega)]; omega)]
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro i h1 h2; omega
  | succ j ih =>
    intro k hk
    rw [FlatShuffler.Flat.containsFrom, dite_eq_left (by rw [FlatShuffler.Flat.ofNat_lt_iff (by omega)]; omega),
      ofNat_succ]
    by_cases hg : get stack (.ofNat 64 k) = slot
    · rw [ite_eq_left hg]
      exact iff_of_true rfl ⟨k, le_refl _, by omega, hg⟩
    · rw [ite_eq_right hg, ih (k + 1) (by omega)]
      constructor
      · rintro ⟨i, h1, h2, h3⟩; exact ⟨i, by omega, h2, h3⟩
      · rintro ⟨i, h1, h2, h3⟩
        refine ⟨i, ?_, h2, h3⟩
        rcases Nat.lt_or_eq_of_le h1 with h | rfl
        · omega
        · exact absurd h3 hg

theorem containsFrom_mem (stack : Vector FlatShuffler.StackSlot FlatShuffler.maxStackSize) {size : FlatShuffler.Word}
    (hs : size.toNat ≤ FlatShuffler.maxStackSize) (slot : FlatShuffler.StackSlot) :
    FlatShuffler.Flat.containsFrom stack size slot 0 = true ↔ slot ∈ stack.toList.take size.toNat := by
  rw [show (0 : FlatShuffler.Word) = .ofNat 64 0 from rfl,
    containsFrom_iff stack hs slot size.toNat 0 (by omega), mem_take_iff stack hs]
  simp

-- The check of one target slot.
def tOk (pl : FlatShuffler.Flat.Planner) (sp : BitVec 32 → BitVec 8) (v : FlatShuffler.StackSlot) : Bool :=
  FlatShuffler.isJunk v || FlatShuffler.canBeFreelyGenerated v || FlatShuffler.Flat.containsFrom pl.source pl.sourceSize v 0 ||
    FlatShuffler.Flat.spillIsSpilled sp v

theorem targetsFrom_iff (pl : FlatShuffler.Flat.Planner) (hn : pl.targetSize.toNat ≤ FlatShuffler.maxStackSize)
    (sp : BitVec 32 → BitVec 8) :
    FlatShuffler.Flat.targetsFrom pl sp 0 = true ↔ ∀ v ∈ pl.target.toList.take pl.targetSize.toNat, tOk pl sp v = true := by
  rw [FlatShuffler.Flat.allFrom_iff hn (fun o => tOk pl sp (get pl.target o)) (FlatShuffler.Flat.targetsFrom pl sp)
    (fun o => by rw [FlatShuffler.Flat.targetsFrom]; simp only [dite_eq_ite]; rfl)]
  constructor
  · intro h v hv
    obtain ⟨i, hi, rfl⟩ := (mem_take_iff _ hn v).mp hv
    exact h i hi
  · intro h d hd
    exact h _ ((mem_take_iff _ hn _).mpr ⟨d, hd, rfl⟩)

theorem tOk_iff {pl : FlatShuffler.Flat.Planner} (hm : pl.sourceSize.toNat ≤ FlatShuffler.maxStackSize)
    (ok : SlotsOk (pl.source.toList.take pl.sourceSize.toNat ++ pl.target.toList.take pl.targetSize.toNat))
    (sp : BitVec 32 → BitVec 8) {v : FlatShuffler.StackSlot} (hv : v ∈ pl.target.toList.take pl.targetSize.toNat) :
    tOk pl sp v = true ↔ ((decodeStackSlot v).is_junk ∨ (decodeStackSlot v).can_be_freely_generated ∨
      decodeStackSlot v ∈ srcOf pl.source pl.sourceSize ∨
      (pSpills (pl.source.toList.take pl.sourceSize.toNat) pl.targetSize.toNat pl.target sp).is_spilled (decodeStackSlot v)) := by
  have hs : v ∈ pl.source.toList.take pl.sourceSize.toNat ↔ decodeStackSlot v ∈ srcOf pl.source pl.sourceSize := by
    simp only [srcOf, List.mem_map]
    constructor
    · intro h; exact ⟨v, h, rfl⟩
    · rintro ⟨w, hw, he⟩
      rw [decode_inj (ok.canon _ (List.mem_append_left _ hw))
        (ok.canon _ (List.mem_append_right _ hv)) he] at hw
      exact hw
  simp only [tOk, Bool.or_eq_true]
  rw [← isJunk_iff, isFree_iff, containsFrom_mem _ hm, hs,
    isSpilled_corr (S := pl.source.toList.take pl.sourceSize.toNat) sp (List.mem_append_right _ hv), or_assoc,
    or_assoc]

/-! ## `run` -/

-- A `for` loop whose body gives `.yield` if `P` holds, and the error `err` if not.
theorem forIn_check {α ε : Type} (P : α → Prop) [dP : DecidablePred P] (err : ε)
    (f : α → PUnit → Except ε (ForInStep PUnit))
    (hT : ∀ x, P x → f x PUnit.unit = .ok (.yield PUnit.unit))
    (hF : ∀ x, ¬P x → f x PUnit.unit = .error err) (L : List α) :
    forIn L PUnit.unit f = if ∀ x ∈ L, P x then Except.ok PUnit.unit else Except.error err := by
  classical
  induction L with
  | nil => simp; rfl
  | cons a L ih =>
    rw [List.forIn_cons]
    by_cases ha : P a
    · rw [hT a ha, except_ok_bind]
      simp only [ih, List.forall_mem_cons, ha, true_and]
    · rw [hF a ha, except_error_bind]
      simp only [List.forall_mem_cons, ha, false_and, ite_false]

theorem plannerRun_corr {pl : FlatShuffler.Flat.Planner} (hm : pl.sourceSize.toNat ≤ FlatShuffler.maxStackSize)
    (hn : pl.targetSize.toNat ≤ FlatShuffler.maxStackSize)
    (ok : SlotsOk (pl.source.toList.take pl.sourceSize.toNat ++ pl.target.toList.take pl.targetSize.toNat))
    (take : Bool) (s : FlatShuffler.Flat.PSt) (us : Nat → FlatShuffler.Flat.RunU)
    (hd : DnR (Vector.replicate (srcOf pl.source pl.sourceSize).length (0 : Byte)) s.dropped) :
    RunR pl (FlatShuffler.Flat.plannerRun pl take s us)
      (Planner.run (srcOf pl.source pl.sourceSize) (srcOf pl.target pl.targetSize)
        (pSpills (pl.source.toList.take pl.sourceSize.toNat) pl.targetSize.toNat pl.target s.spills) pl.allowed
        (if take then .Take else .Leave)) := by
  classical
  rw [FlatShuffler.Flat.plannerRun, Planner.run.eq_1]
  dsimp only
  rw [forIn_check (dP := fun _ => Classical.propDecidable _) _ (.assertion "target slot neither on the stack nor generatable") _
    (fun x hx => by rw [requires_of_true _ hx]; rfl)
    (fun x hx => by rw [requires_of_false _ hx]; rfl)]
  have hall : (∀ x ∈ srcOf pl.target pl.targetSize, x.is_junk ∨ x.can_be_freely_generated ∨
      x ∈ srcOf pl.source pl.sourceSize ∨
      (pSpills (pl.source.toList.take pl.sourceSize.toNat) pl.targetSize.toNat pl.target s.spills).is_spilled x) ↔
      FlatShuffler.Flat.targetsFrom pl s.spills 0 = true := by
    rw [targetsFrom_iff pl hn, srcOf, List.forall_mem_map]
    exact forall₂_congr fun v hv => (tOk_iff hm ok s.spills hv).symm
  by_cases ht : FlatShuffler.Flat.targetsFrom pl s.spills 0#64 = true
  · rw [ite_eq_right (by simp [ht]), ite_eq_left (hall.mpr ht), except_ok_bind]
    exact runLoop_corr hm hn ok take _ _ _ false us rfl ⟨rfl, rfl, hd⟩ rfl
  · rw [ite_eq_left (by simp [ht]), ite_eq_right (mt hall.mp ht), except_error_bind]
    rfl

end ShufflerBridge.Planner
