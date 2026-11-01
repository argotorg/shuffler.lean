module

public import PlanBridge.Run
import all PlanBridge.Run
public import PlanBridge.Loops
import all PlanBridge.Loops

@[expose] public section

/-!
The flat `plannerRun` and PR31 `Planner.run` (`plannerRun_corr`), and the entry `planEntry`
(`planEntry_corr`).
-/

namespace PlanBridge

open Shuffler Shuffler.Planner BbuBridge
open Bbu.Flat (get put optOf NONE ofNat_succ)

/-! ## The check of the target slots -/

theorem mem_take_iff {α : Type} [Inhabited α] (v : Vector α Bbu.MAX_N) {k : Nat}
    (hk : k ≤ Bbu.MAX_N) (x : α) :
    x ∈ v.toList.take k ↔ ∃ i, i < k ∧ get v (.ofNat 64 i) = x := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [List.length_take, Vector.length_toList] at hi
    exact ⟨i, by omega, by rw [Bbu.Flat.get_ofNat v (by omega)]; simp⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by simp; omega, by rw [Bbu.Flat.get_ofNat v (by omega)]; simp⟩

theorem containsFrom_iff (stack : Vector Bbu.StackSlot Bbu.MAX_N) {size : Bbu.Word}
    (hs : size.toNat ≤ Bbu.MAX_N) (slot : Bbu.StackSlot) :
    ∀ j k, k + j = size.toNat →
      (Bbu.Flat.containsFrom stack size slot (.ofNat 64 k) = true ↔
        ∃ i, k ≤ i ∧ i < size.toNat ∧ get stack (.ofNat 64 i) = slot) := by
  intro j
  induction j with
  | zero =>
    intro k hk
    rw [Bbu.Flat.containsFrom, dite_eq_right (by rw [Bbu.Flat.ofNat_lt_iff (by omega)]; omega)]
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro i h1 h2; omega
  | succ j ih =>
    intro k hk
    rw [Bbu.Flat.containsFrom, dite_eq_left (by rw [Bbu.Flat.ofNat_lt_iff (by omega)]; omega),
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

theorem containsFrom_mem (stack : Vector Bbu.StackSlot Bbu.MAX_N) {size : Bbu.Word}
    (hs : size.toNat ≤ Bbu.MAX_N) (slot : Bbu.StackSlot) :
    Bbu.Flat.containsFrom stack size slot 0 = true ↔ slot ∈ stack.toList.take size.toNat := by
  rw [show (0 : Bbu.Word) = .ofNat 64 0 from rfl,
    containsFrom_iff stack hs slot size.toNat 0 (by omega), mem_take_iff stack hs]
  simp

-- The check of one target slot.
def tOk (pl : Bbu.Flat.Planner) (sp : BitVec 32 → BitVec 8) (v : Bbu.StackSlot) : Bool :=
  Bbu.isJunk v || Bbu.canBeFreelyGenerated v || Bbu.Flat.containsFrom pl.source pl.m v 0 ||
    Bbu.Flat.spillIsSpilled sp v

theorem targetsFrom_iff (pl : Bbu.Flat.Planner) (hn : pl.n.toNat ≤ Bbu.MAX_N)
    (sp : BitVec 32 → BitVec 8) :
    Bbu.Flat.targetsFrom pl sp 0 = true ↔ ∀ v ∈ pl.target.toList.take pl.n.toNat, tOk pl sp v = true := by
  rw [Bbu.Flat.allFrom_iff hn (fun o => tOk pl sp (get pl.target o)) (Bbu.Flat.targetsFrom pl sp)
    (fun o => by rw [Bbu.Flat.targetsFrom]; simp only [dite_eq_ite]; rfl)]
  constructor
  · intro h v hv
    obtain ⟨i, hi, rfl⟩ := (mem_take_iff _ hn v).mp hv
    exact h i hi
  · intro h d hd
    exact h _ ((mem_take_iff _ hn _).mpr ⟨d, hd, rfl⟩)

theorem tOk_iff {pl : Bbu.Flat.Planner} (hm : pl.m.toNat ≤ Bbu.MAX_N)
    (ok : SlotsOk (pl.source.toList.take pl.m.toNat ++ pl.target.toList.take pl.n.toNat))
    (sp : BitVec 32 → BitVec 8) {v : Bbu.StackSlot} (hv : v ∈ pl.target.toList.take pl.n.toNat) :
    tOk pl sp v = true ↔ ((decode v).is_junk ∨ (decode v).can_be_freely_generated ∨
      decode v ∈ srcOf pl.source pl.m ∨
      (pSpills (pl.source.toList.take pl.m.toNat) pl.n.toNat pl.target sp).is_spilled (decode v)) := by
  have hs : v ∈ pl.source.toList.take pl.m.toNat ↔ decode v ∈ srcOf pl.source pl.m := by
    simp only [srcOf, List.mem_map]
    constructor
    · intro h; exact ⟨v, h, rfl⟩
    · rintro ⟨w, hw, he⟩
      rw [decode_inj (ok.canon _ (List.mem_append_left _ hw))
        (ok.canon _ (List.mem_append_right _ hv)) he] at hw
      exact hw
  simp only [tOk, Bool.or_eq_true]
  rw [← isJunk_iff, isFree_iff, containsFrom_mem _ hm, hs,
    isSpilled_corr (S := pl.source.toList.take pl.m.toNat) sp (List.mem_append_right _ hv), or_assoc,
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

theorem plannerRun_corr {pl : Bbu.Flat.Planner} (hm : pl.m.toNat ≤ Bbu.MAX_N)
    (hn : pl.n.toNat ≤ Bbu.MAX_N)
    (ok : SlotsOk (pl.source.toList.take pl.m.toNat ++ pl.target.toList.take pl.n.toNat))
    (take : Bool) (s : Bbu.Flat.PSt) (us : Nat → Bbu.Flat.RunU)
    (hd : DnR (Vector.replicate (srcOf pl.source pl.m).length (0 : Byte)) s.dropped) :
    RunR pl (Bbu.Flat.plannerRun pl take s us)
      (Planner.run (srcOf pl.source pl.m) (srcOf pl.target pl.n)
        (pSpills (pl.source.toList.take pl.m.toNat) pl.n.toNat pl.target s.spills) pl.allowed
        (if take then .Take else .Leave)) := by
  classical
  rw [Bbu.Flat.plannerRun, Planner.run.eq_1]
  dsimp only
  rw [forIn_check (dP := fun _ => Classical.propDecidable _) _ (.assertion "target slot neither on the stack nor generatable") _
    (fun x hx => by rw [requires_of_true _ hx]; rfl)
    (fun x hx => by rw [requires_of_false _ hx]; rfl)]
  have hall : (∀ x ∈ srcOf pl.target pl.n, x.is_junk ∨ x.can_be_freely_generated ∨
      x ∈ srcOf pl.source pl.m ∨
      (pSpills (pl.source.toList.take pl.m.toNat) pl.n.toNat pl.target s.spills).is_spilled x) ↔
      Bbu.Flat.targetsFrom pl s.spills 0 = true := by
    rw [targetsFrom_iff pl hn, srcOf, List.forall_mem_map]
    exact forall₂_congr fun v hv => (tOk_iff hm ok s.spills hv).symm
  by_cases ht : Bbu.Flat.targetsFrom pl s.spills 0#64 = true
  · rw [ite_eq_right (by simp [ht]), ite_eq_left (hall.mpr ht), except_ok_bind]
    exact runLoop_corr hm hn ok take _ _ _ false us rfl ⟨rfl, rfl, hd⟩ rfl
  · rw [ite_eq_left (by simp [ht]), ite_eq_right (mt hall.mp ht), except_error_bind]
    rfl

/-! ## The entry -/

-- The return value of `plan` for the result `r` of `run`.
def codeOf (r : Bbu.Flat.Status × Bbu.Flat.PSt) : Bbu.Word :=
  match r.1 with
  | .done => .ofNat 64 r.2.trace.length
  | .blocked => -1
  | .assertionFailed => -2

-- `plan` returns -2 for the arguments that it rejects. Else it runs `Planner.run` and its
-- result is that of PR31 `Planner.run` on the decoded slots.
theorem planEntry_corr (m n : Bbu.Word) (source target : Vector Bbu.StackSlot Bbu.MAX_N)
    (spilled : BitVec 32 → BitVec 8) (idCount : Bbu.Word) (allowed strategy : BitVec 8)
    (dropped : Vector (BitVec 8) Bbu.MAX_N) (data : Vector Bbu.StackSlot Bbu.MAX_N)
    (sources : Vector Bbu.Word Bbu.MAX_N) (us : Nat → Bbu.Flat.RunU)
    (ok : SlotsOk (source.toList.take m.toNat ++ target.toList.take n.toNat)) :
    match Bbu.Flat.planEntry m n source target spilled idCount allowed strategy dropped data
      sources us with
    | (c, none) => c = -2
    | (c, some r) => m.toNat ≤ Bbu.MAX_N ∧ n.toNat ≤ Bbu.MAX_N ∧ c = codeOf r ∧
        RunR ⟨source, m, target, n, allowed = 1⟩ r
          (Planner.run (srcOf source m) (srcOf target n)
            (pSpills (source.toList.take m.toNat) n.toNat target spilled) (allowed = 1)
            (if decide (strategy = 1) then .Take else .Leave)) := by
  unfold Bbu.Flat.planEntry
  split_ifs with h1 <;> try rfl
  all_goals
    obtain ⟨hm, hn⟩ := not_or.mp h1
    rw [gt_iff_lt, Bbu.Flat.ofNat_lt_iff le_rfl, Nat.not_lt] at hm
    replace hn := (not_or.mp hn).1
    rw [gt_iff_lt, Bbu.Flat.ofNat_lt_iff le_rfl, Nat.not_lt] at hn
    have hr := plannerRun_corr (pl := ⟨source, m, target, n, allowed = 1⟩) hm hn ok (strategy = 1)
      ⟨spilled, Bbu.Flat.zeroFrom m 0 dropped, false, data, [], sources⟩ us (dnR_replicate hm dropped)
    first
    | rw [ite_eq_left ‹decide (strategy = 1) = true›] at hr
    | rw [ite_eq_right ‹¬decide (strategy = 1) = true›] at hr
    dsimp only
    generalize Bbu.Flat.plannerRun _ _ _ _ = r at hr ⊢
    rcases r with ⟨st, ps⟩
    cases st <;> exact ⟨hm, hn, rfl, hr⟩

end PlanBridge
