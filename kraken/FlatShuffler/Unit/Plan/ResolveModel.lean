module

public import FlatShuffler.Unit.Plan.ClassifyMem
import all FlatShuffler.Unit.Plan.ClassifyMem

@[expose] public section

/-! Steps of the three loops in `Planner::resolve`. Each step follows one
branch of the assembly. These lemmas do not assume correctness of a callee. -/

namespace FlatShuffler.Unit.ResolveU

open FlatShuffler.Sep

section
variable {m o : Word} {dn : Vector (BitVec 8) maxStackSize}

theorem zero_done (h : ¬ o < m) : Flat.zeroFrom m o dn = dn := by
  rw [Flat.zeroFrom, dite_eq_right h]

theorem zero_step (h : o < m) :
    Flat.zeroFrom m o dn = Flat.zeroFrom m (o + 1) (Flat.put dn o 0) := by
  rw [Flat.zeroFrom, dite_eq_left h]
end

section
variable {M current : Flat.Mapping} {size pos count : Word}
  {cand : Vector Word maxStackSize}

theorem candidates_done (h : ¬ pos < size) :
    Flat.candidatesFrom M current size pos cand count = some (cand, count) := by
  rw [Flat.candidatesFrom, dite_eq_right h]

theorem candidates_skip_dest (h : pos < size)
    (hd : Flat.get current.dest pos = Flat.NONE) :
    Flat.candidatesFrom M current size pos cand count =
      Flat.candidatesFrom M current size (pos + 1) cand count := by
  rw [Flat.candidatesFrom, dite_eq_left h]
  simp [hd]

theorem candidates_skip_source (h : pos < size)
    (hp : Flat.get M.pos (Flat.get current.dest pos) = Flat.NONE) :
    Flat.candidatesFrom M current size pos cand count =
      Flat.candidatesFrom M current size (pos + 1) cand count := by
  rw [Flat.candidatesFrom, dite_eq_left h]
  simp [hp]

theorem candidates_fail (h : pos < size)
    (hd : Flat.get current.dest pos ≠ Flat.NONE)
    (hp : Flat.get M.pos (Flat.get current.dest pos) ≠ Flat.NONE)
    (hr : Flat.get M.dest (Flat.get M.pos (Flat.get current.dest pos)) = Flat.NONE) :
    Flat.candidatesFrom M current size pos cand count = none := by
  rw [Flat.candidatesFrom, dite_eq_left h]
  simp [hd, hp, hr]

theorem candidates_add (h : pos < size)
    (hd : Flat.get current.dest pos ≠ Flat.NONE)
    (hp : Flat.get M.pos (Flat.get current.dest pos) ≠ Flat.NONE)
    (hr : Flat.get M.dest (Flat.get M.pos (Flat.get current.dest pos)) ≠ Flat.NONE) :
    Flat.candidatesFrom M current size pos cand count =
      Flat.candidatesFrom M current size (pos + 1)
        (Flat.put cand count (Flat.get M.pos (Flat.get current.dest pos))) (count + 1) := by
  rw [Flat.candidatesFrom, dite_eq_left h]
  simp [hd, hp, hr]
end

section
variable {p : Flat.Planner} {sp : BitVec 32 → BitVec 8} {M : Flat.Mapping}
  {dn : Vector (BitVec 8) maxStackSize} {cand : Vector Word maxStackSize}
  {count i best : Word} {cls : BitVec 8}

theorem pick_done (h : ¬ i < count) :
    Flat.pickFrom p sp M dn cand count i best cls = (best, cls) := by
  rw [Flat.pickFrom, dite_eq_right h]

theorem pick_skip_dropped (h : i < count) (hd : Flat.get dn (Flat.get cand i) ≠ 0#8) :
    Flat.pickFrom p sp M dn cand count i best cls =
      Flat.pickFrom p sp M dn cand count (i + 1) best cls := by
  rw [Flat.pickFrom, dite_eq_left h]
  simp [hd]

theorem pick_skip_class (h : i < count) (hd : Flat.get dn (Flat.get cand i) = 0#8)
    (hc : Flat.classify p sp M dn (Flat.get cand i) = Flat.NOCLASS) :
    Flat.pickFrom p sp M dn cand count i best cls =
      Flat.pickFrom p sp M dn cand count (i + 1) best cls := by
  rw [Flat.pickFrom, dite_eq_left h]
  simp [hd, hc]

-- `classify` returns a class. The assembly tests class order before it tests `NONE`.
def better (M : Flat.Mapping) (off best : Word) (c cls : BitVec 8) : Bool :=
  best == Flat.NONE || decide (c < cls) ||
    (c == cls && decide (Flat.get M.dest off > Flat.get M.dest best))

theorem better_absent (off : Word) (c cls : BitVec 8) :
    better M off Flat.NONE c cls = true := by simp [better]

theorem better_lower (off best : Word) (c cls : BitVec 8) (h : c < cls) :
    better M off best c cls = true := by simp [better, h]

theorem better_tie (off best : Word) (c : BitVec 8) (h : best ≠ Flat.NONE) :
    better M off best c c = decide (Flat.get M.dest off > Flat.get M.dest best) := by
  simp [better, h]

theorem better_higher (off best : Word) (c cls : BitVec 8)
    (hb : best ≠ Flat.NONE) (hc : cls < c) : better M off best c cls = false := by
  have hn : ¬ c < cls := by bv_omega
  have he : c ≠ cls := by bv_omega
  simp [better, hb, hn, he]

theorem rank_spill (x : ClassifyU.Inputs) (h : x.rank = Flat.SPILL) :
    x.allowed = true ∧ Flat.isVariable x.slot = true := by
  unfold ClassifyU.Inputs.rank at h
  split at h
  · simp [Flat.SPILL] at h
  · split at h
    · simp [Flat.SPILL] at h
    · split at h
      · simp [Flat.SPILL] at h
      · split at h
        · rename_i hc
          simpa only [Bool.and_eq_true] using hc
        · simp [Flat.NOCLASS, Flat.SPILL] at h

theorem eval_spill (x : ClassifyU.Inputs) (h : x.eval = Flat.SPILL) :
    x.allowed = true ∧ Flat.isVariable x.slot = true := by
  unfold ClassifyU.Inputs.eval at h
  split at h
  · simp [Flat.NOCLASS, Flat.SPILL] at h
  · split at h
    · simp [Flat.SPILL] at h
    · exact rank_spill x h

theorem classify_spill (p : Flat.Planner) (sp : BitVec 32 → BitVec 8) (M : Flat.Mapping)
    (dn : Vector (BitVec 8) maxStackSize) (off : Word)
    (h : Flat.classify p sp M dn off = Flat.SPILL) :
    p.allowed = true ∧ Flat.isVariable (Flat.get p.source off) = true := by
  exact eval_spill (ClassifyU.inputs p sp M dn off)
    ((ClassifyU.eval_eq_classify p sp M dn off).trans h)

theorem pick_take (h : i < count) (hd : Flat.get dn (Flat.get cand i) = 0#8)
    (hc : Flat.classify p sp M dn (Flat.get cand i) ≠ Flat.NOCLASS)
    (hb : better M (Flat.get cand i) best (Flat.classify p sp M dn (Flat.get cand i)) cls = true) :
    Flat.pickFrom p sp M dn cand count i best cls =
      Flat.pickFrom p sp M dn cand count (i + 1) (Flat.get cand i)
        (Flat.classify p sp M dn (Flat.get cand i)) := by
  rw [Flat.pickFrom, dite_eq_left h]
  rw [ite_eq_right (fun hn => hn hd), ite_eq_right hc]
  simpa only [better, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq,
    Bool.and_eq_true, ite_true] using congrArg
      (fun b => if b then
        Flat.pickFrom p sp M dn cand count (i + 1) (Flat.get cand i)
          (Flat.classify p sp M dn (Flat.get cand i))
        else Flat.pickFrom p sp M dn cand count (i + 1) best cls) hb

theorem pick_keep (h : i < count) (hd : Flat.get dn (Flat.get cand i) = 0#8)
    (hc : Flat.classify p sp M dn (Flat.get cand i) ≠ Flat.NOCLASS)
    (hb : better M (Flat.get cand i) best (Flat.classify p sp M dn (Flat.get cand i)) cls = false) :
    Flat.pickFrom p sp M dn cand count i best cls =
      Flat.pickFrom p sp M dn cand count (i + 1) best cls := by
  rw [Flat.pickFrom, dite_eq_left h]
  rw [ite_eq_right (fun hn => hn hd), ite_eq_right hc]
  simpa only [better, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq,
    Bool.and_eq_true, Bool.false_eq_true, ite_false] using congrArg
      (fun b => if b then
        Flat.pickFrom p sp M dn cand count (i + 1) (Flat.get cand i)
          (Flat.classify p sp M dn (Flat.get cand i))
        else Flat.pickFrom p sp M dn cand count (i + 1) best cls) hb
end

section
variable {p : Flat.Planner} {M : Flat.Mapping} {cand : Vector Word maxStackSize}
  {count excess k : Word} {s : Flat.RState}

abbrev picked (p : Flat.Planner) (M : Flat.Mapping) (cand : Vector Word maxStackSize)
    (count : Word) (s : Flat.RState) : Word × BitVec 8 :=
  Flat.pickFrom p s.spills M s.droppedNow cand count 0#64 Flat.NONE 0#8

theorem pass_done (h : ¬ k < excess) :
    Flat.passFrom p M cand count excess k s = (.dropped, s) := by
  rw [Flat.passFrom, dite_eq_right h]

theorem pass_stuck (h : k < excess) (hb : (picked p M cand count s).1 = Flat.NONE) :
    Flat.passFrom p M cand count excess k s = (.stuck, s) := by
  rw [Flat.passFrom, dite_eq_left h]
  simp only [picked] at hb
  simp [hb]

theorem pass_fail (h : k < excess) (hb : (picked p M cand count s).1 ≠ Flat.NONE)
    (hc : (picked p M cand count s).2 = Flat.SPILL)
    (ha : (Flat.spillAdd s.spills (Flat.get p.source (picked p M cand count s).1)).1 ≠ .done) :
    Flat.passFrom p M cand count excess k s = (.assertionExit, s) := by
  rw [Flat.passFrom, dite_eq_left h]
  simp only [picked] at hb hc ha
  simp [hb, hc, ha]

theorem pass_drop (h : k < excess) (hb : (picked p M cand count s).1 ≠ Flat.NONE)
    (hc : (picked p M cand count s).2 ≠ Flat.SPILL) :
    Flat.passFrom p M cand count excess k s =
      Flat.passFrom p M cand count excess (k + 1)
        ⟨s.spills, Flat.put s.dropped (picked p M cand count s).1 1,
          Flat.put s.droppedNow (picked p M cand count s).1 1⟩ := by
  rw [Flat.passFrom, dite_eq_left h]
  simp only [picked] at hb hc
  simp [hb, hc]

theorem pass_spill (h : k < excess) (hb : (picked p M cand count s).1 ≠ Flat.NONE)
    (hc : (picked p M cand count s).2 = Flat.SPILL)
    (ha : (Flat.spillAdd s.spills (Flat.get p.source (picked p M cand count s).1)).1 = .done) :
    Flat.passFrom p M cand count excess k s =
      Flat.passFrom p M cand count excess (k + 1)
        ⟨(Flat.spillAdd s.spills (Flat.get p.source (picked p M cand count s).1)).2,
          Flat.put s.dropped (picked p M cand count s).1 1,
          Flat.put s.droppedNow (picked p M cand count s).1 1⟩ := by
  rw [Flat.passFrom, dite_eq_left h]
  simp only [picked] at hb hc ha
  simp [hb, hc, ha]

theorem pass_empty (h : k < excess) :
    Flat.passFrom p M cand 0#64 excess k s = (.stuck, s) := by
  apply pass_stuck h
  exact congrArg Prod.fst (pick_done (by decide))
end

section
variable {p : Flat.Planner} {sp : BitVec 32 → BitVec 8} {M current : Flat.Mapping}
    {dropped : Vector (BitVec 8) maxStackSize} {blocked excess size : Word} {u : Flat.ResolveU}
    {cand : Vector Word maxStackSize} {count : Word}

theorem resolve_failed_candidates
    (h : Flat.candidatesFrom M current size (blocked + 1) u.candidates 0 = none) :
    Flat.resolve p sp dropped M blocked excess current size u = (.assertionExit, sp, dropped) := by
  rw [Flat.resolve, h]

theorem resolve_zero_excess
    (h : Flat.candidatesFrom M current size (blocked + 1) u.candidates 0 = some (cand, count)) :
    Flat.resolve p sp dropped M blocked 0#64 current size u = (.dropped, sp, dropped) := by
  simp only [Flat.resolve, h]
  rw [pass_done (by decide)]

theorem resolve_no_candidates
    (h : Flat.candidatesFrom M current size (blocked + 1) u.candidates 0 = some (cand, 0#64))
    (he : 0#64 < excess) :
    Flat.resolve p sp dropped M blocked excess current size u = (.stuck, sp, dropped) := by
  simp only [Flat.resolve, h]
  exact congrArg (fun q : Flat.ResolutionOutcome × Flat.RState => (q.1, q.2.spills, q.2.dropped))
    (pass_empty (k := 0) he)
end

def code : Flat.ResolutionOutcome → Option (BitVec 8)
  | .dropped => some 0
  | .stuck => some 1
  | .assertionExit => none

theorem code_injective : Function.Injective code := by
  intro a b h
  cases a with
  | returned status =>
    cases status <;> cases b with
    | returned status => cases status <;> simp_all [code]
    | assertionExit => simp_all [code]
  | assertionExit =>
    cases b with
    | returned status => cases status <;> simp_all [code]
    | assertionExit => rfl

end FlatShuffler.Unit.ResolveU
