module

public import PlanBridge.ForIn
import all PlanBridge.ForIn
public import PlanBridge.List
import all PlanBridge.List
public import Shuffler.BuildMapping.Defs
import all Shuffler.BuildMapping.Defs

@[expose] public section

/-!
The flat `Mapping` arrays and the PR31 `Mapping`, and the members of the flat `Builder` and the
PR31 `MappingBuilder`.

`MapR M P`: the arrays `M` hold the PR31 mapping `P` at each source position and target offset.
`BR`: the flat builder and mapping `M` and the PR31 builder have the same dropped bytes, the same
mapping, and the same `sawWildcardCopy`.
-/

namespace PlanBridge

open Shuffler Shuffler.BuildMapping BbuBridge
open Bbu.Flat (get put optOf NONE ofNat_lt_iff ofNat_succ)

/-! ## Stacks -/

-- The PR31 stack of the first `m` slots of `v`.
def srcOf (v : Vector Bbu.StackSlot Bbu.MAX_N) (m : Bbu.Word) : Stack :=
  (v.toList.take m.toNat).map decode

theorem srcOf_length {v : Vector Bbu.StackSlot Bbu.MAX_N} {m : Bbu.Word} (hm : m.toNat ≤ Bbu.MAX_N) :
    (srcOf v m).length = m.toNat := by
  simp [srcOf]; omega

theorem srcOf_get {v : Vector Bbu.StackSlot Bbu.MAX_N} {m : Bbu.Word} {i : Nat}
    (h : i < (srcOf v m).length) : (srcOf v m)[i] = decode (get v (.ofNat 64 i)) := by
  simp only [srcOf, List.length_map, List.length_take, Vector.length_toList] at h
  simp only [srcOf, List.getElem_map, List.getElem_take, Vector.getElem_toList]
  rw [Bbu.Flat.get_ofNat v (by omega)]

-- The PR31 dropped bytes of the first `m` bytes of `d`.
def drops (d : Vector (BitVec 8) Bbu.MAX_N) (m : Bbu.Word) : List Byte :=
  (d.toList.take m.toNat).map BitVec.toFin

theorem drops_length {d : Vector (BitVec 8) Bbu.MAX_N} {m : Bbu.Word} (hm : m.toNat ≤ Bbu.MAX_N) :
    (drops d m).length = m.toNat := by
  simp [drops]; omega

theorem drops_get_eq_zero {d : Vector (BitVec 8) Bbu.MAX_N} {m : Bbu.Word} {i : Nat}
    (h : i < (drops d m).length) : (drops d m)[i] = 0 ↔ get d (.ofNat 64 i) = 0 := by
  simp only [drops, List.length_map, List.length_take, Vector.length_toList] at h
  simp only [drops, List.getElem_map, List.getElem_take, Vector.getElem_toList]
  rw [Bbu.Flat.get_ofNat d (by omega)]
  constructor
  · intro h'; apply BitVec.eq_of_toFin_eq; exact h'
  · intro h'; rw [h']; rfl

/-! ## Mappings -/

-- The arrays `M` hold the PR31 mapping `P`.
structure MapR (M : Bbu.Flat.Mapping) {s t : Nat} (P : Mapping s t) : Prop where
  dest : ∀ i : Fin s, optOf (get M.dest (.ofNat 64 i.val)) = (P i).map Fin.val
  pos : ∀ j : Fin t, optOf (get M.pos (.ofNat 64 j.val)) = (P.symm j).map Fin.val

theorem bind_apply {s t : Nat} (P : Mapping s t) (p : Fin s) (d : Fin t) (hp hd) (i : Fin s) :
    (P.bind p d hp hd) i = Function.update P p (some d) i := rfl

theorem bind_symm {s t : Nat} (P : Mapping s t) (p : Fin s) (d : Fin t) (hp hd) (j : Fin t) :
    (P.bind p d hp hd).symm j = Function.update P.symm d (some p) j := rfl

theorem optOf_ofNat {i : Nat} (h : i < Bbu.MAX_N) : optOf (.ofNat 64 i) = some i := by
  rw [Bbu.Flat.optOf_some (Bbu.Flat.ne_none (by rw [Bbu.Flat.toNat_ofNat_lt h]; exact h)),
    Bbu.Flat.toNat_ofNat_lt h]

-- `get` of a `put` at an offset below `MAX_N`.
theorem get_put {α : Type} [Inhabited α] (v : Vector α Bbu.MAX_N) {p i : Nat} (hp : p < Bbu.MAX_N)
    (hi : i < Bbu.MAX_N) (x : α) :
    get (put v (.ofNat 64 p) x) (.ofNat 64 i) = if i = p then x else get v (.ofNat 64 i) := by
  rw [Bbu.Flat.get_ofNat _ hi, Bbu.Flat.get_ofNat _ hi, Bbu.Flat.getElem_put _ hp _ hi]
  by_cases h : i = p
  · subst h; simp
  · simp [h, Ne.symm h]

theorem mapR_bind {M : Bbu.Flat.Mapping} {s t : Nat} {P : Mapping s t} (hs : s ≤ Bbu.MAX_N)
    (ht : t ≤ Bbu.MAX_N) (hR : MapR M P) (p : Fin s) (d : Fin t) (hp hd) :
    MapR (M.bind (.ofNat 64 p.val) (.ofNat 64 d.val)) (P.bind p d hp hd) := by
  constructor
  · intro i
    simp only [Bbu.Flat.Mapping.bind, bind_apply, Function.update_apply]
    rw [get_put _ (by omega) (by omega)]
    by_cases h : i = p
    · subst h; simp [optOf_ofNat (show d.val < Bbu.MAX_N by omega)]
    · simp [Fin.val_ne_of_ne h, h, hR.dest i]
  · intro j
    simp only [Bbu.Flat.Mapping.bind, bind_symm, Function.update_apply]
    rw [get_put _ (by omega) (by omega)]
    by_cases h : j = d
    · subst h; simp [optOf_ofNat (show p.val < Bbu.MAX_N by omega)]
    · simp [Fin.val_ne_of_ne h, h, hR.pos j]

theorem mapR_init (u : Bbu.Flat.Mapping) {m n : Bbu.Word} (hm : m.toNat ≤ Bbu.MAX_N)
    (hn : n.toNat ≤ Bbu.MAX_N) {s t : Nat} (hs : s = m.toNat) (ht : t = n.toNat) :
    MapR (u.init m n) (⊥ : Mapping s t) := by
  subst hs ht
  constructor
  · intro i
    simp only [Bbu.Flat.Mapping.init]
    rw [Bbu.Flat.get_ofNat _ (by omega), Bbu.Flat.fill_get _ _ hm (by omega)]
    simp [i.isLt, Bbu.Flat.optOf_none]
  · intro j
    simp only [Bbu.Flat.Mapping.init]
    rw [Bbu.Flat.get_ofNat _ (by omega), Bbu.Flat.fill_get _ _ hn (by omega)]
    simp [j.isLt, Bbu.Flat.optOf_none]

theorem mapR_abs {M : Bbu.Flat.Mapping} {m n : Bbu.Word} (hm : m.toNat ≤ Bbu.MAX_N)
    (hn : n.toNat ≤ Bbu.MAX_N) {s t : Nat} (hs : s = m.toNat) (ht : t = n.toNat) {P : Mapping s t}
    (hR : MapR M P) : Bbu.Flat.absMapping M.dest M.pos m n = absP P := by
  subst hs ht
  simp only [Bbu.Flat.absMapping, absP, Bbu.Map.Mapping.mk.injEq]
  constructor
  · apply List.ext_getElem (by simp; omega)
    intro i h1 h2
    simp only [List.length_map, List.length_finRange] at h2
    have := hR.dest ⟨i, h2⟩
    rw [Bbu.Flat.get_ofNat _ (by omega)] at this
    simpa [List.getElem_map, List.getElem_take] using this
  · apply List.ext_getElem (by simp; omega)
    intro i h1 h2
    simp only [List.length_map, List.length_finRange] at h2
    have := hR.pos ⟨i, h2⟩
    rw [Bbu.Flat.get_ofNat _ (by omega)] at this
    simpa [List.getElem_map, List.getElem_take] using this

/-! ## Builders -/

-- The sizes of the flat builder are at most `MAX_N`, and its slots are canonical.
structure BOk (b : Bbu.Flat.Builder) : Prop where
  hm : b.m.toNat ≤ Bbu.MAX_N
  hn : b.n.toNat ≤ Bbu.MAX_N
  cs : ∀ i < b.m.toNat, Canon (get b.source (.ofNat 64 i))
  ct : ∀ j < b.n.toNat, Canon (get b.target (.ofNat 64 j))

-- The PR31 source and target of a flat builder.
abbrev bsrc (b : Bbu.Flat.Builder) : Stack := srcOf b.source b.m
abbrev btgt (b : Bbu.Flat.Builder) : Stack := srcOf b.target b.n

-- The flat builder `b` with the mapping `M` and `saw`, and the PR31 builder `mb`.
structure BR (b : Bbu.Flat.Builder) (M : Bbu.Flat.Mapping) (saw : Bool)
    (mb : MappingBuilder (bsrc b) (btgt b)) : Prop where
  dropped : mb.dropped = drops b.dropped b.m
  map : MapR M mb.mapping
  saw : mb.sawWildcardCopy = saw

variable {b : Bbu.Flat.Builder} {M : Bbu.Flat.Mapping} {saw : Bool}
  {mb : MappingBuilder (bsrc b) (btgt b)}

theorem dest_eq_none (h : MapR M mb.mapping) (i : Fin (bsrc b).length) :
    mb.mapping i = none ↔ get M.dest (.ofNat 64 i.val) = NONE := by
  rw [← Bbu.Flat.optOf_eq_none, h.dest i, Option.map_eq_none_iff]

theorem pos_eq_none (h : MapR M mb.mapping) (j : Fin (btgt b).length) :
    mb.mapping.symm j = none ↔ get M.pos (.ofNat 64 j.val) = NONE := by
  rw [← Bbu.Flat.optOf_eq_none, h.pos j, Option.map_eq_none_iff]

theorem mappable_eq (ok : BOk b) (h : BR b M saw mb) {k : Nat} (i : Fin k)
    (hk : k ≤ (bsrc b).length) :
    mb.mappable i hk = .ok (Bbu.Flat.mappable b M (.ofNat 64 i.val)) := by
  have hs : (bsrc b).length = b.m.toNat := srcOf_length ok.hm
  have hl : (Fin.castLE hk i).val < mb.dropped.length := by
    rw [h.dropped, drops_length ok.hm]; simp; omega
  simp only [MappingBuilder.mappable, requires, hl, dite_true]
  change Except.ok _ = _
  congr 1
  have h0 := drops_get_eq_zero (d := b.dropped) (m := b.m) (i := i.val)
    (by rw [drops_length ok.hm]; omega)
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bbu.Flat.mappable, Bool.and_eq_true, beq_iff_eq]
  rw [dest_eq_none h.map, ← h0]
  simp only [h.dropped, Fin.val_castLE]

theorem map_corr (ok : BOk b) (h : BR b M saw mb) {k l : Nat} (p : Fin k) (t : Fin l)
    (hs : k ≤ (bsrc b).length) (ht : l ≤ (btgt b).length) :
    LoopCorr (fun M' mb' => BR b M' saw mb')
      (Bbu.Flat.mbMap b M (.ofNat 64 p.val) (.ofNat 64 t.val)) (mb.map p t hs ht) := by
  have hsl : (bsrc b).length = b.m.toNat := srcOf_length ok.hm
  have htl : (btgt b).length = b.n.toNat := srcOf_length ok.hn
  simp only [MappingBuilder.map, mappable_eq ok h, Fin.val_castLE, Bind.bind, Except.bind,
    requires, Bbu.Flat.mbMap]
  by_cases hmp : Bbu.Flat.mappable b M (.ofNat 64 p.val) = true
  · have hd : get M.dest (.ofNat 64 p.val) = NONE := by
      simp only [Bbu.Flat.mappable, Bool.and_eq_true, beq_iff_eq] at hmp; exact hmp.2
    have hp : mb.mapping (Fin.castLE hs p) = none := by
      rw [dest_eq_none h.map]; exact hd
    by_cases hq : get M.pos (.ofNat 64 t.val) = NONE
    · have hq' : mb.mapping.symm (Fin.castLE ht t) = none := by
        rw [pos_eq_none h.map]; exact hq
      simp only [hmp, hp, hq', hq, hd, dite_true, Bool.not_true, Bool.false_eq_true, ite_false,
        ne_eq, not_true_eq_false, pure, Except.pure, LoopCorr]
      exact ⟨h.dropped, mapR_bind (by rw [srcOf_length ok.hm]; exact ok.hm) (by rw [srcOf_length ok.hn]; exact ok.hn) h.map (Fin.castLE hs p) (Fin.castLE ht t) hp hq', h.saw⟩
    · have hq' : ¬ mb.mapping.symm (Fin.castLE ht t) = none := by
        rw [pos_eq_none h.map]; exact hq
      simp [hmp, hp, hq', hq, hd, LoopCorr, throw, throwThe, MonadExceptOf.throw, pure,
        Except.pure]
  · simp [hmp, LoopCorr, throw, throwThe, MonadExceptOf.throw]

-- A PR31 map that yields its builder.
theorem step_of_loop {σ β ε : Type} {R : σ → β → Prop} {r : Bbu.Flat.Status × σ} {e : Except ε β}
    (h : LoopCorr R r e) : StepCorr R r (e >>= fun x => pure (ForInStep.yield x)) := by
  obtain ⟨st, s⟩ := r
  cases st <;> cases e <;> simp_all [LoopCorr, StepCorr, Bind.bind, Except.bind, pure, Except.pure]

-- The slots of a flat builder and of the PR31 stacks.
theorem slot_eq (ok : BOk b) {i j : Nat} (hi : i < (bsrc b).length) (hj : j < (btgt b).length) :
    (bsrc b)[i] = (btgt b)[j] ↔ get b.source (.ofNat 64 i) = get b.target (.ofNat 64 j) := by
  have hsl : (bsrc b).length = b.m.toNat := srcOf_length ok.hm
  have htl : (btgt b).length = b.n.toNat := srcOf_length ok.hn
  rw [srcOf_get, srcOf_get, decode_eq_iff (ok.cs i (by omega)) (ok.ct j (by omega))]

theorem src_eq_src (ok : BOk b) {i j : Nat} (hi : i < (bsrc b).length) (hj : j < (bsrc b).length) :
    (bsrc b)[i] = (bsrc b)[j] ↔ get b.source (.ofNat 64 i) = get b.source (.ofNat 64 j) := by
  have hsl : (bsrc b).length = b.m.toNat := srcOf_length ok.hm
  rw [srcOf_get, srcOf_get, decode_eq_iff (ok.cs i (by omega)) (ok.cs j (by omega))]

theorem tgt_junk (_ok : BOk b) {j : Nat} (hj : j < (btgt b).length) :
    decide ((btgt b)[j].is_junk) = Bbu.Flat.isWildcardTarget b (.ofNat 64 j) := by
  rw [srcOf_get, Bbu.Flat.isWildcardTarget, Bool.eq_iff_iff, decide_eq_true_iff, isJunk_iff]

theorem tgt_frl (ok : BOk b) {j : Nat} (hj : j < (btgt b).length) :
    (btgt b)[j].isFunctionReturnLabel ↔
      (get b.target (.ofNat 64 j)).kind = Bbu.FunctionReturnLabel := by
  have htl : (btgt b).length = b.n.toNat := srcOf_length ok.hn
  rw [srcOf_get, isFRL_iff (ok.ct j (by omega))]

theorem inWild_eq (ok : BOk b) (i : Fin (bsrc b).length) :
    mb.inWildcardSlot i = Bbu.Flat.inWildcardSlot b (.ofNat 64 i.val) := by
  have hsl : (bsrc b).length = b.m.toNat := srcOf_length ok.hm
  have htl : (btgt b).length = b.n.toNat := srcOf_length ok.hn
  have hm := ok.hm
  unfold MappingBuilder.inWildcardSlot Bbu.Flat.inWildcardSlot
  by_cases hi : i.val < (btgt b).length
  · rw [dite_eq_left hi, decide_eq_true ((ofNat_lt_iff (by omega)).mpr (by omega)), Bool.true_and]
    exact tgt_junk ok hi
  · rw [dite_eq_right hi, decide_eq_false (mt (ofNat_lt_iff (by omega)).mp (by omega)), Bool.false_and]

theorem absDiff_eq {a c : Nat} (ha : a < Bbu.MAX_N) (hc : c < Bbu.MAX_N) :
    (Bbu.Flat.absDiff (.ofNat 64 a) (.ofNat 64 c)).toNat = if a > c then a - c else c - a := by
  have ha' := Bbu.Flat.toNat_ofNat_lt ha
  have hc' := Bbu.Flat.toNat_ofNat_lt hc
  generalize BitVec.ofNat 64 a = x at ha'
  generalize BitVec.ofNat 64 c = y at hc'
  subst ha' hc'
  unfold Bbu.Flat.absDiff
  by_cases h : x > y
  · rw [ite_eq_left h, ite_eq_left (by bv_omega)]; bv_omega
  · rw [ite_eq_right h, ite_eq_right (by bv_omega)]; bv_omega

theorem mb_absDiff (ok : BOk b) (i : Fin (bsrc b).length) (t : Fin (btgt b).length) :
    mb.absDiff i t = (Bbu.Flat.absDiff (.ofNat 64 i.val) (.ofNat 64 t.val)).toNat := by
  have hsl : (bsrc b).length = b.m.toNat := srcOf_length ok.hm
  have htl : (btgt b).length = b.n.toNat := srcOf_length ok.hn
  have := ok.hm; have := ok.hn
  rw [absDiff_eq (by omega) (by omega)]; rfl

theorem optOf_eq_some {w : Bbu.Word} {v : Nat} (h : optOf w = some v) : w = .ofNat 64 v := by
  unfold optOf at h
  split at h
  · cases h
  · cases h; simp

-- An offset `best` and a PR31 `Option (Fin s)`.
def OptR {s : Nat} (w : Bbu.Word) (c : Option (Fin s)) : Prop := optOf w = c.map Fin.val

theorem closest_corr (ok : BOk b) (h : BR b M saw mb) (t : Fin (btgt b).length)
    (loc : CopyLocation) :
    ∃ c, mb.closestCopy t loc = .ok c ∧
      OptR (Bbu.Flat.closestCopy b M (.ofNat 64 t.val) (decide (loc = .InWildcardSlots))) c := by
  have hsl : (bsrc b).length = b.m.toNat := srcOf_length ok.hm
  have htl : (btgt b).length = b.n.toNat := srcOf_length ok.hn
  have hm := ok.hm; have hn := ok.hn
  unfold MappingBuilder.closestCopy Bbu.Flat.closestCopy
  dsimp only
  simp only [bind_pure]
  refine fold_corr (n := (bsrc b).length) (by omega)
    (fun i best => Bbu.Flat.closestFrom b M (.ofNat 64 t.val) (decide (loc = .InWildcardSlots)) i best)
    (fun i best =>
      if get b.source i = get b.target (.ofNat 64 t.val) && Bbu.Flat.mappable b M i &&
          Bbu.Flat.inWildcardSlot b i == decide (loc = .InWildcardSlots) then
        if best = NONE || Bbu.Flat.absDiff i (.ofNat 64 t.val) ≤
            Bbu.Flat.absDiff best (.ofNat 64 t.val) then i else best
      else best) ?_ OptR _ ?_ NONE none (by simp [OptR, Bbu.Flat.optOf_none])
  · intro k s hk
    rw [Bbu.Flat.closestFrom]
    by_cases h1 : k < (bsrc b).length
    · rw [dite_eq_left ((ofNat_lt_iff (by omega)).mpr (by omega)), ite_eq_left h1, ofNat_succ]
    · rw [dite_eq_right (mt (ofNat_lt_iff (by omega)).mp (by omega)), ite_eq_right h1]
  · intro k hk s c hR
    simp only [mappable_eq ok h, Bind.bind, Except.bind]
    have hk' : k < Bbu.MAX_N := by omega
    have e1 : ((bsrc b)[(⟨k, hk⟩ : Fin _)] = (btgt b)[t] ∧
        Bbu.Flat.mappable b M (.ofNat 64 k) = true ∧
        mb.inWildcardSlot ⟨k, hk⟩ = decide (loc = .InWildcardSlots)) ↔
        ((decide (get b.source (.ofNat 64 k) = get b.target (.ofNat 64 t.val)) &&
          Bbu.Flat.mappable b M (.ofNat 64 k) &&
          Bbu.Flat.inWildcardSlot b (.ofNat 64 k) == decide (loc = .InWildcardSlots)) = true) := by
      rw [inWild_eq ok ⟨k, hk⟩, Fin.getElem_fin, Fin.getElem_fin, slot_eq ok]
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc]
    by_cases hc : (bsrc b)[(⟨k, hk⟩ : Fin _)] = (btgt b)[t] ∧
        Bbu.Flat.mappable b M (.ofNat 64 k) = true ∧
        mb.inWildcardSlot ⟨k, hk⟩ = decide (loc = .InWildcardSlots)
    · rw [ite_eq_left hc, ite_eq_left (e1.mp hc)]
      cases c with
      | none =>
        have hs : s = NONE := Bbu.Flat.optOf_eq_none.mp hR
        subst hs
        exact ⟨some ⟨k, hk⟩, rfl, by simp [OptR, optOf_ofNat hk']⟩
      | some bb =>
        have hs : s = .ofNat 64 bb.val := optOf_eq_some hR
        subst hs
        have hne : (BitVec.ofNat 64 bb.val) ≠ NONE :=
          Bbu.Flat.ne_none (by rw [Bbu.Flat.toNat_ofNat_lt (by omega)]; omega)
        have e2 : (¬(some bb).isSome = true ∨
            Option.any (fun b_1 => decide (mb.absDiff ⟨k, hk⟩ t ≤ mb.absDiff b_1 t)) (some bb) = true) ↔
            ((decide (BitVec.ofNat 64 bb.val = NONE) ||
              decide (Bbu.Flat.absDiff (.ofNat 64 k) (.ofNat 64 t.val) ≤
                Bbu.Flat.absDiff (.ofNat 64 bb.val) (.ofNat 64 t.val))) = true) := by
          simp only [Option.isSome_some, not_true_eq_false, false_or, Option.any_some,
            decide_eq_true_eq, hne, decide_false, Bool.false_or, BitVec.le_def, mb_absDiff ok]
        by_cases hd : ¬(some bb).isSome = true ∨
            Option.any (fun b_1 => decide (mb.absDiff ⟨k, hk⟩ t ≤ mb.absDiff b_1 t)) (some bb) = true
        · rw [ite_eq_left hd, ite_eq_left (e2.mp hd)]
          exact ⟨some ⟨k, hk⟩, rfl, by simp [OptR, optOf_ofNat hk']⟩
        · rw [ite_eq_right hd, ite_eq_right (mt e2.mpr hd)]
          exact ⟨some bb, rfl, hR⟩
    · rw [ite_eq_right hc, ite_eq_right (mt e1.mpr hc)]
      exact ⟨c, rfl, hR⟩


/-! ## `buildMapping` -/

-- The flat `buildMapping` as a chain of phases.
def bindS {σ X : Type} (r : Bbu.Flat.Status × σ) (K : σ → Option X) : Option X :=
  if r.1 ≠ .done then none else K r.2

-- A flat result and a PR31 result: both are related values, or both fail.
def OptCorr {X Y ε : Type} (Q : X → Y → Prop) : Option X → Except ε Y → Prop
  | some x, .ok y => Q x y
  | none, .error _ => True
  | _, _ => False

theorem chain {σ β X Y ε : Type} {R : σ → β → Prop} {Q : X → Y → Prop} {r : Bbu.Flat.Status × σ}
    {K : σ → Option X} {e : Except ε β} {k : β → Except ε Y} (h : LoopCorr R r e)
    (hk : ∀ s c, R s c → OptCorr Q (K s) (k c)) : OptCorr Q (bindS r K) (e >>= k) := by
  obtain ⟨st, s⟩ := r
  cases st <;> cases e <;> simp_all [LoopCorr, bindS, OptCorr, Bind.bind, Except.bind]

theorem buildMapping_eq :
    Bbu.Flat.buildMapping b M =
      bindS (Bbu.Flat.mapInPlace b M) fun M1 =>
      bindS (Bbu.Flat.mapClosestCopies b M1) fun M2 =>
      bindS (Bbu.Flat.mapWildcardSlotCopies b M2 false) fun w =>
      bindS (Bbu.Flat.keepWildcardSlots b w.1) fun M4 =>
      bindS (Bbu.Flat.absorbSurplus b M4) fun M5 => some (M5, w.2) := rfl

theorem commonSize_toNat (ok : BOk b) :
    (Bbu.Flat.commonSize b).toNat = min (bsrc b).length (btgt b).length := by
  have hsl : (bsrc b).length = b.m.toNat := srcOf_length ok.hm
  have htl : (btgt b).length = b.n.toNat := srcOf_length ok.hn
  unfold Bbu.Flat.commonSize
  split <;> rename_i h <;> rw [BitVec.lt_def] at h <;> omega

-- The result of PR31 `buildMapping` and the flat mapping and `sawWildcardCopy`.
def ResR (b : Bbu.Flat.Builder) (x : Bbu.Flat.Mapping × Bool)
    (r : BuildMappingResult (bsrc b) (btgt b)) : Prop :=
  MapR x.1 r.mapping ∧ r.sawWildcardCopy = x.2

theorem ok_bind {α β ε : Type} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl

theorem hsa_eq (h : MapR M mb.mapping) {k : Nat} (j : Fin k) (hk : k ≤ (btgt b).length) :
    mb.hasSourceAssigned j hk = Bbu.Flat.hasSourceAssigned M (.ofNat 64 j.val) := by
  unfold MappingBuilder.hasSourceAssigned Bbu.Flat.hasSourceAssigned
  rw [Bool.eq_iff_iff, Option.isSome_iff_ne_none, bne_iff_ne, ne_eq, ne_eq,
    pos_eq_none h (Fin.castLE hk j), Fin.val_castLE]

theorem iwt_eq (ok : BOk b) {k : Nat} (j : Fin k) (hk : k ≤ (btgt b).length) :
    mb.isWildcardTarget j hk = Bbu.Flat.isWildcardTarget b (.ofNat 64 j.val) :=
  tgt_junk ok (by omega)

-- A PR31 copy and a flat offset: both are none, or both are the same offset.
theorem optR_cases {s : Nat} (hs : s ≤ Bbu.MAX_N) {w : Bbu.Word} {c : Option (Fin s)}
    (h : OptR w c) : (c = none ∧ w = NONE) ∨ ∃ p : Fin s, c = some p ∧ w = .ofNat 64 p.val ∧ w ≠ NONE := by
  cases c with
  | none => exact .inl ⟨rfl, Bbu.Flat.optOf_eq_none.mp h⟩
  | some p =>
    have hw := optOf_eq_some h
    refine .inr ⟨p, rfl, hw, ?_⟩
    rw [hw]
    exact Bbu.Flat.ne_none (by rw [Bbu.Flat.toNat_ofNat_lt (by omega)]; omega)

theorem loopCorr_map {σ σ' β ε : Type} {R : σ → β → Prop} {R' : σ' → β → Prop}
    {r : Bbu.Flat.Status × σ} {e : Except ε β} (g : σ → σ') (h : LoopCorr R r e)
    (hg : ∀ s c, R s c → R' (g s) c) : LoopCorr R' (r.1, g r.2) e := by
  obtain ⟨st, s⟩ := r
  cases st <;> cases e <;> simp_all [LoopCorr]

-- A PR31 step that first runs a loop without a status.
theorem step_of_fold {σ β γ ε : Type} {R : σ → β → Prop} {r : Bbu.Flat.Status × σ}
    {e : Except ε γ} {k : γ → Except ε (ForInStep β)} (P : γ → Prop)
    (he : ∃ c, e = .ok c ∧ P c) (hk : ∀ c, P c → StepCorr R r (k c)) : StepCorr R r (e >>= k) := by
  obtain ⟨c, rfl, hc⟩ := he
  exact hk c hc

theorem buildMapping_corr (ok : BOk b) (h0 : MapR M (⊥ : Mapping (bsrc b).length (btgt b).length)) :
    OptCorr (ResR b) (Bbu.Flat.buildMapping b M)
      (buildMapping (bsrc b) (btgt b) (drops b.dropped b.m)
        (if b.take then .Take else .Leave)) := by
  have hsl : (bsrc b).length = b.m.toNat := srcOf_length ok.hm
  have htl : (btgt b).length = b.n.toNat := srcOf_length ok.hn
  have hm := ok.hm; have hn := ok.hn
  have hc := commonSize_toNat ok
  have hsm : (bsrc b).length ≤ Bbu.MAX_N := by omega
  rw [buildMapping_eq]
  unfold buildMapping
  rw [requires_of_true _ (by rw [drops_length ok.hm]; omega), ok_bind]
  dsimp only
  -- `mapInPlace`
  refine chain (R := fun M' mb' => BR b M' false mb') ?_ ?_
  · unfold Bbu.Flat.mapInPlace
    refine loop_corr (by omega) (fun j M => Bbu.Flat.inPlaceFrom b M j)
      (fun j M => if get b.source j = get b.target j && Bbu.Flat.mappable b M j then
        Bbu.Flat.mbMap b M j j else (.done, M)) ?_ _ _ ?_ M _ ⟨rfl, h0, rfl⟩
    · intro k s hk
      rw [Bbu.Flat.inPlaceFrom]
      by_cases h1 : k < min (bsrc b).length (btgt b).length
      · rw [dite_eq_left ((ofNat_lt_iff (by omega)).mpr (by omega)), ite_eq_left h1, ofNat_succ]
        split <;> simp_all
      · rw [dite_eq_right (mt (ofNat_lt_iff (by omega)).mp (by omega)), ite_eq_right h1]
    · intro k hk s c hR
      rw [mappable_eq ok hR, ok_bind]
      have e1 : ((bsrc b)[(⟨k, by omega⟩ : Fin _)] = (btgt b)[(⟨k, by omega⟩ : Fin _)] ∧
          Bbu.Flat.mappable b s (.ofNat 64 k) = true) ↔
          ((decide (get b.source (.ofNat 64 k) = get b.target (.ofNat 64 k)) &&
            Bbu.Flat.mappable b s (.ofNat 64 k)) = true) := by
        rw [Fin.getElem_fin, Fin.getElem_fin, slot_eq ok]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
      by_cases hcd : (bsrc b)[(⟨k, by omega⟩ : Fin _)] = (btgt b)[(⟨k, by omega⟩ : Fin _)] ∧
          Bbu.Flat.mappable b s (.ofNat 64 k) = true
      · rw [ite_eq_left hcd, ite_eq_left (e1.mp hcd)]
        exact step_of_loop (map_corr ok hR ⟨k, hk⟩ ⟨k, hk⟩ _ _)
      · rw [ite_eq_right hcd, ite_eq_right (mt e1.mpr hcd)]
        exact hR
  intro M1 mb1 h1
  -- `mapClosestCopies`
  refine chain (R := fun M' mb' => BR b M' false mb') ?_ ?_
  · unfold Bbu.Flat.mapClosestCopies
    refine loop_corr (by omega) (fun j M => Bbu.Flat.closestCopiesFrom b M j)
      (fun j M => if !Bbu.Flat.hasSourceAssigned M j && !Bbu.Flat.isWildcardTarget b j &&
          Bbu.Flat.closestCopy b M j false ≠ NONE then
        Bbu.Flat.mbMap b M (Bbu.Flat.closestCopy b M j false) j else (.done, M)) ?_ _ _ ?_ M1 _ h1
    · intro k s hk
      rw [Bbu.Flat.closestCopiesFrom]
      by_cases h1 : k < (btgt b).length
      · rw [dite_eq_left ((ofNat_lt_iff (by omega)).mpr (by omega)), ite_eq_left h1, ofNat_succ]
        split <;> simp_all
      · rw [dite_eq_right (mt (ofNat_lt_iff (by omega)).mp (by omega)), ite_eq_right h1]
    · intro k hk s c hR
      rw [hsa_eq hR.map, iwt_eq ok]
      obtain ⟨cc, hcc, hcr⟩ := closest_corr ok hR ⟨k, hk⟩ .OutsideWildcardSlots
      simp only [decide_false, reduceCtorEq] at hcr
      rw [hcc, ok_bind]
      rcases optR_cases hsm hcr with ⟨rfl, hw⟩ | ⟨p, rfl, hw, hne⟩
      · rw [ite_eq_right (by simp [hw])]
        split <;> exact hR
      · rw [hw] at hne ⊢
        by_cases hq : ¬Bbu.Flat.hasSourceAssigned s (.ofNat 64 k) = true ∧
            ¬Bbu.Flat.isWildcardTarget b (.ofNat 64 k) = true
        · rw [ite_eq_left hq, ite_eq_left (by simp_all)]
          exact step_of_loop (map_corr ok hR p ⟨k, hk⟩ _ _)
        · rw [ite_eq_right hq, ite_eq_right (by simp_all)]
          exact hR
  intro M2 mb2 h2
  -- `mapWildcardSlotCopies`
  refine chain (R := fun (x : Bbu.Flat.Mapping × Bool) mb' => BR b x.1 x.2 mb') ?_ ?_
  · unfold Bbu.Flat.mapWildcardSlotCopies
    refine loop_corr (by omega) (fun j x => Bbu.Flat.wildcardFrom b x.1 x.2 j)
      (fun j x => if !Bbu.Flat.hasSourceAssigned x.1 j && !Bbu.Flat.isWildcardTarget b j &&
          Bbu.Flat.closestCopy b x.1 j true ≠ NONE then
        (if (get b.target j).kind = Bbu.FunctionReturnLabel then
          ((Bbu.Flat.mbMap b x.1 (Bbu.Flat.closestCopy b x.1 j true) j).1,
            (Bbu.Flat.mbMap b x.1 (Bbu.Flat.closestCopy b x.1 j true) j).2, x.2)
        else if b.take then
          ((Bbu.Flat.mbMap b x.1 (Bbu.Flat.closestCopy b x.1 j true) j).1,
            (Bbu.Flat.mbMap b x.1 (Bbu.Flat.closestCopy b x.1 j true) j).2, true)
        else (.done, x.1, true))
        else (.done, x)) ?_ _ _ ?_ (M2, false) _ h2
    · intro k s hk
      rw [Bbu.Flat.wildcardFrom]
      by_cases h1 : k < (btgt b).length
      · rw [dite_eq_left ((ofNat_lt_iff (by omega)).mpr (by omega)), ite_eq_left h1, ofNat_succ]
        split <;> (try split) <;> (try split) <;> simp_all
      · rw [dite_eq_right (mt (ofNat_lt_iff (by omega)).mp (by omega)), ite_eq_right h1]
    · intro k hk s c hR
      rw [hsa_eq hR.map, iwt_eq ok]
      obtain ⟨cc, hcc, hcr⟩ := closest_corr ok hR ⟨k, hk⟩ .InWildcardSlots
      simp only [decide_true] at hcr
      rw [hcc, ok_bind]
      rcases optR_cases hsm hcr with ⟨rfl, hw⟩ | ⟨p, rfl, hw, hne⟩
      · rw [ite_eq_right (by simp [hw])]
        split <;> exact hR
      · rw [hw] at hne ⊢
        by_cases hq : ¬Bbu.Flat.hasSourceAssigned s.1 (.ofNat 64 k) = true ∧
            ¬Bbu.Flat.isWildcardTarget b (.ofNat 64 k) = true
        · rw [ite_eq_left hq, ite_eq_left (by simp_all)]
          dsimp only
          by_cases hf : (btgt b)[(⟨k, hk⟩ : Fin _)].isFunctionReturnLabel
          · rw [ite_eq_left hf, ite_eq_left ((tgt_frl ok hk).mp hf)]
            exact step_of_loop (loopCorr_map (fun M' => (M', s.2))
              (map_corr ok hR p ⟨k, hk⟩ _ _) fun _ _ h => h)
          · rw [ite_eq_right hf, ite_eq_right (mt (tgt_frl ok hk).mpr hf)]
            have hR' : BR b s.1 true { c with sawWildcardCopy := true } := ⟨hR.dropped, hR.map, rfl⟩
            cases ht : b.take
            · simp only [Bool.false_eq_true, ite_false, reduceCtorEq]
              exact hR'
            · simp only [ite_true]
              exact step_of_loop (loopCorr_map (fun M' => (M', true))
                (map_corr ok hR' p ⟨k, hk⟩ _ _) fun _ _ h => h)
        · rw [ite_eq_right hq, ite_eq_right (by simp_all)]
          exact hR
  intro w mb3 h3
  -- `keepWildcardSlots`
  refine chain (R := fun M' mb' => BR b M' w.2 mb') ?_ ?_
  · unfold Bbu.Flat.keepWildcardSlots
    refine loop_corr (by omega) (fun j M => Bbu.Flat.keepFrom b M j)
      (fun j M => if Bbu.Flat.isWildcardTarget b j && !Bbu.Flat.hasSourceAssigned M j &&
          Bbu.Flat.mappable b M j then
        Bbu.Flat.mbMap b M j j else (.done, M)) ?_ _ _ ?_ w.1 _ h3
    · intro k s hk
      rw [Bbu.Flat.keepFrom]
      by_cases h1 : k < min (bsrc b).length (btgt b).length
      · rw [dite_eq_left ((ofNat_lt_iff (by omega)).mpr (by omega)), ite_eq_left h1, ofNat_succ]
        split <;> simp_all
      · rw [dite_eq_right (mt (ofNat_lt_iff (by omega)).mp (by omega)), ite_eq_right h1]
    · intro k hk s c hR
      rw [mappable_eq ok hR, ok_bind, iwt_eq ok, hsa_eq hR.map]
      by_cases hq : Bbu.Flat.isWildcardTarget b (.ofNat 64 k) = true ∧
          ¬Bbu.Flat.hasSourceAssigned s (.ofNat 64 k) = true ∧
          Bbu.Flat.mappable b s (.ofNat 64 k) = true
      · rw [ite_eq_left hq, ite_eq_left (by simp_all)]
        exact step_of_loop (map_corr ok hR ⟨k, hk⟩ ⟨k, hk⟩ _ _)
      · rw [ite_eq_right hq, ite_eq_right (by simp_all)]
        exact hR
  intro M4 mb4 h4
  -- `absorbSurplus`
  refine chain (R := fun M' mb' => BR b M' w.2 mb') ?_ ?_
  · unfold Bbu.Flat.absorbSurplus
    refine loop_corr (by omega) (fun j M => Bbu.Flat.absorbFrom b M j)
      (fun j M => if Bbu.Flat.isWildcardTarget b j && !Bbu.Flat.hasSourceAssigned M j &&
          Bbu.Flat.absorbBest b M j 0 NONE ≠ NONE then
        Bbu.Flat.mbMap b M (Bbu.Flat.absorbBest b M j 0 NONE) j else (.done, M)) ?_ _ _ ?_ M4 _ h4
    · intro k s hk
      rw [Bbu.Flat.absorbFrom]
      by_cases h1 : k < (btgt b).length
      · rw [dite_eq_left ((ofNat_lt_iff (by omega)).mpr (by omega)), ite_eq_left h1, ofNat_succ]
        split <;> simp_all
      · rw [dite_eq_right (mt (ofNat_lt_iff (by omega)).mp (by omega)), ite_eq_right h1]
    · intro k hk s c hR
      rw [iwt_eq ok, hsa_eq hR.map]
      by_cases hq : Bbu.Flat.isWildcardTarget b (.ofNat 64 k) = true ∧
          ¬Bbu.Flat.hasSourceAssigned s (.ofNat 64 k) = true
      · rw [ite_eq_left hq]
        refine step_of_fold (OptR (Bbu.Flat.absorbBest b s (.ofNat 64 k) 0 NONE)) ?_ ?_
        · refine fold_corr (n := (bsrc b).length) (by omega)
            (fun i best => Bbu.Flat.absorbBest b s (.ofNat 64 k) i best)
            (fun i best => if Bbu.Flat.mappable b s i &&
                (best = NONE || Bbu.Flat.absDiff i (.ofNat 64 k) < Bbu.Flat.absDiff best (.ofNat 64 k))
              then i else best) ?_ OptR _ ?_ NONE none (by simp [OptR, Bbu.Flat.optOf_none])
          · intro i best hi
            rw [Bbu.Flat.absorbBest]
            by_cases h1 : i < (bsrc b).length
            · rw [dite_eq_left ((ofNat_lt_iff (by omega)).mpr (by omega)), ite_eq_left h1, ofNat_succ]
            · rw [dite_eq_right (mt (ofNat_lt_iff (by omega)).mp (by omega)), ite_eq_right h1]
          · intro i hi best cb hRb
            rw [mappable_eq ok hR, ok_bind]
            have hi' : i < Bbu.MAX_N := by omega
            cases cb with
            | none =>
              have hs : best = NONE := Bbu.Flat.optOf_eq_none.mp hRb
              subst hs
              by_cases hmp : Bbu.Flat.mappable b s (.ofNat 64 i) = true
              · rw [ite_eq_left (by simp [hmp]), ite_eq_left (by simp [hmp])]
                exact ⟨_, rfl, by simp [OptR, optOf_ofNat hi']⟩
              · rw [ite_eq_right (by simp [hmp]), ite_eq_right (by simp [hmp])]
                exact ⟨_, rfl, hRb⟩
            | some bb =>
              have hs : best = .ofNat 64 bb.val := optOf_eq_some hRb
              subst hs
              have hne : (BitVec.ofNat 64 bb.val) ≠ NONE :=
                Bbu.Flat.ne_none (by rw [Bbu.Flat.toNat_ofNat_lt (by omega)]; omega)
              have e2 : (Bbu.Flat.mappable b s (.ofNat 64 i) = true ∧ (¬(some bb).isSome = true ∨
                  Option.any (fun b_1 => decide (c.absDiff ⟨i, hi⟩ ⟨k, hk⟩ < c.absDiff b_1 ⟨k, hk⟩))
                    (some bb) = true)) ↔
                  ((Bbu.Flat.mappable b s (.ofNat 64 i) && (decide (BitVec.ofNat 64 bb.val = NONE) ||
                    decide (Bbu.Flat.absDiff (.ofNat 64 i) (.ofNat 64 k) <
                      Bbu.Flat.absDiff (.ofNat 64 bb.val) (.ofNat 64 k)))) = true) := by
                simp only [Option.isSome_some, not_true_eq_false, false_or, Option.any_some,
                  decide_eq_true_eq, hne, decide_false, Bool.false_or, Bool.and_eq_true,
                  BitVec.lt_def, mb_absDiff ok]
              by_cases hd : Bbu.Flat.mappable b s (.ofNat 64 i) = true ∧ (¬(some bb).isSome = true ∨
                  Option.any (fun b_1 => decide (c.absDiff ⟨i, hi⟩ ⟨k, hk⟩ < c.absDiff b_1 ⟨k, hk⟩))
                    (some bb) = true)
              · rw [ite_eq_left hd, ite_eq_left (e2.mp hd)]
                exact ⟨_, rfl, by simp [OptR, optOf_ofNat hi']⟩
              · rw [ite_eq_right hd, ite_eq_right (mt e2.mpr hd)]
                exact ⟨_, rfl, hRb⟩
        · intro cc hcr
          rcases optR_cases hsm hcr with ⟨rfl, hw⟩ | ⟨p, rfl, hw, hne⟩
          · rw [dite_eq_right (by simp), ite_eq_right (fun hh => by simp only [Bool.and_eq_true, decide_eq_true_eq] at hh; exact hh.2 hw)]
            exact hR
          · rw [dite_eq_left (by simp), ite_eq_left (by simp_all), hw]
            exact step_of_loop (map_corr ok hR p ⟨k, hk⟩ _ _)
      · rw [ite_eq_right hq, ite_eq_right (by simp_all)]
        exact hR
  intro M5 mb5 h5
  exact ⟨h5.map, h5.saw⟩
end PlanBridge
