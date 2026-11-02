module

public import ShufflerBridge.Emission.Defs
import all ShufflerBridge.Emission.Defs
public import FlatShuffler.MapModel
import all FlatShuffler.MapModel

@[expose] public section

/-!
The list model of the stack and mapping operations (`FlatShuffler/MapModel.lean`) is an instance of
the original: `FlatShuffler.Map.State.pop` is `State.pop`, `FlatShuffler.Map.Mapping.pop` and `push` are
`Mapping.pop` and `push`, and `FlatShuffler.Map.State.init` is the initial state of `Emission.run`.

`absP` reads the two lists of a list mapping from a `Mapping`: the target offset of each source
position, and the source position of each target offset.
-/

namespace ShufflerBridge.Emission

open Shuffler Shuffler.Emission

-- The list mapping of a mapping.
def absP {s t : Nat} (P : Mapping s t) : FlatShuffler.Map.Mapping :=
  ⟨(List.finRange s).map fun i => (P i).map Fin.val,
   (List.finRange t).map fun j => (P.symm j).map Fin.val⟩

theorem absP_cast {m n t : Nat} (P : Mapping m t) (h : m = n) : absP (h ▸ P) = absP P := by
  subst h; rfl

-- The position of `j` after a pop: none if the top is bound for `j`.
theorem pop_symm_val {s t : Nat} (P : Mapping (s + 1) t) (j : Fin t) :
    (P.pop.symm j).map Fin.val =
      if P (Fin.last s) = some j then none else (P.symm j).map Fin.val := by
  change ((P.symm j).bind fun i => if h : i.val < s then some ⟨i.val, h⟩ else none).map Fin.val = _
  cases hj : P.symm j with
  | none =>
    have : P (Fin.last s) ≠ some j := fun h' => by rw [P.eq_some_iff.mpr h'] at hj; cases hj
    simp [this]
  | some i =>
    have hi := P.eq_some_iff.mp hj
    by_cases hl : i = Fin.last s
    · subst hl; simp [hi]
    · have hlt : i.val < s := by
        have := i.isLt; have := Fin.val_ne_of_ne hl; simp only [Fin.val_last] at this; omega
      have : P (Fin.last s) ≠ some j := fun h' => hl (by
        rw [P.eq_some_iff.mpr h'] at hj; exact (Option.some.inj hj).symm)
      simp [hlt, this]

theorem absP_pop {s t : Nat} (P : Mapping (s + 1) t) : absP P.pop = (absP P).pop := by
  have hd : (absP P).dest = (absP P.pop).dest ++ [(P (Fin.last s)).map Fin.val] := by
    simp [absP, List.finRange_succ_last, Function.comp_def]
  have hp : (absP P.pop).pos =
      (List.finRange t).map fun j => if P (Fin.last s) = some j then none else (P.symm j).map Fin.val := by
    simp only [absP, pop_symm_val]
  unfold FlatShuffler.Map.Mapping.pop
  rw [hd, List.getLast?_concat, List.dropLast_concat]
  cases htop : P (Fin.last s) with
  | none =>
    simp only [htop, reduceCtorEq, ite_false] at hp
    have : (absP P).pos = (absP P.pop).pos := hp.symm
    simp only [Option.map_none]
    rw [this]
  | some d =>
    simp only [htop, Option.some.injEq] at hp
    have : (absP P).pos.set d.val none = (absP P.pop).pos := by
      rw [hp]
      apply List.ext_getElem (by simp [absP])
      intro k h1 h2
      simp [absP, List.getElem_set, Fin.ext_iff]
    simp only [Option.map_some]
    rw [this]

theorem absP_push {s t : Nat} (P : Mapping s t) (d : Fin t) (hd : P.symm d = none) :
    absP (P.push d hd) = (absP P).push d.val := by
  simp only [absP, FlatShuffler.Map.Mapping.push, List.length_map, List.length_finRange,
    FlatShuffler.Map.Mapping.mk.injEq]
  constructor
  · rw [List.finRange_succ_last]
    simp [Function.comp_def]
  · apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_set]
    by_cases hk : d.val = k
    · subst hk
      simp
    · rw [Mapping.push_symm_apply_of_ne _ _ _ _ (by simp [Fin.ext_iff]; omega)]
      simp [hk, Function.comp_def]

theorem absP_count {s t : Nat} (P : Mapping s t) :
    (absP P).pos.count none = P.unmapped_target_slots := by
  simp only [absP, Mapping.unmapped_target_slots, List.count, List.countP_map]
  rw [List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange t).filter _), List.toFinset_filter,
    List.toFinset_finRange]
  congr 1
  ext j
  simp

-- A list state and an original state agree.
structure PopRel {source target : Stack} {spills : SpillSet} (s : FlatShuffler.Map.State)
    (st : State source target spills) : Prop where
  planned : s.planned = absP st.planned_mapping
  stack : st.stack = s.stack.map decodeStackSlot
  trace : s.trace = (traceOperations st.trace).map encodeTraceOperation
  mapping : s.mapping = absP st.mapping
  pend : s.pend = st.pending_generations

-- The initial state of `Emission.run`.
theorem init_rel {target : Stack} {spills : SpillSet} (stack : List FlatShuffler.StackSlot)
    (P : Mapping (stack.map decodeStackSlot).length target.length) :
    PopRel (FlatShuffler.Map.State.init stack (absP P))
      ({ planned_mapping := P, stack := stack.map decodeStackSlot, trace := .Lit _, mapping := P,
         pending_generations := P.unmapped_target_slots } :
        State (stack.map decodeStackSlot) target spills) :=
  ⟨rfl, rfl, rfl, rfl, absP_count P⟩

theorem pop_corr {source target : Stack} {spills : SpillSet} {s : FlatShuffler.Map.State}
    {st : State source target spills} (h : PopRel s st) : Corr PopRel s.pop st.pop := by
  unfold FlatShuffler.Map.State.pop State.pop
  by_cases hs : s.stack = []
  · have hne : ¬ 0 < st.stack.length := by simp [h.stack, hs]
    simp only [hs, ite_true, requires, hne, ↓reduceDIte, bind, Except.bind]
    trivial
  · have hne : 0 < st.stack.length := by
      simpa [h.stack] using List.length_pos_iff.mpr hs
    simp only [hs, ite_false, requires, hne, ↓reduceDIte, pure, Except.pure, bind, Except.bind]
    refine ⟨h.planned, ?_, ?_, ?_, h.pend⟩
    · show st.stack.dropLast = _
      rw [h.stack, List.map_dropLast]
    · simp [traceOperations, h.trace, encodeTraceOperation, FlatShuffler.Op.pop, FlatShuffler.Pop]
    · show s.mapping.pop = absP (Mapping.pop _)
      rw [absP_pop, absP_cast, h.mapping]

-- `Corr` of a sequence.
theorem corr_bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {x : FlatShuffler.M α}
    {y : Except ShuffleErr β} {f : α → FlatShuffler.M γ} {g : β → Except ShuffleErr δ}
    (h : Corr R x y) (hf : ∀ a b, R a b → Corr S (f a) (g b)) :
    Corr S (x.bind f) (y.bind g) :=
  match x, y, h with
  | .ok a, .ok b, h => hf a b h
  | .error .assertion, .error (.assertion _), _ => trivial
  | .ok _, .error _, h => h.elim
  | .error (.blocked ..), _, h => h.elim
  | .error .assertion, .ok _, h => h.elim

-- One pop for each element of `l`, up to the first that fails: the loop of `emission_pop` and
-- of `Fuzz/Oracle.lean`.
theorem pops_corr {source target : Stack} {spills : SpillSet} {s : FlatShuffler.Map.State}
    {st : State source target spills} (h : PopRel s st) (l : List Nat) :
    Corr PopRel (s.pops l.length) (l.foldlM (fun st _ => st.pop) st) := by
  induction l generalizing s st with
  | nil => exact h
  | cons x l ih => exact corr_bind (pop_corr h) fun _ _ hab => ih hab

end ShufflerBridge.Emission
