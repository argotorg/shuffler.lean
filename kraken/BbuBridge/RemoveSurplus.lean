module

public import BbuBridge.Basic
import all BbuBridge.Basic
public import BbuBridge.Pop
import all BbuBridge.Pop
public import BbuBridge.SwapWith
import all BbuBridge.SwapWith
public import Shuffler.RemoveSurplus.Defs
import all Shuffler.RemoveSurplus.Defs

@[expose] public section

/-!
The list model `Bbu.Map.State.removeSurplus` (`BbuKraken/MapModel.lean`) is an instance of the
PR31 model `Shuffler.Emission.removeSurplus`.

`SurplusRel` relates the results: the same blocked slot and excess (or none), and states that
agree (`PopRel`). The list model compares `StackSlot`s and PR31 compares decoded values, so the
slots must be canonical (`Canon`).

The two `forIn` loops of PR31 (the scan for surplus slots and the scan for an equal surplus slot)
are the recursive functions `surplusScan` and `equalBelow` of the list model (`scan_forIn`,
`equal_forIn`). The outer `forIn` is `surplusLoop`, by induction on its list.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

-- The target offset of a slot in the list mapping.
theorem absP_dest_getD {m t : Nat} (P : Mapping m t) (p : Nat) (hp : p < m) :
    (absP P).dest.getD p none = (P ⟨p, hp⟩).map Fin.val := by
  simp [absP, List.getD_eq_getElem?_getD, hp]
-- `swapDestinations` on the target offsets.
theorem absP_dest_swap {m t : Nat} (P : Mapping m t) (a b : Fin m) :
    (absP (P.swapDestinations a b)).dest =
      ((absP P).dest.set a ((absP P).dest.getD b none)).set b ((absP P).dest.getD a none) := by
  rw [absP_dest_getD P a a.isLt, absP_dest_getD P b b.isLt]
  apply List.ext_getElem (by simp [absP])
  intro i h1 h2
  simp only [absP, List.getElem_map, List.getElem_finRange, List.getElem_set,
    Mapping.swapDestinations_apply, Equiv.swap_apply_def]
  by_cases hb : b.val = i
  · subst hb
    by_cases ha : b = a
    · subst ha; simp
    · simp [Fin.ext_iff] at ha; simp [Fin.ext_iff, ha]
  · by_cases ha : a.val = i
    · subst ha; simp [hb]
    · simp [Fin.ext_iff, hb, ha, Ne.symm ha, Ne.symm hb]
-- `swapDestinations` on the positions.
theorem absP_pos_swap {m t : Nat} (P : Mapping m t) (a b : Fin m) (k : Nat) (hk : k < t) :
    ((P.swapDestinations a b).symm ⟨k, hk⟩).map Fin.val =
      if (P a).map Fin.val = some k then some b.val
      else if (P b).map Fin.val = some k then some a.val
      else (P.symm ⟨k, hk⟩).map Fin.val := by
  rw [Mapping.swapDestinations_symm_apply]
  have key : ∀ x : Fin m, (P x).map Fin.val = some k ↔ P.symm ⟨k, hk⟩ = some x := by
    intro x
    rw [PEquiv.eq_some_iff]
    constructor
    · intro h
      obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h
      exact hd
    · intro h; rw [h]; rfl
  simp only [key]
  cases hj : P.symm ⟨k, hk⟩ with
  | none => simp
  | some i =>
    by_cases ha : i = a
    · subst ha; simp
    · by_cases hb : i = b
      · subst hb; simp [ha]
      · simp [hb, ha, Equiv.swap_apply_of_ne_of_ne ha hb]

-- `absP` commutes with `swapDestinations`.
theorem absP_swap {m t : Nat} (P : Mapping m t) (a b : Fin m) :
    absP (P.swapDestinations a b) = (absP P).swapDestinations a.val b.val := by
  unfold Bbu.Map.Mapping.swapDestinations
  dsimp only
  rw [← absP_dest_swap, absP_dest_getD _ a a.isLt, absP_dest_getD _ b b.isLt,
    Mapping.swapDestinations_apply, Mapping.swapDestinations_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  show Bbu.Map.Mapping.mk (absP _).dest (absP _).pos = _
  congr 1
  apply List.ext_getElem?
  intro k
  by_cases hk : k < t
  · have e : (absP (P.swapDestinations a b)).pos[k]? =
        some (((P.swapDestinations a b).symm ⟨k, hk⟩).map Fin.val) := by
      simp [absP, hk]
    rw [e, absP_pos_swap P a b k hk]
    have hp : ∀ j : Fin t, (absP P).pos[j.val]? = some ((P.symm j).map Fin.val) := by
      intro j; simp [absP, j.isLt]
    have hpl : (absP P).pos.length = t := by simp [absP]
    cases ha : P a <;> cases hb : P b <;>
      simp [List.getElem?_set, hp ⟨k, hk⟩, eq_comm, hpl, Fin.is_lt] <;> split_ifs <;> rfl
  · have hl : ∀ L : List (Option Nat), L.length = t → L[k]? = none := fun L hL => by
      simp [hL, Nat.le_of_not_lt hk]
    rw [hl _ (by simp [absP]), hl]
    cases P a <;> cases P b <;> simp [absP]


-- `swapWith` of the list state is an instance of `State.swapWith`.
theorem mapSwapWith_corr {source target : Stack} {spills : SpillSet} {s : Bbu.Map.State}
    {st : State source target spills} (h : PopRel s st) (pos : Nat) :
    Corr PopRel (s.swapWith pos) (st.swapWith pos) := by
  have hl : st.stack.length = s.stack.length := by simp [h.stack]
  unfold Bbu.Map.State.swapWith State.swapWith
  by_cases hp : pos < st.stack.length
  · rw [show index st.stack.length pos = .ok ⟨pos, hp⟩ from index_eq ⟨pos, hp⟩, except_ok_bind]
    have hfin : s.mapping.dest.getD pos none = some pos ↔ st.isFinal ⟨pos, hp⟩ := by
      rw [h.mapping, absP_dest_getD _ pos hp]; rfl
    by_cases hf : st.isFinal ⟨pos, hp⟩
    · rw [ite_eq_left (.inr (hfin.mpr hf))]
      simp only [requires, hf, not_true_eq_false, dite_false]
      exact trivial
    · rw [ite_eq_right (fun h' => h'.elim (by omega) (fun h'' => hf (hfin.mp h'')))]
      simp only [requires, hf, not_false_eq_true, dite_true, pure, Except.pure, bind, Except.bind]
      have hdd : (st.stack.offsetToDepth ⟨pos, hp⟩).val = s.stack.length - 1 - pos := by
        simp only [Stack.offsetToDepth, hl]
      by_cases hdepth : 1 ≤ s.stack.length - 1 - pos ∧ s.stack.length - 1 - pos ≤ MAX_SWAP_DEPTH
      · rw [ite_eq_right (by simp only [Bbu.MAX_SWAP_DEPTH, MAX_SWAP_DEPTH] at *; omega)]
        simp only [hdd, hdepth, and_self, dite_true]
        refine ⟨h.planned, ?_, ?_, ?_, h.pend⟩
        · show st.stack.swap pos (st.stack.length - 1) = _
          rw [List.swap_eq_of_lt hp (by omega)]
          have hg : ∀ k (hk : k < st.stack.length), st.stack[k] = decode (s.stack.getD k default) := by
            intro k hk
            have hk' : k < s.stack.length := hl ▸ hk
            simp [h.stack, List.getD_eq_getElem?_getD, hk']
          apply List.ext_getElem (by simp [hl])
          intro i h1 h2
          simp only [List.getElem_set, List.getElem_map, hl]
          have hi : i < s.stack.length := by simpa [hl] using h1
          split_ifs <;> simp [List.getD_eq_getElem?_getD, *]
        · dsimp only
          rw [traceOps_cast]
          simp [traceOps, encodeOp, h.trace, hdd]
        · dsimp only
          rw [absP_cast, absP_swap, h.mapping]
          exact congrArg _ (by simp [hl])
      · rw [ite_eq_left (by simp only [Bbu.MAX_SWAP_DEPTH, MAX_SWAP_DEPTH] at *; omega)]
        simp only [hdd, hdepth, dite_false]
        exact trivial
  · rw [ite_eq_left (.inl (by omega))]
    simp only [index, hp, dite_false]
    exact trivial


/-! ## Canonical stacks -/

-- The members of the stack of a list state are canonical.
abbrev CanonS (s : Bbu.Map.State) : Prop := ∀ x ∈ s.stack, Canon x

-- A member of a canonical list is canonical.
theorem canon_getD {l : List Bbu.StackSlot} (hl : ∀ x ∈ l, Canon x) (i : Nat) :
    Canon (l.getD i default) := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => exact canon_default
  | some x => exact hl x (List.mem_of_getElem? hi)

-- `set` with a canonical slot keeps a list canonical.
theorem canon_setL {l : List Bbu.StackSlot} (hl : ∀ x ∈ l, Canon x) {i : Nat} {v : Bbu.StackSlot}
    (hv : Canon v) : ∀ x ∈ l.set i v, Canon x :=
  fun x hx => (List.mem_or_eq_of_mem_set hx).elim (hl x) fun h => h ▸ hv

-- `pop` keeps the stack canonical.
theorem pop_canon {s a : Bbu.Map.State} (h : s.pop = .ok a) (hc : CanonS s) : CanonS a := by
  unfold Bbu.Map.State.pop at h
  split at h
  · cases h
  · cases h
    exact fun x hx => hc x (List.mem_of_mem_dropLast hx)

-- `swapWith` keeps the stack canonical.
theorem swapWith_canon {s a : Bbu.Map.State} {p : Nat} (h : s.swapWith p = .ok a) (hc : CanonS s) :
    CanonS a := by
  unfold Bbu.Map.State.swapWith at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · cases h
      exact canon_setL (canon_setL hc (canon_getD hc _)) (canon_getD hc _)

-- `Corr` with a property of the list result.
theorem corr_and {α β : Type} {R : α → β → Prop} {P : α → Prop} {x : Bbu.M α}
    {y : Except ShuffleErr β} (h : Corr R x y) (hp : ∀ a, x = .ok a → P a) :
    Corr (fun a b => R a b ∧ P a) x y :=
  match x, y, h with
  | .ok a, .ok _, h => ⟨h, hp a rfl⟩
  | .error .assertion, .error (.assertion _), _ => trivial
  | .ok _, .error _, h => h.elim
  | .error (.blocked ..), _, h => h.elim
  | .error .assertion, .ok _, h => h.elim

/-! ## The scans -/

-- The scan for surplus slots, from the top down.
theorem scan_forIn (s : Bbu.Map.State) : ∀ (n : Nat)
    (f : Fin n → Option Nat × Option Nat → Except ShuffleErr (ForInStep (Option Nat × Option Nat))),
    (∀ (pos : Fin n) (sh dp : Option Nat), f pos (sh, dp) = .ok (.yield
      (if s.mapping.dest.getD pos.val none = none then
        ((if sh = none then some pos.val else sh),
         (if s.stack.length - 1 - pos.val ≤ Bbu.MAX_SWAP_DEPTH then some pos.val else dp))
      else (sh, dp)))) →
    ∀ sh dp, forIn (List.finRange n).reverse (sh, dp) f = .ok (s.surplusScan n sh dp)
  | 0, _, _, _, _ => rfl
  | n + 1, f, hf, sh, dp => by
    rw [List.finRange_succ_last, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.forIn_cons, hf, ← List.map_reverse, except_ok_bind]
    simp only [List.forIn_map]
    have ih := scan_forIn s n (fun pos b => f pos.castSucc b) (fun pos sh dp => hf pos.castSucc sh dp)
    unfold Bbu.Map.State.surplusScan
    by_cases hd : s.mapping.dest.getD n none = none
    · simp only [Fin.val_last, hd, ite_true]
      exact ih _ _
    · simp only [Fin.val_last, hd, ite_false]
      exact ih _ _

-- The scan for a surplus slot equal to the top, from the top down.
theorem equal_forIn (s : Bbu.Map.State) (top : Nat)
    (f : Nat → Option Nat → Except ShuffleErr (ForInStep (Option Nat))) : ∀ k,
    (∀ c, c < k → f c none = .ok (if s.mapping.dest.getD c none = none ∧
      s.stack.getD c default = s.stack.getD top default then .done (some c) else .yield none)) →
    forIn (List.range k).reverse none f = .ok (s.equalBelow top k)
  | 0, _ => rfl
  | k + 1, hf => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.forIn_cons, hf k (Nat.lt_succ_self k)]
    unfold Bbu.Map.State.equalBelow
    by_cases hc : s.mapping.dest.getD k none = none ∧ s.stack.getD k default = s.stack.getD top default
    · simp only [hc, and_self, ite_true]; rfl
    · simp only [hc, ite_false]
      exact equal_forIn s top f k fun c hc' => hf c (Nat.lt_succ_of_lt hc')

-- The shallowest surplus slot is below the start of the scan.
theorem surplusScan_lt (s : Bbu.Map.State) {n x : Nat} : ∀ p sh dp, p ≤ n →
    (∀ y, sh = some y → y < n) → (s.surplusScan p sh dp).1 = some x → x < n
  | 0, _, _, _, hsh, hx => hsh x hx
  | p + 1, sh, dp, hp, hsh, hx => by
    unfold Bbu.Map.State.surplusScan at hx
    split at hx
    · refine surplusScan_lt s p _ _ (by omega) ?_ hx
      intro y hy
      split at hy
      · cases hy; omega
      · exact hsh y hy
    · exact surplusScan_lt s p _ _ (by omega) hsh hx


-- The equal slot is below the start of the scan.
theorem equalBelow_lt (s : Bbu.Map.State) (top : Nat) {e : Nat} :
    ∀ k, s.equalBelow top k = some e → e < k
  | 0, h => by cases h
  | k + 1, h => by
    unfold Bbu.Map.State.equalBelow at h
    split at h
    · cases h; omega
    · exact Nat.lt_succ_of_lt (equalBelow_lt s top k h)

-- `Except.bind` is associative.
theorem ebind_assoc {ε α β γ : Type} (x : Except ε α) (f : α → Except ε β) (g : β → Except ε γ) :
    (x.bind f).bind g = x.bind (fun a => (f a).bind g) := by
  cases x <;> rfl

-- `Except.bind` of `ok`.
theorem ebind_ok {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a).bind f = f a := rfl

-- A list result and a PR31 result agree.
def SurplusRel {source target : Stack} {spills : SpillSet} (x : Option (Nat × Nat) × Bbu.Map.State)
    (r : Result source target spills) : Prop :=
  r.blocked = x.1.map (fun p => ⟨p.1, p.2⟩) ∧ PopRel x.2 r.state

-- `removeSurplus` of the list model is an instance of PR31 `removeSurplus`, and its stack is
-- canonical.
theorem removeSurplus_corr_canon {source target : Stack} {spills : SpillSet} {s : Bbu.Map.State}
    {st : State source target spills} (h : PopRel s st) (hc : ∀ x ∈ s.stack, Canon x) :
    Corr (fun x r => SurplusRel x r ∧ ∀ v ∈ x.2.stack, Canon v) s.removeSurplus
      (removeSurplus st) := by
  unfold removeSurplus Bbu.Map.State.removeSurplus
  dsimp only
  have hlen : s.stack.length = (List.range st.stack.length).length := by simp [h.stack]
  rw [hlen]
  clear hlen
  generalize List.range st.stack.length = l
  induction l generalizing s st with
  | nil => exact ⟨⟨rfl, h⟩, hc⟩
  | cons a l ih =>
    have hl : st.stack.length = s.stack.length := by simp [h.stack]
    rw [List.forIn_cons, bind_assoc, List.length_cons]
    unfold Bbu.Map.State.surplusLoop
    dsimp only
    by_cases hs : s.stack = []
    · have he : st.stack.isEmpty = true := by simp [h.stack, hs]
      simp only [hs, he, ite_true]
      exact ⟨⟨rfl, h⟩, hc⟩
    · have he : st.stack.isEmpty = false := by simp [h.stack, hs]
      simp only [hs, he, ite_false, Bool.false_eq_true]
      have hpos : 0 < st.stack.length := by
        rw [hl]; exact List.length_pos_iff.mpr hs
      have hsur : ∀ (i : Fin st.stack.length),
          st.isSurplus i ↔ s.mapping.dest.getD i.val none = none := by
        intro i
        rw [h.mapping, absP_dest_getD _ i.val i.isLt, Option.map_eq_none_iff]
        rfl
      rw [← hl, scan_forIn s _ _ ?hf none none, except_ok_bind]
      case hf =>
        intro pos sh dp
        have hreach : st.isSwapReachable pos ↔ s.stack.length - 1 - pos.val ≤ Bbu.MAX_SWAP_DEPTH := by
          simp only [State.isSwapReachable, State.depthOf, Stack.offsetToDepth, hl, Bbu.MAX_SWAP_DEPTH,
            MAX_SWAP_DEPTH]
        dsimp only
        by_cases h1 : st.isSurplus pos
        · have h1' := (hsur pos).mp h1
          by_cases h2 : st.isSwapReachable pos
          · have h2' := hreach.mp h2
            cases sh <;> simp only [h1, h1', h2, h2', ite_true, Option.isNone_none,
              Option.isNone_some, Bool.false_eq_true, ite_false, reduceCtorEq] <;> rfl
          · have h2' := mt hreach.mpr h2
            cases sh <;> simp only [h1, h1', h2, h2', ite_true, Option.isNone_none,
              Option.isNone_some, Bool.false_eq_true, ite_false, reduceCtorEq] <;> rfl
        · have h1' := mt (hsur pos).mpr h1
          simp only [h1, h1', ite_false]
          rfl
      generalize hr : s.surplusScan st.stack.length none none = r
      rcases r with ⟨_ | sh, _ | dp⟩
      · exact ⟨⟨rfl, h⟩, hc⟩
      · exact ⟨⟨rfl, h⟩, hc⟩
      · have hsh : sh < st.stack.length :=
          surplusScan_lt s _ _ _ le_rfl (fun _ hy => by cases hy) (congrArg Prod.fst hr)
        dsimp only
        rw [show index st.stack.length sh = .ok ⟨sh, hsh⟩ from index_eq ⟨sh, hsh⟩, except_ok_bind]
        unfold State.blockSwapUnreachable State.block
        have hd : (st.depthOf ⟨sh, hsh⟩).val = st.stack.length - 1 - sh := rfl
        rw [hd]
        by_cases hx : st.stack.length - 1 - sh - Bbu.MAX_SWAP_DEPTH = 0
        · have hx' : ¬ (st.stack.length - 1 - sh - MAX_SWAP_DEPTH > 0) := by
            simp only [Bbu.MAX_SWAP_DEPTH, MAX_SWAP_DEPTH] at *; omega
          simp only [hx, ite_true, requires, hx', dite_false]
          exact trivial
        · have hx' : st.stack.length - 1 - sh - MAX_SWAP_DEPTH > 0 := by
            simp only [Bbu.MAX_SWAP_DEPTH, MAX_SWAP_DEPTH] at *; omega
          simp only [hx, ite_false, requires, hx', dite_true]
          refine ⟨⟨?_, h⟩, hc⟩
          simp [Bbu.MAX_SWAP_DEPTH, MAX_SWAP_DEPTH]
      · dsimp only
        have hsh : sh < st.stack.length :=
          surplusScan_lt s _ _ _ le_rfl (fun _ hy => by cases hy) (congrArg Prod.fst hr)
        rw [ebind_assoc]
        by_cases heq : sh = st.stack.length - 1
        · subst heq
          simp only [ne_eq, not_true_eq_false, ite_true, ite_false, ebind_ok, bind_assoc, pure_bind]
          exact corr_bind (corr_and (pop_corr h) fun a ha => pop_canon ha hc) fun a b hab => ih hab.1 hab.2
        · simp only [heq, ne_eq, not_false_eq_true, ite_true, ite_false]
          have ht : st.stack.length - 1 < st.stack.length := by omega
          have hg : ∀ k (hk : k < st.stack.length), st.stack[k] = decode (s.stack.getD k default) := by
            intro k hk
            have hk' : k < s.stack.length := hl ▸ hk
            simp [h.stack, List.getD_eq_getElem?_getD, hk']
          rw [equal_forIn s (st.stack.length - 1) _ (st.stack.length - 1) ?hf2, except_ok_bind]
          case hf2 =>
            intro c hc'
            have hcl : c < st.stack.length := by omega
            rw [show index st.stack.length c = .ok ⟨c, hcl⟩ from index_eq ⟨c, hcl⟩, except_ok_bind,
              show slotAt st.stack c = _ from slotAt_index st.stack ⟨c, hcl⟩, except_ok_bind,
              show slotAt st.stack (st.stack.length - 1) = _ from slotAt_index st.stack ⟨_, ht⟩,
              except_ok_bind]
            simp only [Fin.getElem_fin]
            have hiff : (st.isSurplus ⟨c, hcl⟩ ∧ st.stack[c] = st.stack[st.stack.length - 1]) ↔
                (s.mapping.dest.getD c none = none ∧
                  s.stack.getD c default = s.stack.getD (st.stack.length - 1) default) := by
              rw [hsur, hg, hg, decode_eq_iff (canon_getD hc _) (canon_getD hc _)]
            by_cases hx : s.mapping.dest.getD c none = none ∧
                s.stack.getD c default = s.stack.getD (st.stack.length - 1) default
            · rw [ite_eq_left (hiff.mpr hx), ite_eq_left hx]; rfl
            · rw [ite_eq_right (mt hiff.mp hx), ite_eq_right hx]; rfl
          generalize hq : s.equalBelow (st.stack.length - 1) (st.stack.length - 1) = q
          cases q with
          | some e =>
            have hel : e < st.stack.length := by
              have := equalBelow_lt s _ _ hq; omega
            dsimp only
            have hsd : st.swapDestinations e (st.stack.length - 1) =
                .ok { st with mapping := st.mapping.swapDestinations ⟨e, hel⟩ ⟨_, ht⟩ } := by
              unfold State.swapDestinations
              rw [show index st.stack.length e = .ok ⟨e, hel⟩ from index_eq ⟨e, hel⟩, except_ok_bind,
                show index st.stack.length (st.stack.length - 1) = .ok ⟨_, ht⟩ from index_eq ⟨_, ht⟩,
                except_ok_bind]
              rfl
            rw [hsd, except_ok_bind]
            simp only [ebind_ok, bind_assoc, pure_bind]
            have hrel : PopRel { s with mapping := s.mapping.swapDestinations e (st.stack.length - 1) }
                { st with mapping := st.mapping.swapDestinations ⟨e, hel⟩ ⟨_, ht⟩ } :=
              ⟨h.planned, h.stack, h.trace, by rw [absP_swap, h.mapping], h.pend⟩
            exact corr_bind (corr_and (pop_corr hrel) fun a ha => pop_canon ha hc)
              fun a b hab => ih hab.1 hab.2
          | none =>
            dsimp only
            simp only [bind_assoc, pure_bind]
            exact corr_bind (corr_and (mapSwapWith_corr h dp) fun a ha => swapWith_canon ha hc)
              fun a b hab => corr_bind (corr_and (pop_corr hab.1) fun a' ha' => pop_canon ha' hab.2)
                fun a' b' hab' => ih hab'.1 hab'.2

theorem removeSurplus_corr {source target : Stack} {spills : SpillSet} {s : Bbu.Map.State}
    {st : State source target spills} (h : PopRel s st) (hc : ∀ x ∈ s.stack, Canon x) :
    Corr SurplusRel s.removeSurplus (removeSurplus st) :=
  corr_mono (removeSurplus_corr_canon h hc) fun _ _ _ hr => hr.1

end BbuBridge
