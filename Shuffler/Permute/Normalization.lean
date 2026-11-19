module

public import Shuffler.Permute.Defs
import Mathlib.Data.List.Nodup
import Shuffler.Emission.Lemmas
import Shuffler.Permute.Cycles

@[expose] public section

namespace Shuffler.Permute

open Emission

-- The permutation that `permute` hands to `go`.
abbrev normalize (stack : Stack) (perm : Permutation stack.length) : Permutation stack.length :=
  permute.minimizeCyclesWithoutTop stack (permute.minimizePermutationSupport stack perm 0)

def Assigns {n : ℕ} (value expected : Fin n → Value) (p : Equiv.Perm (Fin n)) : Prop :=
  ∀ i, value i = expected (p i)

-- Exchanging the destinations of two equal slots keeps every slot bound to an offset expecting its value.
theorem Assigns.mul_swap {n : ℕ} {value expected : Fin n → Value} {p : Equiv.Perm (Fin n)}
    (h : Assigns value expected p) (a b : Fin n) (hab : value a = value b) :
    Assigns value expected (p * Equiv.swap a b) := by
  intro i
  have hv : value (Equiv.swap a b i) = value i := by
    by_cases ha : i = a
    · subst i; simpa using hab.symm
    by_cases hb : i = b
    · subst i; simpa using hab
    rw [Equiv.swap_apply_of_ne_of_ne ha hb]
  simpa [hv] using h (Equiv.swap a b i)

-- The first loop of `normalize`: once every slot before `position` stays or sends its value to an offset that
-- does not already hold it, every slot holding its expected value ends fixed.
theorem minimizePermutationSupport_spec (stack : Stack) (expected : Fin stack.length → Value) (p : Permutation stack.length)
    (position : ℕ) (hp : Assigns (fun i => stack[i]) expected p)
    (hvisited : ∀ i : Fin stack.length, i.val < position → p i = i ∨ stack[p i] ≠ stack[i]) :
    Assigns (fun i => stack[i]) expected (permute.minimizePermutationSupport stack p position) ∧
      ∀ i, stack[i] = expected i → permute.minimizePermutationSupport stack p position i = i := by
  fun_induction permute.minimizePermutationSupport stack p position with
  | case1 p position h destination hd ih =>
    refine ih (hp.mul_swap _ _ (by simpa using hd.2)) fun i hi => ?_
    by_cases hid : i = destination
    · left
      simp [hid, destination]
    · have hip : i ≠ ⟨position, h⟩ := by rintro rfl; exact absurd hi (lt_irrefl _)
      have heq : (p * Equiv.swap destination ⟨position, h⟩) i = p i := by
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hid hip]
      simpa only [heq] using hvisited i hi
  | case2 p position h destination hd ih =>
    refine ih hp fun i hi => ?_
    by_cases hip : i.val < position
    · exact hvisited i hip
    · obtain rfl : i = ⟨position, h⟩ := Fin.ext (Nat.le_antisymm (Nat.lt_succ_iff.mp hi) (Nat.not_lt.mp hip))
      by_cases he : destination = ⟨position, h⟩
      · exact Or.inl he
      · exact Or.inr fun hs => hd ⟨he, by simpa using hs⟩
  | case3 p position h =>
    refine ⟨hp, fun i he => ?_⟩
    have hs : stack[p.symm i] = expected i := by simpa using hp (p.symm i)
    have hlt := (p.symm i).isLt
    rcases hvisited (p.symm i) (by omega) with hf | hne
    · have hfix : p.symm i = i := by simpa using hf.symm
      simpa using (congrArg p hfix).symm
    · exact absurd (hs.trans he.symm).symm (by simpa using hne)

-- A property that every step of a loop keeps, including a step that breaks out of it, holds when the loop ends. It
-- may refer to the elements still to come; a step that breaks out leaves none to come.
theorem forIn_invariant {α β : Type} (xs : List α) (init : β) (f : α → β → Id (ForInStep β))
    (P : List α → β → Prop) (h0 : P xs init)
    (hf : ∀ a rest b, P (a :: rest) b →
      match (f a b).run with
      | .done b' => P [] b'
      | .yield b' => P rest b') :
    P [] (forIn xs init f).run := by
  induction xs generalizing init with
  | nil => exact h0
  | cons a xs ih =>
    have h := hf a xs init h0
    simp only [List.forIn_cons, Id.run_bind]
    cases hs : (f a init).run with
    | done b => rw [hs] at h; exact h
    | yield b => rw [hs] at h; exact ih b h

-- The second loop of `normalize` exchanges destinations only between equal slots, never between a slot below the
-- top that stays in place and another one, and leaves equal slots that move or are the top in one cycle: each moving
-- slot joins the first later equal slot that moves or is the top, and joining never splits a cycle.
theorem minimizeCyclesWithoutTop_spec (stack : Stack) (expected : Fin stack.length → Value) (p : Permutation stack.length)
    (hp : Assigns (fun i => stack[i]) expected p) :
    Assigns (fun i => stack[i]) expected (permute.minimizeCyclesWithoutTop stack p) ∧
      (∀ i, i.val + 1 ≠ stack.length → p i = i → permute.minimizeCyclesWithoutTop stack p i = i) ∧
      ∀ i j, (permute.minimizeCyclesWithoutTop stack p i ≠ i ∨ i.val + 1 = stack.length) →
        (permute.minimizeCyclesWithoutTop stack p j ≠ j ∨ j.val + 1 = stack.length) →
        stack[i] = stack[j] → (permute.minimizeCyclesWithoutTop stack p).SameCycle i j := by
  let M (x : Fin stack.length) : Prop := p x ≠ x ∨ x.val + 1 = stack.length
  -- a moving slot shares a cycle with some later equal slot in `M` if there is one
  let Q (a : Fin stack.length) (q : Permutation stack.length) : Prop :=
    M a → a.val + 1 ≠ stack.length → (∃ b : Fin stack.length, a.val < b.val ∧ stack[a] = stack[b] ∧ M b) →
      ∃ b : Fin stack.length, a.val < b.val ∧ stack[a] = stack[b] ∧ M b ∧ q.SameCycle a b
  have hmono (a : Fin stack.length) (q q' : Permutation stack.length)
      (hq : ∀ x y, q.SameCycle x y → q'.SameCycle x y) (h : Q a q) : Q a q' := fun hm ht hb =>
    (h hm ht hb).imp fun _ ⟨hab, he, hM, hc⟩ => ⟨hab, he, hM, hq _ _ hc⟩
  -- the loop keeps `Assigns` and the slots in `M`, and settles `Q` for each slot it has visited
  let I (rest : List (Fin stack.length)) (q : Permutation stack.length) : Prop :=
    Assigns (fun i => stack[i]) expected q ∧ (∀ x, (q x ≠ x ∨ x.val + 1 = stack.length) ↔ M x) ∧
      ∀ a, a ∉ rest → Q a q
  have hloop : I [] (permute.minimizeCyclesWithoutTop stack p) := by
    unfold permute.minimizeCyclesWithoutTop
    simp only [bind_pure]
    refine forIn_invariant _ _ _ I ⟨hp, fun _ => Iff.rfl, fun a ha => absurd (List.mem_finRange a) ha⟩ ?_
    intro a rest q ⟨hA, hM, hQ⟩
    by_cases ha : q a ≠ a
    · rw [ite_eq_left ha]
      simp only [Id.run_bind, Id.run_pure]
      -- the inner loop still has every later equal slot in `M` to come, or has stopped after joining one
      let P (rest' : List (Fin stack.length)) (r : Permutation stack.length) : Prop :=
        (∀ b ∈ rest', a.val < b.val) ∧
          ((r = q ∧ ∀ b : Fin stack.length, a.val < b.val → stack[a] = stack[b] → M b → b ∈ rest') ∨
            (rest' = [] ∧ I (a :: rest) r ∧ (∀ x y, q.SameCycle x y → r.SameCycle x y) ∧
              ∃ b : Fin stack.length, a.val < b.val ∧ stack[a] = stack[b] ∧ M b ∧ r.SameCycle a b))
      suffices h : ∀ r, P [] r → I rest r from h _ (forIn_invariant _ _ _ P ?h0 ?hf)
      case h0 =>
        refine ⟨fun b hb => ?_, Or.inl ⟨rfl, fun b hab _ _ => ?_⟩⟩
        · obtain ⟨k, hk, rfl⟩ := List.mem_drop_iff_getElem.mp hb
          simp only [List.getElem_finRange, Fin.val_cast]
          omega
        · refine List.mem_drop_iff_getElem.mpr ⟨b.val - (a.val + 1), by simp; omega, Fin.ext ?_⟩
          simp only [List.getElem_finRange, Fin.val_cast]
          omega
      case hf =>
        intro b rest' r ⟨hlt, hr⟩
        obtain ⟨rfl, hnone⟩ := hr.resolve_right fun h => List.cons_ne_nil _ _ h.1
        have hab := hlt b List.mem_cons_self
        by_cases hc : stack[a] = stack[b] ∧ (r b ≠ b ∨ b.val = stack.length - 1)
        · rw [ite_eq_left hc]
          have hMb : M b := (hM b).mp (hc.2.imp_right fun h => by omega)
          by_cases hs : r.SameCycle a b
          · rw [ite_eq_right (not_not.mpr hs)]
            exact ⟨fun _ h => absurd h List.not_mem_nil, Or.inr ⟨rfl, ⟨hA, hM, hQ⟩, fun _ _ h => h, b, hab, hc.1, hMb, hs⟩⟩
          · rw [ite_eq_left hs]
            refine ⟨fun _ h => absurd h List.not_mem_nil, Or.inr ⟨rfl, ⟨hA.mul_swap a b hc.1, fun x => ?_,
              fun a' ha' => hmono a' r _ (fun _ _ h => Permutation.sameCycle_mul_swap hs h) (hQ a' ha')⟩,
              fun _ _ h => Permutation.sameCycle_mul_swap hs h, b, hab, hc.1, hMb,
              Permutation.sameCycle_mul_swap_self hs⟩⟩
            rw [← hM x]
            by_cases hxa : x = a
            · subst hxa
              have : r b ≠ x := fun h => hs (h ▸ Equiv.Perm.sameCycle_apply_right.mpr .rfl).symm
              simp [this, ha]
            by_cases hxb : x = b
            · subst hxb
              have : r a ≠ x := fun h => hs (h ▸ Equiv.Perm.sameCycle_apply_right.mpr .rfl)
              simpa [this] using (hM x).mpr hMb
            · simp [Equiv.swap_apply_of_ne_of_ne hxa hxb]
        · rw [ite_eq_right hc]
          refine ⟨fun b' hb' => hlt b' (List.mem_cons_of_mem _ hb'), Or.inl ⟨rfl, fun b' hab' hb' hMb' => ?_⟩⟩
          rcases List.mem_cons.mp (hnone b' hab' hb' hMb') with rfl | h
          · exact absurd ⟨hb', ((hM b').mpr hMb').imp_right fun h => by omega⟩ hc
          · exact h
      intro r ⟨_, hr⟩
      rcases hr with ⟨rfl, hnone⟩ | ⟨-, ⟨hrA, hrM, hrQ⟩, -, hjoin⟩
      · refine ⟨hA, hM, fun a' ha' => ?_⟩
        by_cases haa : a' = a
        · subst haa
          exact fun _ _ ⟨b, hab, hb, hMb⟩ => absurd (hnone b hab hb hMb) List.not_mem_nil
        · exact hQ a' (by simp [haa, ha'])
      · refine ⟨hrA, hrM, fun a' ha' => ?_⟩
        by_cases haa : a' = a
        · subst haa
          exact fun _ _ _ => hjoin
        · exact hrQ a' (by simp [haa, ha'])
    · rw [ite_eq_right ha]
      refine ⟨hA, hM, fun a' ha' => ?_⟩
      by_cases haa : a' = a
      · subst haa
        intro hMa hat
        exact absurd ((hM a').mpr hMa |>.resolve_right hat) ha
      · exact hQ a' (by simp [haa, ha'])
  obtain ⟨hA, hM, hQ⟩ := hloop
  refine ⟨hA, fun i hi hfix => by_contra fun hq => ((hM i).mp (Or.inl hq)).elim (· hfix) hi,
    fun i j hi hj he => ?_⟩
  -- a slot of `M` shares a cycle with every later equal one, by descent from the top
  have hchain (k : ℕ) : ∀ i j : Fin stack.length, stack.length - i.val = k → i.val < j.val → M i → M j →
      stack[i] = stack[j] → (permute.minimizeCyclesWithoutTop stack p).SameCycle i j := by
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro i j hk hij hi hj he
    have := j.isLt
    obtain ⟨b, hib, hb, hMb, hc⟩ := hQ i List.not_mem_nil hi (by omega) ⟨j, hij, he, hj⟩
    have := b.isLt
    rcases lt_trichotomy b.val j.val with hbj | hbj | hjb
    · exact hc.trans (ih _ (by omega) b j rfl hbj hMb hj (hb.symm.trans he))
    · obtain rfl : b = j := Fin.ext hbj
      exact hc
    · exact hc.trans (ih _ (by omega) j b rfl hjb hj hMb (he.symm.trans hb)).symm
  rcases lt_trichotomy i.val j.val with hij | hij | hji
  · exact hchain _ i j rfl hij ((hM i).mp hi) ((hM j).mp hj) he
  · obtain rfl : i = j := Fin.ext hij
    exact .rfl
  · exact (hchain _ j i rfl hji ((hM j).mp hj) ((hM i).mp hi) he.symm).symm

theorem normalize_assigns (stack : Stack) (p : Permutation stack.length)
    (expected : Fin stack.length → Value) (hp : Assigns (fun i => stack[i]) expected p) :
    Assigns (fun i => stack[i]) expected (normalize stack p) ∧
      (∀ i, i.val + 1 ≠ stack.length → stack[i] = expected i → normalize stack p i = i) ∧
      ∀ i j, (normalize stack p i ≠ i ∨ i.val + 1 = stack.length) →
        (normalize stack p j ≠ j ∨ j.val + 1 = stack.length) →
        stack[i] = stack[j] → (normalize stack p).SameCycle i j := by
  obtain ⟨hfa, hff⟩ := minimizePermutationSupport_spec stack expected p 0 hp (fun _ hi => absurd hi (Nat.not_lt_zero _))
  obtain ⟨hma, hmf, hmj⟩ := minimizeCyclesWithoutTop_spec stack expected _ hfa
  exact ⟨hma, fun i hi he => hmf i hi (hff i he), hmj⟩

theorem all_swaps_reachable.values {stack : Stack} {p : Permutation stack.length}
    (h : all_swaps_reachable p) : values_reachable p := by
  intro i hne
  apply h i
  apply Equiv.Perm.mem_support.mpr
  intro hfix
  apply hne
  have hi : p.symm i = i := by
    apply p.injective
    simpa using hfix.symm
  simp only [hi]

-- Only the top can move without being moved by `p`: it joins a cycle that holds its value.
theorem normalize_spec (stack : Stack) (p : Permutation stack.length) :
    apply_permutation stack (normalize stack p) = apply_permutation stack p ∧
      (∀ i ∈ (normalize stack p).support, i ∈ p.support ∨ i.val + 1 = stack.length) ∧
      (all_swaps_reachable (normalize stack p) ↔ values_reachable p) := by
  obtain ⟨ha, hc, -⟩ := normalize_assigns stack p
    (fun i => stack[p.symm i]) (by intro i; simp)
  generalize normalize stack p = q at *
  refine ⟨?_, ?_, ?_⟩
  · apply congrArg List.ofFn
    funext i
    simpa using ha (q.symm i)
  · intro i hi
    by_cases ht : i.val + 1 = stack.length
    · exact Or.inr ht
    · refine Or.inl (Equiv.Perm.mem_support.mpr fun hfix => Equiv.Perm.mem_support.mp hi (hc i ht ?_))
      have hs : p.symm i = i := by simpa using (congrArg p.symm hfix).symm
      simp only [hs]
  · constructor
    · intro hr i hne
      apply hr i
      apply Equiv.Perm.mem_support.mpr
      intro hfix
      exact hne (by simpa [hfix] using ha i)
    · intro hr i hi
      by_cases he : stack[i] = stack[p.symm i]
      · by_cases ht : i.val + 1 = stack.length
        · simp only [Stack.isSwapReachable]; omega
        · exact ((Equiv.Perm.mem_support.mp hi) (hc i ht he)).elim
      · exact hr i he

theorem normalize_of_nodup (stack : Stack) (p : Permutation stack.length) (hn : stack.Nodup) :
    normalize stack p = p := by
  obtain ⟨ha, _⟩ := normalize_assigns stack p
    (fun i => stack[p.symm i]) (by intro i; simp)
  generalize normalize stack p = q at *
  have hsymm : q.symm = p.symm := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    exact hn.getElem_inj_iff.mp (by simpa using ha (q.symm i))
  simpa using congrArg Equiv.symm hsymm

theorem values_reachable_congr {stack : Stack} (p q : Permutation stack.length)
    (he : apply_permutation stack p = apply_permutation stack q) :
    values_reachable p ↔ values_reachable q := by
  have hv (i : Fin stack.length) : stack[p.symm i] = stack[q.symm i] := by
    simpa [apply_permutation] using congrArg (fun xs => xs[i.val]?) he
  simp only [values_reachable, hv]

theorem values_reachable_iff_deep (stack : Stack) (p : Permutation stack.length) :
    values_reachable p ↔ ∀ i, i < stack.length - (MAX_SWAP_DEPTH + 1) →
      stack[i]? = (apply_permutation stack p)[i]? := by
  constructor
  · intro hr i hi
    have hin : i < stack.length := by omega
    have he : stack[i] = stack[p.symm ⟨i, hin⟩] := by
      by_contra hne
      have hd := hr ⟨i, hin⟩ hne
      simp only [Stack.isSwapReachable] at hd
      omega
    simpa [apply_permutation, hin] using he
  · intro hr i hne
    by_contra hd
    have hi : i.val < stack.length - (MAX_SWAP_DEPTH + 1) := by
      simp only [Stack.isSwapReachable] at hd
      omega
    apply hne
    simpa [apply_permutation, i.isLt] using hr i.val hi

end Shuffler.Permute
