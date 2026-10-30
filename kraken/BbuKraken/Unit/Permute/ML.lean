import BbuKraken.Unit.Permute.Inv

/-!
# `permute`: facts of the model for the blocks

* The destinations of `PermOk` are below the size and not `NONE`.
* `start`: the model vectors at `.LB71`, from the locals at the end of phase B.
-/

namespace Bbu.Unit
open Bbu.Sep
namespace Permute

-- The variant goal of an edge.
macro "pm_dec" : tactic => `(tactic| (
  simp only [V, wC, Names.permute, String.reduceEq, ↓reduceIte, Nat.reducePow, Nat.reduceAdd,
    Nat.reduceMul, true_or, or_true]
  try omega))

theorem lt_max {g : G} (hok : g.Ok) {x : Word} (hx : x < g.h.len) : x.toNat < MAX_N :=
  Nat.lt_of_lt_of_le (BitVec.lt_def.mp hx) (Nat.le_trans hok.len hok.n)

theorem dest_lt {g : G} (hp : PermOk (flat g)) {x : Word} (hx : x < g.h.len) :
    Flat.get g.h.dest x < g.h.len := by
  have h1 := hp.lt x.toNat (BitVec.lt_def.mp hx)
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h1
  exact BitVec.lt_def.mpr h1

theorem dest_ne_none {g : G} (hp : PermOk (flat g)) {x : Word} (hx : x < g.h.len) :
    Flat.get g.h.dest x ≠ Flat.NONE := by
  intro h
  have h1 := BitVec.lt_def.mp (dest_lt hp hx)
  rw [h, none_toNat] at h1
  have := g.h.len.isLt
  omega

-- `permutation[x] = destinationOf[x]`: the agreement goes up to `x + 1`.
theorem agB_step {P d : Vector Word MAX_N} {x : Word} (hag : AgB x P d) (hx : x.toNat < MAX_N) :
    AgB (x + 1#64) (P.set x.toNat (Flat.get d x) hx) d := by
  intro i hi
  have hix : i.toNat < MAX_N := by simp only [MAX_N] at hx ⊢; bv_omega
  rw [get_eq _ _ hix]
  by_cases h : i = x
  · subst h; rw [Vector.getElem_set_self]
  · rw [Vector.getElem_set_ne _ _ (by intro e; exact h (BitVec.eq_of_toNat_eq e.symm)),
      ← get_eq _ _ hix]
    exact hag i (by simp only [MAX_N] at hx; bv_omega)

theorem AgB.trans {k : Word} {u v w : Vector Word MAX_N} (h1 : AgB k u v) (h2 : AgB k v w) :
    AgB k u w := fun i hi => (h1 i hi).trans (h2 i hi)

theorem AgB.symm {k : Word} {u v : Vector Word MAX_N} (h : AgB k u v) : AgB k v u :=
  fun i hi => (h i hi).symm

-- `readDestinations` gives a vector if no destination is `NONE`.
theorem rd_some (st : Flat.St) (hne : ∀ i < st.size, Flat.get st.dest i ≠ Flat.NONE)
    (pos : Word) (v : Vector Word MAX_N) : ∃ p, Flat.readDestinations st pos v = some p := by
  fun_induction Flat.readDestinations st pos v with
  | case1 pos v hlt d hd => exact absurd hd (hne pos hlt)
  | case2 pos v hlt d hd ih => exact ih
  | case3 pos v hge => exact ⟨_, rfl⟩

-- `.LB71` at the start: `permutation` agrees with `destinationOf` and `desiredBy` is `NONE`.
theorem start {g : G} (hok : g.Ok) (hp : PermOk (flat g)) {P D : Vector Word MAX_N}
    (hP : AgB g.h.len P g.h.dest) (hD : ∀ i < g.h.len, Flat.get D i = Flat.NONE) :
    ∃ p0, RG (flat g) (Flat.regroup (flat g) 0 p0 (Flat.clearDesired (flat g) 0 Flat.initial))
      ∧ AgB g.h.len P p0 ∧ AgB g.h.len D (Flat.clearDesired (flat g) 0 Flat.initial)
      ∧ LtB g.h.len p0 := by
  have hn : (flat g).size.toNat ≤ MAX_N := Nat.le_trans hok.len hok.n
  obtain ⟨p0, hrd⟩ := rd_some (flat g) (fun i hi => dest_ne_none hp hi) 0 Flat.initial
  have hp0 : AgB g.h.len p0 g.h.dest := fun i hi => by
    rw [readDestinations_spec (flat g) hn 0 _ _ hrd i hi, ite_eq_left (by bv_omega)]; rfl
  refine ⟨p0, ⟨p0, hrd, rfl⟩, hP.trans hp0.symm, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hD i hi, clearDesired_spec (flat g) hn 0 _ i hi, ite_eq_left (by bv_omega)]
  · rw [hp0 i hi]; exact dest_lt hp hi

theorem none_toInt : Flat.NONE.toInt = -1 := by decide

-- `desiredBy[k] = NONE`: the `NONE` part goes up to `k + 1`.
theorem none_step {D : Vector Word MAX_N} {k : Nat} (hk : k < MAX_N)
    (hD : ∀ i : Word, i.toNat < k → Flat.get D i = Flat.NONE) :
    ∀ i : Word, i.toNat < k + 1 → Flat.get (D.set k Flat.NONE hk) i = Flat.NONE := by
  intro i hi
  have hix : i.toNat < MAX_N := by omega
  rw [get_eq _ _ hix]
  by_cases h : i.toNat = k
  · subst h; rw [Vector.getElem_set_self]
  · rw [Vector.getElem_set_ne _ _ (fun e => h e.symm), ← get_eq _ _ hix]
    exact hD i (by omega)

end Permute
end Bbu.Unit
