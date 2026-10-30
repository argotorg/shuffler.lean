import BbuKraken.Unit.Permute.Inv

/-!
# `permute`: facts of the model for the blocks

* The destinations of `PermOk` are below the size and not `NONE`.
* `start`: the model vectors at `.LB.Emission.permute.12`, from the locals at the end of the
  loop `.LB.Emission.permute.0`.
-/

namespace Bbu.Unit
open Bbu.Sep
namespace Permute

-- The variant goal of an edge.
macro "pm_dec" : tactic => `(tactic| (
  simp only [V, wC, Names.permute, String.reduceEq, ↓reduceIte, Nat.reducePow, Nat.reduceAdd,
    Nat.reduceMul, Nat.reduceLT, true_or, or_true, or_false, false_or, true_and, and_true]
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

-- `.LB.Emission.permute.12` at the start: `permutation` agrees with `destinationOf` and `desiredBy` is `NONE`.
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

/-! ## The local arrays and the model vectors -/

-- A store into a local array and a `put` into its model vector.
theorem agB_set {n : Word} {u w : Vector Word MAX_N} (h : AgB n u w) {k : Word}
    (hk : k.toNat < MAX_N) (x : Word) : AgB n (u.set k.toNat x hk) (Flat.put w k x) := by
  intro i hi
  rw [← put_eq_set _ _ _ hk, get_put _ hk, get_put _ hk]
  split
  · rfl
  · exact h i hi

theorem ltB_put {n : Word} {p : Vector Word MAX_N} (h : LtB n p) (k : Word) {x : Word}
    (hx : x < n) : LtB n (Flat.put p k x) := by
  intro i hi
  by_cases hk : k.toNat < MAX_N
  · rw [get_put _ hk]
    split
    · exact hx
    · exact h i hi
  · have e : Flat.put p k x = p := by
      apply Vector.ext; intro j hj
      simp only [Flat.put, Vector.getElem_setIfInBounds]
      split
      · next e => omega
      · rfl
    rw [e]; exact h i hi

/-! ## Phase C: the steps of `regroup` -/

section
variable {st : Flat.St}

theorem regroup_ge {l : Word} (h : ¬l < st.size) (p dB : Vector Word MAX_N) :
    Flat.regroup st l p dB = some p := by
  rw [Flat.regroup, dite_eq_right h]

theorem regroup_skip {l : Word} (h : l < st.size)
    (hne : Flat.shallowestCopyPosition st (Flat.get st.data l) ≠ l) (p dB : Vector Word MAX_N) :
    Flat.regroup st l p dB = Flat.regroup st (l + 1) p dB := by
  rw [Flat.regroup, dite_eq_left h, ite_eq_left hne]

theorem regroup_lead {l : Word} (h : l < st.size)
    (he : Flat.shallowestCopyPosition st (Flat.get st.data l) = l) (p dB : Vector Word MAX_N) :
    Flat.regroup st l p dB = pg st l h (Flat.get st.data l)
      (Flat.markDesired st l h (Flat.get st.data l) p 0 dB) 0 0 p := by
  rw [Flat.regroup, dite_eq_left h, ite_eq_right (fun h => h he)]
  rfl

variable {l : Word} {hl : l < st.size} {σ : StackSlot}

theorem md_eq {p dB : Vector Word MAX_N} {j : Word} (hj : j ≤ l) (hd : Flat.get st.data j = σ) :
    Flat.markDesired st l hl σ p j dB
      = Flat.markDesired st l hl σ p (j + 1) (Flat.put dB (Flat.get p j) l) := by
  rw [Flat.markDesired, dite_eq_left hj, ite_eq_left hd]

theorem md_ne {p dB : Vector Word MAX_N} {j : Word} (hj : j ≤ l) (hd : Flat.get st.data j ≠ σ) :
    Flat.markDesired st l hl σ p j dB = Flat.markDesired st l hl σ p (j + 1) dB := by
  rw [Flat.markDesired, dite_eq_left hj, ite_eq_right hd]

theorem md_end {p dB : Vector Word MAX_N} {j : Word} (hj : ¬j ≤ l) :
    Flat.markDesired st l hl σ p j dB = dB := by
  rw [Flat.markDesired, dite_eq_right hj]

variable {dB : Vector Word MAX_N}

theorem pg_end {pos vac : Word} {pc : Vector Word MAX_N} (hpos : ¬pos ≤ l) :
    pg st l hl σ dB pos vac pc = Flat.regroup st (l + 1) pc dB := by
  unfold pg; rw [Flat.placeGroup, dite_eq_right hpos]

theorem pg_skip {pos vac : Word} {pc : Vector Word MAX_N} (hpos : pos ≤ l)
    (hd : Flat.get st.data pos ≠ σ) :
    pg st l hl σ dB pos vac pc = pg st l hl σ dB (pos + 1) vac pc := by
  unfold pg; rw [Flat.placeGroup, dite_eq_left hpos, ite_eq_left hd]

theorem pg_self {pos vac : Word} {pc : Vector Word MAX_N} (hpos : pos ≤ l)
    (hd : Flat.get st.data pos = σ) (hb : Flat.get dB pos = l) :
    pg st l hl σ dB pos vac pc = pg st l hl σ dB (pos + 1) vac (Flat.put pc pos pos) := by
  unfold pg; rw [Flat.placeGroup, dite_eq_left hpos, ite_eq_right (fun h => h hd), ite_eq_left hb]

theorem pg_nv {pos vac : Word} {pc : Vector Word MAX_N} (hpos : pos ≤ l)
    (hd : Flat.get st.data pos = σ) (hb : Flat.get dB pos ≠ l) :
    pg st l hl σ dB pos vac pc = nv st l hl σ dB pos vac pc := by
  unfold pg nv
  rw [Flat.placeGroup, dite_eq_left hpos, ite_eq_right (fun h => h hd), ite_eq_right hb]
  by_cases hv : Flat.nextVacant st l σ dB vac < st.size
  · simp only [hv, not_true_eq_false, ↓reduceIte]; rfl
  · simp only [hv, not_false_eq_true, ↓reduceIte]

theorem nv_next {pos x : Word} {pc : Vector Word MAX_N} (hx : x < st.size)
    (hc : ¬(Flat.get dB x = l ∧ ¬Flat.get st.data x = σ)) :
    nv st l hl σ dB pos x pc = nv st l hl σ dB pos (x + 1) pc := by
  have e : Flat.nextVacant st l σ dB x = Flat.nextVacant st l σ dB (x + 1) := by
    rw [Flat.nextVacant, dite_eq_left ⟨hx, hc⟩]
  unfold nv; rw [e]

theorem nv_found {pos x : Word} {pc : Vector Word MAX_N} (hx : x < st.size)
    (hb : Flat.get dB x = l) (hd : Flat.get st.data x ≠ σ) :
    nv st l hl σ dB pos x pc = pg st l hl σ dB (pos + 1) (x + 1) (Flat.put pc pos x) := by
  have e : Flat.nextVacant st l σ dB x = x := by
    rw [Flat.nextVacant, dite_eq_right (fun h => h.2 ⟨hb, hd⟩)]
  unfold nv; rw [e, ite_eq_left hx]

theorem nv_ge {pos x : Word} {pc : Vector Word MAX_N} (hx : ¬x < st.size) :
    nv st l hl σ dB pos x pc = none := by
  have e : Flat.nextVacant st l σ dB x = x := by
    rw [Flat.nextVacant, dite_eq_right (fun h => hx h.1)]
  unfold nv; rw [e, ite_eq_right hx]

end

/-! ## The end of phase C -/

-- `regroup` fails: `permute` fails.
theorem rg_none {st : Flat.St} (h : RG st none) (h0 : st.size ≠ 0) :
    Flat.permute st = (.assertionFailed, st) := by
  obtain ⟨p0, h1, h2⟩ := h
  rw [Flat.permute, ite_eq_right h0]
  simp only [h1, h2]

-- `regroup` gives `p`: the loop of `permute` starts with `p`, a bijection.
theorem rg_some {st : Flat.St} {p : Vector Word MAX_N} (h : RG st (some p)) (h0 : st.size ≠ 0)
    (hn : st.size.toNat ≤ MAX_N) (hp : PermOk st) :
    Flat.permute st = Flat.permuteLoop (2 * st.size.toNat) st (st.size - 1) p
      ∧ Bij st.size p := by
  obtain ⟨p0, h1, h2⟩ := h
  refine ⟨?_, regroup_bij hn hp h1 h2⟩
  rw [Flat.permute, ite_eq_right h0]
  simp only [h1, h2]

/-! ## The registers of phase C -/

-- `GC` for a state with the same leader registers.
theorem GC.step {S : Addr} {g : G} {F : MProp 64} {s : MachineData} {ra : Int64} {L L' : Lc}
    {l : Word} {t P : MachineData} (hG : GC S g F s ra L l t) (hF : Fm S g F s ra L' P)
    (h0 : L'.c0 = L.c0) (h1 : L'.c1 = L.c1) (hbp : P.regs.rbp = t.regs.rbp)
    (h12 : P.regs.r12 = t.regs.r12) (h13 : P.regs.r13 = t.regs.r13)
    (h14 : P.regs.r14 = t.regs.r14) (h15 : P.regs.r15 = t.regs.r15)
    (hbx : P.regs.rbx = t.regs.rbx) : GC S g F s ra L' l P :=
  ⟨⟨hF, hG.cc.lt, by rw [hbx]; exact hG.cc.bx, by rw [h15]; exact hG.cc.r15,
    by rw [h0]; exact hG.cc.c0, by rw [hbp]; exact hG.cc.bp, by rw [h13]; exact hG.cc.r13,
    by rw [h14]; exact hG.cc.r14⟩, by rw [h1]; exact hG.c1, by rw [h12]; exact hG.r12⟩

end Permute
end Bbu.Unit
