module

/-
The primitives of a lifted function (a Kraken program turned into a Lean function over
loads and stores). A load or a store of 8 bytes at an unmapped address gives `none`; the
lifted function is then `none`. The names and shapes are those of the specs of Kraken, so
that a proof of the code against the lifted function meets the same terms.
-/
public import Kraken.StateCfg

@[expose] public section

namespace Lift

/-- `movq (a), %r`: the 8 bytes at `a`, or `none` if `a` is not mapped. -/
def ld64 (m : Mem 64) (a : BitVec 64) : Option (BitVec 64) :=
  (m.loadInt a 8).map (BitVec.ofInt 64)

/-- `movq %r, (a)`: the memory with the 8 bytes at `a` changed, or `none` if `a` is not mapped. -/
def st64 (m : Mem 64) (a v : BitVec 64) : Option (Mem 64) :=
  if (m.loadInt a 8).isSome then some (m.storeInt a 8 v.toInt) else none

theorem exists_least {p : Nat → Prop} (h : ∃ n, p n) : ∃ n, p n ∧ ∀ m, m < n → ¬ p m := by
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hm : ∃ m, m < n ∧ p m
    · obtain ⟨m, hm1, hm2⟩ := hm
      exact ih m hm1 hm2
    · exact ⟨n, hn, fun m hm' hp => hm ⟨m, hm', hp⟩⟩

theorem ld64_eq_some {m : Mem 64} {a v : BitVec 64} (h : ld64 m a = some v) :
    ∃ i, m.loadInt a 8 = some i ∧ BitVec.ofInt 64 i = v := by
  unfold ld64 at h
  exact Option.map_eq_some_iff.mp h

theorem st64_eq_some {m m' : Mem 64} {a v : BitVec 64} (h : st64 m a v = some m') :
    (m.loadInt a 8).isSome = true ∧ m.storeInt a 8 v.toInt = m' := by
  unfold st64 at h
  split at h
  · exact ⟨‹_›, Option.some.inj h⟩
  · exact absurd h (by simp)

open Classical in
/-- The least fuel with which `f` gives `r`, if there is one. The variant of a loop. -/
noncomputable def NR {α : Type} (f : Nat → Option α) (r : α) : Option Nat :=
  if h : ∃ n, f n = some r then some (Classical.choose (exists_least h)) else none

theorem NR_spec {α : Type} {f : Nat → Option α} {r : α} {m : Nat} (h : NR f r = some m) :
    f m = some r ∧ ∀ j, j < m → f j ≠ some r := by
  unfold NR at h
  by_cases hex : ∃ n, f n = some r
  · rw [dif_pos hex] at h
    cases h
    exact Classical.choose_spec (exists_least hex)
  · rw [dif_neg hex] at h
    cases h

theorem NR_pred {α : Type} {f g : Nat → Option α} {r : α} {k : Nat}
    (hs : ∀ n, f (n + 1) = g n) (h : NR f r = some (k + 1)) : NR g r = some k := by
  obtain ⟨h1, h2⟩ := NR_spec h
  have hg : ∃ n, g n = some r := ⟨k, by rw [← hs]; exact h1⟩
  unfold NR
  rw [dif_pos hg]
  congr 1
  obtain ⟨c1, c2⟩ := Classical.choose_spec (exists_least hg)
  generalize Classical.choose (exists_least hg) = c at *
  have hgk : g k = some r := by rw [← hs]; exact h1
  apply Nat.le_antisymm
  · exact Nat.le_of_not_lt fun hlt => c2 k hlt hgk
  · exact Nat.le_of_not_lt fun hlt => h2 (c + 1) (by omega) (by rw [hs]; exact c1)

theorem NR_zero {α : Type} {f : Nat → Option α} {r : α} {m : Nat} (h0 : f 0 = none)
    (h : NR f r = some m) : ∃ k, m = k + 1 := by
  obtain ⟨h1, -⟩ := NR_spec h
  cases m with
  | zero => rw [h0] at h1; exact absurd h1 (by simp)
  | succ k => exact ⟨k, rfl⟩

/-- The least fuel with which the block `B` run from `st` gives `r`. -/
noncomputable def NRb {σ : Type} (B : Nat → σ → Option σ) (st r : σ) : Option Nat :=
  NR (fun n => B n st) r

theorem NRb_spec {σ : Type} {B : Nat → σ → Option σ} {st r : σ} {m : Nat}
    (h : NRb B st r = some m) : B m st = some r := (NR_spec h).1

theorem NRb_zero {σ : Type} {B : Nat → σ → Option σ} {st r : σ} {m : Nat}
    (h0 : B 0 st = none) (h : NRb B st r = some m) : ∃ k, m = k + 1 :=
  NR_zero h0 h

theorem NRb_pred {σ : Type} {B B' : Nat → σ → Option σ} {st st' r : σ} {k : Nat}
    (hs : ∀ n, B (n + 1) st = B' n st') (h : NRb B st r = some (k + 1)) :
    NRb B' st' r = some k := NR_pred (f := fun n => B n st) (g := fun n => B' n st') hs h


theorem NRb_of_run {σ : Type} {B : Nat → σ → Option σ} {st r : σ} {n : Nat}
    (h : B n st = some r) : ∃ m, NRb B st r = some m := by
  unfold NRb NR
  rw [dif_pos ⟨n, h⟩]
  exact ⟨_, rfl⟩

end Lift
