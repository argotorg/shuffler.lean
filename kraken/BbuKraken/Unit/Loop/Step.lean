module

public import BbuKraken.Unit.Loop.Inv
import all BbuKraken.Unit.Loop.Inv
public import BbuKraken.Unit.Loop.Ctor
import all BbuKraken.Unit.Loop.Ctor
public import BbuKraken.Unit.PermuteModel
import all BbuKraken.Unit.PermuteModel

@[expose] public section

/-!
# `buildBottomUp`: the model steps of the invariant (part P1)

`HInv` at the start, `Bud` in an iteration, `HInv` at the next head, and the preconditions of
the callees from `HInv` and `Bud`. Only the model: no asm.
-/

namespace Bbu.Flat

section
variable {st : St} {T : Word} {k x : Nat}

-- `T + 1` does not overflow below `MAX_N`.
private theorem toNat_add_one {T : Word} (h : T.toNat < MAX_N) : (T + 1).toNat = T.toNat + 1 := by
  rw [max_n] at h; bv_omega

-- `swapWith` keeps `pend` and `targetSize`.
theorem swapWith_pend (st : St) (p : Word) : (swapWith st p).2.pend = st.pend := by
  unfold Flat.swapWith; dsimp only; repeat' split
  all_goals rfl

theorem swapWith_tsize (st : St) (p : Word) :
    (swapWith st p).2.targetSize = st.targetSize := by
  unfold Flat.swapWith; dsimp only; repeat' split
  all_goals rfl

-- `generate` is done: one pending generation less, and the same `targetSize`.
theorem generate_keep {t : Word} (hd : (generate st t).1 = .done) :
    (generate st t).2.pend = st.pend - 1 ∧ (generate st t).2.targetSize = st.targetSize := by
  by_cases ht : t < st.targetSize
  case neg => rw [gen_fail ht] at hd; cases hd
  by_cases h1 : (produce st t).1 = .done
  case neg => rw [gen_prod ht h1] at hd; exact absurd hd h1
  obtain ⟨st', g, e⟩ := produce_grow h1
  have hX : (produce st t).2.pend = st.pend - 1
      ∧ (produce st t).2.targetSize = st.targetSize := by
    rw [e]; exact ⟨rfl, g.tsize⟩
  rw [gen_after ht h1]
  repeat' split
  all_goals first | exact hX | (rw [swapWith_pend, swapWith_tsize]; exact hX)

-- An iteration at `T < n` starts with a budget of 2 operations.
theorem HInv.bud (h : HInv st T x) (hT : T < st.targetSize) : Bud st T 2 x := by
  have := h.ops; rw [BitVec.lt_def] at hT; unfold Bud; omega

-- A final slot at `T`: the next head.
theorem HInv.succ (h : HInv st T x) (hT : T < st.size) : HInv st (T + 1) x := by
  have := h.f.size_le; have := h.f.n; have := h.ops
  rw [BitVec.lt_def] at hT
  have e := toNat_add_one (T := T) (by omega)
  exact ⟨h.f, by rw [e]; omega, by rw [e]; omega⟩

theorem Bud.mono (h : Bud st T (k + 1) x) : Bud st T k x := by
  unfold Bud at *; omega

-- The end of an iteration at `T < size`: the next head.
theorem Bud.next (hf : FInv st) (hT : T < st.size) (hb : Bud st T k x) : HInv st (T + 1) x := by
  have := hf.size_le; have := hf.n
  rw [BitVec.lt_def] at hT
  have e := toNat_add_one (T := T) (by omega)
  unfold Bud at hb
  exact ⟨hf, by rw [e]; omega, by rw [e]; omega⟩

-- `swapWith` uses one operation of the budget and keeps `pend` and `size`.
theorem Bud.swapWith {p : Word} (hf : FInv st) (hb : Bud st T (k + 1) x)
    (hd : (swapWith st p).1 = .done) :
    FInv (swapWith st p).2 ∧ Bud (swapWith st p).2 T k x ∧ (swapWith st p).2.pend = st.pend
      ∧ (swapWith st p).2.size = st.size := by
  obtain ⟨hf', htl, hs⟩ := hf.swapWith hd
  refine ⟨hf', ?_, swapWith_pend st p, hs⟩
  unfold Bud at *
  rw [htl, swapWith_pend, swapWith_tsize]; omega

-- `generate` in the iteration at `T`: one pending generation less, and a budget of 1.
theorem HInv.gen {y : Word} (h : HInv st T x) (hT : T < st.targetSize) (hp : st.pend ≠ 0)
    (hd : (generate st y).1 = .done) :
    FInv (generate st y).2 ∧ Bud (generate st y).2 T 1 x ∧ HInv (generate st y).2 T x
      ∧ (generate st y).2.pend.toNat + 1 = st.pend.toNat := by
  obtain ⟨hf', htl⟩ := h.f.generate hp hd
  obtain ⟨ep, et⟩ := generate_keep hd
  have ep' : (generate st y).2.pend.toNat + 1 = st.pend.toNat := by rw [ep]; bv_omega
  have := h.f.cnt; have c := hf'.cnt; have := h.le; have := h.ops
  rw [et] at c
  rw [BitVec.lt_def] at hT
  refine ⟨hf', ?_, ⟨hf', ?_, ?_⟩, ep'⟩
  · unfold Bud; rw [et]; omega
  · omega
  · rw [et]; omega

end

end Bbu.Flat

namespace Bbu.Unit
open Bbu.Sep
namespace Loop

section
variable {g : G} {T : Word} {k : Nat} {s : MachineData}

theorem trace_length_flat (ok : g.Ok) : (flat g).trace.length = g.h.nops.toNat := by
  have := ok.nops
  simp only [flat, List.length_map, List.length_take, Vector.length_toList]; omega

theorem generateA_of (ok : g.Ok) (h : Flat.HInv (flat g) T g.xo) (hp : g.h.pend ≠ 0) :
    generateA g s := by
  have ho := h.ops
  rw [trace_length_flat ok] at ho
  change g.h.nops.toNat + 2 * g.h.pend.toNat + 2 * (g.h.n.toNat - T.toNat)
    ≤ 4 * g.h.n.toNat + g.xo at ho
  have : g.h.pend.toNat ≠ 0 := fun e => hp (BitVec.eq_of_toNat_eq (by simpa using e))
  exact ⟨BitVec.lt_def.mp (h.f.size_lt hp), by omega, h.f.destOk⟩

theorem swapWithA_of (ok : g.Ok) (hf : Flat.FInv (flat g))
    (hb : Flat.Bud (flat g) T (k + 1) g.xo) :
    swapWithA g s := by
  unfold Flat.Bud at hb
  rw [trace_length_flat ok] at hb
  change g.h.nops.toNat + (k + 1) + 2 * g.h.pend.toNat + 2 * (g.h.n.toNat - (T.toNat + 1))
    ≤ 4 * g.h.n.toNat + g.xo at hb
  exact ⟨by omega, hf.destOk⟩

-- `hrd`: the ghost `p0` is the result of `readDestinations`. `harr`: the array at `rsi` holds
-- `dest` below `size` (the copy loop at `.1`), so it holds `p0`.
theorem permuteA_of (ok : g.Ok) (h : Flat.HInv (flat g) T g.xo) (hp : g.h.pend = 0)
    {p0 : Vector Word MAX_N} (hrd : Flat.readDestinations (flat g) 0 Flat.initial = some p0)
    (harr : ∀ i < g.h.len.toNat,
      rd s.dmem (rsi s + BitVec.ofNat 64 (8 * i)) = Flat.get g.h.dest (BitVec.ofNat 64 i)) :
    permuteA p0 g s := by
  have ho := h.ops
  rw [trace_length_flat ok] at ho
  change g.h.nops.toNat + 2 * g.h.pend.toNat + 2 * (g.h.n.toNat - T.toNat)
    ≤ 4 * g.h.n.toNat + g.xo at ho
  have := ok.len
  have : g.h.len.toNat ≤ g.h.n.toNat := h.f.size_le
  have hn : (flat g).size.toNat ≤ MAX_N := Nat.le_trans ok.len ok.xs
  have hr := Permute.readDestinations_spec (flat g) hn 0 _ _ hrd
  refine ⟨by omega, h.f.destOk, Permute.permOk_bij hn (h.f.permOk (h.f.size_eq hp)) hrd,
    fun i hi => ?_⟩
  have hi' : BitVec.ofNat 64 i < (flat g).size := by
    simp only [MAX_N] at hn
    show BitVec.ofNat 64 i < g.h.len
    rw [BitVec.lt_def, BitVec.toNat_ofNat]
    omega
  rw [harr i hi, hr _ hi', ite_eq_left (by bv_omega)]
  rfl

end

end Loop
end Bbu.Unit
