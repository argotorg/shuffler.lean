import BbuKraken.Unit.Permute.ML

/-!
# `permute`: facts of the model for phase D

* `mD_eq`: the variant of phase D is `mu` of the model permutation `p`.
* The steps of `permuteLoop`, `permuteStep`, `misplacedBelow`, `exchange` and
  `blockSwapUnreachable`.
* `flat_swap`: the stores of `Flat.stackSwap` on the ghost.
-/

namespace Bbu.Unit
open Bbu.Sep
namespace Permute

/-! ## The variant -/

theorem memVec_eq {S : Addr} {g : G} {F : MProp 64} {s : MachineData} {ra : Int64} {L : Lc}
    {t : MachineData} (h : Fm S g F s ra L t) : memVec s t = L.P := by
  apply Vector.ext; intro i hi
  simp only [memVec, Vector.getElem_ofFn]
  exact h.rdP hi rfl

-- `mu` reads the offsets below `n` only.
theorem mu_agB {n : Word} {u v : Vector Word MAX_N} (h0 : 0 < n) (h : AgB n u v) :
    mu (n - 1) u = mu (n - 1) v := by
  have e : misplaced (n - 1) u = misplaced (n - 1) v := by
    unfold misplaced
    refine countP_congr fun i hi => ?_
    have hlt : BitVec.ofNat 64 i < n := by
      have : (BitVec.ofNat 64 i).toNat = i := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := (n - 1).isLt; omega)
      bv_omega
    rw [h _ hlt]
  unfold mu; rw [e, h _ (by bv_omega)]

theorem mD_eq {S : Addr} {g g' : G} {F : MProp 64} {s : MachineData} {ra : Int64} {L : Lc}
    {t : MachineData} {p : Vector Word MAX_N} (h : Fm S g' F s ra L t) (h0 : 0 < g.h.len)
    (hag : AgB g.h.len L.P p) : mD s g t = mu (g.h.len - 1) p := by
  rw [mD, memVec_eq h, mu_agB h0 hag]

-- `mD` reads the memory only: a state with the memory of `t`.
theorem mD_mk {s : MachineData} {g : G} {t : MachineData} {r z st} :
    mD s g { regs := r, zmms := z, status := st, dmem := t.dmem } = mD s g t := rfl

-- `mD` reads the memory only: the state `t` with the memory `m`.
theorem mD_dmem {s g : _} {r z st m} (t : MachineData) :
    mD s g { regs := r, zmms := z, status := st, dmem := m } = mD s g { t with dmem := m } := rfl

-- The variant goal of an edge of phase D without stores (`mD_mk`).
macro "pd_dec" : tactic => `(tactic| (
  simp only [V, wC, mD_mk, Names.permute, String.reduceEq, ↓reduceIte, Nat.reducePow,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, true_or, or_true, or_false, false_or, true_and,
    and_true]
  try omega))

-- `leaq -1(%r)` as `kvcgen64` gives it. Rewrite it before `symexec_norm`:
-- the kernel check of the proof of `symexec_norm` on this form uses more than 12 GB.
theorem add_m1i (x : Word) : x + BitVec.ofInt 64 (-1 : Int64).toInt = x - 1#64 := by
  rw [show (-1 : Int64).toInt = -1 from rfl]; bv_omega

/-! ## The loop of `permute` -/

theorem loop_succ (f : Nat) (st : Flat.St) (top : Word) (p : Vector Word MAX_N) :
    Flat.permuteLoop (f + 1) st top p = after f top (Flat.permuteStep st top p) := by
  cases h : Flat.permuteStep st top p <;> simp [Flat.permuteLoop, h, after]

theorem after_cont (f : Nat) (top : Word) (st : Flat.St) (p : Vector Word MAX_N) :
    after f top (.cont st p) = Flat.permuteLoop f st top p := rfl

theorem after_ret (f : Nat) (top : Word) (r : Flat.Status × Flat.St) :
    after f top (.ret r) = r := rfl

-- `permutation[top] != top`: `exchange` of `permutation[top]`.
theorem step_ne {st : Flat.St} {top : Word} {p : Vector Word MAX_N} (h : Flat.get p top ≠ top) :
    Flat.permuteStep st top p = Flat.exchange st top p (Flat.get p top) := by
  rw [Flat.permuteStep]; dsimp only; rw [ite_eq_right h]

-- `permutation[top] == top`: the `candidate` loop.
theorem step_eq {st : Flat.St} {top : Word} {p : Vector Word MAX_N} (h : Flat.get p top = top) :
    Flat.permuteStep st top p = if Flat.misplacedBelow p top top = top then .ret (.done, st)
      else Flat.exchange st top p (Flat.misplacedBelow p top top) := by
  rw [Flat.permuteStep]; dsimp only; rw [ite_eq_left h]

theorem mb_zero (p : Vector Word MAX_N) (top : Word) : Flat.misplacedBelow p top 0 = top := by
  rw [Flat.misplacedBelow, dite_eq_left rfl]

theorem mb_in {p : Vector Word MAX_N} {top c : Word} (h0 : c ≠ 0) (h : Flat.get p (c - 1) = c - 1) :
    Flat.misplacedBelow p top c = Flat.misplacedBelow p top (c - 1) := by
  rw [Flat.misplacedBelow, dite_eq_right h0, ite_eq_right (fun e => e h)]

theorem mb_out {p : Vector Word MAX_N} {top c : Word} (h0 : c ≠ 0)
    (h : Flat.get p (c - 1) ≠ c - 1) : Flat.misplacedBelow p top c = c - 1 := by
  rw [Flat.misplacedBelow, dite_eq_right h0, ite_eq_left h]

/-! ## `exchange` -/

section
variable {st : Flat.St} {top pos : Word} {p : Vector Word MAX_N}

-- Equal slots: no swap.
theorem ex_eq (h : Flat.get st.data pos = Flat.get st.data (st.size - 1)) :
    Flat.exchange st top p pos = .cont (Flat.swapDestinations st pos top) (swapP p top pos) := by
  simp only [Flat.exchange, h, ite_true]; rfl

-- The slot at `pos` is too deep.
theorem ex_unr (hne : Flat.get st.data pos ≠ Flat.get st.data (st.size - 1))
    (hr : Flat.isSwapReachable st pos = false) :
    Flat.exchange st top p pos = .ret (Flat.blockSwapUnreachable st pos) := by
  simp only [Flat.exchange, hne, hr, ite_false, Bool.not_false, ite_true]

-- A swap.
theorem ex_sw (hne : Flat.get st.data pos ≠ Flat.get st.data (st.size - 1))
    (hr : Flat.isSwapReachable st pos = true) :
    Flat.exchange st top p pos
      = .cont (Flat.swapDestinations (Flat.stackSwap st pos) pos top) (swapP p top pos) := by
  simp only [Flat.exchange, hne, hr, ite_false, Bool.not_true]; rfl

end

-- `blockSwapUnreachable` with `size - pos - 1 > 16`.
theorem bsu_eq {st : Flat.St} {pos : Word} (h : ¬(st.size - pos - 1#64 ≤ 16#64)) :
    Flat.blockSwapUnreachable st pos
      = (.blocked, { st with blockedOffset := pos, blockedExcess := st.size - pos - 17#64 }) := by
  have e : Flat.depthOf st pos - Flat.maxSwapDepth = st.size - pos - 17#64 := by
    simp only [Flat.depthOf, Flat.maxSwapDepth]; bv_omega
  rw [Flat.blockSwapUnreachable, Flat.block, e, ite_eq_right (by bv_omega)]

/-! ## The permutation -/

-- The offset at `.LB.Emission.permute.24` is misplaced: the swap keeps `Bij` and makes `mu` smaller.
theorem Mis.step {n pos : Word} {p : Vector Word MAX_N} (hn : n.toNat ≤ MAX_N) (hb : Bij n p)
    (h : Mis n pos p) :
    Bij n (swapP p (n - 1) pos) ∧ mu (n - 1) (swapP p (n - 1) pos) < mu (n - 1) p :=
  ⟨swapP_bij hn hb (by have := h.1; bv_omega) h.1, swapP_mu hn hb h.1 h.2.1 h.2.2⟩

-- The two stores of `.LB.Emission.permute.22` into `permutation`.
theorem agB_swap {n top pos : Word} {P p : Vector Word MAX_N} (h : AgB n P p) (ht : top < n)
    (hpos : pos < n) (htM : top.toNat < MAX_N) (hpM : pos.toNat < MAX_N) :
    AgB n ((P.set pos.toNat P[top.toNat] hpM).set top.toNat P[pos.toNat] htM) (swapP p top pos) := by
  have e1 : P[top.toNat] = Flat.get p top := (get_eq _ _ htM).symm.trans (h top ht)
  have e2 : P[pos.toNat] = Flat.get p pos := (get_eq _ _ hpM).symm.trans (h pos hpos)
  rw [e1, e2]
  exact agB_set (agB_set h hpM _) htM _

-- `swapD` keeps the destinations below `n`.
theorem ltB_swapD {n a b : Word} {d : Vector Word MAX_N} (h : LtB n d) (ha : a < n) (hb : b < n) :
    LtB n (swapD d a b) :=
  ltB_put (ltB_put h a (h b hb)) b (h a ha)


/-! ## The registers of phase D -/

-- `DC` for a state with the same memory, `rsp`, `r15`, `rbx`, `rcx` and `rsi`.
theorem DC.next {S : Addr} {g g' : G} {F : MProp 64} {s : MachineData} {ra : Int64} {L : Lc}
    {p : Vector Word MAX_N} {t P : MachineData} (h : DC S g F s ra g' L p t)
    (hm : P.dmem = t.dmem) (hsp : P.regs.rsp = t.regs.rsp) (h15 : P.regs.r15 = t.regs.r15)
    (hbx : P.regs.rbx = t.regs.rbx) (hcx : P.regs.rcx = t.regs.rcx)
    (hsi : P.regs.rsi = t.regs.rsi) : DC S g F s ra g' L p P :=
  ⟨h.fm.next hm hsp, h.ok, h.keep, h.len, h.pos, h.dl, by rw [h15]; exact h.r15,
    by rw [hbx]; exact h.bx, by rw [hcx]; exact h.cx, by rw [hsi]; exact h.si, h.agP, h.bij⟩

end Permute
end Bbu.Unit
