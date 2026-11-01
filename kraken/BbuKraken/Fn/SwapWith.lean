module

public import BbuKraken.Fn.SwapWithLemmas
import all BbuKraken.Fn.SwapWithLemmas
public import BbuKraken.ModelLemmas
import all BbuKraken.ModelLemmas

@[expose] public section
open Std.WP Lean.Order
open scoped Program.WP
namespace Bbu
set_option experimental.vcgen true

namespace SwapWithFn

theorem swapWith_err {st : St} {pos : Nat}
    (h : st.len ≤ pos ∨ st.dest pos = pos ∨ st.len - 1 - pos < 1 ∨ MAX_SWAP_DEPTH < st.len - 1 - pos) :
    swapWith st pos = .error .assertion := by
  unfold swapWith
  split
  · rfl
  · dsimp only; split
    · rfl
    · simp only [MAX_SWAP_DEPTH] at *; omega

theorem slot_addr (S r : BitVec 64) (k : Nat) :
    wordAt S (k + r.toNat) = S + r * 8#64 + BitVec.ofNat 64 (8 * k) := by
  simp only [wordAt]; bv_omega

theorem depth_big (L r : BitVec 64) (hlt : r.toNat < L.toNat)
    (h : ((L - r + -2#64 - 15#64).toNat : Int) = ((L - r + -2#64).toNat : Int) - 15
      ∧ ¬ L - r + -2#64 - 15#64 = 0#64) :
    L.toNat - 1 - r.toNat < 1 ∨ 16 < L.toNat - 1 - r.toNat := by
  bv_omega

theorem depth_ok (L r : BitVec 64) (hlt : r.toNat < L.toNat)
    (h : ¬ ((L - r + -2#64 - 15#64).toNat : Int) = ((L - r + -2#64).toNat : Int) - 15
      ∨ L - r + -2#64 - 15#64 = 0#64) :
    1 ≤ L.toNat - 1 - r.toNat ∧ L.toNat - 1 - r.toNat ≤ 16 := by
  bv_omega

theorem swapWith_eq {st : St} {pos : Nat} (h1 : pos < st.len) (h2 : st.dest pos ≠ pos)
    (h3 : 1 ≤ st.len - 1 - pos) (h4 : st.len - 1 - pos ≤ MAX_SWAP_DEPTH) :
    swapWith st pos = .ok (swapDestinations { st with
      slots := (st.slots.set pos ⟨st.val (st.len - 1), st.dest pos⟩).set (st.len - 1)
        ⟨st.val pos, st.dest (st.len - 1)⟩
      trace := st.trace ++ [.swap (st.len - 1 - pos)] } pos (st.len - 1)) := by
  unfold swapWith
  rw [ite_eq_right (by omega)]
  dsimp only
  rw [ite_eq_right (by omega)]

-- The state after `swapWith`: the slots `pos` and `top` change places, with their
-- destinations, and `positionOf` follows.
theorem swapDest_swap (st : St) {pos top : Nat} (hp : pos < top) (ht : top < st.len) (tr : List Op) :
    swapDestinations { st with
      slots := (st.slots.set pos ⟨st.val top, st.dest pos⟩).set top ⟨st.val pos, st.dest top⟩
      trace := tr } pos top = { st with
      slots := (st.slots.set pos ⟨st.val top, st.dest top⟩).set top ⟨st.val pos, st.dest pos⟩
      positionOf := (st.positionOf.set (st.dest top) (some pos)).set (st.dest pos) (some top)
      trace := tr } := by
  rw [swapDest_eq (by simp [St.len] at ht ⊢; omega) (by simp [St.len] at ht ⊢; omega)]
  simp only [St.len] at ht
  simp [St.val, St.dest, Nat.ne_of_gt hp, show pos < st.slots.length by omega, ht]
  rw [List.set_comm _ _ (Nat.ne_of_lt hp).symm, List.set_set, List.set_set]

open Kit

-- Two reads at equal addresses.
theorem rd_addr {m : Mem 64} {a b : Addr} (h : a = b) : rd m a = rd m b := h ▸ rfl

theorem pos_addr (S r : Addr) :
    wordAt S (DEST + r.toNat) = S + r * 8#64 + 56#64 := by
  simp only [wordAt, DEST_eq]; bv_omega

-- The addresses of the stores, as words from a base.
theorem w_r (X r : Addr) : wordAt X r.toNat = X + r * 8#64 := by
  simp only [wordAt]; bv_omega

theorem w_top (X L : Addr) (h0 : 0 < L.toNat) : wordAt X (L.toNat - 1) = X + (L + -1#64) * 8#64 := by
  simp only [wordAt]; bv_omega

theorem top_addr' (S L : Addr) (h0 : 0 < L.toNat) :
    wordAt S (DEST + (L.toNat - 1)) = S + (L + -1#64) * 8#64 + 56#64 := by
  simp only [wordAt, DEST_eq]; bv_omega

theorem p_addr (S X : Addr) : wordAt S (POS + X.toNat) = S + X * 8#64 + 8248#64 := by
  simp only [wordAt, POS_eq]; bv_omega

theorem optOf_some {w : Word} (h : w ≠ -1#64) : optOf w = some w.toNat := by
  simp only [optOf, h, ↓reduceIte]

end SwapWithFn

end Bbu
