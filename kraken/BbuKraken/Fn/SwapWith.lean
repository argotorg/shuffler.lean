import BbuKraken.Fn.SwapWithLemmas
import BbuKraken.ModelLemmas
open Std.WP Lean.Order
open scoped Program.WP
namespace Bbu
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

namespace SwapWithFn

-- The state at `.LB12`, `.LB13` and `.LB14`: the memory and the registers of the
-- call, and an assertion error in the model.
def Fail (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  t.dmem = (s.pushRa ra).dmem ∧ rsp t = rsp s - 8#64
    ∧ (∀ q, q ∉ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .rsp] →
      t.regs.get64 q = s.regs.get64 q)
    ∧ swapWith (st s) (rsi s).toNat = .error .assertion

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
  simp only [St.len] at ht
  simp [swapDestinations, St.val, St.dest, Nat.ne_of_gt hp, show pos < st.slots.length by omega, ht]
  rw [List.set_comm _ _ (Nat.ne_of_lt hp).symm, List.set_set, List.set_set]

open Kit

-- The registers that `swapWith` saves, in the order of the pushes.
abbrev regs : List Reg64 := [.r12, .rbp, .rbx]

-- Two reads at equal addresses.
theorem rd_addr {m : Mem 64} {a b : Addr} (h : a = b) : rd m a = rd m b := h ▸ rfl

section
variable {s : MachineData} {ra : Int64}

-- The memory after the stores of `swapWith`, in the form of the `kvcgen64` goals.
def fin (s : MachineData) (ra : Int64) : Mem 64 :=
  let S := s.regs.rdi.toBitVec
  let r := s.regs.rsi.toBitVec
  let sp := s.regs.rsp.toBitVec
  let M0 := Mem.storeInt s.dmem (sp - 8#64) 8 ra.toBitVec.toInt
  let L := rd M0 S
  let M3 := ((M0.storeInt (sp - 8#64 - 8#64) 8 s.regs.r12.toBitVec.toInt).storeInt
    (sp - 8#64 - 8#64 - 8#64) 8 s.regs.rbp.toBitVec.toInt).storeInt
    (sp - 8#64 - 8#64 - 8#64 - 8#64) 8 s.regs.rbx.toBitVec.toInt
  let OP := rd M3 (S + 48#64) + (rd M3 (S + 16#64) + rd M3 (S + 16#64) * 2#64) * 4#64
  let M4 := M3.storeInt OP 1 0
  let M5 := M4.storeInt (OP + 1#64) 1 ((L - r - 1#64).take 8).toInt
  let M6 := M5.storeInt (OP + 4#64) 4 0
  let M7 := M6.storeInt (OP + 8#64) 1 1
  let M8 := M7.storeInt (OP + 9#64) 1 5
  let M9 := M8.storeInt (S + 16#64) 8 (1#64 + rd M8 (S + 16#64)).toInt
  let D := rd M9 (S + 64#64)
  let M10 := M9.storeInt (D + r * 8#64) 8 (BitVec.toInt (rd M9 (D + (L + -1#64) * 8#64)))
  let D10 := rd M10 (S + 64#64)
  let M11 := M10.storeInt (D10 + (L + -1#64) * 8#64) 4
    (BitVec.ofInt 32 (M9.loadInt (D + r * 8#64) 4).get!).toInt
  let M12 := M11.storeInt (D10 + (L + -1#64) * 8#64 + 4#64) 1
    ((BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.ofInt 8 (M9.loadInt (D + r * 8#64 + 4#64) 1).get!))).take 8).toInt
  let M13 := M12.storeInt (D10 + (L + -1#64) * 8#64 + 5#64) 1
    ((BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.ofInt 8 (M9.loadInt (D + r * 8#64 + 5#64) 1).get!))).take 8).toInt
  let M14 := M13.storeInt (S + r * 8#64 + 72#64) 8 (BitVec.toInt (rd M13 (S + L * 8#64 + 64#64)))
  let M15 := M14.storeInt (S + (L + -1#64) * 8#64 + 72#64) 8
    (BitVec.toInt (rd M13 (S + r * 8#64 + 72#64)))
  let M16 := M15.storeInt (S + rd M15 (S + r * 8#64 + 72#64) * 8#64 + 8264#64) 8 r.toInt
  M16.storeInt (S + rd M13 (S + r * 8#64 + 72#64) * 8#64 + 8264#64) 8 (L + -1#64).toInt

-- The same memory, with the reads done in `s.dmem`.
def finC (s : MachineData) (ra : Int64) : Mem 64 :=
  let S := s.regs.rdi.toBitVec
  let r := s.regs.rsi.toBitVec
  let L := rd s.dmem S
  let N := rd s.dmem (S + 16#64)
  let D := rd s.dmem (S + 64#64)
  let OP := rd s.dmem (S + 48#64) + (N + N * 2#64) * 4#64
  let T := rd s.dmem (S + L * 8#64 + 64#64)
  let E := rd s.dmem (S + r * 8#64 + 72#64)
  let a := D + r * 8#64
  let b := D + (L + -1#64) * 8#64
  ((((((((((((((pushes s ra regs).storeInt OP 1 0).storeInt (OP + 1#64) 1
    ((L - r - 1#64).take 8).toInt).storeInt (OP + 4#64) 4 0).storeInt (OP + 8#64) 1 1).storeInt
    (OP + 9#64) 1 5).storeInt (S + 16#64) 8 (1#64 + N).toInt).storeInt a 8
    (rd s.dmem b).toInt).storeInt b 4 (BitVec.ofInt 32 (s.dmem.loadInt a 4).get!).toInt).storeInt
    (b + 4#64) 1 ((BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.ofInt 8 (s.dmem.loadInt (a + 4#64) 1).get!))).take 8).toInt).storeInt
    (b + 5#64) 1 ((BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.ofInt 8 (s.dmem.loadInt (a + 5#64) 1).get!))).take 8).toInt).storeInt
    (S + r * 8#64 + 72#64) 8 T.toInt).storeInt (S + (L + -1#64) * 8#64 + 72#64) 8 E.toInt).storeInt
    (S + T * 8#64 + 8264#64) 8 r.toInt).storeInt (S + E * 8#64 + 8264#64) 8 (L + -1#64).toInt

-- The facts of `Pre` for `bv_omega`.
theorem facts (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat < (rd s.dmem s.regs.rdi.toBitVec).toNat) :
    32 ≤ s.regs.rsp.toBitVec.toNat
    ∧ (s.regs.rsp.toBitVec.toNat ≤ s.regs.rdi.toBitVec.toNat ∨
      s.regs.rdi.toBitVec.toNat + 16456 ≤ s.regs.rsp.toBitVec.toNat - 32)
    ∧ s.regs.rdi.toBitVec.toNat + 16456 ≤ 2 ^ 64
    ∧ (rd s.dmem s.regs.rdi.toBitVec).toNat ≤ nOf s.dmem s.regs.rdi.toBitVec
    ∧ nOf s.dmem s.regs.rdi.toBitVec ≤ 1024
    ∧ (rd s.dmem (s.regs.rdi.toBitVec + 16#64)).toNat < 6 * nOf s.dmem s.regs.rdi.toBitVec
    ∧ (rd s.dmem (s.regs.rdi.toBitVec + 64#64)).toNat + 8 * nOf s.dmem s.regs.rdi.toBitVec ≤ 2 ^ 64
    ∧ ((rd s.dmem (s.regs.rdi.toBitVec + 64#64)).toNat + 8 * nOf s.dmem s.regs.rdi.toBitVec
          ≤ s.regs.rdi.toBitVec.toNat
        ∨ s.regs.rdi.toBitVec.toNat + 16456 ≤ (rd s.dmem (s.regs.rdi.toBitVec + 64#64)).toNat)
    ∧ (s.regs.rsp.toBitVec.toNat ≤ (rd s.dmem (s.regs.rdi.toBitVec + 64#64)).toNat
      ∨ (rd s.dmem (s.regs.rdi.toBitVec + 64#64)).toNat + 8 * nOf s.dmem s.regs.rdi.toBitVec
        ≤ s.regs.rsp.toBitVec.toNat - 32)
    ∧ (rd s.dmem (s.regs.rdi.toBitVec + 48#64)).toNat + 72 * nOf s.dmem s.regs.rdi.toBitVec ≤ 2 ^ 64
    ∧ ((rd s.dmem (s.regs.rdi.toBitVec + 48#64)).toNat + 72 * nOf s.dmem s.regs.rdi.toBitVec
          ≤ s.regs.rdi.toBitVec.toNat
        ∨ s.regs.rdi.toBitVec.toNat + 16456 ≤ (rd s.dmem (s.regs.rdi.toBitVec + 48#64)).toNat)
    ∧ (s.regs.rsp.toBitVec.toNat ≤ (rd s.dmem (s.regs.rdi.toBitVec + 48#64)).toNat
      ∨ (rd s.dmem (s.regs.rdi.toBitVec + 48#64)).toNat + 72 * nOf s.dmem s.regs.rdi.toBitVec
        ≤ s.regs.rsp.toBitVec.toNat - 32)
    ∧ ((rd s.dmem (s.regs.rdi.toBitVec + 64#64)).toNat + 8 * nOf s.dmem s.regs.rdi.toBitVec
          ≤ (rd s.dmem (s.regs.rdi.toBitVec + 48#64)).toNat
        ∨ (rd s.dmem (s.regs.rdi.toBitVec + 48#64)).toNat + 72 * nOf s.dmem s.regs.rdi.toBitVec
          ≤ (rd s.dmem (s.regs.rdi.toBitVec + 64#64)).toNat) := by
  have hw := hpre.1
  have hfr := hpre.2.1
  have hle := hfr.le
  have hsep := hfr.sep_struct (by decide)
  have hst := hw.struct_lt
  have hlen := hw.len_le
  have hn : _ ≤ 1024 := hw.n_le
  have hnlt : (st s).trace.length < cap s := hpre.2.2.2
  simp only [cap, st, nops_stOf] at hnlt
  bbu_norm at hlen
  have hn0 : 0 < nOf s.dmem (rdi s) := by bbu_norm; omega
  have hsd := hw.sep_data hn0
  have hso := hw.sep_ops hn0
  have hdo := hw.sep_data_ops hn0
  have hdl := hw.data_lt
  have hol := hw.ops_lt
  have hfd := hfr.sep_data (by decide) hn0
  have hfo := hfr.sep_ops (by decide) hn0
  simp only [swapWithF, WORDS_eq, dataOf, opsOf] at hle hsep hst hsd hso hdo hdl hol hfd hfo
  bbu_norm at hle hsep hst hn hnlt hsd hso hdo hdl hol hfd hfo
  exact ⟨hle, hsep, hst, hlen, hn, hnlt, hdl, hsd, hfd, hol, hso, hfo, hdo⟩

-- The destination of a slot is below `n`: `positionOf` holds it.
theorem dest_lt (hpre : Pre swapWithF swapWithA s) {i : Nat}
    (hi : i < (rd s.dmem s.regs.rdi.toBitVec).toNat) :
    (rd s.dmem (wordAt s.regs.rdi.toBitVec (DEST + i))).toNat < nOf s.dmem s.regs.rdi.toBitVec := by
  have hp := hpre.2.2.1
  have h0 : i < (rd s.dmem (wordAt (rdi s) 0)).toNat := by bbu_norm; exact hi
  have hlen : i < (st s).dests.length := by rw [St.length_dests, len_stOf]; exact h0
  have h := positionOf_lt hp ((hp.iff _ i).2 ⟨hlen, rfl⟩)
  have he : (st s).dests[i] = (st s).dest i := by rw [St.dest_eq]; simp [hlen]
  rw [he, dest_stOf h0, n_envOf] at h
  exact h

theorem top_addr (S L : Addr) (h0 : 0 < L.toNat) :
    wordAt S (DEST + (L.toNat - 1)) = S + L * 8#64 + 64#64 := by
  simp only [wordAt, DEST_eq]; bv_omega

theorem pos_addr (S r : Addr) :
    wordAt S (DEST + r.toNat) = S + r * 8#64 + 72#64 := by
  simp only [wordAt, DEST_eq]; bv_omega

-- The separations of `facts` as distances, region by region: the frame below `rsp`, the
-- struct, the data and the operations.
theorem dist (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat < (rd s.dmem s.regs.rdi.toBitVec).toNat) :
    (32 ≤ (s.regs.rdi.toBitVec - (s.regs.rsp.toBitVec - 32#64)).toNat
      ∧ 16456 ≤ (s.regs.rsp.toBitVec - 32#64 - s.regs.rdi.toBitVec).toNat)
    ∧ (16456 ≤ (rd s.dmem (s.regs.rdi.toBitVec + 64#64) - s.regs.rdi.toBitVec).toNat
      ∧ 8 * nOf s.dmem s.regs.rdi.toBitVec
        ≤ (s.regs.rdi.toBitVec - rd s.dmem (s.regs.rdi.toBitVec + 64#64)).toNat)
    ∧ (16456 ≤ (rd s.dmem (s.regs.rdi.toBitVec + 48#64) - s.regs.rdi.toBitVec).toNat
      ∧ 72 * nOf s.dmem s.regs.rdi.toBitVec
        ≤ (s.regs.rdi.toBitVec - rd s.dmem (s.regs.rdi.toBitVec + 48#64)).toNat)
    ∧ (32 ≤ (rd s.dmem (s.regs.rdi.toBitVec + 64#64) - (s.regs.rsp.toBitVec - 32#64)).toNat
      ∧ 8 * nOf s.dmem s.regs.rdi.toBitVec
        ≤ (s.regs.rsp.toBitVec - 32#64 - rd s.dmem (s.regs.rdi.toBitVec + 64#64)).toNat)
    ∧ (32 ≤ (rd s.dmem (s.regs.rdi.toBitVec + 48#64) - (s.regs.rsp.toBitVec - 32#64)).toNat
      ∧ 72 * nOf s.dmem s.regs.rdi.toBitVec
        ≤ (s.regs.rsp.toBitVec - 32#64 - rd s.dmem (s.regs.rdi.toBitVec + 48#64)).toNat)
    ∧ (8 * nOf s.dmem s.regs.rdi.toBitVec
        ≤ (rd s.dmem (s.regs.rdi.toBitVec + 48#64) - rd s.dmem (s.regs.rdi.toBitVec + 64#64)).toNat
      ∧ 72 * nOf s.dmem s.regs.rdi.toBitVec
        ≤ (rd s.dmem (s.regs.rdi.toBitVec + 64#64) - rd s.dmem (s.regs.rdi.toBitVec + 48#64)).toNat) := by
  obtain ⟨h0, hfs, hs, _, hn, _, hd, hsd, hfd, ho, hso, hfo, hdo⟩ := facts hpre hpos
  generalize nOf s.dmem s.regs.rdi.toBitVec = n at *
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> bv_omega

-- The side conditions of the reads: an access in one region against an access in another
-- region (with the facts `hs1` to `hs6` of `dist`), or two accesses in the same region.
set_option hygiene false in
scoped macro "sw_disch" : tactic => `(tactic| first
  | (refine region_sep hs1 ?_ ?_ ?_ ?_ <;> in_omega)
  | (refine region_sep' hs1 ?_ ?_ ?_ ?_ <;> in_omega)
  | (refine region_sep hs2 ?_ ?_ ?_ ?_ <;> in_omega)
  | (refine region_sep' hs2 ?_ ?_ ?_ ?_ <;> in_omega)
  | (refine region_sep hs3 ?_ ?_ ?_ ?_ <;> in_omega)
  | (refine region_sep' hs3 ?_ ?_ ?_ ?_ <;> in_omega)
  | (refine region_sep hs4 ?_ ?_ ?_ ?_ <;> in_omega)
  | (refine region_sep' hs4 ?_ ?_ ?_ ?_ <;> in_omega)
  | (refine region_sep hs5 ?_ ?_ ?_ ?_ <;> in_omega)
  | (refine region_sep' hs5 ?_ ?_ ?_ ?_ <;> in_omega)
  | (refine region_sep hs6 ?_ ?_ ?_ ?_ <;> in_omega)
  | (refine region_sep' hs6 ?_ ?_ ?_ ?_ <;> in_omega)
  | (refine same_sep (B := s.regs.rsp.toBitVec - 32#64) ?_ ?_ ?_ <;> in_omega)
  | (refine same_sep' (B := s.regs.rsp.toBitVec - 32#64) ?_ ?_ ?_ <;> in_omega)
  | (refine same_sep (B := s.regs.rdi.toBitVec) ?_ ?_ ?_ <;> in_omega)
  | (refine same_sep' (B := s.regs.rdi.toBitVec) ?_ ?_ ?_ <;> in_omega)
  | (refine same_sep (B := rd s.dmem (s.regs.rdi.toBitVec + 64#64)) ?_ ?_ ?_ <;> in_omega)
  | (refine same_sep' (B := rd s.dmem (s.regs.rdi.toBitVec + 64#64)) ?_ ?_ ?_ <;> in_omega)
  | (refine same_sep (B := rd s.dmem (s.regs.rdi.toBitVec + 48#64)) ?_ ?_ ?_ <;> in_omega)
  | (refine same_sep' (B := rd s.dmem (s.regs.rdi.toBitVec + 48#64)) ?_ ?_ ?_ <;> in_omega)
  | fail)

/-- The reads after stores of any width. A read at the address of a store must have the same
address term: a failed `omega` call is slow, so the `_same` lemmas use only `rfl`. -/
scoped macro "sw_rd" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| repeat (first
    | simp (disch := rfl) only [rd_store_same, rdb_store_same, BitVec.ofInt_toInt,
        BitVec.ofInt_ofNat] $(loc)?
    | simp (disch := sw_disch) only [rd_store_off, rdb_store_off, load_store_off] $(loc)?))

-- The facts for `sw_disch` that do not come from `dist`: the bounds, and the scaled indices
-- in `Nat`. `L` is the length, `N` the number of ops, `T` and `E` the destinations of the
-- slots `L - 1` and `r`.
theorem ctx (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat + 1 < (rd s.dmem s.regs.rdi.toBitVec).toNat) :
    (rd s.dmem s.regs.rdi.toBitVec).toNat ≤ nOf s.dmem s.regs.rdi.toBitVec
    ∧ nOf s.dmem s.regs.rdi.toBitVec ≤ 1024
    ∧ (rd s.dmem (s.regs.rdi.toBitVec + 16#64)).toNat < 6 * nOf s.dmem s.regs.rdi.toBitVec
    ∧ (rd s.dmem (s.regs.rdi.toBitVec + rd s.dmem s.regs.rdi.toBitVec * 8#64 + 64#64)).toNat
      < nOf s.dmem s.regs.rdi.toBitVec
    ∧ (rd s.dmem (s.regs.rdi.toBitVec + s.regs.rsi.toBitVec * 8#64 + 72#64)).toNat
      < nOf s.dmem s.regs.rdi.toBitVec
    ∧ ((rd s.dmem (s.regs.rdi.toBitVec + 16#64) + rd s.dmem (s.regs.rdi.toBitVec + 16#64) * 2#64)
      * 4#64).toNat = 12 * (rd s.dmem (s.regs.rdi.toBitVec + 16#64)).toNat
    ∧ (s.regs.rsi.toBitVec * 8#64).toNat = 8 * s.regs.rsi.toBitVec.toNat
    ∧ (rd s.dmem s.regs.rdi.toBitVec * 8#64).toNat = 8 * (rd s.dmem s.regs.rdi.toBitVec).toNat
    ∧ ((rd s.dmem s.regs.rdi.toBitVec + -1#64) * 8#64).toNat
      = 8 * (rd s.dmem s.regs.rdi.toBitVec).toNat - 8
    ∧ (rd s.dmem (s.regs.rdi.toBitVec + rd s.dmem s.regs.rdi.toBitVec * 8#64 + 64#64) * 8#64).toNat
      = 8 * (rd s.dmem (s.regs.rdi.toBitVec + rd s.dmem s.regs.rdi.toBitVec * 8#64 + 64#64)).toNat
    ∧ (rd s.dmem (s.regs.rdi.toBitVec + s.regs.rsi.toBitVec * 8#64 + 72#64) * 8#64).toNat
      = 8 * (rd s.dmem (s.regs.rdi.toBitVec + s.regs.rsi.toBitVec * 8#64 + 72#64)).toNat := by
  obtain ⟨_, -, _, hL, hn, hN, _, -, -, _, -, -, -⟩ := facts hpre (by omega)
  have hTd := dest_lt hpre (i := (rd s.dmem s.regs.rdi.toBitVec).toNat - 1) (by omega)
  rw [top_addr _ _ (by omega)] at hTd
  have hEd := dest_lt hpre (i := s.regs.rsi.toBitVec.toNat) (by omega)
  rw [pos_addr] at hEd
  exact ⟨hL, hn, hN, hTd, hEd, toNat_mul12 (by omega), toNat_mul8 (by omega), toNat_mul8 (by omega),
    toNat_pred8 (by omega) (by omega), toNat_mul8 (by omega), toNat_mul8 (by omega)⟩

-- All the facts for `sw_disch`, from `hpre` and `hpos`.
set_option hygiene false in
scoped macro "sw_ctx" : tactic => `(tactic| (
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ := dist hpre (by omega)
  obtain ⟨hL, hn, hN, hTd, hEd, hX, hR, hL8, hT8, hTT, hEE⟩ := ctx hpre hpos))

theorem fin_eq (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat + 1 < (rd s.dmem s.regs.rdi.toBitVec).toNat) :
    fin s ra = finC s ra := by
  sw_ctx
  simp only [fin, finC, pushes, pushAt]
  bbu_norm
  sw_rd

/-! ## The reads of `finC` -/

-- The header words other than `nops`.
theorem fin_hdr (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat + 1 < (rd s.dmem s.regs.rdi.toBitVec).toNat) {k : Nat}
    (hk : k < 9) (hk2 : k ≠ 2) :
    rd (finC s ra) (wordAt s.regs.rdi.toBitVec k) = rd s.dmem (wordAt s.regs.rdi.toBitVec k) := by
  sw_ctx
  simp only [finC, pushes, pushAt]
  bbu_norm
  rcases Nat.lt_or_gt_of_ne hk2 with h | h <;> sw_rd

theorem fin_nops (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat + 1 < (rd s.dmem s.regs.rdi.toBitVec).toNat) :
    rd (finC s ra) (wordAt s.regs.rdi.toBitVec 2)
      = 1#64 + rd s.dmem (wordAt s.regs.rdi.toBitVec 2) := by
  sw_ctx
  simp only [finC, pushes, pushAt]
  bbu_norm
  sw_rd

-- A store of `finC` is in `writable`.
set_option hygiene false in
scoped macro "sw_in" : tactic => `(tactic| (
  refine inside_writable ?_
  simp only [dataOf, opsOf, DEST_eq, WORDS_eq]
  bbu_norm
  first
  | (refine Or.inl ?_; in_omega)
  | (refine Or.inr (Or.inl ⟨?_, ?_⟩) <;> in_omega)
  | (refine Or.inr (Or.inr (Or.inl ?_)); in_omega)
  | (refine Or.inr (Or.inr (Or.inr (Or.inl ?_))); in_omega)
  | fail))

theorem fin_fm (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat + 1 < (rd s.dmem s.regs.rdi.toBitVec).toNat) :
    Fm swapWithF regs s ra (finC s ra) := by
  have h0 := Fm.init (rs := regs) (ra := ra) (by decide) hpre
  have hm0 : Mem.Mapped (writable s.dmem (rdi s)) (pushes s ra regs) := fun x hx => h0.map x (Or.inr hx)
  have hl := fin_hdr (ra := ra) hpre hpos (k := 0) (by decide) (by decide)
  have hn := fin_hdr (ra := ra) hpre hpos (k := 3) (by decide) (by decide)
  have hN := fin_nops (ra := ra) hpre hpos
  refine Fm.write (by decide) hpre h0 ?_ ?_ ?_ ?_
  · sw_ctx
    simp only [finC]
    iterate 14 refine Mem.UnchangedOutside.storeInt ?_ ?_ _
    all_goals first | exact fun _ _ => rfl | sw_in
  · simp only [finC]
    iterate 14 refine Mem.Mapped.storeInt ?_ _ _ _
    exact hm0
  · obtain ⟨_, -, _, hL, -⟩ := facts hpre (by omega)
    simp only [nOf] at hL ⊢
    bbu_norm at hl hL ⊢
    rw [hl]; exact hL
  · obtain ⟨_, -, _, -, -, hN', -⟩ := facts hpre (by omega)
    simp only [nOf] at hN' ⊢
    bbu_norm at hN hN' ⊢
    rw [hN]
    bv_omega

-- The addresses of the stores, as words from a base.
theorem w_r (X r : Addr) : wordAt X r.toNat = X + r * 8#64 := by
  simp only [wordAt]; bv_omega

theorem w_top (X L : Addr) (h0 : 0 < L.toNat) : wordAt X (L.toNat - 1) = X + (L + -1#64) * 8#64 := by
  simp only [wordAt]; bv_omega

theorem top_addr' (S L : Addr) (h0 : 0 < L.toNat) :
    wordAt S (DEST + (L.toNat - 1)) = S + (L + -1#64) * 8#64 + 72#64 := by
  simp only [wordAt, DEST_eq]; bv_omega

theorem p_addr (S X : Addr) : wordAt S (POS + X.toNat) = S + X * 8#64 + 8264#64 := by
  simp only [wordAt, POS_eq]; bv_omega

-- The data words.
theorem fin_dat (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat + 1 < (rd s.dmem s.regs.rdi.toBitVec).toNat) {i : Nat}
    (hi : i + 1 < (rd s.dmem s.regs.rdi.toBitVec).toNat) (hr : i ≠ s.regs.rsi.toBitVec.toNat) :
    rd (finC s ra) (wordAt (dataOf s.dmem s.regs.rdi.toBitVec) i)
      = rd s.dmem (wordAt (dataOf s.dmem s.regs.rdi.toBitVec) i) := by
  sw_ctx
  simp only [finC, pushes, pushAt, dataOf]
  bbu_norm
  rcases Nat.lt_or_gt_of_ne hr with h | h <;> sw_rd

theorem fin_dat_r (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat + 1 < (rd s.dmem s.regs.rdi.toBitVec).toNat) :
    rd (finC s ra) (wordAt (dataOf s.dmem s.regs.rdi.toBitVec) s.regs.rsi.toBitVec.toNat)
      = rd s.dmem (wordAt (dataOf s.dmem s.regs.rdi.toBitVec) ((rd s.dmem s.regs.rdi.toBitVec).toNat - 1)) := by
  sw_ctx
  rw [w_r, w_top _ _ (by omega)]
  simp only [finC, pushes, pushAt, dataOf]
  bbu_norm
  sw_rd

-- The destination words.
theorem fin_dst (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat + 1 < (rd s.dmem s.regs.rdi.toBitVec).toNat) {i : Nat}
    (hi : i + 1 < (rd s.dmem s.regs.rdi.toBitVec).toNat) (hr : i ≠ s.regs.rsi.toBitVec.toNat) :
    rd (finC s ra) (wordAt s.regs.rdi.toBitVec (DEST + i))
      = rd s.dmem (wordAt s.regs.rdi.toBitVec (DEST + i)) := by
  sw_ctx
  simp only [finC, pushes, pushAt, DEST_eq]
  bbu_norm
  rcases Nat.lt_or_gt_of_ne hr with h | h <;> sw_rd

theorem fin_dst_r (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat + 1 < (rd s.dmem s.regs.rdi.toBitVec).toNat) :
    rd (finC s ra) (wordAt s.regs.rdi.toBitVec (DEST + s.regs.rsi.toBitVec.toNat))
      = rd s.dmem (wordAt s.regs.rdi.toBitVec (DEST + ((rd s.dmem s.regs.rdi.toBitVec).toNat - 1))) := by
  sw_ctx
  rw [pos_addr, top_addr _ _ (by omega)]
  simp only [finC, pushes, pushAt]
  bbu_norm
  sw_rd

theorem fin_dst_top (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat + 1 < (rd s.dmem s.regs.rdi.toBitVec).toNat) :
    rd (finC s ra) (wordAt s.regs.rdi.toBitVec (DEST + ((rd s.dmem s.regs.rdi.toBitVec).toNat - 1)))
      = rd s.dmem (wordAt s.regs.rdi.toBitVec (DEST + s.regs.rsi.toBitVec.toNat)) := by
  sw_ctx
  rw [pos_addr, top_addr' _ _ (by omega)]
  simp only [finC, pushes, pushAt]
  bbu_norm
  sw_rd

-- The `positionOf` words. `T` and `E` are the destinations of the slots `L - 1` and `r`.
theorem fin_pos (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat + 1 < (rd s.dmem s.regs.rdi.toBitVec).toNat) {d : Nat}
    (hd : d < nOf s.dmem s.regs.rdi.toBitVec)
    (hT : d ≠ (rd s.dmem (s.regs.rdi.toBitVec + rd s.dmem s.regs.rdi.toBitVec * 8#64 + 64#64)).toNat)
    (hE : d ≠ (rd s.dmem (s.regs.rdi.toBitVec + s.regs.rsi.toBitVec * 8#64 + 72#64)).toNat) :
    rd (finC s ra) (wordAt s.regs.rdi.toBitVec (POS + d))
      = rd s.dmem (wordAt s.regs.rdi.toBitVec (POS + d)) := by
  sw_ctx
  simp only [finC, pushes, pushAt, POS_eq]
  bbu_norm
  rcases Nat.lt_or_gt_of_ne hT with h | h <;> rcases Nat.lt_or_gt_of_ne hE with h' | h' <;> sw_rd

theorem fin_pos_E :
    rd (finC s ra) (wordAt s.regs.rdi.toBitVec
      (POS + (rd s.dmem (s.regs.rdi.toBitVec + s.regs.rsi.toBitVec * 8#64 + 72#64)).toNat))
      = rd s.dmem s.regs.rdi.toBitVec + -1#64 := by
  rw [p_addr]
  simp only [finC]
  exact (rd_store_same _ rfl).trans BitVec.ofInt_toInt

theorem fin_pos_T (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat + 1 < (rd s.dmem s.regs.rdi.toBitVec).toNat)
    (hTE : (rd s.dmem (s.regs.rdi.toBitVec + rd s.dmem s.regs.rdi.toBitVec * 8#64 + 64#64)).toNat
      ≠ (rd s.dmem (s.regs.rdi.toBitVec + s.regs.rsi.toBitVec * 8#64 + 72#64)).toNat) :
    rd (finC s ra) (wordAt s.regs.rdi.toBitVec
      (POS + (rd s.dmem (s.regs.rdi.toBitVec + rd s.dmem s.regs.rdi.toBitVec * 8#64 + 64#64)).toNat))
      = s.regs.rsi.toBitVec := by
  sw_ctx
  rw [p_addr]
  simp only [finC, pushes, pushAt]
  bbu_norm
  rcases Nat.lt_or_gt_of_ne hTE with h | h <;> sw_rd

-- The operations before the new one.
theorem fin_op (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat + 1 < (rd s.dmem s.regs.rdi.toBitVec).toNat) {i : Nat}
    (hi : i < (rd s.dmem (s.regs.rdi.toBitVec + 16#64)).toNat) :
    opOf (finC s ra) s.regs.rdi.toBitVec i = opOf s.dmem s.regs.rdi.toBitVec i := by
  sw_ctx
  simp only [finC, pushes, pushAt, opOf, opAt, opsOf]
  bbu_norm
  simp only [add_lit]
  sw_rd

-- The new operation.
theorem fin_opN (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat + 1 < (rd s.dmem s.regs.rdi.toBitVec).toNat) :
    opOf (finC s ra) s.regs.rdi.toBitVec (rd s.dmem (s.regs.rdi.toBitVec + 16#64)).toNat
      = Op.swap ((rd s.dmem s.regs.rdi.toBitVec).toNat - 1 - s.regs.rsi.toBitVec.toNat) := by
  have hm := (fin_fm (ra := ra) hpre hpos).map
  sw_ctx
  simp only [opOf, opAt, opsOf, Op.swap, ofNat12]
  rw [fin_hdr hpre hpos (by decide) (by decide)]
  bbu_norm
  have hs : ((finC s ra).loadInt (rd s.dmem (s.regs.rdi.toBitVec + 48#64)
      + (rd s.dmem (s.regs.rdi.toBitVec + 16#64) + rd s.dmem (s.regs.rdi.toBitVec + 16#64) * 2#64)
        * 4#64 + 4#64) 8).isSome :=
    hm.loadInt_isSome (Or.inr (inside_writable (Or.inr (Or.inr (Or.inr (Or.inl (by
      simp only [opsOf]; bbu_norm; in_omega)))))))
  rw [Op.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · simp only [finC, pushes, pushAt]
    bbu_norm
    sw_rd
    rfl
  · simp only [finC, pushes, pushAt]
    bbu_norm
    sw_rd
    exact take_sub (by omega)
  · rw [junk_eq]
    refine ofWord_of_mod ?_
    rw [low48 hs]
    simp only [add_lit, Nat.reduceAdd]
    simp only [finC, pushes, pushAt]
    bbu_norm
    sw_rd
    simp (disch := first | rfl | decide) only [load_store_same, Option.get!_some]
    decide

-- The data word of the top: the stores write its low 6 bytes.
theorem fin_dat_top (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat + 1 < (rd s.dmem s.regs.rdi.toBitVec).toNat) :
    StackSlot.ofWord (rd (finC s ra)
      (wordAt (dataOf s.dmem s.regs.rdi.toBitVec) ((rd s.dmem s.regs.rdi.toBitVec).toNat - 1)))
      = StackSlot.ofWord (rd s.dmem (wordAt (dataOf s.dmem s.regs.rdi.toBitVec) s.regs.rsi.toBitVec.toNat)) := by
  have hm := (fin_fm (ra := ra) hpre hpos).map
  have hw := hpre.1.mapped
  sw_ctx
  rw [w_r, w_top _ _ (by omega)]
  simp only [dataOf]
  bbu_norm
  have h1 : ((finC s ra).loadInt (rd s.dmem (s.regs.rdi.toBitVec + 64#64)
      + (rd s.dmem s.regs.rdi.toBitVec + -1#64) * 8#64) 8).isSome :=
    hm.loadInt_isSome (Or.inr (inside_writable (Or.inr (Or.inr (Or.inl (by
      simp only [dataOf]; bbu_norm; in_omega))))))
  have h2 : (s.dmem.loadInt (rd s.dmem (s.regs.rdi.toBitVec + 64#64)
      + s.regs.rsi.toBitVec * 8#64) 8).isSome :=
    hw.loadInt_isSome (inside_append.mpr (Or.inl (inside_writable (Or.inr (Or.inr (Or.inl (by
      simp only [dataOf]; bbu_norm; in_omega)))))))
  refine ofWord_of_mod ?_
  rw [low48 h1, low48 h2]
  simp only [finC, pushes, pushAt]
  bbu_norm
  sw_rd
  simp (disch := first | rfl | decide) only [load_store_same, Option.get!_some,
    Nat.reduceMul, mod32, mod8]

theorem optOf_some {w : Word} (h : w ≠ -1#64) : optOf w = some w.toNat := by
  simp only [optOf, h, ↓reduceIte]

-- The model state after the stores: the state of `swapWith_eq` and `swapDest_swap`.
theorem stOf_fin (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat + 1 < (rd s.dmem s.regs.rdi.toBitVec).toNat) :
    stOf (finC s ra) (rdi s) = { st s with
      slots := ((st s).slots.set (rsi s).toNat
          ⟨(st s).val ((st s).len - 1), (st s).dest ((st s).len - 1)⟩).set
        ((st s).len - 1) ⟨(st s).val (rsi s).toNat, (st s).dest (rsi s).toNat⟩
      positionOf := ((st s).positionOf.set ((st s).dest ((st s).len - 1)) (some (rsi s).toNat)).set
        ((st s).dest (rsi s).toNat) (some ((st s).len - 1))
      trace := (st s).trace ++ [.swap ((st s).len - 1 - (rsi s).toNat)] } := by
  have hL : (st s).len = (rd s.dmem (wordAt (rdi s) 0)).toNat := len_stOf
  have hN : (st s).trace.length = (rd s.dmem (wordAt (rdi s) 2)).toNat := nops_stOf
  have hD : dataOf (finC s ra) (rdi s) = dataOf s.dmem (rdi s) := by
    simp only [dataOf]; exact fin_hdr hpre hpos (by decide) (by decide)
  have hn : nOf (finC s ra) (rdi s) = nOf s.dmem (rdi s) := by
    simp only [nOf]; exact congrArg BitVec.toNat (fin_hdr hpre hpos (by decide) (by decide))
  have hpl : (st s).positionOf.length = nOf s.dmem (rdi s) := by simp [stOf]
  have hlt : ∀ j, j < (rd s.dmem s.regs.rdi.toBitVec).toNat → j < (rd s.dmem (wordAt (rdi s) 0)).toNat :=
    fun j h => by simp only [wordAt, rdi, Reg64s.get64_rdi, Nat.mul_zero, BitVec.add_zero]; exact h
  simp only [rdi, rsi, Reg64s.get64_rdi, Reg64s.get64_rsi] at hL hN hD hn hpl ⊢
  have hL0 : (st s).len = (rd s.dmem s.regs.rdi.toBitVec).toNat := by
    rw [hL]; simp only [wordAt, Nat.mul_zero, BitVec.add_zero]
  refine stOf_eq ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [congrArg BitVec.toNat (fin_hdr hpre hpos (k := 0) (by decide) (by decide))]
    simp only [St.len, List.length_set]
    exact hL.symm
  · rw [congrArg BitVec.toNat (fin_hdr hpre hpos (k := 1) (by decide) (by decide))]
    simp [stOf]
  · rw [congrArg BitVec.toNat (fin_nops hpre hpos)]
    simp only [List.length_append, List.length_singleton, hN]
    obtain ⟨-, -, -, -, h, h', -⟩ := facts hpre (by omega)
    simp only [nOf] at h h'
    bbu_norm at h h' ⊢
    bv_omega
  -- The slots `r` and `L - 1` change places.
  · simp only [St.len]
    intro i hi
    simp only [List.length_set] at hi
    simp only [St.len] at hL0
    simp only [slotOf, hD]
    rw [List.getElem_set, List.getElem_set]
    split
    · rename_i h1
      subst h1
      rw [val_stOf (hlt _ (by omega)), dest_stOf (hlt _ (by omega))]
      simp only [rdi, Reg64s.get64_rdi, hL0]
      rw [fin_dat_top hpre hpos, fin_dst_top hpre hpos]
    · split
      · rename_i h1 h2
        subst h2
        rw [val_stOf (hlt _ (by omega)), dest_stOf (hlt _ (by omega))]
        simp only [rdi, Reg64s.get64_rdi, hL0]
        rw [fin_dat_r hpre hpos, fin_dst_r hpre hpos]
      · rename_i h1 h2
        rw [fin_dat hpre hpos (by omega) (Ne.symm h2), fin_dst hpre hpos (by omega) (Ne.symm h2)]
        simp [stOf, slotOf]
  · simp only [List.length_set, hpl, hn]
  -- `positionOf` of the destinations `E` and `T` of the two slots.
  · intro d hd
    have hd' := hd
    simp only [List.length_set, hpl] at hd'
    have hE : (st s).dest s.regs.rsi.toBitVec.toNat
        = (rd s.dmem (s.regs.rdi.toBitVec + s.regs.rsi.toBitVec * 8#64 + 72#64)).toNat := by
      rw [dest_stOf (hlt _ (by omega))]; exact congrArg BitVec.toNat (rd_addr (pos_addr _ _))
    have hT : (st s).dest ((st s).len - 1)
        = (rd s.dmem (s.regs.rdi.toBitVec + rd s.dmem s.regs.rdi.toBitVec * 8#64 + 64#64)).toNat := by
      rw [dest_stOf (hlt _ (by omega)), hL0]
      exact congrArg BitVec.toNat (rd_addr (top_addr _ _ (by omega)))
    rw [List.getElem_set, List.getElem_set]
    simp only [hE, hT]
    simp only [hL0]
    split
    · rename_i h1
      subst h1
      rw [fin_pos_E, optOf_some (by bv_omega)]
      exact congrArg some (by bv_omega)
    · split
      · rename_i h1 h2
        subst h2
        rw [fin_pos_T hpre hpos (Ne.symm h1), optOf_some (by bv_omega)]
      · rename_i h1 h2
        rw [fin_pos hpre hpos hd' (Ne.symm h2) (Ne.symm h1)]
        simp [stOf]
  -- The operations: the new one at the end.
  · intro i hi
    have hN2 : (st s).trace.length = (rd s.dmem (s.regs.rdi.toBitVec + 16#64)).toNat := hN
    rw [List.getElem_append]
    split
    · rename_i h
      rw [fin_op hpre hpos (by omega)]
      simp [stOf]
    · rename_i h
      simp only [List.length_append, List.length_singleton] at hi
      have hi' : i = (rd s.dmem (s.regs.rdi.toBitVec + 16#64)).toNat := by omega
      subst hi'
      rw [List.getElem_singleton, fin_opN hpre hpos, hL0]

-- The result after the stores, if the three checks pass.
theorem R_fin (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat + 1 < (rd s.dmem s.regs.rdi.toBitVec).toNat)
    (hdz : rd s.dmem (s.regs.rdi.toBitVec + s.regs.rsi.toBitVec * 8#64 + 72#64) ≠ s.regs.rsi.toBitVec)
    (hdep : (rd s.dmem s.regs.rdi.toBitVec).toNat - 1 - s.regs.rsi.toBitVec.toNat ≤ 16) {t : MachineData}
    (hm : t.dmem = finC s ra) (hax : rax t = 0#64) : swapWithR s t := by
  have hL : (st s).len = (rd s.dmem s.regs.rdi.toBitVec).toNat := by
    rw [len_stOf]; simp only [wordAt, rdi, Reg64s.get64_rdi, Nat.mul_zero, BitVec.add_zero]
  have hd : (st s).dest (rsi s).toNat ≠ (rsi s).toNat := by
    rw [dest_stOf (by simp only [wordAt, rdi, rsi, Reg64s.get64_rdi, Reg64s.get64_rsi, Nat.mul_zero, BitVec.add_zero]; omega)]
    simp only [rdi, rsi, Reg64s.get64_rdi, Reg64s.get64_rsi]
    rw [rd_addr (pos_addr _ _)]
    exact fun h => hdz (BitVec.eq_of_toNat_eq h)
  have hp : (rsi s).toNat < (st s).len - 1 := by
    simp only [rsi, Reg64s.get64_rsi, hL]; omega
  unfold swapWithR
  rw [swapWith_eq (by omega) hd (by omega) (by simp only [MAX_SWAP_DEPTH, rsi, Reg64s.get64_rsi, hL]; omega),
    swapDest_swap _ hp (by omega)]
  exact ⟨hax, by simp only [st', hm, id]; exact stOf_fin hpre hpos⟩

end
end SwapWithFn

open SwapWithFn Kit

-- A jump to a label of the cfg.
local macro "cfg_goto" : tactic => `(tactic| (
  apply Program.Intercept.intro_label
  · repeat ((fail_if_success (apply List.getElem?_cons_zero)); (apply List.getElem?_cons_succ_of))
    apply List.getElem?_cons_zero
  refine Or.inl ⟨?_, ?_, ?_⟩))

set_option maxHeartbeats 6000000 in
theorem swapWith_body [Host] [FunDecls] : Body swapWithAsm swapWithF swapWithA swapWithR := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  refine Program.WP.cfg (fun
      | .entry, t | .label "swapWith", t => t = s.pushRa ra
      | .label ".LB12", t | .label ".LB13", t | .label ".LB14", t => Fail s ra t
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  case left t ht =>
    subst ht
    kvcgen64
  case right.left t ht =>
    subst ht
    have hF : 8 ≤ swapWithF := by decide
    have hle := hpre.2.1.le
    have hsep := hpre.2.1.sep_struct (by decide)
    have hst := hpre.1.struct_lt
    simp only [swapWithF, WORDS_eq] at hle hsep hst
    bbu_norm at hle hsep hst
    have hR : ∀ a, (a - s.regs.rdi.toBitVec).toNat + 8 ≤ 16456 →
        rd (Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt) a = rd s.dmem a :=
      fun a ha => rd_store_other _ (by bv_omega)
    have hm0 : Mem.Mapped (mod swapWithF s).mem s.dmem := fun x hx =>
      hx.elim (fun h => hpre.2.1.mapped x (Or.inl h))
        (fun h => hpre.1.mapped x (inside_append.mpr (Or.inl h)))
    kvcgen64
    case vc2 =>
      rename_i hc
      bbu_norm at hc
      rw [hR _ (by simp)] at hc
      bbu_flags at hc
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [MachineData.regs_pushRa, Reg64s.get64_rsp, Reg64s.set64_rsp]
        bv_omega
      · refine ⟨rfl, rfl, ?_, swapWith_err (Or.inl ?_)⟩
        · intro q hq; cases q <;> first | (simp at hq; done) | rfl
        · rw [len_stOf]; bbu_norm; exact (no_borrow_iff _ _).1 hc
      · simp
    case vc4 =>
      rename_i hc hz
      bbu_norm at hc hz
      rw [hR _ (by simp)] at hc
      bbu_flags at hc
      have hpos := (borrow_iff _ _).1 hc
      obtain ⟨-, -, -, hL, hn, -⟩ := facts hpre hpos
      rw [hR _ (by bv_omega)] at hz
      bbu_flags at hz
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [MachineData.regs_pushRa, Reg64s.get64_rsp, Reg64s.set64_rsp]
        bv_omega
      · refine ⟨rfl, rfl, ?_, swapWith_err (Or.inr (Or.inl ?_))⟩
        · intro q hq; cases q <;> first | (simp at hq; done) | rfl
        · rw [dest_stOf (by bbu_norm; exact hpos), pos_addr]
          bbu_norm
          bv_omega
      · simp
    case vc5 =>
      rename_i hc hz ha
      bbu_norm at hc hz ha ⊢
      rw [hR _ (by simp)] at hc ha
      bbu_flags at hc ha
      have hpos := (borrow_iff _ _).1 hc
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [MachineData.regs_pushRa, Reg64s.get64_rsp, Reg64s.set64_rsp]
        bv_omega
      · refine ⟨rfl, rfl, ?_, swapWith_err (Or.inr (Or.inr ?_))⟩
        · intro q hq; cases q <;> first | (simp at hq; done) | rfl
        · rw [len_stOf]; bbu_norm; simp only [MAX_SWAP_DEPTH]; exact depth_big _ _ hpos ha
      · simp
    case vc1 =>
      bbu_norm
      apply loadInt_isSome_store
      exact hpre.1.isSome_struct (by bbu_norm; simp only [WORDS_eq]; bv_omega)
    case vc3 =>
      rename_i hc
      bbu_norm at hc
      rw [hR _ (by simp)] at hc
      bbu_flags at hc
      have hpos := (borrow_iff _ _).1 hc
      obtain ⟨-, -, -, hL, hn, -⟩ := facts hpre hpos
      bbu_norm
      apply loadInt_isSome_store
      exact hpre.1.isSome_struct (by simp only [rdi, Reg64s.get64_rdi, WORDS_eq]; bv_omega)
    all_goals
      rename_i hc hz ha
      bbu_norm at hc hz ha ⊢
      rw [hR _ (by simp)] at hc ha
      bbu_flags at hc ha
      have hpos := (borrow_iff _ _).1 hc
      obtain ⟨-, -, -, hL, hn, -⟩ := facts hpre hpos
      rw [hR _ (by bv_omega)] at hz
      bbu_flags at hz
      have hdep := depth_ok _ _ hpos ha
      clear hc ha
      replace hpos : s.regs.rsi.toBitVec.toNat + 1 < (rd s.dmem s.regs.rdi.toBitVec).toNat := by omega
    case vc37 =>
      have hfm : Fm swapWithF regs s ra (fin s ra) := by rw [fin_eq hpre hpos]; exact fin_fm hpre hpos
      exact Option.isSome_iff_exists.mpr ⟨ra, Mid.retAddr hF hpre hfm.toMid
        (by simp only [rsp, Reg64s.get64_rsp]; bv_omega)⟩
    case vc38 =>
      have hfm : Fm swapWithF regs s ra (fin s ra) := by rw [fin_eq hpre hpos]; exact fin_fm hpre hpos
      refine Fm.ret hF hpre hfm ?_ ?_ ?_
      · simp only [rsp, Reg64s.get64_rsp]; bv_omega
      · intro q hq
        cases q <;> first
          | (simp at hq; done)
          | rfl
          | exact (rd_addr (by simp only [rsp, Reg64s.get64_rsp]; bv_omega)).trans (hfm.saved 2 (by decide))
          | exact (rd_addr (by simp only [rsp, Reg64s.get64_rsp]; bv_omega)).trans (hfm.saved 1 (by decide))
          | exact (rd_addr (by simp only [rsp, Reg64s.get64_rsp]; bv_omega)).trans (hfm.saved 0 (by decide))
      · intro t hm hax
        exact R_fin hpre hpos (fun h => hz (by rw [h, BitVec.sub_self])) hdep.2
          (hm.trans (fin_eq hpre hpos)) (hax.trans rfl)
    case vc6 | vc7 | vc8 | vc34 | vc35 | vc36 =>
      refine Mem.Mapped.loadInt_isSome (bs := [frame swapWithF s]) ?_ (Or.inl ?_)
      · repeat refine Mem.Mapped.storeInt ?_ _ _ _
        exact hpre.2.1.mapped
      · simp only [swapWithF, rsp, Reg64s.get64_rsp]; bv_omega
    case vc9 | vc10 | vc16 | vc17 | vc23 =>
      repeat apply loadInt_isSome_store
      exact hpre.1.isSome_struct (by simp only [rdi, Reg64s.get64_rdi, WORDS_eq]; bv_omega)
    all_goals
      sw_ctx
      refine Mem.Mapped.loadInt_isSome (bs := (mod swapWithF s).mem) ?_ (Or.inr ?_)
      · repeat refine Mem.Mapped.storeInt ?_ _ _ _
        exact hm0
      · sw_rd
        sw_in
  all_goals
    rename_i t ht
    obtain ⟨hm, hsp, hr, he⟩ := ht
    have hfm : Fm swapWithF [] s ra t.dmem := hm ▸ Fm.init (by decide) hpre
    kvcgen64
    · exact Option.isSome_iff_exists.mpr ⟨ra, Mid.retAddr (by decide) hpre hfm.toMid hsp⟩
    · refine Fm.ret (by decide) hpre hfm hsp ?_ fun _ _ hax => ?_
      · intro q hq
        rw [← hr q hq]
        cases q <;> first | (simp at hq; done) | rfl
      · simp only [swapWithR, he, Res]
        exact hax.trans rfl
end Bbu
