import BbuKraken.Unit.Defs
import BbuKraken.Sep.Stores
import ProofKit.Cfg
import ProofKit.Idioms

/-!
# `swapWith`

`c/bbu/<Names.swapWith>.S`: no frame, no call. It asserts `pos < size`, that `pos` is not
final, and `1 ≤ depth ≤ 16`. Then it swaps the two slots (the top slot gets the 6 low bytes of
the other slot), stores the operation, swaps the two destinations, and writes `m_positionOf` at
each destination that is not `-1`.

`DestOk` gives that each such destination is below `n ≤ MAX_N`, so the stores to `m_positionOf`
are in the view. The callers are `generate` (`nops + 1 < 6n` after `produce`, and `produce`
binds the new slot to `t < n`) and `buildBottomUp` (`Inv.lt` and `Inv.pos`). They use the flat
result (`swapWithQ`).
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit

open Bbu.Sep

namespace SwapWith

/-! ## `notq`

`kvcgen64` has no spec for `notq %r64`. -/

theorem notq_spec [Host] [FunDecls] (asz : Width) (r : Reg64)
    {Q : PUnit → MachineData → Prop} {E : Int64 → MachineData → Prop} :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r (~~~(s.regs.get64 r)) } ⦄
      (Directive.instr (.regular asz .W64 (.not (.reg (.low r .W64)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.set,
    MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All]
  exact hn _ hpre

/-! ## Loads and stores of the working stack and of `m_destinationOf` -/

section
variable {S : Addr} {g : G} {F : MProp 64} {m : Mem 64}

theorem addr_succ (a : Addr) (i : Nat) :
    a + BitVec.ofNat 64 (8 * (i + 1)) = a + 8#64 + BitVec.ofNat 64 (8 * i) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

-- Word `i` of an array, the rest, and the array with word `i` set.
theorem arr_focus_set (a : Addr) (vs : List Word) {i : Nat} (hi : i < vs.length) :
    ∃ R, Arr a vs = Wd (a + BitVec.ofNat 64 (8 * i)) vs[i] ∗ R
      ∧ ∀ w, Arr a (vs.set i w) = Wd (a + BitVec.ofNat 64 (8 * i)) w ∗ R := by
  induction vs generalizing a i with
  | nil => simp at hi
  | cons v vs ih =>
    cases i with
    | zero => exact ⟨Arr (a + 8#64) vs, by simp [Arr], fun w => by simp [Arr]⟩
    | succ i =>
      obtain ⟨R, e, e'⟩ := ih (a + 8#64) (Nat.lt_of_succ_lt_succ hi)
      refine ⟨Wd a v ∗ R, ?_, fun w => ?_⟩
      · rw [Arr, e, addr_succ, List.getElem_cons_succ, ← MProp.sep_assoc,
          MProp.sep_comm (Wd a v), MProp.sep_assoc]
      · rw [List.set_cons_succ, Arr, e' w, addr_succ, ← MProp.sep_assoc,
          MProp.sep_comm (Wd a v), MProp.sep_assoc]

theorem wd_slot (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs) :
    ∃ R, (Wd (slotAt g.h.data i) g.stk[i] ∗ R).get m := by
  obtain ⟨R, h⟩ := View.arr_stk h
  obtain ⟨Q, e, -⟩ := arr_focus_set g.h.data g.stk.toList (i := i) (by simpa using hi)
  rw [e, Vector.getElem_toList, MProp.sep_assoc] at h
  exact ⟨_, h⟩

theorem rd_slot (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs) :
    rd m (slotAt g.h.data i) = g.stk[i] :=
  let ⟨_, h⟩ := wd_slot h hi; Wd.rd h

theorem B32.rd32 {a : Addr} {v : BitVec 32} (h : (B32 a v ∗ F).get m) :
    BitVec.ofInt 32 (m.loadInt a 4).get! = v := by
  unfold B32 at h
  simp only [Mem.loadInt_eq_of_AtM h (Int.toBytes_length _ _) (by decide), Option.get!_some,
    BitVec.ofInt_ofBytes_toBytes 32 4 rfl]

-- `movl (slot), %r32`: the low 4 bytes.
theorem rd32_slot (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs) :
    BitVec.ofInt 32 (m.loadInt (slotAt g.h.data i) 4).get! = g.stk[i].extractLsb' 0 32 := by
  obtain ⟨R, h⟩ := wd_slot h hi
  rw [Wd.split, MProp.sep_assoc] at h
  exact B32.rd32 h

theorem isSome32_slot (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs) :
    (m.loadInt (slotAt g.h.data i) 4).isSome = true := by
  obtain ⟨R, h⟩ := wd_slot h hi
  rw [Wd.split, MProp.sep_assoc] at h
  exact B32.isSome h

-- `movzbl 4(slot)` and `movzbl 5(slot)`.
theorem rdb4_slot (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs) :
    rdb m (slotAt g.h.data i + 4#64) = g.stk[i].extractLsb' 32 8 :=
  let ⟨_, h⟩ := wd_slot h hi; Wd.rdb_byte h (j := 4) (by decide)

theorem rdb5_slot (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs) :
    rdb m (slotAt g.h.data i + 5#64) = g.stk[i].extractLsb' 40 8 :=
  let ⟨_, h⟩ := wd_slot h hi; Wd.rdb_byte h (j := 5) (by decide)

theorem isSome4_slot (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs) :
    (m.loadInt (slotAt g.h.data i + 4#64) 1).isSome = true :=
  let ⟨_, h⟩ := wd_slot h hi; Wd.isSome_byte h (j := 4) (by decide)

theorem isSome5_slot (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs) :
    (m.loadInt (slotAt g.h.data i + 5#64) 1).isSome = true :=
  let ⟨_, h⟩ := wd_slot h hi; Wd.isSome_byte h (j := 5) (by decide)

theorem rd_dest (h : (View S g ∗ F).get m) {i : Nat} (hi : i < MAX_N) :
    rd m (Fld.mapping_destinationOf S i) = g.h.dest[i] := by
  obtain ⟨R, h'⟩ := View.arr_dest h
  exact (Arr.rd h' (by simpa using hi)).trans (by simp)

-- `movl` and two `movb` to slot `i`: the low 6 bytes. Bytes 6 and 7 do not change.
theorem store411_slot (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs)
    (x : BitVec 32) (y z : BitVec 8) :
    (View S { g with stk := g.stk.set i (g.stk[i].extractLsb' 48 16 ++ z ++ y ++ x) } ∗ F).get
      (((m.storeInt (slotAt g.h.data i) 4 x.toInt).storeInt (slotAt g.h.data i + 4#64) 1
        y.toInt).storeInt (slotAt g.h.data i + 5#64) 1 z.toInt) := by
  obtain ⟨R, e, e'⟩ := arr_focus_set g.h.data g.stk.toList (i := i) (by simpa using hi)
  refine swap_of_eq h (A := Arr g.h.data g.stk.toList)
    (A' := Arr g.h.data (g.stk.set i (g.stk[i].extractLsb' 48 16 ++ z ++ y ++ x)).toList)
    (by unfold View; ecancel) (by unfold View; ecancel) fun h => ?_
  rw [e, MProp.sep_assoc, Vector.getElem_toList] at h
  rw [Vector.toList_set, e', MProp.sep_assoc]
  exact Wd.store411 h x y z

-- The bytes `4` and `5` of slot `i` between the stores of `store411_slot`.
theorem isSome4_411 (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs) (x : BitVec 32) :
    ((m.storeInt (slotAt g.h.data i) 4 x.toInt).loadInt (slotAt g.h.data i + 4#64) 1).isSome
      = true := by
  obtain ⟨R, h⟩ := wd_slot h hi
  rw [Wd.split] at h
  simp only [MProp.sep_assoc] at h
  have h1 := B32.store h x.toInt
  rw [sep_lc] at h1
  exact B8.isSome h1

theorem isSome5_411 (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs) (x : BitVec 32)
    (y : BitVec 8) :
    (((m.storeInt (slotAt g.h.data i) 4 x.toInt).storeInt (slotAt g.h.data i + 4#64) 1
      y.toInt).loadInt (slotAt g.h.data i + 5#64) 1).isSome = true := by
  obtain ⟨R, h⟩ := wd_slot h hi
  rw [Wd.split] at h
  simp only [MProp.sep_assoc] at h
  have h1 := B32.store h x.toInt
  rw [sep_lc] at h1
  have h2 := B8.store h1 y.toInt
  rw [sep_lc (B8 (slotAt g.h.data i + 4#64) _), sep_lc (B8 (slotAt g.h.data i + 4#64) _),
    sep_lc (B32 (slotAt g.h.data i) _)] at h2
  exact B8.isSome h2

end

/-! ## The asm forms after `symexec_norm` -/

theorem rd_eq (m : Mem 64) (a : Addr) : BitVec.ofInt 64 (Mem.loadInt m a 8).get! = rd m a := rfl
theorem rdb_eq (m : Mem 64) (a : Addr) : BitVec.ofInt 8 (Mem.loadInt m a 1).get! = rdb m a := rfl

-- `leaq -8(%d,%size,8)`: the top slot.
theorem top_slot (d x : Word) : slotAt d x.toNat + BitVec.ofInt 64 (-8) = slotAt d (x - 1).toNat := by
  unfold slotAt; bv_omega

-- `leaq -1(%size)`
theorem add_neg_one (x : Word) : x + BitVec.ofInt 64 (-1) = x - 1 := by bv_omega

-- `symexec_norm` writes `rsi s` as the register.
theorem rsi_eq (s : MachineData) : rsi s = s.regs.rsi.toBitVec := rfl

-- `movzbl` and then `movb %r8b`: the byte.
theorem byte_rt (b : BitVec 8) :
    BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (BitVec.setWidth 32 b)) = b := by bv_decide

-- `zf` of `cmp b, a` (the VC writes the zero as `BitVec.zero`).
theorem sub_beq_zero (a b : Word) : (a - b == BitVec.zero 64) = (a == b) := by
  rw [BitVec.zero_eq]; exact Idioms.sub_beq_zero a b

-- `cmpq $-1`: the test for `NONE`.
theorem cmp_none (x : Word) :
    (x - 18446744073709551615#64 == BitVec.zero 64) = (x == Flat.NONE) := by
  rw [sub_beq_zero]; rfl

-- `cmpq $15, %r8; ja`
theorem ja15 (x : Word) :
    (!(((x - 15#64).toNat : Int) != (x.toNat : Int) - 15) && !(x - 15#64 == BitVec.zero 64))
      = decide (15 < x.toNat) := by
  rw [Idioms.cf_sub_imm x 15 (by decide), sub_beq_zero, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_eq_false_iff_ne,
    decide_eq_true_eq, ne_eq, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_ofNat]
  omega

-- The depth test of the C++ and the test of the asm (`size - pos - 2 ≤ 15`).
theorem depth_iff (l p : Word) :
    (1 ≤ l - 1 - p ∧ l - 1 - p ≤ Flat.maxSwapDepth) ↔ ¬ 15 < (l - p + BitVec.ofInt 64 (-2)).toNat := by
  simp only [Flat.maxSwapDepth, BitVec.le_def]
  bv_omega

-- `movl %ecx, %eax`: the low byte of `eax` is the low byte of `rcx`.
theorem al_movl (x : Word) : (BitVec.setWidth 64 (x.take 32)).setWidth 8 = x.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  omega

/-! ## Indexes in bounds

`Flat.get` and `Flat.put` take a `Word` index and do nothing out of bounds. The ghost uses
`Vector.set` with a proof of the bound. -/

theorem put_eq_set {α : Type} (v : Vector α MAX_N) (i : Word) (x : α) (h : i.toNat < MAX_N) :
    Flat.put v i x = v.set i.toNat x h := by
  apply Vector.ext; intro j hj
  simp only [Flat.put, Vector.getElem_setIfInBounds hj, Vector.getElem_set h hj]

theorem get_eq {α : Type} [Inhabited α] (v : Vector α MAX_N) (i : Word) (h : i.toNat < MAX_N) :
    Flat.get v i = v[i.toNat] := by
  simp [Flat.get, h]

theorem vec_set {α : Type} [Inhabited α] (l : List α) (i : Nat) (x : α) (hi : i < l.length)
    (hn : i < MAX_N) : vec (l.set i x) = (vec l).set i x hn := by
  apply Vector.ext; intro j hj
  simp only [vec, Vector.getElem_ofFn, Vector.getElem_set, List.getElem?_set]
  by_cases e : i = j
  · subst e; simp [hi]
  · simp [e]

theorem get_vec {α : Type} [Inhabited α] (l : List α) (i : Word) (hi : i.toNat < l.length)
    (hn : i.toNat < MAX_N) : Flat.get (vec l) i = l[i.toNat] := by
  simp [Flat.get, hn, vec, hi]

theorem take_set_succ {α : Type} (l : List α) (i : Nat) (r : α) (hi : i < l.length) :
    (l.set i r).take (i + 1) = l.take i ++ [r] := by
  rw [List.take_add_one, List.getElem?_set_self hi, List.take_set_of_le (Nat.le_refl i)]
  rfl

/-! ## The cases of `Flat.swapWith` -/

-- The two stores of `m_destinationOf` in `swapDestinations`.
def swapD (d : Vector Word MAX_N) (a b : Word) : Vector Word MAX_N :=
  Flat.put (Flat.put d a (Flat.get d b)) b (Flat.get d a)

-- The `m_positionOf` store of `swapDestinations` for the slot `b`.
def posFix (fs : Flat.St) (b : Word) : Flat.St :=
  if Flat.get fs.dest b ≠ Flat.NONE then { fs with pos := Flat.put fs.pos (Flat.get fs.dest b) b }
  else fs

theorem swapDest_eq (st : Flat.St) (a b : Word) :
    Flat.swapDestinations st a b = posFix (posFix { st with dest := swapD st.dest a b } a) b := by
  simp only [Flat.swapDestinations, posFix, swapD]
  by_cases h1 : Flat.get (Flat.put (Flat.put st.dest a (Flat.get st.dest b)) b
      (Flat.get st.dest a)) a = Flat.NONE <;>
    by_cases h2 : Flat.get (Flat.put (Flat.put st.dest a (Flat.get st.dest b)) b
      (Flat.get st.dest a)) b = Flat.NONE <;>
    simp only [h1, h2, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]

theorem sw_err1 (fs : Flat.St) (p : Word) (h : ¬ p.toNat < fs.size.toNat) :
    Flat.swapWith fs p = (.assertionFailed, fs) := by
  simp [Flat.swapWith, BitVec.lt_def, h]

theorem sw_err2 (fs : Flat.St) (p : Word) (h1 : p.toNat < fs.size.toNat)
    (h : Flat.get fs.dest p = p) : Flat.swapWith fs p = (.assertionFailed, fs) := by
  simp [Flat.swapWith, Flat.isFinal, BitVec.lt_def, h1, h]

theorem sw_err3 (fs : Flat.St) (p : Word) (h1 : p.toNat < fs.size.toNat)
    (h2 : Flat.get fs.dest p ≠ p) (h : 15 < (fs.size - p + BitVec.ofInt 64 (-2)).toNat) :
    Flat.swapWith fs p = (.assertionFailed, fs) := by
  have h3 : ¬(1 ≤ fs.size - 1 - p ∧ fs.size - 1 - p ≤ Flat.maxSwapDepth) :=
    fun hc => (depth_iff fs.size p).mp hc h
  simp only [Flat.swapWith, Flat.isFinal, Flat.depthOf, BitVec.lt_def, h1, h2, h3, beq_iff_eq,
    not_true_eq_false, not_false_eq_true, ↓reduceIte]

-- One of the three asserts fails. The failure run of the proof has this hypothesis, not the
-- branch that fails.
theorem sw_err (fs : Flat.St) (p : Word)
    (h : ¬ (p.toNat < fs.size.toNat ∧ Flat.get fs.dest p ≠ p
      ∧ ¬ 15 < (fs.size - p + BitVec.ofInt 64 (-2)).toNat)) :
    Flat.swapWith fs p = (.assertionFailed, fs) := by
  by_cases h1 : p.toNat < fs.size.toNat
  · by_cases h2 : Flat.get fs.dest p = p
    · exact sw_err2 fs p h1 h2
    · exact sw_err3 fs p h1 h2 (Classical.byContradiction fun h3 => h ⟨h1, h2, h3⟩)
  · exact sw_err1 fs p h1

theorem sw_ok (fs : Flat.St) (p : Word) (h1 : p.toNat < fs.size.toNat)
    (h2 : Flat.get fs.dest p ≠ p) (h : ¬ 15 < (fs.size - p + BitVec.ofInt 64 (-2)).toNat) :
    Flat.swapWith fs p = (.done, posFix (posFix { Flat.stackSwap fs p with
      dest := swapD fs.dest p (fs.size - 1) } p) (fs.size - 1)) := by
  have h3 := (depth_iff fs.size p).mpr h
  simp only [Flat.swapWith, Flat.isFinal, Flat.depthOf, BitVec.lt_def, h1, h2, h3, beq_iff_eq,
    not_true_eq_false, and_self, ↓reduceIte, swapDest_eq]
  rfl

/-! ## `flat` of the ghost after the stores -/

theorem none_toNat : Flat.NONE.toNat = 2 ^ 64 - 1 := rfl

theorem posFix_none (g : G) (b : Word) (hb : b.toNat < MAX_N) (h : g.h.dest[b.toNat] = Flat.NONE) :
    posFix (flat g) b = flat g := by
  simp [posFix, flat, get_eq _ _ hb, h]

theorem posFix_some (g : G) (b : Word) (hb : b.toNat < MAX_N)
    (hd : g.h.dest[b.toNat].toNat < MAX_N) :
    posFix (flat g) b
      = flat { g with h := { g.h with pos := g.h.pos.set g.h.dest[b.toNat].toNat b hd } } := by
  have hne : g.h.dest[b.toNat] ≠ Flat.NONE := by
    intro e; rw [e, none_toNat] at hd; simp [MAX_N] at hd
  simp only [posFix, flat, get_eq _ _ hb, ne_eq, hne, not_false_eq_true, ↓reduceIte,
    put_eq_set _ _ _ hd]

-- The slot of the top word after the `movl` and the two `movb`.
theorem ofWord_411 (a b : Word) :
    StackSlot.ofWord (a.extractLsb' 48 16 ++ b.extractLsb' 40 8 ++ b.extractLsb' 32 8
      ++ b.extractLsb' 0 32) = StackSlot.ofWord b := by
  simp only [StackSlot.ofWord, StackSlot.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> bv_decide

-- The stores of `Flat.stackSwap` and the two stores of `m_destinationOf`.
theorem flat_swap (g : G) (hok : g.Ok) (p : Word) (hp : p.toNat < g.h.len.toNat)
    (hn : g.h.nops.toNat < 6 * g.h.n.toNat + g.xo) (hpn : p.toNat < g.h.n.toNat + g.xs)
    (ht : (g.h.len - 1).toNat < g.h.n.toNat + g.xs) (hpM : p.toNat < MAX_N)
    (htM : (g.h.len - 1).toNat < MAX_N) (w : Word)
    (hw : StackSlot.ofWord w = StackSlot.ofWord g.stk[p.toNat]) (r : OpR)
    (hr : r.op = Op.swapW (g.h.len - 1 - p)) :
    flat { h := { g.h with
             nops := g.h.nops + 1#64,
             dest := (g.h.dest.set p.toNat g.h.dest[(g.h.len - 1).toNat] hpM).set
               (g.h.len - 1).toNat g.h.dest[p.toNat] htM },
           xs := g.xs, xo := g.xo,
           stk := (g.stk.set p.toNat g.stk[(g.h.len - 1).toNat] hpn).set (g.h.len - 1).toNat w ht,
           ops := g.ops.set g.h.nops.toNat r hn, tgt := g.tgt, spl := g.spl }
      = { Flat.stackSwap (flat g) p with dest := swapD (flat g).dest p ((flat g).size - 1) } := by
  have hN := hok.n
  have hx := hok.xo
  have hs : (g.h.nops + 1#64).toNat = g.h.nops.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [MAX_N] at hN hx; omega
  have hl : (g.stk.toList.map StackSlot.ofWord).length = g.h.n.toNat + g.xs := by simp
  have e1 := (get_eq _ _ htM).symm.trans
    (get_vec (g.stk.toList.map StackSlot.ofWord) _ (by rw [hl]; exact ht) htM)
  have e2 := (get_eq _ _ hpM).symm.trans
    (get_vec (g.stk.toList.map StackSlot.ofWord) _ (by rw [hl]; exact hpn) hpM)
  simp only [flat, Flat.stackSwap, swapD, get_eq _ _ hpM, get_eq _ _ htM, put_eq_set _ _ _ hpM,
    put_eq_set _ _ _ htM, Vector.toList_set, List.map_set, hs, Flat.St.mk.injEq, true_and,
    and_true]
  refine ⟨?_, ?_⟩
  · have b1 : (g.h.len - 1).toNat < ((g.stk.toList.map StackSlot.ofWord).set p.toNat
        (StackSlot.ofWord g.stk[(g.h.len - 1).toNat])).length := by simp; exact ht
    rw [vec_set _ _ _ b1 htM, vec_set _ _ _ (by rw [hl]; exact hpn) hpM, e1, e2]
    simp [hw]
  · have b2 : g.h.nops.toNat < g.ops.toList.length := by simp; exact hn
    rw [take_set_succ _ _ _ b2, List.map_append, List.map_singleton, hr]

-- `posFix_some` with the destination as a parameter.
theorem posFix_some' (g : G) (b : Word) (hb : b.toNat < MAX_N) (d : Word)
    (hdM : d.toNat < MAX_N) (hd : g.h.dest[b.toNat] = d) :
    posFix (flat g) b = flat { g with h := { g.h with pos := g.h.pos.set d.toNat b hdM } } := by
  subst hd; exact posFix_some g b hb hdM

-- The record of the asm: `movb $0`, `movb %sil` (`sil` is `size + ~pos`), `movl $0`, `movb $1`,
-- `movb $5`.
theorem op_eq (l p : Word) :
    (⟨BitVec.ofInt 8 0, BitVec.ofInt 8 ((l + ~~~p).extractLsb' 0 8).toInt,
      ⟨BitVec.ofInt 32 0, BitVec.ofInt 8 1, BitVec.ofInt 8 5⟩⟩ : Op) = Op.swapW (l - 1 - p) := by
  simp only [Op.swapW, StackSlot.junk, BitVec.ofInt_toInt, Op.mk.injEq, StackSlot.mk.injEq]
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  bv_decide


/-! ## `mem_load`

The main block has 15 sep hypotheses, one for each memory after a store. `sep_load` tries each
lemma on each of them. `mem_load` takes the memory `m` of the first load in the goal, and tries the
lemmas only on the hypotheses `h : P.get m`. If no hypothesis is on `m`, it takes the memory under
the last store of `m`, and so on. (A load between the parts of `Wd.store411` needs the hypothesis
before the first part.) The match is reducible, as in `apply`. Untrusted: it only selects a lemma.
-/

open Lean in
/-- `m`, then the memories under the stores of `m`, the last store first. -/
partial def memChain (m : Expr) : List Expr :=
  if m.isAppOfArity ``Mem.storeInt 5 then m :: memChain (m.getArg! 1) else [m]

open Lean Meta Elab Tactic in
elab "mem_load " "[" ls:term,* "]" : tactic => withMainContext do
  let some ld := (← instantiateMVars (← getMainTarget)).find? (·.isAppOfArity ``Mem.loadInt 4)
    | throwError "mem_load: no load in the goal"
  for m in memChain (ld.getArg! 1) do
    let mut found := false
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty := (← instantiateMVars d.type).consumeMData
      unless ty.isAppOfArity ``MProp.get 3 do continue
      unless ← withNewMCtxDepth <| withReducible <| isDefEq ty.appArg! m do continue
      found := true
      for l in ls.getElems do
        let s ← saveState
        try
          let hs ← Term.exprToSyntax d.toExpr
          Term.withoutErrToSorry <| evalTactic (← `(tactic|
            focus ((with_reducible apply $l $hs) <;> assumption) <;> done))
          return
        catch _ => s.restore
    if found then break
  throwError "mem_load: no lemma gives this load from the sep hyps on its memory"

/-! ## The invariants of the labels -/

/-- `.LB.Emission.swapWith.0`: the stores before the `m_positionOf` store of the top slot `b` are done. -/
def inv37 (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) (t : MachineData) :
    Prop :=
  ∃ g' b, Kp S g' F s ra [] t ∧ g'.Ok ∧ Keep g g' ∧ t.regs.rax.toBitVec = S
    ∧ t.regs.rcx.toBitVec = b ∧ b.toNat < MAX_N
    ∧ (Flat.get g'.h.dest b = Flat.NONE ∨ (Flat.get g'.h.dest b).toNat < MAX_N)
    ∧ Flat.swapWith (flat g) (rsi s) = (.done, posFix (flat g') b)

/-- `.LB.Emission.swapWith.1`: all the stores are done, and the status is `done`. -/
def inv38 (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) (t : MachineData) :
    Prop :=
  ∃ g', Kp S g' F s ra [] t ∧ g'.Ok ∧ Keep g g'
    ∧ flat g' = (Flat.swapWith (flat g) (rsi s)).2 ∧ (Flat.swapWith (flat g) (rsi s)).1 = .done

/-- `.LB.Emission.swapWith.2`: `ecx` holds the status. -/
def inv35 (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) (t : MachineData) :
    Prop :=
  ∃ g', Kp S g' F s ra [] t ∧ g'.Ok ∧ Keep g g'
    ∧ flat g' = (Flat.swapWith (flat g) (rsi s)).2
    ∧ t.regs.rcx.toBitVec.setWidth 8 = code (Flat.swapWith (flat g) (rsi s)).1

end SwapWith

open SwapWith in
theorem swapWith_unit [Host] [FunDecls] : UnitThm swapWithAsm swapWithA 0 swapWithQ := by
  intro S g F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨fr, v, hfr, hm⟩ := hpre.mem
  obtain rfl : fr = [] := List.length_eq_zero_iff.mp hfr
  have hk0 : Kp S g F s ra [] (s.pushRa ra) := Kp.init hm
  refine Program.WP.cfg (fun
      | .entry, t => t = s.pushRa ra
      | .label "_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset", t => t = s.pushRa ra
      | .label ".LB.Emission.swapWith.0", t => inv37 S g F s ra t
      | .label ".LB.Emission.swapWith.1", t => inv38 S g F s ra t
      | .label ".LB.Emission.swapWith.2", t => inv35 S g F s ra t
      | _, _ => False)
    (fun | _, _ => 0) ?_ rfl
  cfg_blocks
  case entry t ht => subst ht; kvcgen64
  case «_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset» t ht =>
    subst ht
    have hS : (s.pushRa ra).regs.rdi.toBitVec = S := hpre.rdi
    have hok := hpre.ok
    have hm0 := hk0.mem
    obtain ⟨hn, hdok⟩ := hpre.args
    have hN := hok.n
    have hx := hok.xo
    have hX := hok.xs
    have hLn := hok.len
    have hpM {x : Word} (h : x.toNat < g.h.len.toNat) : x.toNat < MAX_N :=
      Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h hLn) hX
    by_cases c : (s.pushRa ra).regs.rsi.toBitVec.toNat < g.h.len.toNat
        ∧ Flat.get g.h.dest (s.pushRa ra).regs.rsi.toBitVec ≠ (s.pushRa ra).regs.rsi.toBitVec
        ∧ ¬ 15 < (g.h.len - (s.pushRa ra).regs.rsi.toBitVec + BitVec.ofInt 64 (-2)).toNat
    · -- The three asserts pass.
      obtain ⟨hp, hd, hdep⟩ := c
      have hpn : (s.pushRa ra).regs.rsi.toBitVec.toNat < g.h.n.toNat + g.xs :=
        Nat.lt_of_lt_of_le hp hLn
      have hpM' := hpM hp
      have hdep' := (depth_iff _ _).mpr hdep
      have hpt : (s.pushRa ra).regs.rsi.toBitVec.toNat < (g.h.len - 1#64).toNat := by
        have := hdep'.1; simp only [BitVec.le_def] at this; bv_omega
      have htl : (g.h.len - 1#64).toNat < g.h.len.toNat := by bv_omega
      have ht : (g.h.len - 1#64).toNat < g.h.n.toNat + g.xs := Nat.lt_of_lt_of_le htl hLn
      have htM := hpM htl
      have hdp := hdok _ hp
      have hdt := hdok _ htl
      simp only [flat, BitVec.ofNat_toNat, BitVec.setWidth_eq, get_eq _ _ hpM', get_eq _ _ htM] at hdp hdt
      -- The view after each store of the asm, in the order of the asm.
      have h1 := View.store_stk hm0 hpn g.stk[(g.h.len - 1#64).toNat]
      have h2 := store411_slot h1 ht (g.stk[(s.pushRa ra).regs.rsi.toBitVec.toNat].extractLsb' 0 32)
        (g.stk[(s.pushRa ra).regs.rsi.toBitVec.toNat].extractLsb' 32 8)
        (g.stk[(s.pushRa ra).regs.rsi.toBitVec.toNat].extractLsb' 40 8)
      have h3 := View.store_nops h2 (g.h.nops + 1#64)
      have hf := View.focus h3 (i := g.h.nops.toNat) hn
      have hr1 := OpM.store_kind hf 0
      have hr2 := OpM.store_depth hr1
        ((g.h.len + ~~~(s.pushRa ra).regs.rsi.toBitVec).extractLsb' 0 8).toInt
      have hr3 := OpM.store_payload hr2 0
      have hr4 := OpM.store_skind hr3 1
      have hr5 := OpM.store_sop hr4 5
      have h8 := View.unfocus hr5 hn
      have h9 := View.store_dest h8 hpM' g.h.dest[(g.h.len - 1#64).toNat]
      have h10 := View.store_dest h9 htM g.h.dest[(s.pushRa ra).regs.rsi.toBitVec.toNat]
      dsimp only at h2 h3 hf hr1 hr2 hr3 hr4 hr5 h8 h9 h10
      have hd' : (s.pushRa ra).regs.rsi.toBitVec ≠ g.h.dest[(s.pushRa ra).regs.rsi.toBitVec.toNat] := by
        rw [get_eq _ _ hpM'] at hd; exact Ne.symm hd
      have hnops : (g.h.nops + 1#64).toNat ≤ 6 * g.h.n.toNat + g.xo := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [MAX_N] at hN hx; omega
      -- `Flat.swapWith` before the `m_positionOf` stores, on the ghost of `h10`.
      have hres := (sw_ok (flat g) _ hp hd hdep).trans (by
        rw [← flat_swap g hok _ hp hn hpn ht hpM' htM
          ((g.stk.set (s.pushRa ra).regs.rsi.toBitVec.toNat g.stk[(g.h.len - 1#64).toNat]
              hpn)[(g.h.len - 1#64).toNat].extractLsb' 48 16
            ++ g.stk[(s.pushRa ra).regs.rsi.toBitVec.toNat].extractLsb' 40 8
            ++ g.stk[(s.pushRa ra).regs.rsi.toBitVec.toNat].extractLsb' 32 8
            ++ g.stk[(s.pushRa ra).regs.rsi.toBitVec.toNat].extractLsb' 0 32)
          (ofWord_411 _ _)
          { g.ops[g.h.nops.toNat] with op := ⟨BitVec.ofInt 8 0,
              BitVec.ofInt 8 ((g.h.len + ~~~(s.pushRa ra).regs.rsi.toBitVec).extractLsb' 0 8).toInt,
              ⟨BitVec.ofInt 32 0, BitVec.ofInt 8 1, BitVec.ofInt 8 5⟩⟩ }
          (op_eq _ _)])
      kvcgen64 [notq_spec]
      -- The goal only: `simp` on the 15 sep hypotheses in each of the 35 goals takes about 3 s.
      -- The cases below normalize the branch hypotheses that they use.
      all_goals symexec_norm at ⊢
      all_goals try simp only [hS, rd_eq, rdb_eq, Fld.fold_stack_size, Fld.fold_stack_data,
        Fld.fold_stack_trace, Fld.fold_stack_traceSize, ↓Fld.fold_mapping_destinationOf,
        ↓Fld.fold_mapping_positionOf, fold_slot, fold_op, top_slot, add_neg_one, byte_rt,
        View.rd_len hm0, View.rd_data hm0, rd_dest hm0 hpM', rd_slot hm0 ht, rd32_slot hm0 hpn,
        rdb4_slot hm0 hpn, rdb5_slot hm0 hpn, Idioms.cf_sub, BitVec.ofNat_eq_ofNat,
        View.rd_len h1, View.rd_data h1, View.rd_len h2, View.rd_nops h2, View.rd_ops h3,
        View.rd_len h8, rd_dest h8 hpM', rd_dest h8 htM, rd_dest h10 hpM',
        Vector.getElem_set_self, Vector.getElem_set_ne htM hpM' (Nat.ne_of_lt hpt).symm]
      vc_by_shape
      | closed => decide
      | load => first
        | mem_load [View.isSome_data, View.isSome_len, View.isSome_ops, View.isSome_nops,
            View.isSome_slot, View.isSome_pos, View.isSome_dest, OpM.isSome_kind,
            OpM.isSome_depth, OpM.isSome_payload, OpM.isSome_skind, OpM.isSome_sop,
            isSome32_slot, isSome4_slot, isSome5_slot, isSome4_411, isSome5_411]
        | skip
      | goto ".LB.Emission.swapWith.2" =>
        -- The paths of a failed assert: the branch hypothesis contradicts `c`. The big
        -- hypotheses go first, else `simp at *` runs out of heartbeats.
        clear hres h10 h9 h8 hr5 hr4 hr3 hr2 hr1 hf h3 h2 h1
        symexec_norm
        simp only [hS, rd_eq, Fld.fold_stack_size, ↓Fld.fold_mapping_destinationOf,
          View.rd_len hm0, rd_dest hm0 hpM', Idioms.cf_sub, sub_beq_zero, ↓ja15, hp, hd', hdep,
          not_true_eq_false, Bool.not_eq_false', Bool.not_eq_true', decide_eq_true_eq,
          decide_eq_false_iff_not, beq_iff_eq, beq_eq_false_iff_ne] at *
      -- The three paths after `cmpq $-1` on the new `dest[pos]`, that is the old `dest[top]`. The
      -- last hypothesis is the branch.
      all_goals
        rename_i hc
        symexec_norm at hc
        simp only [hS, rd_eq, rdb_eq, Fld.fold_stack_size, Fld.fold_stack_data,
          Fld.fold_stack_trace, Fld.fold_stack_traceSize, ↓Fld.fold_mapping_destinationOf,
          fold_slot, fold_op, top_slot, add_neg_one, byte_rt, View.rd_len hm0, View.rd_data hm0,
          rd_slot hm0 ht, rd32_slot hm0 hpn, rdb4_slot hm0 hpn, rdb5_slot hm0 hpn, sub_beq_zero,
          BitVec.ofNat_eq_ofNat, View.rd_len h1, View.rd_data h1, View.rd_len h2,
          View.rd_nops h2, View.rd_ops h3, View.rd_len h8, rd_dest h8 hpM', rd_dest h8 htM,
          rd_dest h10 hpM', Vector.getElem_set_self,
          Vector.getElem_set_ne htM hpM' (Nat.ne_of_lt hpt).symm, beq_iff_eq,
          beq_eq_false_iff_ne] at hc
      vc_by_shape
      | goto ".LB.Emission.swapWith.0" =>
        -- `je .LB.Emission.swapWith.0`: the new `dest[pos]` is `NONE`, no store.
        cfg_goto
        · exact Kp.stack (fr := []) ⟨h10, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · refine ⟨_, _, ⟨h10, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
            Keep.ok (g := g) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hok hLn hnops,
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hS, rfl, htM, ?_, ?_⟩
          · simp only [get_eq _ _ htM, Vector.getElem_set_self]
            exact hdp.imp_right fun h => Nat.lt_of_lt_of_le h hN
          · show Flat.swapWith (flat g) (s.pushRa ra).regs.rsi.toBitVec = _
            rw [hres, posFix_none _ _ hpM']
            · rfl
            · -- `hres` has `len - 1`, from `flat_swap`; `ofNat_eq_ofNat` gives `len - 1#64`.
              simp only [BitVec.ofNat_eq_ofNat, Vector.getElem_set_self,
                Vector.getElem_set_ne htM hpM' (Nat.ne_of_lt hpt).symm]
              exact hc
        · simp
      | load =>
        -- `m_positionOf[dest[pos]]`: the new `dest[pos]` is not `NONE`.
        have hdtM : g.h.dest[(g.h.len - 1#64).toNat].toNat < MAX_N :=
          Nat.lt_of_lt_of_le (hdt.resolve_left hc) hN
        exact View.isSome_pos h10 hdtM
      | other =>
        -- The store `pos[dest[pos]] := pos`, then `.LB.Emission.swapWith.0`.
        have hdtM : g.h.dest[(g.h.len - 1#64).toNat].toNat < MAX_N :=
          Nat.lt_of_lt_of_le (hdt.resolve_left hc) hN
        have h11 := View.store_pos h10 hdtM (s.pushRa ra).regs.rsi.toBitVec
        refine ⟨_, _, ⟨h11, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
          Keep.ok (g := g) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hok hLn hnops,
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hS, rfl, htM, ?_, ?_⟩
        · simp only [get_eq _ _ htM, Vector.getElem_set_self]
          exact hdp.imp_right fun h => Nat.lt_of_lt_of_le h hN
        · show Flat.swapWith (flat g) (s.pushRa ra).regs.rsi.toBitVec = _
          rw [hres, posFix_some' _ _ hpM' _ hdtM]
          · rfl
          · -- `hres` has `len - 1`, from `flat_swap`; `ofNat_eq_ofNat` gives `len - 1#64`.
            simp only [BitVec.ofNat_eq_ofNat, Vector.getElem_set_self,
              Vector.getElem_set_ne htM hpM' (Nat.ne_of_lt hpt).symm]
    · -- An assert fails: `ecx = 2` and no store.
      kvcgen64 [notq_spec]
      all_goals symexec_norm
      all_goals try simp only [hS, rd_eq, Fld.fold_stack_size, ↓Fld.fold_mapping_destinationOf,
        View.rd_len hm0, Idioms.cf_sub, sub_beq_zero, ↓ja15, Bool.not_eq_false', Bool.not_eq_true',
        decide_eq_true_eq, decide_eq_false_iff_not, beq_iff_eq, beq_eq_false_iff_ne] at *
      -- The paths that pass the three asserts: the branch hypotheses contradict `c`.
      all_goals try
        exfalso
        have h1 : (s.pushRa ra).regs.rsi.toBitVec.toNat < g.h.len.toNat := by
          with_reducible assumption
        refine c ⟨h1, ?_, by with_reducible assumption⟩
        rw [get_eq _ _ (hpM h1), ← rd_dest hm0 (hpM h1)]
        exact Ne.symm (by with_reducible assumption)
      vc_by_shape
      | load => first
        | view_load
        | -- `m_destinationOf[pos]`, after `pos < size`.
          have := hpM (x := (s.pushRa ra).regs.rsi.toBitVec) (by with_reducible assumption)
          view_load
      | goto ".LB.Emission.swapWith.2" =>
        -- `jnb`, `je` or `ja`: `c` gives the result. (`symexec_norm at *` unfolds `rsi s`, so `e`
        -- comes after it.)
        have e : Flat.swapWith (flat g) (rsi s) = (.assertionFailed, flat g) := sw_err _ _ c
        cfg_goto
        · exact Kp.stack (fr := []) ⟨hm0, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · exact ⟨g, ⟨hm0, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hok,
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by rw [e], by rw [e]; rfl⟩
        · simp
  case «.LB.Emission.swapWith.0» t ht =>
    -- `movq dest[b], %rdx; cmpq $-1, %rdx; je .LB.Emission.swapWith.1; movq %rcx, pos[dest[b]]`.
    obtain ⟨g', b, hk, hok, hkeep, hax, hcx, hb, hdb, hres⟩ := ht
    have hm := hk.mem
    rw [get_eq _ _ hb] at hdb
    kvcgen64
    all_goals symexec_norm
    all_goals try simp only [hax, hcx, rd_eq, ↓Fld.fold_mapping_destinationOf,
      ↓Fld.fold_mapping_positionOf, rd_dest hm hb]
    vc_by_shape
    | closed => simp
    | load => first
      | view_load
      | skip
    -- The three paths after `cmpq $-1` on `dest[b]`. The last hypothesis is the branch.
    all_goals
      rename_i hc
      simp only [hax, hcx, rd_eq, ↓Fld.fold_mapping_destinationOf, rd_dest hm hb, cmp_none,
        beq_iff_eq, beq_eq_false_iff_ne] at hc
    vc_by_shape
    | goto ".LB.Emission.swapWith.1" =>
      -- `je .LB.Emission.swapWith.1`: `dest[b] = -1`, no store.
      cfg_goto
      · exact Kp.stack (hk.next rfl rfl rfl rfl rfl rfl rfl rfl)
      · exact ⟨g', hk.next rfl rfl rfl rfl rfl rfl rfl rfl, hok, hkeep,
          by rw [rsi_eq, hres, posFix_none _ _ hb hc], by rw [rsi_eq, hres]⟩
      · simp
    | load =>
      -- `m_positionOf[dest[b]]`: `dest[b]` is not `NONE`.
      have hdM : g'.h.dest[b.toNat].toNat < MAX_N := hdb.resolve_left hc
      view_load
    | other =>
      -- The store `pos[dest[b]] := b`.
      have hdM : g'.h.dest[b.toNat].toNat < MAX_N := hdb.resolve_left hc
      have h1 := View.store_pos hm hdM b
      refine ⟨_, ⟨h1, hk.sp, hk.bx, hk.bp, hk.r12, hk.r13, hk.r14, hk.r15⟩,
        Keep.ok (g := g') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hok hok.len hok.nops,
        ⟨hkeep.tgtp, hkeep.n, hkeep.splp, hkeep.data, hkeep.ops, hkeep.xs, hkeep.xo, hkeep.tgt, hkeep.spl⟩, ?_, ?_⟩
      · rw [rsi_eq, hres, posFix_some _ _ hb hdM]
      · rw [rsi_eq, hres]
  case «.LB.Emission.swapWith.1» t ht =>
    -- `movl $0, %ecx`, then `.LB.Emission.swapWith.2`.
    obtain ⟨g', hk, hok, hkeep, hflat, hdone⟩ := ht
    kvcgen64
    vc_by_shape
    | other =>
      exact ⟨g', hk.next rfl rfl rfl rfl rfl rfl rfl rfl, hok, hkeep, hflat, by rw [hdone]; rfl⟩
    | closed => simp
  case «.LB.Emission.swapWith.2» t ht =>
    obtain ⟨g', hk, hok, hkeep, hflat, hcode⟩ := ht
    kvcgen64
    vc_by_shape
    | retAddr => exact (show t.retAddr.isSome = true by simp [hk.retAddr])
    | ret =>
      exact Kp.ret (hk.next rfl rfl rfl rfl rfl rfl rfl rfl) rfl hok fun t' _ hax =>
        ⟨hkeep, hflat, by show (rax t').setWidth 8 = _; rw [hax]; exact (al_movl _).trans hcode⟩

end Bbu.Unit
