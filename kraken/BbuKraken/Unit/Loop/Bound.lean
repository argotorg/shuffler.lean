import BbuKraken.Unit.Loop.Step

/-!
# `buildBottomUp`: `bound` and the swap of the destinations (part P5)

The blocks `.8` (the source `b = pos[T]`), `.18`, `.20`, `.19`, `.21` (the
`candidate` loop) and `.9`, `.10` (`swapDestinations` inline).
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace Bbu.Unit
open Bbu.Sep
namespace Loop

/-! ## Local lemmas: the slot compare and the loads of `data` and `dest` -/

namespace Bound

-- `xorq; salq $16` is zero if and only if the slots (the low 6 bytes) are equal.
theorem slot_shl_iff (a b : Word) :
    (a ^^^ b) <<< 16 = 0#64 ↔ StackSlot.ofWord a = StackSlot.ofWord b := by
  rw [Idioms.slot_eq_iff]
  simp only [StackSlot.ofWord, StackSlot.mk.injEq]

section
variable {S : Addr} {g : G} {R : MProp 64} {m : Mem 64}

theorem get_eq {α : Type} [Inhabited α] (v : Vector α MAX_N) {i : Word} (hi : i.toNat < MAX_N) :
    Flat.get v i = v[i.toNat] := by
  simp [Flat.get, hi]

theorem get_data (hok : g.Ok) {i : Word} (hi : i.toNat < g.h.n.toNat + g.xs) :
    Flat.get (flat g).data i = StackSlot.ofWord g.stk[i.toNat] := by
  simp [Flat.get, flat, vec, Nat.lt_of_lt_of_le hi hok.xs, hi]

theorem none_eq : Flat.NONE = 18446744073709551615#64 := by decide

-- The slot of the load `(%rcx,%rax,8)` with `rcx` the address of the stack data.
theorem rd_data_slot (h : (View S g ∗ R).get m) (hok : g.Ok) {x : Word}
    (hi : x.toNat < g.h.n.toNat + g.xs) :
    StackSlot.ofWord (BitVec.ofInt 64 (m.loadInt (g.h.data + x * 8#64) 8).get!)
      = Flat.get (flat g).data x := by
  rw [get_data hok hi, fold_slot]
  exact congrArg StackSlot.ofWord (View.rd_slot h hi)

theorem isSome_data (h : (View S g ∗ R).get m) {x : Word} (hi : x.toNat < g.h.n.toNat + g.xs) :
    (m.loadInt (g.h.data + x * 8#64) 8).isSome = true := by
  rw [fold_slot]; exact View.isSome_slot h hi

-- The load `24(%r12)`: the address of the stack data.
theorem rd_data_ptr (h : (View S g ∗ R).get m) :
    BitVec.ofInt 64 (m.loadInt (S + 24#64) 8).get! = g.h.data :=
  View.rd_data h

theorem isSome_data_ptr (h : (View S g ∗ R).get m) : (m.loadInt (S + 24#64) 8).isSome = true :=
  View.isSome_data h

-- The load `8248(%r12,%rbx)` with `rbx = 8 * x`: `pos[x]`.
theorem rd_pos_get (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < MAX_N) :
    BitVec.ofInt 64 (m.loadInt (S + x * 8#64 + 8248#64) 8).get! = Flat.get g.h.pos x := by
  rw [Fld.fold_mapping_positionOf, get_eq _ hx]
  exact View.rd_pos h hx

theorem isSome_pos (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < MAX_N) :
    (m.loadInt (S + x * 8#64 + 8248#64) 8).isSome = true := by
  rw [Fld.fold_mapping_positionOf]; exact View.isSome_pos h hx

-- The load `56(%r12,%rax,8)`: `dest[rax]`.
theorem rd_dest_get (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < MAX_N) :
    BitVec.ofInt 64 (m.loadInt (S + x * 8#64 + 56#64) 8).get! = Flat.get g.h.dest x := by
  obtain ⟨R', h'⟩ := View.arr_dest h
  rw [Fld.fold_mapping_destinationOf, get_eq _ hx]
  exact (Arr.rd h' (by simpa using hx)).trans (by simp)

theorem isSome_dest (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < MAX_N) :
    (m.loadInt (S + x * 8#64 + 56#64) 8).isSome = true := by
  rw [Fld.fold_mapping_destinationOf]; exact View.isSome_dest h hx


theorem put_eq {α : Type} (v : Vector α MAX_N) {i : Word} (hi : i.toNat < MAX_N) (x : α) :
    Flat.put v i x = v.set i.toNat x hi := by
  ext j hj; simp [Flat.put, Vector.getElem_set, Vector.getElem_setIfInBounds]

-- The stores `movq %r, 56(%r12,%i,8)` and `movq %r, 8248(%r12,%i,8)` with `Flat.put`.
theorem store_dest (h : (View S g ∗ R).get m) {i : Word} (hi : i.toNat < MAX_N) (x : Word) :
    (View S { g with h := { g.h with dest := Flat.put g.h.dest i x } } ∗ R).get
      (m.storeInt (S + i * 8#64 + 56#64) 8 x.toInt) := by
  rw [put_eq _ hi, Fld.fold_mapping_destinationOf]; exact View.store_dest h hi x

theorem store_pos (h : (View S g ∗ R).get m) {i : Word} (hi : i.toNat < MAX_N) (x : Word) :
    (View S { g with h := { g.h with pos := Flat.put g.h.pos i x } } ∗ R).get
      (m.storeInt (S + i * 8#64 + 8248#64) 8 x.toInt) := by
  rw [put_eq _ hi, Fld.fold_mapping_positionOf]; exact View.store_pos h hi x

end

/-! ## The ghost of the swap of the destinations -/

-- The ghost after `.9` writes `dest[a]` and `dest[b]`.
def swapG (g : G) (a b : Word) : G :=
  { g with h := { g.h with
    dest := Flat.put (Flat.put g.h.dest a (Flat.get g.h.dest b)) b (Flat.get g.h.dest a) } }

-- The ghost after a write of `pos[c] := x`.
def posG (g : G) (c x : Word) : G :=
  { g with h := { g.h with pos := Flat.put g.h.pos c x } }

section
variable {S : Addr} {g g₀ : G} {R : MProp 64} {m : Mem 64} {a b c x : Word}

theorem mem_swapG (h : (View S g ∗ R).get m) (ha : a.toNat < MAX_N) (hb : b.toNat < MAX_N) :
    (View S (swapG g a b) ∗ R).get ((m.storeInt (S + a * 8#64 + 56#64) 8
      (Flat.get g.h.dest b).toInt).storeInt (S + b * 8#64 + 56#64) 8 (Flat.get g.h.dest a).toInt) :=
  store_dest (store_dest h ha _) hb _

theorem mem_posG (h : (View S g ∗ R).get m) (hc : c.toNat < MAX_N) (x : Word) :
    (View S (posG g c x) ∗ R).get (m.storeInt (S + c * 8#64 + 8248#64) 8 x.toInt) :=
  store_pos h hc x

theorem ok_swapG (h : g.Ok) : (swapG g a b).Ok := ⟨h.len, h.n, h.xs, h.xo, h.nops, h.spl⟩

theorem ok_posG (h : g.Ok) : (posG g c x).Ok := ⟨h.len, h.n, h.xs, h.xo, h.nops, h.spl⟩

theorem keep_swapG (h : Keep g₀ g) : Keep g₀ (swapG g a b) :=
  ⟨h.tgtp, h.n, h.splp, h.data, h.ops, h.xs, h.xo, h.tgt, h.spl⟩

theorem keep_posG (h : Keep g₀ g) : Keep g₀ (posG g c x) :=
  ⟨h.tgtp, h.n, h.splp, h.data, h.ops, h.xs, h.xo, h.tgt, h.spl⟩

-- After the swap, `dest[a]` is the old `dest[b]`, also for `a = b`.
theorem get_swap_a (v : Vector Word MAX_N) (ha : a.toNat < MAX_N) (hb : b.toNat < MAX_N) :
    Flat.get (Flat.put (Flat.put v a (Flat.get v b)) b (Flat.get v a)) a = Flat.get v b := by
  by_cases e : a = b
  · subst e; exact Flat.get_put_self _ _ ha
  · rw [Flat.get_put_ne _ _ e, Flat.get_put_self _ _ ha]

-- After the swap, `dest[b]` is the old `dest[a]`.
theorem get_swap_b (v : Vector Word MAX_N) (hb : b.toNat < MAX_N) :
    Flat.get (Flat.put (Flat.put v a (Flat.get v b)) b (Flat.get v a)) b = Flat.get v a :=
  Flat.get_put_self _ _ hb

theorem flat_swapG (h : Flat.get (swapG g a b).h.dest a = Flat.NONE) :
    flat (swapG g a b) = Flat.swapHalf (flat g) a b := by
  have h' : Flat.get (Flat.put (Flat.put (flat g).dest a (Flat.get (flat g).dest b)) b
      (Flat.get (flat g).dest a)) a = Flat.NONE := h
  simp only [Flat.swapHalf, h', ne_eq, not_true_eq_false, ↓reduceIte]
  rfl

theorem flat_posG (h : Flat.get (swapG g a b).h.dest a ≠ Flat.NONE) :
    flat (posG (swapG g a b) (Flat.get (swapG g a b).h.dest a) a) = Flat.swapHalf (flat g) a b := by
  have h' : Flat.get (Flat.put (Flat.put (flat g).dest a (Flat.get (flat g).dest b)) b
      (Flat.get (flat g).dest a)) a ≠ Flat.NONE := h
  simp only [Flat.swapHalf, h', ne_eq, not_false_eq_true, ↓reduceIte]
  rfl

-- After `swapHalf`, `dest[b]` is the old `dest[a]`.
theorem dest_half {st : Flat.St} (h : flat g = Flat.swapHalf st a b) (hb : b.toNat < MAX_N) :
    Flat.get g.h.dest b = Flat.get st.dest a := by
  have hd : g.h.dest = Flat.put (Flat.put st.dest a (Flat.get st.dest b)) b (Flat.get st.dest a) :=
    congrArg Flat.St.dest h
  rw [hd]
  exact get_swap_b _ hb

theorem flat_rest_none (h : Flat.get g.h.dest b = Flat.NONE) :
    flat g = Flat.swapRest (flat g) b := by
  have h' : Flat.get (flat g).dest b = Flat.NONE := h
  simp only [Flat.swapRest, h', ne_eq, not_true_eq_false, ↓reduceIte]

theorem flat_rest_pos (h : Flat.get g.h.dest b ≠ Flat.NONE) :
    flat (posG g (Flat.get g.h.dest b) b) = Flat.swapRest (flat g) b := by
  have h' : Flat.get (flat g).dest b ≠ Flat.NONE := h
  simp only [Flat.swapRest, h', ne_eq, not_false_eq_true, ↓reduceIte]
  rfl

end

-- `H` reads only `pendingGenerations`.
theorem H_eq {S : Addr} {T : Word} {t t' : MachineData}
    (h : rd t'.dmem (Fld.pendingGenerations S) = rd t.dmem (Fld.pendingGenerations S)) :
    H S T t' = H S T t := by
  simp only [H, h]

end Bound

theorem b_8 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.8" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, hH, hR⟩ := ht
  have hI := hH.2.2.2.1
  have hTn : t.regs.r14.toBitVec.toNat < g'.h.n.toNat := BitVec.lt_def.mp hH.2.2.1
  have hTx : t.regs.r14.toBitVec.toNat < g'.h.n.toNat + g'.xs := Nat.lt_add_right _ hTn
  have hTm : t.regs.r14.toBitVec.toNat < MAX_N := Nat.lt_of_lt_of_le hTn hok.n
  have hP : BitVec.ofInt 64 (Mem.loadInt t.dmem
      (t.regs.r12.toBitVec + t.regs.r14.toBitVec * 8#64 + 8248#64) 8).get!
        = Flat.get (flat g').pos t.regs.r14.toBitVec := by
    rw [hM.r12]; exact Bound.rd_pos_get hM.mem hTm
  have hC : BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.r12.toBitVec + 24#64) 8).get!
      = g'.h.data := by
    rw [hM.r12]; exact Bound.rd_data_ptr hM.mem
  -- `pos[T] ≠ NONE` gives `pos[T] < size`.
  have hlen : Flat.get (flat g').pos t.regs.r14.toBitVec ≠ Flat.NONE →
      Flat.get (flat g').pos t.regs.r14.toBitVec < g'.h.len := fun hn =>
    ((hI.f.pos _ hH.2.2.1).resolve_left hn).1
  have hpn : Flat.get (flat g').pos t.regs.r14.toBitVec ≠ Flat.NONE →
      (Flat.get (flat g').pos t.regs.r14.toBitVec).toNat < g'.h.n.toNat + g'.xs := fun hn =>
    Nat.lt_of_lt_of_le (BitVec.lt_def.mp (hlen hn)) hok.len
  have hge : ¬(Flat.get (flat g').pos t.regs.r14.toBitVec).toNat < t.regs.r14.toBitVec.toNat →
      Flat.get (flat g').pos t.regs.r14.toBitVec ≥ t.regs.r14.toBitVec := fun hj =>
    BitVec.le_def.mpr (Nat.not_lt.mp hj)
  kvcgen64
  all_goals try symexec_norm
  · rw [hM.r12]; exact Bound.isSome_pos hM.mem hTm
  · -- `.16`: `pos[T] = NONE`.
    rename_i hj
    try idioms at hj
    rw [hP, ← Bound.none_eq] at hj
    rw [Flat.kU3, if_neg (fun h => h hj)] at hR
    cfg_goto
    · exact Mid.stack (hM.next rfl rfl rfl)
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, ⟨hH.1, hH.2⟩, by bv_omega, hR⟩
    · loop_dec
      simp only [H]; omega
  · -- `.28`: `pos[T] < T`.
    rename_i hn hj
    try idioms at hn hj
    rw [hP, ← Bound.none_eq] at hn
    rw [hP] at hj
    rw [Flat.kU3, if_pos hn, Flat.bound_eq,
      if_pos (fun ⟨_, h⟩ => absurd hj (Nat.not_lt.mpr (BitVec.le_def.mp h)))] at hR
    cfg_goto
    · exact Mid.stack (hM.next rfl rfl rfl)
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hR.symm⟩
    · loop_dec
  · rw [hM.r12]; exact Bound.isSome_data_ptr hM.mem
  · rename_i hn _
    try idioms at hn
    rw [hP, ← Bound.none_eq] at hn
    rw [hC, hP]
    exact Bound.isSome_data hM.mem (hpn hn)
  · rw [hC]; exact Bound.isSome_data hM.mem hTx
  · decide
  · -- `.18`: the slots differ; the search for the candidate starts.
    rename_i hn hj hs
    try idioms at hn hj hs
    rw [hP, ← Bound.none_eq] at hn
    rw [hP] at hj
    rw [hC, hP, Bound.slot_shl_iff,
      Bound.rd_data_slot hM.mem hok (hpn hn), Bound.rd_data_slot hM.mem hok hTx] at hs
    rw [Flat.kU3, if_pos hn, Flat.bound_eq, if_neg (not_not_intro ⟨hn, hge hj⟩),
      if_neg (fun e => hs e.symm)] at hR
    cfg_goto
    · exact Mid.stack (hM.next rfl rfl rfl)
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, ⟨hH.1, hH.2⟩, by bv_omega,
        by rw [hP]; exact hlen hn, hC,
        by rw [hP, hC]; exact Bound.rd_data_slot hM.mem hok (hpn hn), by rw [hP]; exact hR⟩
    · loop_dec
      simp only [H]; omega
  · -- `.9`: the slots are equal; the candidate is `T`.
    rename_i hn hj hs
    try idioms at hn hj hs
    rw [hP, ← Bound.none_eq] at hn
    rw [hP] at hj
    rw [hC, hP, Bound.slot_shl_iff,
      Bound.rd_data_slot hM.mem hok (hpn hn), Bound.rd_data_slot hM.mem hok hTx] at hs
    rw [Flat.kU3, if_pos hn, Flat.bound_eq, if_neg (not_not_intro ⟨hn, hge hj⟩),
      if_pos hs.symm] at hR
    simp only [Flat.kB, hs, ne_eq, not_true_eq_false, ↓reduceIte] at hR
    simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
    exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hH.2.1, by bv_omega,
      BitVec.lt_def.mpr (Nat.lt_of_le_of_lt (BitVec.le_def.mp (hge hj)) (BitVec.lt_def.mp (hlen hn))),
      by rw [hP]; exact hlen hn, hI.f, Flat.HInv.bud hI hH.2.2.1, by rw [hP]; exact hR⟩
  · loop_dec
    simp only [H]; omega

theorem b_18 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.18" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, hH, hbx, hdx, hcx, hsi, hR⟩ := ht
  have hI := hH.2.2.2.1
  have hn : (flat g').targetSize.toNat ≤ 1024 := hI.f.n
  have hsz := hI.f.size_le
  have e : t.regs.r15.toBitVec + BitVec.ofInt 64 (-1) = (flat g').size - 1#64 := by
    show _ = g'.h.len - 1#64
    rw [hH.2.1]; bv_omega
  have hdx' : t.regs.rdx.toBitVec < (flat g').size := hdx
  kvcgen64
  all_goals try symexec_norm
  · rename_i hj
    idioms at hj
    rw [e] at hj ⊢
    cfg_goto
    · exact (hM.next rfl rfl rfl).stack
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      refine ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hH, hbx, ?_, ?_, hcx, hsi, hR⟩
      · rw [BitVec.lt_def]; exact hj
      · show _ < (flat g').size; bv_omega
    · loop_dec
      simp only [H]
      have : ((flat g').size - 1#64).toNat < 1024 := by bv_omega
      omega
  · rename_i hj
    idioms at hj
    rw [e] at hj
    cfg_goto
    · exact (hM.next rfl rfl rfl).stack
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      rw [Flat.cf_le (by rw [gt_iff_lt, BitVec.lt_def]; exact hj)] at hR
      simp only [Flat.kB, ne_eq, not_true_eq_false, ↓reduceIte] at hR
      exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hH.2.1, hbx, hdx, hdx, hI.f,
        Flat.HInv.bud hI hH.2.2.1, hR⟩
    · loop_dec
      simp only [H]; omega

theorem b_19 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.19" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, hH, hbx, hda, hax, hcx, hsi, hR⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  all_goals (rename_i hj; idioms at hj)
  · cfg_goto
    · exact (hM.next rfl rfl rfl).stack
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      rw [Flat.cf_le (by rw [gt_iff_lt, BitVec.lt_def]; exact hj)] at hR
      exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hH, hbx, by bv_omega, hR⟩
    · loop_dec
      simp only [H]; omega
  · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
    exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hH, hbx,
      BitVec.lt_def.mpr hj, by bv_omega, hcx, hsi, hR⟩
  · loop_dec
    simp only [H]
    have : (t.regs.rax.toBitVec - 1#64).toNat + 1 = t.regs.rax.toBitVec.toNat := by bv_omega
    omega

theorem b_20 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.20" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, hH, hbx, hda, hax, hcx, hsi, hR⟩ := ht
  have hrn : t.regs.rax.toBitVec.toNat < g'.h.n.toNat + g'.xs :=
    Nat.lt_of_lt_of_le (BitVec.lt_def.mp hax) hok.len
  have hmax : t.regs.rax.toBitVec.toNat < MAX_N := Nat.lt_of_lt_of_le hrn hok.xs
  have hD : StackSlot.ofWord (BitVec.ofInt 64 (Mem.loadInt t.dmem
      (t.regs.rcx.toBitVec + t.regs.rax.toBitVec * 8#64) 8).get!)
        = Flat.get (flat g').data t.regs.rax.toBitVec := by
    rw [hcx]; exact Bound.rd_data_slot hM.mem hok hrn
  have hE : BitVec.ofInt 64 (Mem.loadInt t.dmem
      (t.regs.r12.toBitVec + t.regs.rax.toBitVec * 8#64 + 56#64) 8).get!
        = Flat.get (flat g').dest t.regs.rax.toBitVec := by
    rw [hM.r12]; exact Bound.rd_dest_get hM.mem hmax
  kvcgen64
  all_goals try symexec_norm
  · rw [hcx]; exact Bound.isSome_data hM.mem hrn
  · decide
  · -- `.19`: the slot at `rax` is not the slot of the source.
    rename_i hj
    idioms at hj
    rw [Bound.slot_shl_iff, hD] at hj
    rw [Flat.cf_next hda (fun ⟨e, _⟩ => hj (hsi.trans e.symm))] at hR
    cfg_goto
    · exact Mid.stack (hM.next rfl rfl rfl)
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, ⟨hH.1, hH.2⟩, hbx, hda, hax, hcx, hsi, hR⟩
    · loop_dec
      simp only [H]; omega
  · rw [hM.r12]; exact Bound.isSome_dest hM.mem hmax
  · -- `.19`: the slot at `rax` is final.
    rename_i hj _
    idioms at hj
    rw [hE] at hj
    have hf : Flat.isFinal (flat g') t.regs.rax.toBitVec = true := by
      simp only [Flat.isFinal, beq_iff_eq]; exact hj
    rw [Flat.cf_next hda (by simp [hf])] at hR
    cfg_goto
    · exact Mid.stack (hM.next rfl rfl rfl)
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, ⟨hH.1, hH.2⟩, hbx, hda, hax, hcx, hsi, hR⟩
    · loop_dec
      simp only [H]; omega
  · rw [hcx]; exact Bound.isSome_data hM.mem hrn
  · decide
  · -- `.9`: the candidate is `rax`.
    rename_i hn _ _ _ _ _ hj
    idioms at hn hj
    rw [hE] at hn
    rw [Bound.slot_shl_iff, hD] at hj
    have hf : Flat.isFinal (flat g') t.regs.rax.toBitVec = false := by
      simp only [Flat.isFinal, beq_eq_false_iff_ne]; exact hn
    have hd : Flat.get (flat g').data t.regs.rax.toBitVec
        = Flat.get (flat g').data t.regs.rdx.toBitVec := hj.symm.trans hsi
    rw [Flat.cf_hit hda hd hf] at hR
    simp only [Flat.kB, hd, ne_eq, not_true_eq_false, ↓reduceIte] at hR
    have hI := hH.2.2.2.1
    cfg_goto
    · exact Mid.stack (hM.next rfl rfl rfl)
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hH.2.1, hbx, hax,
        BitVec.lt_trans hda hax, hI.f, Flat.HInv.bud hI hH.2.2.1, hR⟩
    · loop_dec
      simp only [H]; omega
  · -- `.13`: not reachable, the second compare is the first.
    rename_i h1 h2
    idioms at h1 h2
    exact absurd h1 h2

theorem b_21 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.21" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, hH, hbx, hdx, hR⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  cfg_goto
  · exact Mid.stack (hM.next rfl rfl rfl)
  · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
    obtain ⟨_, h15, h14, hI, _⟩ := hH
    simp only [Flat.kB, ne_eq, not_true_eq_false, ↓reduceIte] at hR
    exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, h15, hbx, hdx, hdx, hI.f,
      Flat.HInv.bud hI h14, hR⟩
  · loop_dec
    simp only [H]; omega

theorem b_9 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.9" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, h15, hbx, hax, hdx, hF, hB, hR⟩ := ht
  have ha : t.regs.rax.toBitVec.toNat < MAX_N :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (BitVec.lt_def.mp hax) hok.len) hok.xs
  have hb : t.regs.rdx.toBitVec.toNat < MAX_N :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (BitVec.lt_def.mp hdx) hok.len) hok.xs
  have hLa := Bound.rd_dest_get hM.mem ha
  have hLb := Bound.rd_dest_get hM.mem hb
  have hm2 := Bound.mem_swapG hM.mem ha hb
  have hLa2 := Bound.rd_dest_get hm2 ha
  -- The new `dest[a]` is the old `dest[b]`, a destination below `n`.
  have hc : (Flat.get (Bound.swapG g' t.regs.rax.toBitVec t.regs.rdx.toBitVec).h.dest
      t.regs.rax.toBitVec).toNat < MAX_N := by
    rw [show Flat.get (Bound.swapG g' t.regs.rax.toBitVec t.regs.rdx.toBitVec).h.dest
        t.regs.rax.toBitVec = Flat.get g'.h.dest t.regs.rdx.toBitVec from Bound.get_swap_a _ ha hb]
    exact Nat.lt_of_lt_of_le (BitVec.lt_def.mp (hF.dest _ hdx)) hok.n
  have hm3 := Bound.mem_posG hm2 hc t.regs.rax.toBitVec
  kvcgen64
  all_goals try symexec_norm
  · rw [hM.r12]; exact Bound.isSome_dest hM.mem ha
  · rw [hM.r12]; exact Bound.isSome_dest hM.mem hb
  · rw [hM.r12]; exact Bound.isSome_dest hM.mem ha
  · rw [hM.r12, hLb]; exact Bound.isSome_dest (Bound.store_dest hM.mem ha _) hb
  · rw [hM.r12, hLa, hLb]; exact Bound.isSome_dest hm2 ha
  · -- `.10`: the new `dest[a]` is `NONE`.
    rename_i hj
    idioms at hj
    rw [hM.r12, hLa, hLb, hLa2, ← Bound.none_eq] at hj
    cfg_goto
    · rw [hM.r12, hLa, hLb]; exact Mid.stack (hM.step hm2 rfl rfl)
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      rw [hM.r12, hLa, hLb]
      exact ⟨_, u, flat g', ⟨x0, x2, lo, w, hM.step hm2 rfl rfl, Bound.ok_swapG hok,
        Bound.keep_swapG hk⟩, h15, hbx, rfl, hax, hdx, hF, hB, Bound.flat_swapG hj, hR⟩
    · loop_dec
      right
      refine ⟨?_, by decide⟩
      rw [hM.r12, hLa, hLb]
      exact congrArg (· + 10) (Bound.H_eq ((rd_pend hm2).trans (Mid.rd_pend hM).symm))
  · rw [hM.r12, hLa, hLb, hLa2]; exact Bound.isSome_pos hm2 hc
  · -- `.10` after `pos[dest[a]] := a`.
    rename_i hj
    idioms at hj
    rw [hM.r12, hLa, hLb, hLa2, ← Bound.none_eq] at hj
    simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
    rw [hM.r12, hLa, hLb, hLa2]
    exact ⟨_, u, flat g', ⟨x0, x2, lo, w, hM.step hm3 rfl rfl, Bound.ok_posG (Bound.ok_swapG hok),
      Bound.keep_posG (Bound.keep_swapG hk)⟩, h15, hbx, rfl, hax, hdx, hF, hB, Bound.flat_posG hj, hR⟩
  · loop_dec
    right
    refine ⟨?_, by decide⟩
    rw [hM.r12, hLa, hLb, hLa2]
    exact congrArg (· + 10) (Bound.H_eq ((rd_pend hm3).trans (Mid.rd_pend hM).symm))

theorem b_10 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.10" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, st₀, ⟨x0, x2, lo, w, hM, hok, hk⟩, h15, hbx, hsi, hax, hdx, hF, hB, hfl, hR⟩ := ht
  have hsz : g'.h.len = st₀.size := congrArg Flat.St.size hfl
  have htn : g'.h.n = st₀.targetSize := congrArg Flat.St.targetSize hfl
  have hax' : t.regs.rax.toBitVec < g'.h.len := by rw [hsz]; exact hax
  have hdx' : t.regs.rdx.toBitVec < g'.h.len := by rw [hsz]; exact hdx
  have hb : t.regs.rdx.toBitVec.toNat < MAX_N :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (BitVec.lt_def.mp hdx') hok.len) hok.xs
  have hLb := Bound.rd_dest_get hM.mem hb
  have hc : (Flat.get g'.h.dest t.regs.rdx.toBitVec).toNat < MAX_N := by
    rw [Bound.dest_half hfl hb]
    have h1 := BitVec.lt_def.mp (hF.dest _ hax)
    rw [← htn] at h1
    exact Nat.lt_of_lt_of_le h1 hok.n
  have hm3 := Bound.mem_posG hM.mem hc t.regs.rdx.toBitVec
  kvcgen64
  all_goals try symexec_norm
  · rw [hM.r12]; exact Bound.isSome_dest hM.mem hb
  · -- `.11`: `dest[b]` is `NONE`; the memory does not change.
    rename_i hj
    idioms at hj
    rw [hM.r12, hLb, ← Bound.none_eq] at hj
    have hsw : flat g' = Flat.swapDestinations st₀ t.regs.rax.toBitVec t.regs.rdx.toBitVec := by
      rw [Flat.swapDestinations_split, ← hfl]; exact Bound.flat_rest_none hj
    cfg_goto
    · exact Mid.stack (hM.next rfl rfl rfl)
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      refine ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, h15.trans hsz.symm, hbx, hsi,
        hax', ?_, ?_, ?_⟩
      · rw [hsw]; exact hF.swapDestinations hax hdx
      · rw [hsw]; exact hB
      · rw [hsw]; exact hR
    · loop_dec
      right
      exact ⟨congrArg (· + 10) (Bound.H_eq rfl), by decide⟩
  · rw [hM.r12, hLb]; exact Bound.isSome_pos hM.mem hc
  · -- `.11` after `pos[dest[b]] := b`.
    rename_i hj
    idioms at hj
    rw [hM.r12, hLb, ← Bound.none_eq] at hj
    have hsw : flat (Bound.posG g' (Flat.get g'.h.dest t.regs.rdx.toBitVec) t.regs.rdx.toBitVec)
        = Flat.swapDestinations st₀ t.regs.rax.toBitVec t.regs.rdx.toBitVec := by
      rw [Flat.swapDestinations_split, ← hfl]; exact Bound.flat_rest_pos hj
    simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
    rw [hM.r12, hLb]
    refine ⟨_, u, ⟨x0, x2, lo, w, hM.step hm3 rfl rfl, Bound.ok_posG hok, Bound.keep_posG hk⟩,
      h15.trans hsz.symm, hbx, hsi, hax', ?_, ?_, ?_⟩
    · rw [hsw]; exact hF.swapDestinations hax hdx
    · rw [hsw]; exact hB
    · rw [hsw]; exact hR
  · loop_dec
    right
    refine ⟨?_, by decide⟩
    rw [hM.r12, hLb]
    exact congrArg (· + 10) (Bound.H_eq ((rd_pend hm3).trans (Mid.rd_pend hM).symm))

end Loop
end Bbu.Unit
