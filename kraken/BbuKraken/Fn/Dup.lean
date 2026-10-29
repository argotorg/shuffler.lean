import BbuKraken.Fn.PushDup

/-!
The body triple of `dup` (`c/bbu/dup.S`). `dup` has no frame and no call: it reads
`m_positionOf[d]`, and if it is `-1` it writes the new slot, the operation and the counters.
-/

open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Bbu

namespace DupFn
open Kit PushDup

-- The depth of a `dup`: the length minus the copy position, in 8 bits.
theorem take_sub {L r : Word} (h : r.toNat ≤ L.toNat) :
    (L - r).take 8 = BitVec.ofNat 8 (L.toNat - r.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_ofNat,
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)]

-- A one-byte store, read back at its address.
theorem get?_store_at (m : Mem 64) (a : Addr) (v : Int) :
    (m.storeInt a 1 v).get? a = (Int.toBytes 1 v)[0]? := by
  have := get?_store_idx (m := m) a (n := 1) v (i := 0) (by decide) (by decide)
  simpa using this

-- The slot of a `dup` operation: bytes 4 to 7 are 0, byte 8 is 1 and byte 9 is 5.
theorem slot_junk {m : Mem 64} {O : Addr} (x : Int) (hm : Mem.Mapped [(O + 4#64, 8)] m) :
    StackSlot.ofWord (rd (((((m.storeInt O 1 1).storeInt (O + 1#64) 1 x).storeInt (O + 4#64) 4 0
      ).storeInt (O + 8#64) 1 1).storeInt (O + 9#64) 1 5) (O + 4#64)) = .junk := by
  apply ofWord_junk
  · repeat apply Mem.Mapped.storeInt
    exact hm
  · intro i hi
    rw [Mem.get?_storeInt_of_ne _ _ _ _ _ (fun j hj he => by
          simp only [Nat.lt_one_iff] at hj; subst hj; bv_omega),
      Mem.get?_storeInt_of_ne _ _ _ _ _ (fun j hj he => by
          simp only [Nat.lt_one_iff] at hj; subst hj; bv_omega),
      get?_store_idx _ _ hi (by decide)]
    match i, hi with
    | 0, _ | 1, _ | 2, _ | 3, _ => decide
  · rw [Mem.get?_storeInt_of_ne _ _ _ _ _ (fun j hj he => by
          simp only [Nat.lt_one_iff] at hj; subst hj; bv_omega),
      show O + 4#64 + 4#64 = O + 8#64 by bv_omega, get?_store_at]
    decide
  · rw [show O + 4#64 + 5#64 = O + 9#64 by bv_omega, get?_store_at]
    decide

-- The memory at `ret`, as the asm computes it: `M0` has the return address.
def fin (s : MachineData) (ra : Int64) : Mem 64 :=
  let S := s.regs.rdi.toBitVec
  let M0 := Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt
  let L := rd M0 S
  let M2 := (M0.storeInt (S + L * 8#64 + 72#64) 8 s.regs.rdx.toBitVec.toInt).storeInt
    (S + s.regs.rdx.toBitVec * 8#64 + 8264#64) 8 L.toInt
  let O := rd M2 (S + 48#64) + (rd M2 (S + 16#64) + rd M2 (S + 16#64) * 2#64) * 4#64
  let M7 := ((((M2.storeInt O 1 1).storeInt (O + 1#64) 1 ((L - s.regs.rsi.toBitVec).take 8).toInt
    ).storeInt (O + 4#64) 4 0).storeInt (O + 8#64) 1 1).storeInt (O + 9#64) 1 5
  let M8 := M7.storeInt (S + 16#64) 8 (1#64 + rd M7 (S + 16#64)).toInt
  let D := rd M8 (S + 64#64)
  let M9 := M8.storeInt (D + rd M8 S * 8#64) 8 (rd M8 (D + s.regs.rsi.toBitVec * 8#64)).toInt
  M9.storeInt S 8 (1#64 + rd M9 S).toInt

-- The same memory, with all reads done in `s.dmem`.
def finC (s : MachineData) (ra : Int64) : Mem 64 :=
  let S := s.regs.rdi.toBitVec
  let L := rd s.dmem S
  let N := rd s.dmem (S + 16#64)
  let O := rd s.dmem (S + 48#64) + N * 12#64
  let D := rd s.dmem (S + 64#64)
  (((((((((Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt).storeInt
    (S + L * 8#64 + 72#64) 8 s.regs.rdx.toBitVec.toInt).storeInt
    (S + s.regs.rdx.toBitVec * 8#64 + 8264#64) 8 L.toInt).storeInt O 1 1).storeInt
    (O + 1#64) 1 ((L - s.regs.rsi.toBitVec).take 8).toInt).storeInt (O + 4#64) 4 0).storeInt
    (O + 8#64) 1 1).storeInt (O + 9#64) 1 5).storeInt (S + 16#64) 8 (1#64 + N).toInt).storeInt
    (D + L * 8#64) 8 (rd s.dmem (D + s.regs.rsi.toBitVec * 8#64)).toInt
    |>.storeInt S 8 (1#64 + L).toInt

variable {s : MachineData} {ra : Int64}

-- The copy position is below the length in memory.
theorem copy_lt (hpre : Pre dupF dupA s) :
    s.regs.rsi.toBitVec.toNat < (rd s.dmem s.regs.rdi.toBitVec).toNat := by
  have h := hpre.2.2.1
  simp only [st, len_stOf, rsi, rdi, Reg64s.get64_rsi, Reg64s.get64_rdi] at h
  bbu_norm at h
  exact h

-- The reads of `fin` are reads of `s.dmem`: each store is at a different address.
theorem fin_eq (hpre : Pre dupF dupA s) : fin s ra = finC s ra := by
  obtain ⟨-, hd, hL, hN⟩ := hpre.2.2
  have hc := copy_lt hpre
  obtain ⟨hL', hd', hN', hn, hs1, hs2, hs3, hs4, hs5, hs6, -, -, -⟩ := facts hpre hL hd hN
  clear hpre hd hL hN
  generalize nOf s.dmem s.regs.rdi.toBitVec = n at *
  simp only [fin, finC]
  pd_rd
  simp only [mul12]

-- Each store is in the writable memory.
theorem finC_mid (hpre : Pre dupF dupA s) : Mid dupF s ra (finC s ra) := by
  obtain ⟨-, hd, hL, hN⟩ := hpre.2.2
  obtain ⟨hL', hd', hN', hn, -⟩ := facts hpre hL hd hN
  simp only [finC]
  iterate 10 refine Mid.store_w (by decide) hpre ?_ ?_ _
  · exact Mid.init (by decide) hpre
  all_goals
    apply inside_writable
    simp only [dataOf, opsOf, blkOf, rdi, Reg64s.get64_rdi, DEST_eq, WORDS_eq]
    first
      | (left; addr_omega)
      | (right; left; constructor <;> addr_omega)
      | (right; right; left; addr_omega)
      | (right; right; right; left; addr_omega)

-- The memory at `ret` is a `Mid` memory.
theorem fin_mid (hpre : Pre dupF dupA s) : Mid dupF s ra (fin s ra) :=
  fin_eq hpre ▸ finC_mid hpre

-- `add` gives the model state of `finC`.
set_option maxHeartbeats 1000000 in
theorem dup_st (hpre : Pre dupF dupA s) (hnone : positionOf (st s) (rdx s).toNat = none) :
    add (st s) ((st s).val (rsi s).toNat) (rdx s).toNat (.dup ((st s).len - (rsi s).toNat))
      = .ok (stOf (finC s ra) (rdi s)) := by
  obtain ⟨-, hd, hL, hN⟩ := hpre.2.2
  have hc := copy_lt hpre
  obtain ⟨hL', hd', hN', hn, hs1, hs2, hs3, hs4, hs5, hs6, -, -, -⟩ := facts hpre hL hd hN
  have hmap := hpre.1.mapped
  clear hd hL hN hpre
  simp only [st, rdi, rdx, rsi, Reg64s.get64_rdi, Reg64s.get64_rdx, Reg64s.get64_rsi] at hnone ⊢
  rw [val_stOf (by simpa [wordAt] using hc), len_stOf]
  apply st_add hnone
  all_goals generalize hn0 : nOf s.dmem s.regs.rdi.toBitVec = n at *
  · rw [← hn0]; simp only [nOf, finC]; bbu_norm; pd_rd
  · simp only [finC]; bbu_norm; pd_rd
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · simp only [finC]; bbu_norm; pd_rd
  · simp only [finC]; bbu_norm; pd_rd
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · simp only [dataOf, finC]; bbu_norm; pd_rd
  · intro i hi
    simp only [dataOf, finC]
    bbu_norm at hi ⊢
    pd_rd
  · simp only [dataOf, finC]
    rw [wordAt_toNat, wordAt_toNat]
    bbu_norm
    pd_rd
  · intro i hi
    simp only [finC]
    bbu_norm at hi ⊢
    simp only [DEST_eq]
    pd_rd
  · simp only [finC]
    rw [wordAt_dest]
    bbu_norm
    pd_rd
  · intro e he hne
    simp only [finC]
    bbu_norm
    simp only [POS_eq]
    rcases Nat.lt_or_gt_of_ne hne with h | h <;> pd_rd
  · simp only [finC]
    rw [wordAt_pos]
    bbu_norm
    pd_rd
    simp only [optOf]
    split
    · rename_i h; rw [h] at hL'
      exact absurd hL' (by rw [BitVec.toNat_neg]; simp only [BitVec.toNat_ofNat]; omega)
    · rfl
  all_goals
    have hO : opsOf (finC s ra) s.regs.rdi.toBitVec = opsOf s.dmem s.regs.rdi.toBitVec := by
      simp only [opsOf, finC]; bbu_norm; pd_rd
    simp only [opOf, opAt, hO]
    simp only [opsOf, finC]
    bbu_norm
  · intro i hi
    obtain ⟨x, rfl⟩ : ∃ x : Addr, x.toNat = i := ⟨BitVec.ofNat 64 i, by
      rw [BitVec.toNat_ofNat]; omega⟩
    simp only [ofNat_mul_toNat]
    pd_rd
  · simp only [ofNat_mul_toNat, Op.dup, Op.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · pd_rd
      rfl
    · pd_rd
      exact take_sub (Nat.le_of_lt hc)
    · pd_rd
      apply slot_junk
      repeat apply Mem.Mapped.storeInt
      refine fun x hx => hmap x (inside_bytes (inside_append.mpr (Or.inl (inside_writable ?_))) x hx)
      simp only [opsOf, rdi, Reg64s.get64_rdi]
      right; right; right; left
      rw [hn0]
      addr_omega

-- The memory at `ret` is well formed.
theorem fin_wf (hpre : Pre dupF dupA s) : Wf (fin s ra) (rdi s) := by
  obtain ⟨-, hd, hL, hN⟩ := hpre.2.2
  obtain ⟨hL', hd', hN', hn, hs1, hs2, hs3, hs4, hs5, hs6, -, -, -⟩ := facts hpre hL hd hN
  refine Mid.wf hpre (fin_mid hpre) ?_ ?_ <;> rw [fin_eq hpre] <;> clear hpre hd hL hN <;>
    simp only [finC, rdi, Reg64s.get64_rdi] <;> bbu_norm <;>
    generalize nOf s.dmem s.regs.rdi.toBitVec = n at * <;> pd_rd <;>
    rw [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega

-- The result: `rax = 0` and the model state of `add`.
theorem fin_res (hpre : Pre dupF dupA s) (hnone : positionOf (st s) (rdx s).toNat = none)
    {u : MachineData} (hm : u.dmem = fin s ra) (hax : rax u = 0#64) : dupR s u := by
  simp only [dupR]
  rw [dup_st (ra := ra) hpre hnone]
  exact ⟨hax, by simp only [st', hm, fin_eq hpre, id]⟩

-- `.LB27`: the destination has a slot.
def Fail (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  t.dmem = (s.pushRa ra).dmem ∧ rsp t = rsp s - 8#64
    ∧ (∀ q, q ∉ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .rsp] →
      t.regs.get64 q = s.regs.get64 q)
    ∧ (positionOf (st s) (rdx s).toNat).isSome

end DupFn

open Kit PushDup DupFn

-- A jump to a label of the cfg: the stack, the invariant and the variant.
local macro "cfg_goto" : tactic => `(tactic| (
  apply Program.Intercept.intro_label
  · repeat ((fail_if_success (apply List.getElem?_cons_zero)); (apply List.getElem?_cons_succ_of))
    apply List.getElem?_cons_zero
  refine Or.inl ⟨?_, ?_, ?_⟩))

-- The isSome goals of the reads after the ten stores need more than the default heartbeats.
set_option maxHeartbeats 400000 in
theorem dup_body [Host] [FunDecls] : Body dupAsm dupF dupA dupR := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  replace hpre : Pre 8 dupA s := hpre
  refine Program.WP.cfg (fun
      | .entry, t | .label "dup", t => t = s.pushRa ra
      | .label ".LB27", t => Fail s ra t
      | _, _ => False)
    (fun | "dup", _ => 1 | _, _ => 0) ?_ rfl
  cfg_cases
  case left t ht => subst ht; kvcgen64
  case right.left t ht =>
    subst ht
    obtain ⟨-, hd, hL, hN⟩ := hpre.2.2
    kvcgen64
    all_goals bbu_norm at *
    case vc2 =>
      have hpos := pos_flag (ra := ra) hpre hL hd hN ‹_›
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        have := hpre.2.1.le
        simp only [MachineData.regs_pushRa, Reg64s.get64_rsp, Reg64s.set64_rsp, rsp] at *
        bv_omega
      · refine ⟨rfl, ?_, ?_, hpos⟩
        · simp [rsp]
        · intro q hq
          cases q <;> simp at hq ⊢
      · simp
    case vc19 =>
      exact Option.isSome_iff_exists.mpr ⟨ra, Mid.retAddr (by decide) hpre (fin_mid hpre)
        (by simp [rsp])⟩
    case vc20 =>
      have hnone := pos_flag (ra := ra) hpre hL hd hN ‹_›
      refine Mid.ret (by decide) hpre (fin_mid hpre) (by simp [rsp]) rfl ?_ ?_ (fin_wf hpre)
        (fin_res hpre (by simpa using hnone) rfl rfl)
      · simp [rsp]
      · intro q hq
        cases q <;> simp at hq ⊢
    all_goals
      obtain ⟨hL', hd', hN', hn, hs1, hs2, hs3, hs4, hs5, hs6, -, -, -⟩ := facts hpre hL hd hN
      have hc := copy_lt hpre
      have hD : wordAt s.regs.rdi.toBitVec 8 = s.regs.rdi.toBitVec + 64#64 := rfl
      repeat apply loadInt_isSome_store
      try pd_rd
      first
        | (refine Wf.isSome_struct hpre.1 ?_
           simp only [rdi, Reg64s.get64_rdi, WORDS_eq]
           addr_omega)
        | refine Mem.Mapped.loadInt_isSome hpre.1.mapped
            (inside_append.mpr (Or.inl (inside_writable ?_)))
          simp only [dataOf, opsOf, blkOf, rdi, Reg64s.get64_rdi, DEST_eq, WORDS_eq, hD]
          generalize nOf s.dmem s.regs.rdi.toBitVec = n at *
          first
            | (left; addr_omega)
            | (right; left; constructor <;> addr_omega)
            | (right; right; left; addr_omega)
            | (right; right; right; left; addr_omega)
  case right.right t ht =>
    obtain ⟨hm, hsp, hr, hpos⟩ := ht
    kvcgen64
    · exact Option.isSome_iff_exists.mpr ⟨ra, Mid.retAddr (by decide) hpre
        (hm ▸ Mid.init (by decide) hpre) (by simpa [rsp] using hsp)⟩
    · refine Mid.ret (by decide) hpre (hm ▸ Mid.init (by decide) hpre) (by simpa [rsp] using hsp)
        rfl ?_ ?_ (hm ▸ wf_pushRa (by decide) hpre) ?_
      · simp only [rsp, Reg64s.get64_rsp] at hsp ⊢
        simp
        bv_omega
      · intro q hq
        have h := hr q hq
        cases q <;> simp at hq ⊢ <;> simpa using h
      · simp only [dupR, add, hpos, ite_true, Res]
        rfl
  all_goals simp_all

end Bbu
