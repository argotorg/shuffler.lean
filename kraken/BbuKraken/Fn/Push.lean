import BbuKraken.Fn.PushDup

/-!
The body triple of `push` (`c/bbu/push.S`). `push` has no frame and no call: it reads
`m_positionOf[d]`, and if it is `-1` it writes the new slot, the operation and the counters.
-/

open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Bbu

namespace PushFn
open Kit PushDup

-- The memory at `ret` with the kind `k`, as the asm computes it: `M0` has the return address.
def fin (s : MachineData) (ra : Int64) (k : BitVec 8) : Mem 64 :=
  let S := s.regs.rdi.toBitVec
  let M0 := Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt
  let L := rd M0 S
  let M2 := (M0.storeInt (S + L * 8#64 + 72#64) 8 s.regs.rdx.toBitVec.toInt).storeInt
    (S + s.regs.rdx.toBitVec * 8#64 + 8264#64) 8 L.toInt
  let O := rd M2 (S + 48#64) + (rd M2 (S + 16#64) + rd M2 (S + 16#64) * 2#64) * 4#64
  let M5 := ((M2.storeInt O 1 k.toInt).storeInt (O + 1#64) 1 0).storeInt (O + 4#64) 8
    s.regs.rsi.toBitVec.toInt
  let M6 := M5.storeInt (S + 16#64) 8 (1#64 + rd M5 (S + 16#64)).toInt
  let M7 := M6.storeInt (rd M6 (S + 64#64) + rd M6 S * 8#64) 8 s.regs.rsi.toBitVec.toInt
  M7.storeInt S 8 (1#64 + rd M7 S).toInt

-- The same memory, with all reads done in `s.dmem`.
def finC (s : MachineData) (ra : Int64) (k : BitVec 8) : Mem 64 :=
  let S := s.regs.rdi.toBitVec
  let L := rd s.dmem S
  let N := rd s.dmem (S + 16#64)
  let O := rd s.dmem (S + 48#64) + N * 12#64
  (((((((Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt).storeInt
    (S + L * 8#64 + 72#64) 8 s.regs.rdx.toBitVec.toInt).storeInt
    (S + s.regs.rdx.toBitVec * 8#64 + 8264#64) 8 L.toInt).storeInt O 1 k.toInt).storeInt
    (O + 1#64) 1 0).storeInt (O + 4#64) 8 s.regs.rsi.toBitVec.toInt).storeInt
    (S + 16#64) 8 (1#64 + N).toInt).storeInt (rd s.dmem (S + 64#64) + L * 8#64) 8
    s.regs.rsi.toBitVec.toInt |>.storeInt S 8 (1#64 + L).toInt

variable {s : MachineData} {ra : Int64}

-- The reads of `fin` are reads of `s.dmem`: each store is at a different address.
theorem fin_eq (hpre : Pre pushF pushA s) (k : BitVec 8) : fin s ra k = finC s ra k := by
  obtain ⟨hd, hL, hN⟩ := hpre.2.2
  obtain ⟨hL', hd', hN', hn, hs1, hs2, hs3, hs4, hs5, hs6, -, -, -⟩ := facts hpre hL hd hN
  clear hpre hd hL hN
  generalize nOf s.dmem s.regs.rdi.toBitVec = n at *
  simp only [fin, finC]
  pd_rd
  simp only [mul12]

-- Each store is in the writable memory.
theorem finC_mid (hpre : Pre pushF pushA s) (k : BitVec 8) : Mid pushF s ra (finC s ra k) := by
  obtain ⟨hd, hL, hN⟩ := hpre.2.2
  obtain ⟨hL', hd', hN', hn, -⟩ := facts hpre hL hd hN
  simp only [finC]
  iterate 8 refine Mid.store_w (by decide) hpre ?_ ?_ _
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
theorem fin_mid (hpre : Pre pushF pushA s) (k : BitVec 8) : Mid pushF s ra (fin s ra k) :=
  fin_eq hpre k ▸ finC_mid hpre k

-- `add` gives the model state of `finC`.
set_option maxHeartbeats 1000000 in
theorem push_st (hpre : Pre pushF pushA s) (k : BitVec 8)
    (hnone : positionOf (st s) (rdx s).toNat = none) :
    add (st s) (StackSlot.ofWord (rsi s)) (rdx s).toNat ⟨k, 0#8, StackSlot.ofWord (rsi s)⟩
      = .ok (stOf (finC s ra k) (rdi s)) := by
  obtain ⟨hd, hL, hN⟩ := hpre.2.2
  obtain ⟨hL', hd', hN', hn, hs1, hs2, hs3, hs4, hs5, hs6, -, -, -⟩ := facts hpre hL hd hN
  clear hd hL hN hpre
  simp only [st, rdi, rdx, rsi, Reg64s.get64_rdi, Reg64s.get64_rdx, Reg64s.get64_rsi] at hnone ⊢
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
    rw [wordAt_toNat]
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
    have hO : opsOf (finC s ra k) s.regs.rdi.toBitVec = opsOf s.dmem s.regs.rdi.toBitVec := by
      simp only [opsOf, finC]; bbu_norm; pd_rd
    simp only [opOf, opAt, hO]
    simp only [opsOf, finC]
    bbu_norm
  · intro i hi
    obtain ⟨x, rfl⟩ : ∃ x : Addr, x.toNat = i := ⟨BitVec.ofNat 64 i, by
      rw [BitVec.toNat_ofNat]; omega⟩
    simp only [ofNat_mul_toNat]
    pd_rd
  · simp only [ofNat_mul_toNat]
    pd_rd

/-! ## The kind of the operation -/

theorem take_shr (w : Word) (i : Nat) : (w >>> i).take 8 = w.extractLsb' i 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.take, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight]

-- `cmpb $1, %dl; movl $3, %edx; sbbb $-1, %dl; testb %sil, %sil; cmovne` gives the kind.
theorem push_kind (w : Word) (af : Bool) :
    (BitVec.setWidth 64
      (if CondCode.nz.interp (StatusFlags.from_result ((w >>> 32).take 8 &&& (w >>> 32).take 8)
          { cf := false, af := af, of := false }) = true then
        (3#64).take 32
      else
        ((3#64).replaceLow ((3#64).take 8 - 255#8 -
          BitVec.ofNat 8 ((((w >>> 40).take 8 - 1#8).toNat : Int)
            != (((w >>> 40).take 8).toNat : Int) - 1).toNat)).take 32)).take 8
      = (Op.push (StackSlot.ofWord w)).kind := by
  generalize hk : (w >>> 32).take 8 = k
  generalize hb : (w >>> 40).take 8 = b
  have hc : ((((b - 1#8).toNat : Int) != (b.toNat : Int) - 1)) = decide (b = 0#8) := by
    by_cases h0 : b = 0#8
    · subst h0; decide
    · have : b.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
      simp only [h0, decide_false, bne_eq_false_iff_eq]
      rw [BitVec.toNat_sub]; simp; omega
  rw [hc]
  simp only [CondCode.interp_nz, StatusFlags.zf_from_result, BitVec.and_self]
  rw [take_shr] at hk hb
  simp only [Op.push, StackSlot.ofWord, isLiteralValue, Value, Const, Load, Push, hk, hb]
  by_cases h1 : k = 0#8 <;> by_cases h2 : b = 0#8
  · subst h1 h2; decide
  · subst h1; simp [h2]; decide
  · simp [h1]; decide
  · simp [h1]; decide

/-! ## The state at `ret` -/

-- The memory at `ret` is well formed.
theorem fin_wf (hpre : Pre pushF pushA s) (k : BitVec 8) : Wf (fin s ra k) (rdi s) := by
  obtain ⟨hd, hL, hN⟩ := hpre.2.2
  obtain ⟨hL', hd', hN', hn, hs1, hs2, hs3, hs4, hs5, hs6, -, -, -⟩ := facts hpre hL hd hN
  refine Mid.wf hpre (fin_mid hpre k) ?_ ?_ <;> rw [fin_eq hpre] <;> clear hpre hd hL hN <;>
    simp only [finC, rdi, Reg64s.get64_rdi] <;> bbu_norm <;>
    generalize nOf s.dmem s.regs.rdi.toBitVec = n at * <;> pd_rd <;>
    rw [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega

-- The result: `rax = 0` and the model state of `add`.
theorem fin_res (hpre : Pre pushF pushA s) (hnone : positionOf (st s) (rdx s).toNat = none)
    {u : MachineData} (hm : u.dmem = fin s ra (Op.push (slot s)).kind) (hax : rax u = 0#64) :
    pushR s u := by
  simp only [pushR]
  rw [show Op.push (slot s) = ⟨(Op.push (slot s)).kind, 0#8, slot s⟩ from rfl,
    push_st (ra := ra) hpre _ hnone]
  exact ⟨hax, by simp only [st', hm, fin_eq hpre, id]⟩

-- `.LB22`: the destination has a slot.
def Fail (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  t.dmem = (s.pushRa ra).dmem ∧ rsp t = rsp s - 8#64
    ∧ (∀ q, q ∉ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .rsp] →
      t.regs.get64 q = s.regs.get64 q)
    ∧ (positionOf (st s) (rdx s).toNat).isSome

end PushFn

open Kit PushDup PushFn

-- A jump to a label of the cfg: the stack, the invariant and the variant.
local macro "cfg_goto" : tactic => `(tactic| (
  apply Program.Intercept.intro_label
  · repeat ((fail_if_success (apply List.getElem?_cons_zero)); (apply List.getElem?_cons_succ_of))
    apply List.getElem?_cons_zero
  refine Or.inl ⟨?_, ?_, ?_⟩))

theorem push_body [Host] [FunDecls] : Body pushAsm pushF pushA pushR := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  replace hpre : Pre 8 pushA s := hpre
  refine Program.WP.cfg (fun
      | .entry, t | .label "push", t => t = s.pushRa ra
      | .label ".LB22", t => Fail s ra t
      | _, _ => False)
    (fun | "push", _ => 1 | _, _ => 0) ?_ rfl
  cfg_cases
  case left t ht => subst ht; kvcgen64
  case right.left t ht =>
    subst ht
    obtain ⟨hd, hL, hN⟩ := hpre.2.2
    kvcgen64
    all_goals bbu_norm at *
    case vc6 | vc7 => decide
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
    case vc18 =>
      exact Option.isSome_iff_exists.mpr ⟨ra, Mid.retAddr (by decide) hpre (fin_mid hpre _)
        (by simp [rsp])⟩
    case vc19 =>
      have hnone := pos_flag (ra := ra) hpre hL hd hN ‹_›
      rw [push_kind]
      refine Mid.ret (by decide) hpre (fin_mid hpre _) (by simp [rsp]) rfl ?_ ?_ (fin_wf hpre _)
        (fin_res hpre (by simpa using hnone) rfl rfl)
      · simp [rsp]
      · intro q hq
        cases q <;> simp at hq ⊢
    all_goals
      obtain ⟨hL', hd', hN', hn, hs1, hs2, hs3, hs4, hs5, hs6, -, -, -⟩ := facts hpre hL hd hN
      repeat apply loadInt_isSome_store
      try pd_rd
      first
        | (refine Wf.isSome_struct hpre.1 ?_
           simp only [rdi, Reg64s.get64_rdi, WORDS_eq]
           addr_omega)
        | refine Mem.Mapped.loadInt_isSome hpre.1.mapped
            (inside_append.mpr (Or.inl (inside_writable ?_)))
          simp only [dataOf, opsOf, blkOf, rdi, Reg64s.get64_rdi, DEST_eq, WORDS_eq]
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
      · simp only [pushR, add, hpos, ite_true, Res]
        rfl

end Bbu
