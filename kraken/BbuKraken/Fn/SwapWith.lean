import BbuKraken.Kit
open Std.WP Lean.Order
open scoped Program.WP
namespace Bbu
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

namespace SwapWithFn

-- The state at `.LB23`, `.LB24` and `.LB25`: the memory and the registers of the
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
    (h : ((L + -1#64 - r + -1#64 - 15#64).toNat : Int) = ((L + -1#64 - r + -1#64).toNat : Int) - 15
      ∧ ¬ L + -1#64 - r + -1#64 - 15#64 = 0#64) :
    L.toNat - 1 - r.toNat < 1 ∨ 16 < L.toNat - 1 - r.toNat := by
  bv_omega

theorem depth_ok (L r : BitVec 64) (hlt : r.toNat < L.toNat)
    (h : ¬ ((L + -1#64 - r + -1#64 - 15#64).toNat : Int) = ((L + -1#64 - r + -1#64).toNat : Int) - 15
      ∨ L + -1#64 - r + -1#64 - 15#64 = 0#64) :
    1 ≤ L.toNat - 1 - r.toNat ∧ L.toNat - 1 - r.toNat ≤ 16 := by
  bv_omega

theorem shl4 (x : BitVec 64) : x <<< 4 = x * 16#64 := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]; rfl

theorem swapWith_eq {st : St} {pos : Nat} (h1 : pos < st.len) (h2 : st.dest pos ≠ pos)
    (h3 : 1 ≤ st.len - 1 - pos) (h4 : st.len - 1 - pos ≤ MAX_SWAP_DEPTH) :
    swapWith st pos = .ok { st with
      slots := (st.slots.set pos ⟨st.val (st.len - 1), st.dest (st.len - 1)⟩).set (st.len - 1)
        ⟨st.val pos, st.dest pos⟩
      ops := st.ops ++ [.swap (st.len - 1 - pos)] } := by
  unfold swapWith
  rw [ite_eq_right (by omega)]
  dsimp only
  rw [ite_eq_right (by omega)]

open Kit

-- Two reads at equal addresses.
theorem rd_addr {m : Mem 64} {a b : Addr} (h : a = b) : rd m a = rd m b := h ▸ rfl

-- The last step of a read after the stores of `swap_with`.
local macro "swap_fin" : tactic => `(tactic| first
  | exact True.intro
  | exact rd_addr (by bv_omega)
  | exact congrArg BitVec.toNat (rd_addr (by bv_omega)))

-- `Mid` after the stores of `swap_with`.
local macro "swap_mid" : tactic => `(tactic| (
  iterate 7 (refine Mid.store_w (by decide) (by assumption) ?_ ?_ _)
  exact Mid.init (by decide) (by assumption)
  all_goals
    try simp only [shl4]
    try bbu_rd
    apply inside_writable
    simp only [opsOf, STACK, WORDS]
    bbu_norm
  · right; right; left; bv_omega
  · right; right; left; bv_omega
  · left; bv_omega
  all_goals right; left; bv_omega))

section
variable {s : MachineData} {ra : Int64}

-- The memory after the stores of `swap_with`, in the form of the `kvcgen64` goals.
def fin (s : MachineData) (ra : Int64) : Mem 64 :=
  let S := s.regs.rdi.toBitVec
  let r := s.regs.rsi.toBitVec
  let L := rd s.dmem S
  let m0 := Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt
  let m1 := m0.storeInt (rd m0 (S + 48#64) + rd m0 (S + 16#64) <<< 4) 8 0
  let m2 := m1.storeInt (rd m1 (S + 48#64) + rd m1 (S + 16#64) <<< 4 + 8#64) 8 (L + -1#64 - r).toInt
  let m3 := m2.storeInt (S + 16#64) 8 (1#64 + rd m2 (S + 16#64)).toInt
  let m4 := m3.storeInt (S + r * 8#64 + 64#64) 8 (rd m3 (S + L * 8#64 + 56#64)).toInt
  let m5 := m4.storeInt (S + L * 8#64 + 56#64) 8 (rd m3 (S + r * 8#64 + 64#64)).toInt
  let m6 := m5.storeInt (S + r * 8#64 + 2112#64) 8 (rd m5 (S + L * 8#64 + 2104#64)).toInt
  m6.storeInt (S + L * 8#64 + 2104#64) 8 (rd m5 (S + r * 8#64 + 2112#64)).toInt

-- The facts of `Pre` for `bv_omega`.
theorem facts (hpre : Pre swapWithF swapWithA s) :
    (s.regs.rsp.toBitVec.toNat ≤ s.regs.rdi.toBitVec.toNat ∨
      s.regs.rdi.toBitVec.toNat + 4160 ≤ s.regs.rsp.toBitVec.toNat - 8)
    ∧ s.regs.rdi.toBitVec.toNat + 4160 ≤ 2 ^ 64 ∧ 8 ≤ s.regs.rsp.toBitVec.toNat
    ∧ (rd s.dmem s.regs.rdi.toBitVec).toNat ≤ 256
    ∧ (rd s.dmem (s.regs.rdi.toBitVec + 16#64)).toNat < 6 * nOf s.dmem s.regs.rdi.toBitVec
    ∧ nOf s.dmem s.regs.rdi.toBitVec ≤ 256
    ∧ ((rd s.dmem (s.regs.rdi.toBitVec + 48#64)).toNat + 96 * nOf s.dmem s.regs.rdi.toBitVec
          ≤ s.regs.rdi.toBitVec.toNat
        ∨ s.regs.rdi.toBitVec.toNat + 4160 ≤ (rd s.dmem (s.regs.rdi.toBitVec + 48#64)).toNat)
    ∧ (rd s.dmem (s.regs.rdi.toBitVec + 48#64)).toNat + 96 * nOf s.dmem s.regs.rdi.toBitVec
        ≤ 2 ^ 64
    ∧ (s.regs.rsp.toBitVec.toNat ≤ (rd s.dmem (s.regs.rdi.toBitVec + 48#64)).toNat
      ∨ (rd s.dmem (s.regs.rdi.toBitVec + 48#64)).toNat + 96 * nOf s.dmem s.regs.rdi.toBitVec
        ≤ s.regs.rsp.toBitVec.toNat - 8) := by
  have hw := hpre.1
  have hfr := hpre.2.1
  have hsep := hfr.sep_struct (by decide)
  have hst := hw.struct_lt
  have hle := hfr.le
  have hlen := hw.len_le
  have hn := hw.n_le
  have hnlt : (st s).ops.length < cap s := hpre.2.2
  simp only [cap, st, nops_stOf] at hnlt
  have hso := hw.sep_ops (by omega)
  have hol := hw.ops_lt
  have hfo := hfr.sep_ops (by decide) (by omega)
  simp only [swapWithF, WORDS, opsOf] at hsep hst hle hso hol hfo
  bbu_norm at hsep hst hle hlen hn hnlt hso hol hfo
  exact ⟨hsep, hst, hle, hlen, hnlt, hn, hso, hol, hfo⟩

-- The stores of `swap_with` stay in the frame and `writable`.
theorem mid_fin (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat < (rd s.dmem s.regs.rdi.toBitVec).toNat)
    (_hdep : 1 ≤ (rd s.dmem s.regs.rdi.toBitVec).toNat - 1 - s.regs.rsi.toBitVec.toNat) :
    Mid swapWithF s ra (fin s ra) := by
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := facts hpre
  simp only [fin]
  swap_mid

-- The header words 0 and 2 after the stores.
theorem rd_fin (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat < (rd s.dmem s.regs.rdi.toBitVec).toNat)
    (_hdep : 1 ≤ (rd s.dmem s.regs.rdi.toBitVec).toNat - 1 - s.regs.rsi.toBitVec.toNat) :
    rd (fin s ra) s.regs.rdi.toBitVec = rd s.dmem s.regs.rdi.toBitVec
      ∧ rd (fin s ra) (s.regs.rdi.toBitVec + 16#64) = 1#64 + rd s.dmem (s.regs.rdi.toBitVec + 16#64) := by
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := facts hpre
  constructor <;> (simp only [fin, shl4]; bbu_rd)

-- The header word 1 after the stores.
theorem rd_fin_pend (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat < (rd s.dmem s.regs.rdi.toBitVec).toNat)
    (_hdep : 1 ≤ (rd s.dmem s.regs.rdi.toBitVec).toNat - 1 - s.regs.rsi.toBitVec.toNat) :
    rd (fin s ra) (s.regs.rdi.toBitVec + 8#64) = rd s.dmem (s.regs.rdi.toBitVec + 8#64) := by
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := facts hpre
  simp only [fin, shl4]; bbu_rd

-- A slot after the stores of `swap_with`.
local macro "slot_tac" : tactic => `(tactic| (
  simp only [slotOf, Slot.mk.injEq, fin, shl4, STACK, DEST]; bbu_norm; bbu_rd
  refine ⟨?_, ?_⟩ <;> swap_fin))

-- The slots after the stores: slots `r` and `L - 1` change places.
theorem slot_fin_top (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat < (rd s.dmem s.regs.rdi.toBitVec).toNat)
    (_hdep : 1 ≤ (rd s.dmem s.regs.rdi.toBitVec).toNat - 1 - s.regs.rsi.toBitVec.toNat) :
    slotOf (fin s ra) s.regs.rdi.toBitVec ((rd s.dmem s.regs.rdi.toBitVec).toNat - 1) =
      slotOf s.dmem s.regs.rdi.toBitVec s.regs.rsi.toBitVec.toNat := by
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := facts hpre
  slot_tac

theorem slot_fin_pos (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat < (rd s.dmem s.regs.rdi.toBitVec).toNat)
    (hdep : 1 ≤ (rd s.dmem s.regs.rdi.toBitVec).toNat - 1 - s.regs.rsi.toBitVec.toNat) :
    slotOf (fin s ra) s.regs.rdi.toBitVec s.regs.rsi.toBitVec.toNat =
      slotOf s.dmem s.regs.rdi.toBitVec ((rd s.dmem s.regs.rdi.toBitVec).toNat - 1) := by
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := facts hpre
  slot_tac

theorem slot_fin_other (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat < (rd s.dmem s.regs.rdi.toBitVec).toNat)
    (_hdep : 1 ≤ (rd s.dmem s.regs.rdi.toBitVec).toNat - 1 - s.regs.rsi.toBitVec.toNat)
    {i : Nat} (hi : i < (rd s.dmem s.regs.rdi.toBitVec).toNat)
    (h1 : i ≠ (rd s.dmem s.regs.rdi.toBitVec).toNat - 1) (h2 : i ≠ s.regs.rsi.toBitVec.toNat) :
    slotOf (fin s ra) s.regs.rdi.toBitVec i = slotOf s.dmem s.regs.rdi.toBitVec i := by
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := facts hpre
  slot_tac

-- The ops before the new op do not change.
theorem op_fin (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat < (rd s.dmem s.regs.rdi.toBitVec).toNat)
    (_hdep : 1 ≤ (rd s.dmem s.regs.rdi.toBitVec).toNat - 1 - s.regs.rsi.toBitVec.toNat)
    {i : Nat} (hi : i < (rd s.dmem (s.regs.rdi.toBitVec + 16#64)).toNat) :
    opOf (fin s ra) s.regs.rdi.toBitVec i = opOf s.dmem s.regs.rdi.toBitVec i := by
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := facts hpre
  simp only [opOf, opsOf, Op.mk.injEq, fin, shl4]; bbu_norm; bbu_rd
  constructor <;> trivial

-- The new op.
theorem op_fin_last (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat < (rd s.dmem s.regs.rdi.toBitVec).toNat)
    (_hdep : 1 ≤ (rd s.dmem s.regs.rdi.toBitVec).toNat - 1 - s.regs.rsi.toBitVec.toNat) :
    opOf (fin s ra) s.regs.rdi.toBitVec (rd s.dmem (s.regs.rdi.toBitVec + 16#64)).toNat =
      Op.swap ((rd s.dmem s.regs.rdi.toBitVec).toNat - 1 - s.regs.rsi.toBitVec.toNat) := by
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := facts hpre
  simp only [opOf, opsOf, Op.swap, Op.mk.injEq, fin, shl4]; bbu_norm; bbu_rd
  exact ⟨trivial, by bv_omega⟩

-- The model state in the memory of the call.
theorem st_slot {j : Nat} (hj : j < (st s).slots.length) :
    (st s).slots[j] = slotOf s.dmem (rdi s) j := by
  simp [st, stOf]

theorem st_slot' {j : Nat} (hj : j < (rd s.dmem s.regs.rdi.toBitVec).toNat) :
    Slot.mk ((st s).val j) ((st s).dest j) = slotOf s.dmem (rdi s) j := by
  rw [val_stOf (m := s.dmem) (S := rdi s) (by bbu_norm; exact hj),
    dest_stOf (m := s.dmem) (S := rdi s) (by bbu_norm; exact hj)]
  rfl

theorem st_op {j : Nat} (hj : j < (st s).ops.length) :
    (st s).ops[j] = opOf s.dmem (rdi s) j := by
  simp [st, stOf]

theorem len_st : (st s).len = (rd s.dmem s.regs.rdi.toBitVec).toNat := by
  rw [len_stOf]; bbu_norm

theorem nops_st : (st s).ops.length = (rd s.dmem (s.regs.rdi.toBitVec + 16#64)).toNat := by
  rw [nops_stOf]; bbu_norm

-- The slots of the model after `swapWith`.
theorem slots_fin (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat < (rd s.dmem s.regs.rdi.toBitVec).toNat)
    (hdep : 1 ≤ (rd s.dmem s.regs.rdi.toBitVec).toNat - 1 - s.regs.rsi.toBitVec.toNat)
    {i : Nat} (hi : i < (st s).len) (h) :
    slotOf (fin s ra) (rdi s) i = (((st s).slots.set (rsi s).toNat
      ⟨(st s).val ((st s).len - 1), (st s).dest ((st s).len - 1)⟩).set ((st s).len - 1)
        ⟨(st s).val (rsi s).toNat, (st s).dest (rsi s).toNat⟩)[i]'h := by
  have hr : rsi s = s.regs.rsi.toBitVec := by bbu_norm
  simp only [hr] at h ⊢
  simp only [List.getElem_set]
  rw [len_st] at hi
  by_cases h1 : i = (rd s.dmem s.regs.rdi.toBitVec).toNat - 1
  · rw [ite_eq_left (by rw [len_st]; exact h1.symm), st_slot' hpos, h1]
    exact slot_fin_top hpre hpos hdep
  · rw [ite_eq_right (by rw [len_st]; exact Ne.symm h1)]
    by_cases h2 : i = s.regs.rsi.toBitVec.toNat
    · rw [ite_eq_left h2.symm, st_slot' (by rw [len_st]; omega), len_st, h2]
      exact slot_fin_pos hpre hpos hdep
    · rw [ite_eq_right (Ne.symm h2), st_slot]
      exact slot_fin_other hpre hpos hdep hi h1 h2

-- The ops of the model after `swapWith`.
theorem ops_fin (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat < (rd s.dmem s.regs.rdi.toBitVec).toNat)
    (hdep : 1 ≤ (rd s.dmem s.regs.rdi.toBitVec).toNat - 1 - s.regs.rsi.toBitVec.toNat)
    {i : Nat} (h) :
    opOf (fin s ra) (rdi s) i =
      ((st s).ops ++ [Op.swap ((st s).len - 1 - (rsi s).toNat)])[i]'h := by
  rw [List.getElem_append]
  split
  · rw [st_op]
    exact op_fin hpre hpos hdep (by rw [← nops_st]; assumption)
  · have hi : i = (st s).ops.length := by simp only [List.length_append, List.length_singleton] at h; omega
    simp only [List.getElem_singleton, len_st]
    rw [hi, nops_st]
    exact op_fin_last hpre hpos hdep

-- The model result at the return of the success path.
theorem R_fin {t : MachineData} (hpre : Pre swapWithF swapWithA s)
    (hpos : s.regs.rsi.toBitVec.toNat < (rd s.dmem s.regs.rdi.toBitVec).toNat)
    (hdep : 1 ≤ (rd s.dmem s.regs.rdi.toBitVec).toNat - 1 - s.regs.rsi.toBitVec.toNat ∧
      (rd s.dmem s.regs.rdi.toBitVec).toNat - 1 - s.regs.rsi.toBitVec.toNat ≤ 16)
    (hdz : ¬rd s.dmem (s.regs.rdi.toBitVec + s.regs.rsi.toBitVec * 8#64 + 2112#64)
      - s.regs.rsi.toBitVec = 0#64)
    (hm : t.dmem = fin s ra) (hax : t.regs.rax.toBitVec = 0#64) : swapWithR s t := by
  obtain ⟨_, _, _, _, hnlt, _, _, _, _⟩ := facts hpre
  have hd : (st s).dest (rsi s).toNat ≠ (rsi s).toNat := by
    rw [dest_stOf (by bbu_norm; exact hpos), slot_addr]
    simp only [DEST]; bbu_norm; bv_omega
  rw [swapWithR, swapWith_eq (by rw [len_st]; exact hpos) hd (by rw [len_st]; exact hdep.1)
    (by rw [len_st]; exact hdep.2)]
  refine ⟨hax, ?_⟩
  show stOf t.dmem (rdi s) = _
  rw [hm, id_eq]
  have hrd := rd_fin (ra := ra) hpre hpos hdep.1
  apply stOf_eq
  · simp only [St.len, List.length_set]
    rw [← St.len, len_st]
    bbu_norm
    rw [hrd.1]
  · simp only [st, stOf]
    bbu_norm
    rw [rd_fin_pend (ra := ra) hpre hpos hdep.1]
  · simp only [List.length_append, nops_st, List.length_singleton]
    bbu_norm
    rw [hrd.2]
    bv_omega
  · intro i hi
    exact slots_fin hpre hpos hdep.1 (by simp only [St.len, List.length_set] at hi; exact hi) _
  · intro i hi
    exact ops_fin hpre hpos hdep.1 _
end
end SwapWithFn

open SwapWithFn Kit

theorem swapWith_body [Host] [FunDecls] : Body swapWithAsm swapWithF swapWithA swapWithR := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  refine Program.WP.cfg (fun
      | .entry, t | .label "swap_with", t => t = s.pushRa ra
      | .label ".LB23", t | .label ".LB24", t | .label ".LB25", t => Fail s ra t
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  have hF : 8 ≤ swapWithF := by decide
  cfg_cases
  case left t ht =>
    subst ht
    kvcgen64
  case right.right.left t ht | right.right.right.left t ht | right.right.right.right t ht =>
    obtain ⟨hm, hsp, hr, he⟩ := ht
    have hmid : Mid swapWithF s ra t.dmem := hm ▸ Mid.init hF hpre
    have hw : Wf t.dmem (rdi s) := hm ▸ wf_pushRa hF hpre
    kvcgen64
    · show t.retAddr.isSome
      rw [hmid.retAddr hF hpre hsp]; rfl
    · refine Mid.ret hF hpre hmid hsp rfl ?_ ?_ hw ?_
      · show t.regs.rsp.toBitVec + 8#64 = rsp s
        rw [show t.regs.rsp.toBitVec = rsp s - 8#64 from hsp]; exact BitVec.sub_add_cancel _ _
      · intro q hq
        rw [← hr q hq]
        cases q <;> first | rfl | simp at hq
      · simp only [swapWithR, he, Res]; rfl
  case right.left t ht =>
    subst ht
    have hw := hpre.1
    have hfr := hpre.2.1
    have hA : swapWithA s := hpre.2.2
    have hsep := hfr.sep_struct (by decide)
    have hst := hw.struct_lt
    have hle := hfr.le
    have hlen := hw.len_le
    have hnops := hw.nops_le
    have hn := hw.n_le
    simp only [swapWithF, WORDS] at hsep hst hle
    bbu_norm at hsep hst hle hlen hnops hn hw
    have hnlt : (rd s.dmem (s.regs.rdi.toBitVec + 16#64)).toNat < 6 * nOf s.dmem s.regs.rdi.toBitVec := by
      have := hA; simp only [swapWithA, cap, st, nops_stOf] at this; bbu_norm at this; exact this
    have hso := hw.sep_ops (by omega)
    have hol := hw.ops_lt
    simp only [opsOf, WORDS] at hso hol
    bbu_norm at hso hol
    have hR : ∀ a, (a - s.regs.rdi.toBitVec).toNat + 8 ≤ 4160 →
        rd (Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt) a = rd s.dmem a :=
      fun a ha => rd_store_other _ (by bv_omega)
    kvcgen64
    all_goals bbu_norm at *
    all_goals try simp only [hR s.regs.rdi.toBitVec (by simp)] at *
    all_goals try bbu_flags at *
    case vc2 =>
      rename_i hcf
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [MachineData.regs_pushRa, Reg64s.get64_rsp, Reg64s.set64_rsp]
        bv_omega
      · refine ⟨rfl, rfl, ?_, swapWith_err (Or.inl ?_)⟩
        · intro q hq; cases q <;> first | rfl | simp at hq
        · rw [len_stOf]; bbu_norm; exact (no_borrow_iff _ _).1 hcf
      · simp
    case vc4 =>
      rename_i hdz hcf
      have hpos := (borrow_iff _ _).1 hcf
      rw [hR _ (by bv_omega)] at hdz
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [MachineData.regs_pushRa, Reg64s.get64_rsp, Reg64s.set64_rsp]
        bv_omega
      · refine ⟨rfl, rfl, ?_, swapWith_err (Or.inr (Or.inl ?_))⟩
        · intro q hq; cases q <;> first | rfl | simp at hq
        · rw [dest_stOf (by bbu_norm; exact hpos), slot_addr]
          simp only [DEST]; bbu_norm
          have : rd s.dmem (s.regs.rdi.toBitVec + s.regs.rsi.toBitVec * 8#64 + 2112#64) =
            s.regs.rsi.toBitVec := by bv_omega
          rw [this]
      · simp
    case vc5 =>
      rename_i hdz hcf hja
      have hpos := (borrow_iff _ _).1 hcf
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [MachineData.regs_pushRa, Reg64s.get64_rsp, Reg64s.set64_rsp]
        bv_omega
      · refine ⟨rfl, rfl, ?_, swapWith_err (Or.inr (Or.inr ?_))⟩
        · intro q hq; cases q <;> first | (simp at hq; done) | rfl
        · rw [len_stOf]; bbu_norm; simp only [MAX_SWAP_DEPTH]; exact depth_big _ _ hpos hja
      · simp
    all_goals try (have hpos : s.regs.rsi.toBitVec.toNat < (rd s.dmem s.regs.rdi.toBitVec).toNat :=
      (borrow_iff _ _).1 (by assumption))
    case vc7 | vc11 => decide
    case vc9 | vc13 =>
      simp only [shl4]
      bbu_rd
      repeat apply loadInt_isSome_store
      refine hw.mapped.loadInt_isSome (inside_append.mpr (Or.inl (inside_writable (Or.inr (Or.inr (Or.inl ?_))))))
      simp only [opsOf]; bbu_norm; bv_omega
    case vc23 =>
      rename_i hdz hcf hja
      have hdep := depth_ok _ _ hpos hja
      clear hcf hja
      exact Option.isSome_iff_exists.mpr ⟨ra, Mid.retAddr hF hpre (mid_fin hpre hpos hdep.1) rfl⟩
    case vc24 =>
      rename_i hdz hcf hja
      have hdep := depth_ok _ _ hpos hja
      clear hcf hja
      rw [hR _ (by bv_omega)] at hdz
      have hmid := mid_fin (ra := ra) hpre hpos hdep.1
      have hrd := rd_fin (ra := ra) hpre hpos hdep.1
      refine Mid.ret hF hpre hmid rfl rfl ?_ ?_ ?_ (R_fin hpre hpos hdep hdz rfl rfl)
      · show s.regs.rsp.toBitVec - 8#64 + 8#64 = s.regs.rsp.toBitVec
        exact BitVec.sub_add_cancel _ _
      · intro q hq
        cases q <;> first | (simp at hq; done) | rfl
      · show Wf (fin s ra) (rdi s)
        refine Mid.wf hpre hmid ?_ ?_ <;> bbu_norm
        · rw [hrd.1]; exact hlen
        · rw [hrd.2]; bv_omega
    all_goals (repeat apply loadInt_isSome_store); exact hw.isSome_struct (by simp only [WORDS]; bv_omega)
end Bbu
