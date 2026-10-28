import PermuteKraken.Asm
import PermuteKraken.Specs
import PermuteKraken.Trace
import PermuteKraken.Bytes

open Std.WP Lean.Order
open scoped Program.WP
open PermuteKraken

set_option experimental.vcgen true

namespace State

section
variable (s : MachineData)

abbrev N := s.regs.get64 .rdi
abbrev P := s.regs.get64 .rsi
abbrev T := s.regs.get64 .rdx
abbrev B := s.regs.get64 .rcx
abbrev S := s.regs.get64 .rsp

-- The caller memory that `permute` writes: `perm`, `trace` and `blocked`.
abbrev heap : List (BitVec 64 × Nat) :=
  [(P s, (N s).toNat), (T s, 2 * (N s).toNat), (B s, 2)]

-- The memory that `permute` writes: the stack frame and `heap`.
abbrev blocks : List (BitVec 64 × Nat) := (S s - 16#64, 16) :: heap s

abbrev pmod : Modifies :=
  ⟨[.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11], blocks s⟩

-- The result of `permute` in `t`, with the return value `r`.
def Result (p0 : Perm) (r : BitVec 64) (t : MachineData) : Prop :=
  match permute p0 with
  | .ok ds => r = BitVec.ofNat 64 ds.length ∧ Mem.Contains t.dmem (T s) (bytes ds)
  | .error b => r = -1#64 ∧ Mem.Contains t.dmem (B s) (bytes [b.offset, b.excess])

-- The stack frame after `pushq %rbx`.
abbrev Frame (ra : Int64) (t : MachineData) : Prop :=
  t.regs.get64 .rsp = S s - 16#64 ∧ t.regs.get64 .rbx = B s
    ∧ t.regs.get64 .rbp = s.regs.get64 .rbp ∧ t.regs.get64 .r12 = s.regs.get64 .r12
    ∧ t.regs.get64 .r13 = s.regs.get64 .r13 ∧ t.regs.get64 .r14 = s.regs.get64 .r14
    ∧ t.regs.get64 .r15 = s.regs.get64 .r15
    ∧ Mem.Contains t.dmem (S s - 16#64) (Int.toBytes 8 (s.regs.get64 .rbx).toInt)
    ∧ Mem.Contains t.dmem (S s - 8#64) (Int.toBytes 8 ra.toBitVec.toInt)
    ∧ Mem.Mapped (blocks s) t.dmem
    ∧ Mem.UnchangedOutside (blocks s) s.dmem t.dmem

-- The loop state after `k` swaps, with `k` in `rcx`.
abbrev Common (p0 : Perm) (ra : Int64) (t : MachineData) : Prop :=
  Frame s ra t ∧ t.regs.get64 .r9 = P s ∧ t.regs.get64 .r11 = T s
    ∧ t.regs.get64 .r10 = N s - 1#64 ∧ t.regs.get64 .rdi = P s + (N s - 1#64)
    ∧ (t.regs.get64 .rcx).toNat ≤ steps p0
    ∧ Mem.Contains t.dmem (P s) (bytes (p0.state (t.regs.get64 .rcx).toNat).toList)
    ∧ Mem.Contains t.dmem (T s) (bytes (p0.trace (t.regs.get64 .rcx).toNat))
    ∧ 0 < (N s).toNat

end

-- The swap state in `t`: the count `k` is in `rcx`.
abbrev cur (p0 : Perm) (t : MachineData) : List Nat := (p0.state (t.regs.get64 .rcx).toNat).toList

-- The loop invariants. `top` is `n - 1`.
def Inv (s : MachineData) (p0 : Perm) (ra : Int64) : CfgLabel → MachineData → Prop
  | .entry, t | .label "permute", t => t = s.pushRa ra
  | .label ".L7", t => Common s p0 ra t
  | .label ".L3", t => Common s p0 ra t
      ∧ target (cur p0 t) = some (t.regs.get64 .rax).toNat
  | .label ".L13", t => Common s p0 ra t
      ∧ (cur p0 t)[(N s).toNat - 1]! = (N s).toNat - 1
      ∧ t.regs.get64 .rdx = N s - 1#64
      ∧ t.regs.get64 .rsi = BitVec.ofNat 64
          ((lastMisplaced (cur p0 t) ((N s).toNat - 1)).getD ((N s).toNat - 1))
  | .label ".L5", t => Common s p0 ra t
      ∧ (cur p0 t)[(N s).toNat - 1]! = (N s).toNat - 1
      ∧ t.regs.get64 .rax = N s - 1#64
      ∧ (t.regs.get64 .rdx).toNat < (N s).toNat - 1
      ∧ t.regs.get64 .rsi = BitVec.ofNat 64
          ((lastMisplaced (cur p0 t) (t.regs.get64 .rdx).toNat).getD ((N s).toNat - 1))
  | .label ".L12", t => Common s p0 ra t
      ∧ step (cur p0 t) = .blocked ⟨(t.regs.get64 .rax).toNat, (t.regs.get64 .rdx).toNat - 16⟩
      ∧ (t.regs.get64 .rax).toNat < 256 ∧ 16 < (t.regs.get64 .rdx).toNat
      ∧ (t.regs.get64 .rdx).toNat < 256
  | .label ".L1", t => Frame s ra t ∧ Result s p0 (t.regs.get64 .rcx) t
  | _, _ => False

-- Each loop iteration lowers `steps p0 - k`, and the scan in `.L5` lowers `n - i`.
def Var (s : MachineData) (p0 : Perm) (l : Label) (t : MachineData) : Nat :=
  let n := (N s).toNat
  let r := steps p0 - (t.regs.get64 .rcx).toNat
  match l with
  | "permute" => (n + 1) * (steps p0 + 1)
  | ".L7" => (n + 1) * (r + 1)
  | ".L3" | ".L13" => (n + 1) * r
  | ".L5" => (n + 1) * r + (n - (t.regs.get64 .rdx).toNat)
  | _ => 0

/-! ## Frame transfer -/

section
variable {s t t' : MachineData} {ra : Int64}

-- `t'` keeps the registers that `Frame` fixes.
abbrev FrameRegs (t t' : MachineData) : Prop :=
  ∀ r ∈ [Reg64.rsp, .rbx, .rbp, .r12, .r13, .r14, .r15], t'.regs.get64 r = t.regs.get64 r

theorem stack_ok (h : t.regs.get64 .rsp = S s - 16#64) : t.StackAtOrBelow (s.pushRa ra) :=
  MachineData.stackAtOrBelow_of_toNat_lt (by simp [MachineData.pushRa, h]; bv_omega)

theorem inside_stack (x : BitVec 64) (h : (x - (S s - 16#64)).toNat + 8 ≤ 16) :
    Mem.Blocks.Inside x 8 (blocks s) := Or.inl h

theorem frame_entry (hmap : Mem.Mapped (blocks s) s.dmem)
    (hrsp : t.regs.get64 .rsp = S s - 8#64 - 8#64) (hrbx : t.regs.get64 .rbx = B s)
    (hrbp : t.regs.get64 .rbp = s.regs.get64 .rbp) (h12 : t.regs.get64 .r12 = s.regs.get64 .r12)
    (h13 : t.regs.get64 .r13 = s.regs.get64 .r13) (h14 : t.regs.get64 .r14 = s.regs.get64 .r14)
    (h15 : t.regs.get64 .r15 = s.regs.get64 .r15)
    (hm : t.dmem = (s.dmem.storeInt (S s - 8#64) 8 ra.toBitVec.toInt).storeInt (S s - 8#64 - 8#64) 8
      (s.regs.get64 .rbx).toInt) :
    Frame s ra t := by
  have e : S s - 8#64 - 8#64 = S s - 16#64 := by bv_omega
  rw [e] at hrsp hm
  have i1 : Mem.Blocks.Inside (S s - 8#64) 8 (blocks s) := inside_stack _ (by
    rw [show S s - 8#64 - (S s - 16#64) = 8#64 by bv_omega]; decide)
  have i2 : Mem.Blocks.Inside (S s - 16#64) 8 (blocks s) := Mem.Blocks.Inside.base (by omega)
  refine ⟨hrsp, hrbx, hrbp, h12, h13, h14, h15, ?_, ?_, ?_, ?_⟩
  · rw [hm]; exact Mem.Contains.storeInt_self _ _ _ _ (by decide)
  · rw [hm]
    refine (Mem.Contains.storeInt_self _ _ _ _ (by decide)).storeInt_ne (fun j hj i hi => ?_) _
    simp only [Int.toBytes_length] at hi
    bv_omega
  · rw [hm]; exact (hmap.storeInt _ _ _).storeInt _ _ _
  · rw [hm]
    have hu : Mem.UnchangedOutside (blocks s) s.dmem s.dmem := fun _ _ => rfl
    exact (hu.storeInt i1 _).storeInt i2 _

theorem Frame.congr (h : Frame s ra t) (hr : FrameRegs t t') (hm : t'.dmem = t.dmem) :
    Frame s ra t' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  simp only [FrameRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hr
  rw [← hm] at h8 h9 h10 h11
  exact ⟨e1.trans h1, e2.trans h2, e3.trans h3, e4.trans h4, e5.trans h5, e6.trans h6, e7.trans h7,
    h8, h9, h10, h11⟩

theorem Frame.store (hd : Mem.Blocks.Disjoint (heap s) [(S s - 16#64, 16)]) (h : Frame s ra t)
    (hr : FrameRegs t t') {addr : BitVec 64} {n : Nat} {v : Int} (hin : Mem.Blocks.Inside addr n (heap s))
    (hm : t'.dmem = t.dmem.storeInt addr n v) : Frame s ra t' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  simp only [FrameRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hr
  dsimp only [Frame]; rw [hm]
  refine ⟨e1.trans h1, e2.trans h2, e3.trans h3, e4.trans h4, e5.trans h5, e6.trans h6, e7.trans h7,
    h8.storeInt_of_disjoint hin hd
    (Mem.Blocks.Inside.base (by simp [Int.toBytes_length])) v, h9.storeInt_of_disjoint hin hd
    (Or.inl (by rw [show S s - 8#64 - (S s - 16#64) = 8#64 by bv_omega, Int.toBytes_length]; decide)) v,
    h10.storeInt _ _ _, h11.storeInt hin.tail v⟩

-- `t'` keeps the registers that `Common` fixes.
abbrev CommonRegs (t t' : MachineData) : Prop :=
  FrameRegs t t' ∧ ∀ r ∈ [Reg64.r9, .r10, .r11, .rdi, .rcx], t'.regs.get64 r = t.regs.get64 r

theorem Common.congr {p0 : Perm} (h : Common s p0 ra t) (hr : CommonRegs t t')
    (hm : t'.dmem = t.dmem) : Common s p0 ra t' := by
  obtain ⟨hf, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  obtain ⟨hfr, hr⟩ := hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨e1, e2, e3, e4, e5⟩ := hr
  dsimp only [Common]
  rw [e1, e2, e3, e4, e5, hm]
  exact ⟨hf.congr hfr hm, h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem cur_congr {p0 : Perm} (h : t'.regs.get64 .rcx = t.regs.get64 .rcx) : cur p0 t' = cur p0 t := by
  simp only [cur, h]

end

-- Enter the block at label `l` from an internal jump: the stack pointer stays in the frame,
-- `Inv` holds at `l`, and `Var` decreases.
macro "cfg_goto" : tactic => `(tactic| (
  apply Program.Intercept.intro_label
  · repeat ((fail_if_success (apply List.getElem?_cons_zero)); (apply List.getElem?_cons_succ_of))
    apply List.getElem?_cons_zero
  refine Or.inl ⟨?_, ?_, ?_⟩))

theorem L1_result_congr {s t t' : MachineData} {p0 : Perm} {r : BitVec 64} (h : Result s p0 r t)
    (hm : t'.dmem = t.dmem) : Result s p0 r t' := by
  unfold Result at h ⊢
  rw [hm]
  exact h


theorem entry_permute_nil (p : Perm) (h : p.toList.length = 0) : permute p = .ok [] := by
  have hs : step p.toList = .done := by simp [step, h]
  rw [permute]
  split <;> simp_all

-- The two stack stores of the entry keep the caller memory.
theorem entry_contains_heap {s : MachineData} (hd1 : Mem.Blocks.Disjoint (heap s) [(S s - 16#64, 16)])
    {a : BitVec 64} {bs : List UInt8} (h : Mem.Contains s.dmem a bs)
    (ha : Mem.Blocks.Inside a bs.length (heap s)) (v w : Int) :
    Mem.Contains ((s.dmem.storeInt (S s - 8#64) 8 v).storeInt (S s - 8#64 - 8#64) 8 w) a bs := by
  have i1 : Mem.Blocks.Inside (S s - 8#64) 8 [(S s - 16#64, 16)] :=
    Or.inl (by rw [show S s - 8#64 - (S s - 16#64) = 8#64 by bv_omega]; decide)
  have i2 : Mem.Blocks.Inside (S s - 8#64 - 8#64) 8 [(S s - 16#64, 16)] :=
    Or.inl (by rw [show S s - 8#64 - 8#64 - (S s - 16#64) = 0#64 by bv_omega]; decide)
  exact (h.storeInt_of_disjoint' i1 hd1 ha v).storeInt_of_disjoint' i2 hd1 ha w


theorem L12_inside {s : MachineData} {i n : Nat} (h : i + n ≤ 2) :
    Mem.Blocks.Inside (B s + BitVec.ofNat 64 i) n (heap s) :=
  Or.inr (Or.inr (Or.inl (by
    rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]; omega)))

theorem L12_sub16 (x : BitVec 64) (h1 : 16 < x.toNat) (h2 : x.toNat < 256) :
    (BitVec.setWidth 64 (x.take 32 - 16#32)).toNat = x.toNat - 16 := by
  simp only [BitVec.take, BitVec.toNat_setWidth, BitVec.toNat_sub]
  simp
  omega

-- `.L12` stops at the swap count `k`: the step is blocked.
theorem L12_permute {p0 : Perm} {k : Nat} {b : Blocked} (hk : k ≤ steps p0)
    (h : step (p0.state k).toList = .blocked b) : permute p0 = .error b := by
  have hk' : k = steps p0 := by
    refine Nat.le_antisymm hk (Nat.not_lt.mp fun hlt => ?_)
    have := p0.step_state_lt k hlt
    rw [h] at this
    simp [Step.isSwap] at this
  rw [Perm.permute_eq, ← hk', h]


theorem L13_target (l : List Nat) (hn : 0 < l.length) (htop : l[l.length - 1]! = l.length - 1) :
    target l = lastMisplaced l (l.length - 1) := by
  have e : l.length = (l.length - 1) + 1 := by omega
  simp only [target, htop, ne_eq, not_true_eq_false, ite_false]
  conv => lhs; rw [e]
  rw [lastMisplaced_succ]
  simp [htop]

theorem L13_lm (l : List Nat) (hn : 0 < l.length) (h256 : l.length ≤ 256) {N : BitVec 64}
    (hN : N.toNat = l.length) :
    BitVec.ofNat 64 ((lastMisplaced l (l.length - 1)).getD (l.length - 1)) = N - 1#64
      ↔ lastMisplaced l (l.length - 1) = none := by
  cases h : lastMisplaced l (l.length - 1) with
  | none => simp; bv_omega
  | some pos =>
    have := (lastMisplaced_spec l _ pos h).1
    simp only [Option.getD_some, reduceCtorEq, iff_false]
    intro he
    have := congrArg BitVec.toNat he
    simp at this
    bv_omega

theorem L13_done (l : List Nat) (hn : 0 < l.length) (htop : l[l.length - 1]! = l.length - 1)
    (h : lastMisplaced l (l.length - 1) = none) : step l = .done := by
  unfold step
  have hne : l.length ≠ 0 := by omega
  simp [hne, L13_target l hn htop, h]

theorem L13_k (p0 : Perm) (k : Nat) (hk : k ≤ steps p0) (h : (step (p0.state k).toList).isSwap = false) :
    k = steps p0 := by
  rcases Nat.lt_or_ge k (steps p0) with hl | hl
  · have := p0.step_state_lt k hl
    simp_all
  · omega


/-! ## `.L7` -/

theorem L7_len {p0 : Perm} {s t : MachineData} (hlen : p0.toList.length = (N s).toNat) :
    (cur p0 t).length = (N s).toNat := by
  rw [cur, Perm.length_state, hlen]

theorem L7_lt {p0 : Perm} {s t : MachineData} {ra : Int64} (hlen : p0.toList.length = (N s).toNat)
    (h : Common s p0 ra t) : (cur p0 t)[(N s).toNat - 1]! < (N s).toNat := by
  have h0 := h.2.2.2.2.2.2.2.2
  have := Perm.getElem!_lt (p0.state (t.regs.get64 .rcx).toNat) (i := (N s).toNat - 1)
    (by rw [Perm.length_state, hlen]; omega)
  rwa [Perm.length_state, hlen] at this

theorem L7_load {p0 : Perm} {s t : MachineData} {ra : Int64} (hlen : p0.toList.length = (N s).toNat)
    (hn : (N s).toNat ≤ 256) (h : Common s p0 ra t) :
    Mem.loadInt t.dmem (t.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 0)) 1
      = some ((cur p0 t)[(N s).toNat - 1]! : Int) := by
  have hv := L7_lt hlen h
  obtain ⟨-, -, -, -, hdi, -, hcp, -, h0⟩ := h
  have e : t.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 0)
      = P s + BitVec.ofNat 64 ((N s).toNat - 1) := by
    rw [show BitVec.ofInt 64 (Int64.toInt 0) = 0#64 from rfl, BitVec.add_zero, ← Reg64s.get64_rdi, hdi]
    generalize P s = p at *
    generalize hN : N s = x at *
    bv_omega
  rw [e]
  exact hcp.load_byte (by rw [Perm.length_state, hlen]; omega) (by simp only [cur] at hv; omega)
    (by rw [Perm.length_state, hlen]; omega)

-- A length-one permutation is the identity, so `step` is done.
theorem L7_step_one {l : List Nat} (hl : l.length = 1) (h0 : l[0]! = 0) : step l = .done := by
  have h0' : l[0] = 0 := by rwa [getElem!_pos l 0 (by omega)] at h0
  simp [step, target, hl, h0', lastMisplaced_succ, lastMisplaced_zero]

-- `rcx` is the swap count when `step` gives no swap.
theorem L7_k_eq {p0 : Perm} {k : Nat} (hk : k ≤ steps p0)
    (h : (step (p0.state k).toList).isSwap = false) : k = steps p0 := by
  rcases Nat.lt_or_eq_of_le hk with hlt | heq
  · have := p0.step_state_lt k hlt; simp_all
  · exact heq

theorem L7_top_iff {x : BitVec 64} {v : Nat} (h0 : 0 < x.toNat) (hn : x.toNat ≤ 256)
    (hv : v < x.toNat) :
    (x - 1#64 - BitVec.ofNat 64 v == BitVec.zero 64) = decide (v = x.toNat - 1) := by
  by_cases h : v = x.toNat - 1
  · simp only [h, decide_true, beq_iff_eq, BitVec.zero_eq]; bv_omega
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq, BitVec.zero_eq]; bv_omega

theorem L7_zero_iff {v : Nat} (hv : v < 256) : (BitVec.ofNat 64 v == BitVec.zero 64) = decide (v = 0) := by
  by_cases h : v = 0
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq, BitVec.zero_eq]; bv_omega

-- `Result` at a state where `step` is done.
theorem L7_result {p0 : Perm} {s t t' : MachineData} {ra : Int64} (h : Common s p0 ra t)
    (hdone : step (cur p0 t) = .done) (hrcx : t'.regs.get64 .rcx = t.regs.get64 .rcx)
    (hm : t'.dmem = t.dmem) : Result s p0 (t'.regs.get64 .rcx) t' := by
  obtain ⟨-, -, -, -, -, hk, -, hct, -⟩ := h
  simp only [cur] at hdone
  have hk' := L7_k_eq hk (by rw [hdone]; rfl)
  unfold Result
  rw [hrcx, hm, Perm.permute_eq, ← hk', hdone]
  exact ⟨by simp [Perm.length_trace], hct⟩


/-! ## `.L5` -/

-- The `cmovne` in `.L5` keeps the last out-of-place position below `i + 1`.
theorem L5_rsi {l : List Nat} {i n : Nat} (hx : l[i]! < 256) (hi : i < 256) {rdx rsi : BitVec 64}
    (hrdx : rdx.toNat = i) (hrsi : rsi = BitVec.ofNat 64 ((lastMisplaced l i).getD n)) :
    (if BitVec.ofNat 64 l[i]! - rdx = 0#64 then rsi else rdx)
      = BitVec.ofNat 64 ((lastMisplaced l (i + 1)).getD n) := by
  rw [lastMisplaced_succ]
  by_cases h : l[i]! = i
  · have e : BitVec.ofNat 64 l[i]! - rdx = 0#64 := by rw [h]; bv_omega
    simp only [e, ite_true]
    simp [h, hrsi]
  · have e : BitVec.ofNat 64 l[i]! - rdx ≠ 0#64 := by
      intro he
      generalize l[i]! = x at hx he h
      subst hrdx
      bv_omega
    simp only [e, ite_false, ne_eq, h, not_false_eq_true, ite_true, Option.getD_some]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    omega

-- The loop test of `.L5`: `rax - (i + 1) = 0` iff the scan reached `n - 1`.
theorem L5_cond {n x a : BitVec 64} (ha : a = n - 1#64) (h0 : 0 < n.toNat) (hi : x.toNat < n.toNat - 1) :
    a - (1#64 + x) = 0#64 ↔ x.toNat + 1 = n.toNat - 1 := by
  subst ha
  bv_omega

-- One step of the scan in `.L5`.
theorem L5_step {s t t' : MachineData} {p0 : Perm} {ra : Int64}
    (hlen : p0.toList.length = (N s).toNat) (hn : (N s).toNat ≤ 256)
    (h : Inv s p0 ra (.label ".L5") t) (hcr : CommonRegs t t') (hm : t'.dmem = t.dmem)
    (hrax : t'.regs.get64 .rax = t.regs.get64 .rax)
    (hrdx : t'.regs.get64 .rdx = 1#64 + t.regs.get64 .rdx)
    (hrsi : t'.regs.get64 .rsi = if BitVec.ofNat 64 (cur p0 t)[(t.regs.get64 .rdx).toNat]!
      - t.regs.get64 .rdx = 0#64 then t.regs.get64 .rsi else t.regs.get64 .rdx) :
    Common s p0 ra t' ∧ (cur p0 t')[(N s).toNat - 1]! = (N s).toNat - 1
      ∧ t'.regs.get64 .rax = N s - 1#64
      ∧ (t'.regs.get64 .rdx).toNat = (t.regs.get64 .rdx).toNat + 1
      ∧ (t.regs.get64 .rdx).toNat + 1 ≤ (N s).toNat - 1
      ∧ t'.regs.get64 .rsi = BitVec.ofNat 64
          ((lastMisplaced (cur p0 t') (t'.regs.get64 .rdx).toNat).getD ((N s).toNat - 1))
      ∧ t'.regs.get64 .rcx = t.regs.get64 .rcx := by
  simp only [Inv] at h
  obtain ⟨hc, htop, hrax0, hi, hrsi0⟩ := h
  have hrcx : t'.regs.get64 .rcx = t.regs.get64 .rcx := hcr.2 _ (by simp)
  have hcur : cur p0 t' = cur p0 t := cur_congr hrcx
  have hd : (t'.regs.get64 .rdx).toNat = (t.regs.get64 .rdx).toNat + 1 := by
    rw [hrdx]
    generalize t.regs.get64 .rdx = x at hi ⊢
    bv_omega
  have hl : (cur p0 t).length = (N s).toNat := by simp [cur, Perm.length_state, hlen]
  have hx : (cur p0 t)[(t.regs.get64 .rdx).toNat]! < 256 := by
    have := (p0.state (t.regs.get64 .rcx).toNat).getElem!_lt (i := (t.regs.get64 .rdx).toNat)
      (by rw [Perm.length_state, hlen]; omega)
    rw [Perm.length_state, hlen] at this
    unfold cur; omega
  refine ⟨hc.congr hcr hm, hcur ▸ htop, hrax.trans hrax0, hd, by omega, ?_, hrcx⟩
  rw [hcur, hd, hrsi]
  exact L5_rsi hx (by omega) rfl hrsi0

-- Name the state at a jump.
theorem L5_gen [Host] {ls : List Label} {s₀ : MachineData}
    {I' : CfgLabel → Nat → Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} {a : Int64}
    {x : MachineData} (h : ∀ u, x = u → Program.Intercept ls s₀ I' E a u) :
    Program.Intercept ls s₀ I' E a x := h x rfl


/-! ## `.L3` -/

theorem L3_pos (p : Perm) {pos : Nat} (h : target p.toList = some pos) : pos < p.toList.length - 1 := by
  simp only [target] at h
  split at h
  · rename_i htop
    simp only [Option.some.injEq] at h
    subst h
    have hne : 0 < p.toList.length := by
      cases hl : p.toList with
      | nil => simp [hl] at htop
      | cons _ _ => simp
    have := p.getElem!_lt (i := p.toList.length - 1) (by omega)
    omega
  · rename_i htop
    have := lastMisplaced_spec _ _ _ h
    have : pos ≠ p.toList.length - 1 := fun he => this.2 (he ▸ (by simpa using htop))
    omega

theorem L3_step {l : List Nat} {pos : Nat} (h : target l = some pos) (hl : 0 < l.length) :
    step l = if 16 < l.length - 1 - pos then .blocked ⟨pos, l.length - 1 - pos - 16⟩
      else .swap (l.length - 1 - pos) pos := by
  simp only [step, h, MAX_SWAP_DEPTH, gt_iff_lt]
  simp [Nat.ne_of_gt hl]

theorem L3_cond (d : BitVec 64) (hd : d.toNat < 256) :
    ((!(((d - 16#64).toNat : Int) != (d.toNat : Int) - 16)) && !(d - 16#64 == BitVec.zero 64))
      = decide (16 < d.toNat) := by
  by_cases h : 16 < d.toNat
  · have e : (d - 16#64).toNat = d.toNat - 16 := by bv_omega
    have e2 : (d - 16#64 == BitVec.zero 64) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro he; have := congrArg BitVec.toNat he; simp at this; omega
    rw [e2, e]
    simp [h]
    omega
  · by_cases h16 : d.toNat = 16
    · have e : (d - 16#64 == BitVec.zero 64) = true := by
        simp only [beq_iff_eq]; apply BitVec.eq_of_toNat_eq; simp; bv_omega
      rw [e]
      simp [h]
    · have e : (d - 16#64).toNat = d.toNat + 2^64 - 16 := by bv_omega
      rw [e]
      simp [h]
      omega

theorem L3_k_eq {p0 : Perm} {k : Nat} (hk : k ≤ steps p0) (h : (step (p0.state k).toList).isSwap = false) :
    k = steps p0 := by
  refine Nat.le_antisymm hk (Nat.not_lt.mp fun hlt => ?_)
  have := p0.step_state_lt k hlt
  simp_all

theorem L3_k_lt {p0 : Perm} {k idx pos : Nat} (hk : k ≤ steps p0)
    (h : step (p0.state k).toList = .swap idx pos) : k < steps p0 := by
  refine Nat.lt_of_le_of_ne hk fun he => ?_
  have := p0.step_state_steps
  rw [← he, h] at this
  simp [Step.isSwap] at this

theorem L3_byte (x : Nat) (hx : x < 256) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8 (x : Int))) = BitVec.ofNat 64 x :=
  zeroExtend_ofInt_byte x hx

theorem L3_toNat_ofNat (x : Nat) (hx : x < 256) : (BitVec.ofNat 64 x).toNat = x := by
  simp only [BitVec.toNat_ofNat]; omega

-- The memory of the swap path: the trace byte, then the two `perm` bytes.
theorem L3_mem {m : Mem 64} {Pa Ta : BitVec 64} {rest : List (BitVec 64 × Nat)} {l tr : List Nat}
    {pos : Nat} (d : BitVec 64)
    (hP : Mem.Contains m Pa (bytes l)) (hT : Mem.Contains m Ta (bytes tr))
    (hd2 : Mem.Blocks.Disjoint [(Pa, l.length)] ((Ta, 2 * l.length) :: rest))
    (hl : 0 < l.length) (hl256 : l.length ≤ 256) (hpos : pos < l.length - 1)
    (hlt : ∀ i < l.length, l[i]! < l.length) (htr : tr.length < 2 * l.length) :
    (m.storeInt (Ta + .ofNat 64 tr.length) 1 (d.take 8).toInt).loadInt
        (Pa + .ofNat 64 (l.length - 1)) 1 = some (l[l.length - 1]! : Int)
    ∧ (m.storeInt (Ta + .ofNat 64 tr.length) 1 (d.take 8).toInt).loadInt
        (Pa + .ofNat 64 pos) 1 = some (l[pos]! : Int)
    ∧ Mem.Contains
        (((m.storeInt (Ta + .ofNat 64 tr.length) 1 (d.take 8).toInt).storeInt
          (Pa + .ofNat 64 (l.length - 1)) 1 ((BitVec.ofNat 64 l[pos]!).take 8).toInt).storeInt
          (Pa + .ofNat 64 pos) 1 ((BitVec.ofNat 64 l[l.length - 1]!).take 8).toInt)
        Pa (bytes (swapEntries l (l.length - 1) pos))
    ∧ Mem.Contains
        (((m.storeInt (Ta + .ofNat 64 tr.length) 1 (d.take 8).toInt).storeInt
          (Pa + .ofNat 64 (l.length - 1)) 1 ((BitVec.ofNat 64 l[pos]!).take 8).toInt).storeInt
          (Pa + .ofNat 64 pos) 1 ((BitVec.ofNat 64 l[l.length - 1]!).take 8).toInt)
        Ta (bytes tr ++ [d.toNat.toUInt8]) := by
  have hlb : (bytes l).length = l.length := length_bytes l
  have htb : (bytes tr).length = tr.length := length_bytes tr
  have hinT : Mem.Blocks.Inside (Ta + .ofNat 64 tr.length) 1 ((Ta, 2 * l.length) :: rest) :=
    Mem.Blocks.Inside.base_add (by rw [BitVec.toNat_ofNat]; omega)
  have hinP : ∀ i < l.length, Mem.Blocks.Inside (Pa + .ofNat 64 i) 1 [(Pa, l.length)] := fun i hi =>
    Mem.Blocks.Inside.base_add (by rw [BitVec.toNat_ofNat]; omega)
  have hP1 := hP.storeInt_of_disjoint' hinT hd2 (Mem.Blocks.Inside.base (by omega)) (d.take 8).toInt
  have htop := hlt (l.length - 1) (by omega)
  have hposv := hlt pos (by omega)
  refine ⟨hP1.load_byte (by omega) (by omega) (by omega), hP1.load_byte (by omega) (by omega) (by omega),
    ?_, ?_⟩
  · have hP2 := hP1.set_byte (i := l.length - 1) (by omega) (by omega)
      (toBytes_one_take (BitVec.ofNat 64 l[pos]!))
    rw [L3_toNat_ofNat _ (by omega), ← bytes_set] at hP2
    have hP3 := hP2.set_byte (i := pos) (by simp [length_bytes]; omega) (by simp [length_bytes]; omega)
      (toBytes_one_take (BitVec.ofNat 64 l[l.length - 1]!))
    rw [L3_toNat_ofNat _ (by omega), ← bytes_set] at hP3
    exact hP3
  · have hT1 := hT.append_byte (by omega) (toBytes_one_take d)
    rw [htb] at hT1
    have hT2 := hT1.storeInt_of_disjoint (hinP (l.length - 1) (by omega)) hd2
      (Mem.Blocks.Inside.base (by simp [htb]; omega)) ((BitVec.ofNat 64 l[pos]!).take 8).toInt
    exact hT2.storeInt_of_disjoint (hinP pos (by omega)) hd2
      (Mem.Blocks.Inside.base (by simp [htb]; omega)) _

theorem L3_frame {s t t' : MachineData} {ra : Int64}
    (hd : Mem.Blocks.Disjoint (heap s) [(S s - 16#64, 16)]) (h : Frame s ra t) (hr : FrameRegs t t')
    {a1 a2 a3 : BitVec 64} {v1 v2 v3 : Int} (h1 : Mem.Blocks.Inside a1 1 (heap s))
    (h2 : Mem.Blocks.Inside a2 1 (heap s)) (h3 : Mem.Blocks.Inside a3 1 (heap s))
    (hm : t'.dmem = ((t.dmem.storeInt a1 1 v1).storeInt a2 1 v2).storeInt a3 1 v3) : Frame s ra t' :=
  have f1 := Frame.store (t' := { t with dmem := t.dmem.storeInt a1 1 v1 }) hd h (fun _ _ => rfl) h1 rfl
  have f2 := Frame.store (t' := { t with dmem := (t.dmem.storeInt a1 1 v1).storeInt a2 1 v2 }) hd f1
    (fun _ _ => rfl) h2 rfl
  Frame.store hd f2 hr h3 hm

theorem L3_eT (r c : BitVec 64) :
    r + 1#64 + c + BitVec.ofInt 64 (-1 : Int64).toInt = r + .ofNat 64 c.toNat := by
  simp; bv_omega

theorem L3_eT2 (r c : BitVec 64) :
    r + (1#64 + c) + BitVec.ofInt 64 (-1 : Int64).toInt = r + .ofNat 64 c.toNat := by
  simp; bv_omega

theorem L3_eL (p n : BitVec 64) (h : 0 < n.toNat) :
    p + (n - 1#64) + BitVec.ofInt 64 (Int64.toInt 0) = p + .ofNat 64 (n.toNat - 1) := by
  simp; bv_omega

theorem L3_eP (p a : BitVec 64) : p + a + BitVec.ofInt 64 (Int64.toInt 0) = p + .ofNat 64 a.toNat := by
  simp


theorem permute_spec [Host] [FunDecls] (p0 : Perm) (s : MachineData) (ra : Int64)
    (hlen : p0.toList.length = (N s).toNat) (hn : (N s).toNat ≤ 256)
    (hperm : Mem.Contains s.dmem (P s) (bytes p0.toList))
    (hmap : Mem.Mapped (blocks s) s.dmem)
    (hd1 : Mem.Blocks.Disjoint (heap s) [(S s - 16#64, 16)])
    (hd2 : Mem.Blocks.Disjoint [(P s, (N s).toNat)] [(T s, 2 * (N s).toNat), (B s, 2)]) :
    ⦃ fun t => t = s.pushRa ra ⦄
      permuteAsm
    ⦃ (fun _ _ => False); fun a t => a = ra ∧ Result s p0 (t.regs.get64 .rax) t
        ∧ Mem.Mapped (blocks s) t.dmem ∧ (pmod s).Agree s t ⦄ := by
  refine ⟨fun s₀ h₀ => ?_⟩
  subst h₀
  refine Program.WP.cfg (Inv s p0 ra) (Var s p0) ?_ rfl
  cfg_cases
  -- entry
  case left t ht =>
    simp only [Inv] at ht
    subst ht
    kvcgen64
    exact rfl
  -- permute
  case right.left t ht =>
    simp only [Inv] at ht
    subst ht
    have e : (s.pushRa ra).regs.get64 .rsp = S s - 8#64 := by simp [MachineData.pushRa]
    kvcgen64
    · exact (hmap.storeInt _ _ _).loadInt_isSome (inside_stack _ (by
        rw [e, show S s - 8#64 - 8#64 - (S s - 16#64) = 0#64 by bv_omega]; decide))
    · rename_i hz
      cfg_goto
      · exact stack_ok (by simp [MachineData.pushRa]; bv_omega)
      · have hz' : s.regs.get64 .rdi = 0#64 := by
          simpa [MachineData.pushRa, CondCode.interp_z, StatusFlags.zf_from_result] using hz
        have hn0 : p0.toList.length = 0 := by rw [hlen, hz']; rfl
        refine ⟨frame_entry hmap ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, by
          unfold Result
          rw [entry_permute_nil p0 hn0]
          exact ⟨rfl, fun i hi => by simp [bytes] at hi⟩⟩
        all_goals simp [MachineData.pushRa]
      · simp [Var]
    · rename_i hz
      cfg_goto
      · exact stack_ok (by simp [MachineData.pushRa]; bv_omega)
      · have hz' : s.regs.get64 .rdi ≠ 0#64 := by
          simpa [MachineData.pushRa, CondCode.interp_z, StatusFlags.zf_from_result] using hz
        refine ⟨frame_entry hmap ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_, ?_, ?_, ?_, ?_,
          entry_contains_heap hd1 hperm (Mem.Blocks.Inside.base (by simp [length_bytes, hlen])) _ _,
          fun i hi => by simp [bytes, Perm.trace] at hi,
          Nat.pos_of_ne_zero fun h => hz' (BitVec.eq_of_toNat_eq h)⟩
        all_goals simp [MachineData.pushRa]
        all_goals bv_omega
      · simp [Var]
  -- .L13
  case right.right.left t ht =>
    simp only [Inv] at ht
    obtain ⟨hc, htop, hrdx, hrsi⟩ := ht
    have hc' := hc
    obtain ⟨hf, h9, h11, h10, hdi, hk, hP', hT', hn0⟩ := hc'
    have hl : (cur p0 t).length = (N s).toNat := by simp [cur, Perm.length_state, hlen]
    rw [← hl] at htop hrsi hn0
    have hlm := L13_lm _ hn0 (by omega) hl.symm
    kvcgen64
    · rename_i hz
      simp [CondCode.interp_z, StatusFlags.zf_from_result] at hz
      have heq : t.regs.get64 .rsi = t.regs.get64 .rdx := by simp; bv_omega
      rw [hrsi, hrdx] at heq
      have hdone := L13_done _ hn0 htop (hlm.mp heq)
      have hks := L13_k p0 _ hk (by rw [hdone]; rfl)
      cfg_goto
      · exact stack_ok hf.1
      · refine ⟨Frame.congr hf (by simp [FrameRegs]) rfl, ?_⟩
        simp only [Result]
        rw [Perm.permute_eq, ← hks, hdone]
        exact ⟨by simp [Perm.length_trace], hT'⟩
      · simp only [Reg64s.get64_rcx] at hks
        simp [Var, hks]
    · rename_i hz
      simp [CondCode.interp_z, StatusFlags.zf_from_result] at hz
      have hne : ¬ t.regs.get64 .rsi = t.regs.get64 .rdx := by simp; bv_omega
      rw [hrsi, hrdx] at hne
      obtain ⟨pos, hpos⟩ := Option.ne_none_iff_exists'.mp (mt hlm.mpr hne)
      have hlt := (lastMisplaced_spec _ _ pos hpos).1
      rw [hpos] at hrsi
      refine ⟨Common.congr hc (by simp [CommonRegs, FrameRegs]) rfl, ?_⟩
      show target (cur p0 t) = some (t.regs.get64 .rsi).toNat
      rw [L13_target _ hn0 htop, hpos]
      simp [hrsi]
      omega
    · simp [Var]
  -- .L3
  case right.right.right.left t ht =>
    simp only [Inv] at ht
    obtain ⟨hC, htgt⟩ := ht
    have ⟨hf, h9, h11, h10, hdi, hk, hPc, hTc, hN0⟩ := hC
    simp only [Reg64s.get64_r9, Reg64s.get64_r10, Reg64s.get64_r11, Reg64s.get64_rdi,
      Reg64s.get64_rax, Reg64s.get64_rcx, cur] at h9 h10 h11 hdi hk hPc hTc htgt
    have hl : (p0.state t.regs.rcx.toBitVec.toNat).toList.length = (N s).toNat := by
      rw [Perm.length_state, hlen]
    have hpos := L3_pos _ htgt
    have hstep := L3_step htgt (by rw [hl]; exact hN0)
    rw [hl] at hpos hstep
    have hd : (t.regs.r10.toBitVec - t.regs.rax.toBitVec).toNat
        = (N s).toNat - 1 - t.regs.rax.toBitVec.toNat := by
      rw [h10]; simp only [N, Reg64s.get64_rdi] at hpos hn hN0 ⊢; bv_omega
    kvcgen64
    case vc1 =>
      rename_i hc
      simp only [CondCode.interp_a, StatusFlags.cf_from_result, StatusFlags.zf_from_result] at hc
      rw [L3_cond _ (by rw [hd]; omega), hd] at hc
      simp only [decide_eq_true_eq] at hc
      rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at hstep
      have hks := L3_k_eq hk (by rw [hstep]; rfl)
      cfg_goto
      · exact stack_ok hf.1
      · simp only [Inv]
        refine ⟨Common.congr hC (by simp [CommonRegs, FrameRegs]) rfl, ?_, ?_, ?_, ?_⟩
        · rw [cur_congr rfl]
          simp only [cur, Reg64s.get64_rax, Reg64s.get64_rdx, Reg64s.get64_rcx, hd]
          exact hstep
        all_goals simp only [Reg64s.get64_rax, Reg64s.get64_rdx, hd]
        all_goals omega
      · right
        refine ⟨?_, by decide⟩
        simp [Var, ← hks]
    all_goals rename_i hc
    all_goals simp only [CondCode.interp_a, StatusFlags.cf_from_result, StatusFlags.zf_from_result] at hc
    all_goals rw [L3_cond _ (by rw [hd]; omega), hd] at hc
    all_goals simp only [decide_eq_false_iff_not, Nat.not_lt] at hc
    all_goals rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at hstep
    all_goals have hks := L3_k_lt hk hstep
    all_goals
      simp only [Reg64s.get64_rax, Reg64s.get64_rcx, Reg64s.get64_rdi,
        Reg64s.get64_r11]
      have hsl := p0.steps_lt (by rw [hlen]; exact hN0)
      rw [hlen] at hsl
      have hM := L3_mem (m := t.dmem) (pos := t.regs.rax.toBitVec.toNat)
        (t.regs.r10.toBitVec - t.regs.rax.toBitVec) hPc hTc (by rw [hl]; exact hd2) (by rw [hl]; exact hN0)
        (by rw [hl]; exact hn) (by rw [hl]; exact hpos) (fun i hi => (p0.state _).getElem!_lt hi)
        (by rw [Perm.length_trace, hl]; omega)
      have eT : t.regs.r11.toBitVec + 1#64 + t.regs.rcx.toBitVec + BitVec.ofInt 64 (-1 : Int64).toInt
          = s.regs.get64 .rdx + .ofNat 64 (p0.trace t.regs.rcx.toBitVec.toNat).length := by
        rw [Perm.length_trace, h11]; exact L3_eT _ _
      have eT2 : t.regs.r11.toBitVec + (1#64 + t.regs.rcx.toBitVec) + BitVec.ofInt 64 (-1 : Int64).toInt
          = s.regs.get64 .rdx + .ofNat 64 (p0.trace t.regs.rcx.toBitVec.toNat).length := by
        rw [Perm.length_trace, h11]; exact L3_eT2 _ _
      have eL : t.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 0)
          = s.regs.get64 .rsi + .ofNat 64 ((p0.state t.regs.rcx.toBitVec.toNat).toList.length - 1) := by
        rw [hdi, hl]; exact L3_eL _ _ hN0
      have eP : t.regs.r9.toBitVec + t.regs.rax.toBitVec + BitVec.ofInt 64 (Int64.toInt 0)
          = s.regs.get64 .rsi + .ofNat 64 t.regs.rax.toBitVec.toNat := by
        rw [h9]; exact L3_eP _ _
      try simp only [eT, eT2, eL, eP]
      have hmap := hf.2.2.2.2.2.2.2.2.2.1
    case vc2 =>
      exact hmap.loadInt_isSome (.tail (.tail (.base_add (by rw [Perm.length_trace, BitVec.toNat_ofNat]; omega))))
    case vc3 => rw [hM.1]; rfl
    case vc4 => rw [hM.2.1]; rfl
    case vc5 => rw [hM.1]; rfl
    case vc6 =>
      simp only [hM.2.1]
      exact ((hmap.storeInt _ _ _).storeInt _ _ _).loadInt_isSome
        (.tail (.base_add (by rw [BitVec.toNat_ofNat]; omega)))
    case vc7 =>
      have hlt := fun i hi => (p0.state t.regs.rcx.toBitVec.toNat).getElem!_lt (i := i) hi
      have htop := hlt ((p0.state t.regs.rcx.toBitVec.toNat).toList.length - 1) (by omega)
      have hposv := hlt t.regs.rax.toBitVec.toNat (by omega)
      have ek : (1#64 + t.regs.rcx.toBitVec).toNat = t.regs.rcx.toBitVec.toNat + 1 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      rw [hM.1, hM.2.1]
      simp only [Option.get!_some]
      rw [L3_byte _ (by omega), L3_byte _ (by omega)]
      simp only [Inv]
      refine ⟨L3_frame hd1 hf (by simp [FrameRegs]) (.tail (.base_add ?_)) (.base_add ?_) (.base_add ?_) rfl,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, hN0⟩
      · rw [Perm.length_trace, BitVec.toNat_ofNat]; unfold N; omega
      · rw [BitVec.toNat_ofNat, hl]; unfold N; omega
      · rw [BitVec.toNat_ofNat]; unfold N; omega
      · exact hC.2.1
      · exact hC.2.2.1
      · exact hC.2.2.2.1
      · exact hC.2.2.2.2.1
      · show (1#64 + t.regs.rcx.toBitVec).toNat ≤ _
        rw [ek]; omega
      · show Mem.Contains _ _ (bytes (p0.state (1#64 + t.regs.rcx.toBitVec).toNat).toList)
        rw [ek, Perm.state_succ, Perm.advance_eq _ hstep]
        exact hM.2.2.1
      · show Mem.Contains _ _ (bytes (p0.trace (1#64 + t.regs.rcx.toBitVec).toNat))
        rw [ek, Perm.trace_succ, Perm.depth_eq _ hstep, bytes_append]
        have hT' := hM.2.2.2
        rw [hd] at hT'
        exact hT'
    case vc8 =>
      right
      refine ⟨?_, by decide⟩
      simp only [Var, Reg64s.get64_rcx]
      rw [show (1#64 + t.regs.rcx.toBitVec).toNat = t.regs.rcx.toBitVec.toNat + 1 by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega]
      congr 1
      omega
  -- .L7
  case right.right.right.right.left t ht =>
    simp only [Inv] at ht
    have hv := L7_lt hlen ht
    have hload := L7_load hlen hn ht
    have h0 : 0 < (N s).toNat := ht.2.2.2.2.2.2.2.2
    have hr10 : t.regs.r10.toBitVec = N s - 1#64 := by rw [← Reg64s.get64_r10]; exact ht.2.2.2.1
    have hsp : t.regs.rsp.toBitVec = S s - 16#64 := by rw [← Reg64s.get64_rsp]; exact ht.1.1
    have hl := L7_len (t := t) hlen
    generalize hcv : (cur p0 t)[(N s).toNat - 1]! = v at hv hload
    have hz : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8 (v : Int))) = BitVec.ofNat 64 v :=
      zeroExtend_ofInt_byte _ (by omega)
    have hvn : (BitVec.ofNat 64 v).toNat = v := by simp; omega
    kvcgen64
    case vc1 => rw [Reg64s.get64_rdi, hload]; rfl
    case vc2 hnz =>
      simp only [hload, Option.get!_some, hz, CondCode.interp_nz, StatusFlags.zf_from_result, hr10,
        L7_top_iff h0 hn hv, Bool.not_eq_true', decide_eq_false_iff_not] at hnz
      simp only [hload, Option.get!_some, hz]
      cfg_goto
      · exact stack_ok (by simpa using hsp)
      · simp only [Inv]
        refine ⟨Common.congr ht ⟨by simp [FrameRegs], by simp⟩ rfl, ?_⟩
        show target (cur p0 t) = _
        simp only [target, hl, hcv]
        rw [ite_eq_left hnz]
        simp [hvn]
      · simp only [Var, Reg64s.get64_rcx]
        left
        rw [Nat.mul_succ]
        have : 0 < (N s).toNat + 1 := by omega
        omega
    case vc3 hnz _ hz0 =>
      simp only [hload, Option.get!_some, hz, CondCode.interp_nz, StatusFlags.zf_from_result, hr10,
        L7_top_iff h0 hn hv, Bool.not_eq_false', decide_eq_true_eq] at hnz
      simp only [hload, Option.get!_some, hz, CondCode.interp_z, StatusFlags.zf_from_result,
        BitVec.and_self, L7_zero_iff (by omega : v < 256), decide_eq_true_eq] at hz0
      simp only [hload, Option.get!_some, hz]
      have e : (N s).toNat - 1 = 0 := hnz.symm.trans hz0
      rw [e] at hcv
      have hdone : step (cur p0 t) = .done := L7_step_one (by rw [hl]; omega) (by rw [hcv, hz0])
      cfg_goto
      · exact stack_ok (by simpa using hsp)
      · simp only [Inv]
        exact ⟨Frame.congr (s := s) (ra := ra) ht.1 (by simp [FrameRegs]) rfl, L7_result ht hdone rfl rfl⟩
      · simp only [Var, Reg64s.get64_rcx]
        left
        exact Nat.mul_pos (by omega) (by omega)
    case vc4 hnz _ hz0 =>
      simp only [hload, Option.get!_some, hz, CondCode.interp_nz, StatusFlags.zf_from_result, hr10,
        L7_top_iff h0 hn hv, Bool.not_eq_false', decide_eq_true_eq] at hnz
      simp only [hload, Option.get!_some, hz, CondCode.interp_z, StatusFlags.zf_from_result,
        BitVec.and_self, L7_zero_iff (by omega : v < 256), decide_eq_false_iff_not] at hz0
      have hnz' : v = (N s).toNat - 1 := hnz
      simp only [hload, Option.get!_some, hz, Inv]
      refine ⟨Common.congr ht ⟨by simp [FrameRegs], by simp⟩ rfl, ?_, ?_, ?_, ?_⟩
      · show (cur p0 t)[_]! = _
        rw [hcv, hnz']
      · simp only [Reg64s.get64_rax]
        rw [hnz']
        generalize N s = x at *
        bv_omega
      · simp only [Reg64s.get64_rdx, BitVec.toNat_ofNat]
        omega
      · show _ = BitVec.ofNat 64 ((lastMisplaced (cur p0 t) _).getD _)
        simp [lastMisplaced_zero, hnz]
    case vc5 hnz _ hz0 =>
      simp only [hload, Option.get!_some, hz, CondCode.interp_z, StatusFlags.zf_from_result,
        BitVec.and_self, L7_zero_iff (by omega : v < 256), decide_eq_false_iff_not] at hz0
      simp only [Var, Reg64s.get64_rcx, Reg64s.get64_rdx]
      left
      simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero]
      rw [Nat.mul_succ]
      omega
  -- .L5
  case right.right.right.right.right.left t ht =>
    have hinv := ht
    simp only [Inv] at ht
    obtain ⟨hc, htop, hrax, hi, hrsi⟩ := ht
    have hc0 := hc
    obtain ⟨hf, hr9, hr11, hr10, hrdi, hk, hPc, hTc, hn0⟩ := hc0
    have hl : (cur p0 t).length = (N s).toNat := by simp [cur, Perm.length_state, hlen]
    have hx : (cur p0 t)[(t.regs.get64 .rdx).toNat]! < 256 := by
      have := (p0.state (t.regs.get64 .rcx).toNat).getElem!_lt (i := (t.regs.get64 .rdx).toNat)
        (by rw [Perm.length_state, hlen]; omega)
      rw [Perm.length_state, hlen] at this
      unfold cur; omega
    have hload : Mem.loadInt t.dmem (t.regs.get64 .r9 + t.regs.get64 .rdx
        + BitVec.ofInt 64 (Int64.toInt 0)) 1 = some ((cur p0 t)[(t.regs.get64 .rdx).toNat]! : Int) := by
      have := hPc.load_byte (i := (t.regs.get64 .rdx).toNat) (by rw [hl]; omega) hx (by rw [hl]; omega)
      rw [← this]
      simp only [Reg64s.get64_r9] at hr9
      simp [hr9]
    have hload' : Mem.loadInt t.dmem (t.regs.r9.toBitVec + t.regs.rdx.toBitVec
        + BitVec.ofInt 64 (Int64.toInt 0)) 1 = some ((cur p0 t)[(t.regs.get64 .rdx).toNat]! : Int) := hload
    have hr8 : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8
        ((cur p0 t)[(t.regs.get64 .rdx).toNat]! : Int))) = BitVec.ofNat 64 (cur p0 t)[(t.regs.get64 .rdx).toNat]! :=
      zeroExtend_ofInt_byte _ hx
    kvcgen64
    · rw [hload]; rfl
    all_goals rename_i hcond
    all_goals simp only [hload', Option.get!_some, hr8, CondCode.interp_nz,
      StatusFlags.zf_from_result] at hcond ⊢
    all_goals apply L5_gen
    all_goals intro u hu
    all_goals have hrcxu : u.regs.get64 .rcx = t.regs.get64 .rcx := by rw [← hu]; simp
    all_goals (
      obtain ⟨hcu, htopu, hraxu, hdu, hle, hrsiu, -⟩ := L5_step hlen hn hinv (t' := u)
        (by rw [← hu]; simp [CommonRegs, FrameRegs]) (by rw [← hu]) (by rw [← hu]; simp) (by rw [← hu]; simp)
        (by rw [← hu]; simp [cur]))
    all_goals have hcond' := L5_cond hrax hn0 hi
    -- jne .L5: the scan goes on.
    · have hne : (t.regs.get64 .rdx).toNat + 1 ≠ (N s).toNat - 1 := by
        exact fun h => by simp_all
      cfg_goto
      · exact stack_ok (by rw [← hu]; simpa using hf.1)
      · simp only [Inv]
        exact ⟨hcu, htopu, hraxu, by omega, hrsiu⟩
      · left
        simp only [Var, hrcxu, hdu]
        exact Nat.add_lt_add_left (by omega) _
    -- jmp .L13: the scan is complete.
    · have heq : (t.regs.get64 .rdx).toNat + 1 = (N s).toNat - 1 := by
        exact hcond'.mp (by simpa using hcond)
      cfg_goto
      · exact stack_ok (by rw [← hu]; simpa using hf.1)
      · simp only [Inv]
        rw [hdu, heq] at hrsiu
        refine ⟨hcu, htopu, ?_, hrsiu⟩
        apply BitVec.eq_of_toNat_eq
        rw [hdu, heq]
        bv_omega
      · left
        simp only [Var, hrcxu]
        exact Nat.lt_add_of_pos_right (by omega)
  -- .L12
  case right.right.right.right.right.right.left t ht =>
    simp only [Inv] at ht
    obtain ⟨⟨hf, -, -, -, -, hk, -, -, -⟩, hstep, hax, hdx1, hdx2⟩ := ht
    have hrbx : t.regs.get64 .rbx = B s := hf.2.1
    have hrbx' : t.regs.rbx.toBitVec = B s := hf.2.1
    have hmapt : Mem.Mapped (blocks s) t.dmem := hf.2.2.2.2.2.2.2.2.2.1
    have e0 : BitVec.ofInt 64 (Int64.toInt 0) = 0#64 := by simp
    have e1 : BitVec.ofInt 64 (Int64.toInt 1) = 1#64 := by simp
    kvcgen64
    · rw [hrbx, e0]
      exact hmapt.loadInt_isSome (L12_inside (i := 0) (by omega)).tail
    · simp only [Reg64s.get64_rbx, hrbx', e0, e1]
      exact (hmapt.storeInt _ _ _).loadInt_isSome (L12_inside (i := 1) (by omega)).tail
    · simp only [Inv]
      rw [hrbx', e0, e1]
      have hf1 : Frame s ra { t with dmem := Mem.storeInt t.dmem (B s + 0#64) 1 (t.regs.rax.toBitVec.take 8).toInt } :=
        Frame.store hd1 hf (by simp [FrameRegs]) (L12_inside (i := 0) (by omega)) rfl
      refine ⟨Frame.store hd1 hf1 (by simp [FrameRegs]) (L12_inside (i := 1) (by omega)) rfl, ?_⟩
      simp only [Result, L12_permute hk hstep]
      refine ⟨rfl, ?_⟩
      have c0 : Mem.Contains t.dmem (B s) [] := fun i hi => by simp at hi
      have c1 := c0.append_byte (by decide) (toBytes_one_take t.regs.rax.toBitVec)
      have c2 := c1.append_byte (by simp) (toBytes_one_take
        (BitVec.setWidth 64 (t.regs.rdx.toBitVec.take 32 - 16#32)))
      rw [L12_sub16 t.regs.rdx.toBitVec hdx1 hdx2] at c2
      simpa [bytes] using c2
    · exact Or.inr ⟨rfl, by omega⟩
  -- .L1
  case right.right.right.right.right.right.right t ht =>
    simp only [Inv] at ht
    obtain ⟨⟨hrsp, -, hrbp, h12, h13, h14, h15, hc1, hc2, hmb, hu⟩, hres⟩ := ht
    have hl1 : t.dmem.loadInt (t.regs.get64 .rsp) 8 =
        some (Int.ofBytes (Int.toBytes 8 (s.regs.get64 .rbx).toInt)) := by
      rw [hrsp]; exact hc1.loadInt_eq (Int.toBytes_length _ _)
    have hl2 : t.dmem.loadInt (t.regs.get64 .rsp + 8#64) 8 =
        some (Int.ofBytes (Int.toBytes 8 ra.toBitVec.toInt)) := by
      rw [hrsp, show S s - 16#64 + 8#64 = S s - 8#64 by bv_omega]
      exact hc2.loadInt_eq (Int.toBytes_length _ _)
    simp only [Reg64s.get64_rsp, Reg64s.get64_rbp, Reg64s.get64_r12, Reg64s.get64_r13,
      Reg64s.get64_r14, Reg64s.get64_r15] at hl1 hl2 hrsp hrbp h12 h13 h14 h15
    kvcgen64
    · simp [hl1]
    · simp [MachineData.retAddr, hl2]
    · refine Or.inr ⟨⟨?_, L1_result_congr hres rfl, hmb, fun r hr => ?_, hu⟩, fun _ _ _ => ?_⟩
      · simp only [MachineData.retAddr, Reg64s.get64_rsp, hl2, Option.map_some, Option.get!_some]
        exact Int64.ofBitVec_ofBytes_toBytes ra
      · cases r <;> simp at hr ⊢
        all_goals first
          | assumption
          | (rw [hl1]; exact BitVec.ofInt_ofBytes_toBytes 64 8 rfl _)
          | bv_omega
      · apply MachineData.stackBelow_of_add_eight
        simp [MachineData.pushRa, hrsp]
        bv_omega

end State
