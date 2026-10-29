import BbuKraken.Contracts
import PermuteKraken.Proof
import BbuKraken.Kit
import BbuKraken.Fn.FinishMem

open Std.WP Lean.Order
open scoped Program.WP
open PermuteKraken

set_option experimental.vcgen true

namespace Bbu

open FinishMem

/-! ## The contract of `permute` -/

-- The hypotheses of `permute_spec` for the permutation `p0`.
def PermHyp (s : MachineData) (p0 : Perm) : Prop :=
  p0.toList.length = (State.N s).toNat ∧ (State.N s).toNat ≤ Bbu.MAX_N
    ∧ Mem.Contains s.dmem (State.P s) (words p0.toList)
    ∧ Mem.Mapped (State.blocks s) s.dmem
    ∧ Mem.Blocks.Disjoint (State.heap s) [(State.S s - 16#64, 16)]
    ∧ Mem.Blocks.Disjoint [(State.P s, 2 * (State.N s).toNat)]
        [(State.T s, 2 * (State.N s).toNat), (State.B s, 4)]

def PermPre (s : MachineData) : Prop := ∃ p0, PermHyp s p0
def PermPost (s t : MachineData) : Prop :=
  Mem.Mapped (State.blocks s) t.dmem ∧ ∀ p0, PermHyp s p0 → State.Result s p0 (rax t) t
abbrev PermMod (s : MachineData) : Modifies := State.pmod s

-- The bytes in memory fix the permutation.
theorem PermHyp.unique {s : MachineData} {p q : Perm} (hp : PermHyp s p) (hq : PermHyp s q) :
    p = q := by
  obtain ⟨hpl, hn, hpc, -⟩ := hp
  obtain ⟨hql, -, hqc, -⟩ := hq
  have hb : words p.toList = words q.toList := by
    apply List.ext_getElem (by simp [length_words, hpl, hql])
    intro i h1 h2
    have e1 := hpc i h1
    have e2 := hqc i h2
    rw [e1] at e2
    exact Option.some.inj e2
  have hl : p.toList = q.toList := by
    apply List.ext_getElem (by rw [hpl, hql])
    intro i h1 h2
    have e0 := congrArg (·[2 * i]?) hb
    have e1 := congrArg (·[2 * i + 1]?) hb
    simp only [getElem?_words, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
      show 2 * i / 2 = i by omega, show (2 * i + 1) / 2 = i by omega, show 2 * i % 2 = 0 by omega,
      show (2 * i + 1) % 2 = 1 by omega, Option.map_some, Option.some.injEq, ite_true,
      show ¬ (1 = 0) by omega, ite_false] at e0 e1
    have a1 := p.lt i h1
    have a2 := q.lt i h2
    have hN : (State.N s).toNat ≤ 1024 := hn
    have c0 := congrArg UInt8.toNat e0
    have c1 := congrArg UInt8.toNat e1
    simp only [Nat.toUInt8, UInt8.toNat_ofNat'] at c0 c1
    omega
  cases p; cases q
  cases hl
  rfl

theorem permute_callSpec [Host] [FunDecls] [Embeds State.permuteAsm]
    (hg : FunDecls.at (label "permute") = some ⟨State.permuteAsm⟩) :
    Program.WP.CallSpec "permute" PermPre PermPost PermMod := by
  refine Program.WP.callSpec_of_triple hg fun s ra => ⟨fun s₀ ⟨h₀, p0, hp⟩ => ?_⟩
  have h := hp
  obtain ⟨hlen, hn, hperm, hmap, hd1, hd2⟩ := h
  refine Program.wp_mono (fun _ h => h) ?_
    ((State.permute_spec p0 s ra hlen hn hperm hmap hd1 hd2).1 s₀ h₀)
  rintro u ⟨ha, hr, hm, hag⟩
  exact ⟨ha, ⟨hm, fun q hq => (hp.unique hq) ▸ hr⟩, hag⟩

/-! ## Bounds of `permute` -/

theorem target_lt (q : Perm) {pos : Nat} (h : PermuteKraken.target q.toList = some pos) : pos < q.toList.length := by
  unfold PermuteKraken.target at h
  dsimp only at h
  split at h
  · cases h
    exact q.getElem!_lt (by
      rcases Nat.eq_zero_or_pos q.toList.length with h0 | h0
      · rename_i hne; simp [h0] at hne
      · omega)
  · exact (lastMisplaced_spec _ _ _ h).1

theorem step_blocked_lt (q : Perm) {b : Blocked} (h : PermuteKraken.step q.toList = .blocked b) :
    b.offset < q.toList.length ∧ b.excess < q.toList.length := by
  unfold PermuteKraken.step at h
  split at h
  · cases h
  dsimp only at h
  split at h
  · cases h
  · rename_i pos hpos
    have := target_lt q hpos
    split at h
    · cases h
      simp only
      omega
    · cases h

theorem trace_le (p : Perm) : ∀ k ≤ steps p, ∀ x ∈ p.trace k, x ≤ PermuteKraken.MAX_SWAP_DEPTH := by
  intro k
  induction k with
  | zero => simp [Perm.trace]
  | succ k ih =>
    intro hk x hx
    rw [Perm.trace_succ, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ih (by omega) x hx
    · obtain ⟨idx, pos, hs⟩ := Perm.isSwap_iff.mp (p.step_state_lt k (by omega))
      rw [Perm.depth_eq _ hs]
      exact (PermuteKraken.step_swap hs).2.1

theorem permute_ok_bound {p : Perm} {L : List Nat} (h : PermuteKraken.permute p = .ok L) :
    L.length ≤ 2 * p.toList.length ∧ ∀ x ∈ L, x ≤ PermuteKraken.MAX_SWAP_DEPTH := by
  rw [Perm.permute_eq] at h
  split at h
  · cases h
  · cases h
    refine ⟨?_, trace_le p _ (Nat.le_refl _)⟩
    rw [Perm.length_trace]
    rcases Nat.eq_zero_or_pos p.toList.length with h0 | h0
    · rw [p.steps_zero h0]; omega
    · have := p.steps_lt h0; omega

theorem permute_err_bound {p : Perm} {b : Blocked} (h : PermuteKraken.permute p = .error b) :
    b.offset < p.toList.length ∧ b.excess < p.toList.length := by
  rw [Perm.permute_eq] at h
  split at h
  · cases h
    rename_i hs
    have := step_blocked_lt _ hs
    rwa [Perm.length_state] at this
  · cases h

/-! ## The proof of `permuteDestinations` -/

local macro "cfg_goto" : tactic => `(tactic| (
  apply Program.Intercept.intro_label
  · repeat ((fail_if_success (apply List.getElem?_cons_zero)); (apply List.getElem?_cons_succ_of))
    apply List.getElem?_cons_zero
  refine Or.inl ⟨?_, ?_, ?_⟩))

-- Normalize the registers and close a goal on addresses.
local macro "bvo" : tactic => `(tactic| (
  simp only [Reg64s.get64_rsp, Reg64s.get64_rdi, Reg64s.get64_rax, Reg64s.get64_rbx,
    Reg64s.get64_rdx, Reg64s.get64_rsi, Reg64s.get64_rcx, finishF_eq, Mem.Blocks.Inside, or_false,
    Int64.reduceToInt, BitVec.ofInt_ofNat] at *
  bv_omega))

namespace FinishProof

section
variable (s : MachineData) (ra : Int64)

-- The frame of `permuteDestinations` after `subq $4112, %rsp`.
structure Fr (t : MachineData) : Prop where
  hrsp : rsp t = rsp s - 4128#64
  hrbx : t.regs.get64 .rbx = rdi s
  hrbp : t.regs.get64 .rbp = s.regs.get64 .rbp
  h12 : t.regs.get64 .r12 = s.regs.get64 .r12
  h13 : t.regs.get64 .r13 = s.regs.get64 .r13
  h14 : t.regs.get64 .r14 = s.regs.get64 .r14
  h15 : t.regs.get64 .r15 = s.regs.get64 .r15
  cbx : Mem.Contains t.dmem (rsp s - 16#64) (Int.toBytes 8 (s.regs.get64 .rbx).toInt)
  cra : Mem.Contains t.dmem (rsp s - 8#64) (Int.toBytes 8 ra.toBitVec.toInt)
  map : Mem.Mapped (frame finishF s :: writable s.dmem (rdi s)) t.dmem

-- The swap loop has done the first `j` swaps of `L`.
def SwInv (L : List Nat) (j : Nat) (t : MachineData) : Prop :=
  t.regs.get64 .r9 = rsp s - 4112#64 + BitVec.ofNat 64 L.length
    ∧ t.regs.get64 .r10 = rd s.dmem (wordAt (rdi s) 0) - 1#64
    ∧ rsi t = (rd s.dmem (wordAt (rdi s) 0) - 1#64) * 8#64
    ∧ Mem.Contains t.dmem (rsp s - 4112#64) (bytes L)
    ∧ st' s t = (L.take j).foldl swapTop (st s)
    ∧ Mem.UnchangedOutside [frame finishF s, (wordAt (rdi s) 2, 8),
        (dataOf s.dmem (rdi s), 8 * nOf s.dmem (rdi s)), (opsOf s.dmem (rdi s), 72 * nOf s.dmem (rdi s))]
        s.dmem t.dmem

def FInv (p0 : Perm) : CfgLabel → MachineData → Prop
  | .entry, t | .label "permuteDestinations", t => t = s.pushRa ra
  | .label ".LB52", t => Fr s ra t ∧ Mem.UnchangedOutside [frame finishF s] s.dmem t.dmem
      ∧ rdi t = rd s.dmem (wordAt (rdi s) 0) ∧ (rax t).toNat < p0.toList.length
      ∧ Mem.Contains t.dmem (rsp s - 2064#64) (words (p0.toList.take (rax t).toNat))
  | .label ".LB51", t => Fr s ra t ∧ Mem.UnchangedOutside [frame finishF s] s.dmem t.dmem
      ∧ rdi t = rd s.dmem (wordAt (rdi s) 0)
      ∧ Mem.Contains t.dmem (rsp s - 2064#64) (words p0.toList)
  | .label ".LB55", t => Fr s ra t ∧ ∃ L, permute p0 = .ok L ∧ ∃ j < L.length,
      rdx t = rsp s - 4112#64 + BitVec.ofNat 64 j ∧ SwInv s L j t
  | .label ".LB50", t => Fr s ra t ∧ Wf t.dmem (rdi s) ∧ finishR s t
      ∧ Mem.UnchangedOutside (frame finishF s :: writable s.dmem (rdi s)) s.dmem t.dmem
  | .label ".LB60", t => Fr s ra t ∧ Mem.UnchangedOutside [frame finishF s] s.dmem t.dmem
      ∧ ∃ b, permute p0 = .error b
        ∧ Mem.Contains t.dmem (rsp s - 4116#64) (words [b.offset, b.excess])
  | .label ".LB56", t => Fr s ra t ∧ Mem.UnchangedOutside [frame finishF s] s.dmem t.dmem
      ∧ permute p0 = .ok []
  | _, _ => False

def FVar (l : Label) (t : MachineData) : Nat :=
  match l with
  | "permuteDestinations" => 5000
  | ".LB52" => 3000 + (1024 - (rax t).toNat)
  | ".LB51" => 3000
  | ".LB55" => 2100 - (rdx t - (rsp s - 4112#64)).toNat
  | ".LB60" => 1
  | ".LB56" => 1
  | _ => 0

end

/-! ## Frame lemmas -/

section
variable {s t t' : MachineData} {ra : Int64}

-- `t'` keeps the registers that `Fr` fixes.
abbrev FrameRegs (t t' : MachineData) : Prop :=
  ∀ r ∈ [Reg64.rsp, .rbx, .rbp, .r12, .r13, .r14, .r15], t'.regs.get64 r = t.regs.get64 r

theorem frameRegs_of (h1 : t'.regs.rsp = t.regs.rsp) (h2 : t'.regs.rbx = t.regs.rbx)
    (h3 : t'.regs.rbp = t.regs.rbp) (h4 : t'.regs.r12 = t.regs.r12) (h5 : t'.regs.r13 = t.regs.r13)
    (h6 : t'.regs.r14 = t.regs.r14) (h7 : t'.regs.r15 = t.regs.r15) : FrameRegs t t' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [Reg64s.get64_rsp, h1]
  · simp only [Reg64s.get64_rbx, h2]
  · simp only [Reg64s.get64_rbp, h3]
  · simp only [Reg64s.get64_r12, h4]
  · simp only [Reg64s.get64_r13, h5]
  · simp only [Reg64s.get64_r14, h6]
  · simp only [Reg64s.get64_r15, h7]

theorem Fr.congr (h : Fr s ra t) (hr : FrameRegs t t') (hm : t'.dmem = t.dmem) : Fr s ra t' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  simp only [FrameRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hr
  rw [← hm] at h8 h9 h10
  exact ⟨e1.trans h1, e2.trans h2, e3.trans h3, e4.trans h4, e5.trans h5, e6.trans h6, e7.trans h7,
    h8, h9, h10⟩

-- A store outside the saved `rbx` and the return address keeps `Fr`.
theorem Fr.store (h : Fr s ra t) (hr : FrameRegs t t') {a : Addr} {n : Nat} {v : Int}
    (hd : Mem.Blocks.Disjoint [(a, n)] [(rsp s - 16#64, 16)])
    (hm : t'.dmem = t.dmem.storeInt a n v) : Fr s ra t' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  simp only [FrameRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hr
  refine ⟨e1.trans h1, e2.trans h2, e3.trans h3, e4.trans h4, e5.trans h5, e6.trans h6, e7.trans h7,
    ?_, ?_, ?_⟩ <;> rw [hm]
  · exact h8.storeInt_of_disjoint (Mem.Blocks.Inside.base (Nat.le_refl n)) hd
      (Mem.Blocks.Inside.base (by simp [Int.toBytes_length])) v
  · exact h9.storeInt_of_disjoint (Mem.Blocks.Inside.base (Nat.le_refl n)) hd
      (Or.inl (by rw [show rsp s - 8#64 - (rsp s - 16#64) = 8#64 by bv_omega, Int.toBytes_length]; decide)) v
  · exact h10.storeInt _ _ _

theorem mapped_entry (hf : FrameOk finishF s) (hw : Wf s.dmem (rdi s)) :
    Mem.Mapped (frame finishF s :: writable s.dmem (rdi s)) s.dmem := fun x hx =>
  hx.elim (fun h => hf.mapped x (Or.inl h)) fun h => hw.mapped x (inside_append.mpr (Or.inl h))

-- The prologue: `pushq %rbx` and `subq $4112, %rsp` after the call.
theorem Fr.entry (hf : FrameOk finishF s) (hw : Wf s.dmem (rdi s))
    (hrsp : rsp t = rsp s - 4128#64) (hrbx : t.regs.get64 .rbx = rdi s)
    (hrbp : t.regs.get64 .rbp = s.regs.get64 .rbp) (h12 : t.regs.get64 .r12 = s.regs.get64 .r12)
    (h13 : t.regs.get64 .r13 = s.regs.get64 .r13) (h14 : t.regs.get64 .r14 = s.regs.get64 .r14)
    (h15 : t.regs.get64 .r15 = s.regs.get64 .r15)
    (hm : t.dmem = (s.dmem.storeInt (rsp s - 8#64) 8 ra.toBitVec.toInt).storeInt (rsp s - 16#64) 8
      (s.regs.get64 .rbx).toInt) :
    Fr s ra t ∧ Mem.UnchangedOutside [frame finishF s] s.dmem t.dmem := by
  have hle := hf.le
  simp only [finishF_eq] at hle
  have i1 : Mem.Blocks.Inside (rsp s - 8#64) 8 [frame finishF s] :=
    Or.inl (by simp only [finishF_eq]; bv_omega)
  have i2 : Mem.Blocks.Inside (rsp s - 16#64) 8 [frame finishF s] :=
    Or.inl (by simp only [finishF_eq]; bv_omega)
  have u0 : Mem.UnchangedOutside [frame finishF s] s.dmem s.dmem := fun _ _ => rfl
  refine ⟨⟨hrsp, hrbx, hrbp, h12, h13, h14, h15, ?_, ?_, ?_⟩, ?_⟩ <;> rw [hm]
  · exact Mem.Contains.storeInt_self _ (rsp s - 16#64) 8 _ (by decide)
  · refine (Mem.Contains.storeInt_self _ (rsp s - 8#64) 8 _ (by decide)).storeInt_of_disjoint
      (bs₁ := [(rsp s - 16#64, 8)]) (bs₂ := [(rsp s - 8#64, 8)]) (Mem.Blocks.Inside.base (Nat.le_refl 8))
      ?_ (Mem.Blocks.Inside.base (by simp [Int.toBytes_length])) _
    intro x h1 h2
    simp only [Mem.Blocks.Inside, or_false] at h1 h2
    bv_omega
  · exact ((mapped_entry hf hw).storeInt _ _ _).storeInt _ _ _
  · exact (u0.storeInt i1 _).storeInt i2 _

-- A block in `writable` is disjoint from the frame.
theorem disj_frame (hf : FrameOk finishF s) {a : Addr} {n : Nat}
    (h : ∀ x, Mem.Blocks.Inside x 1 [(a, n)] → Mem.Blocks.Inside x 1 (writable s.dmem (rdi s))) :
    Mem.Blocks.Disjoint [(a, n)] [frame finishF s] :=
  disjoint_mono (fun x hx => inside_append.mpr (Or.inl (h x hx))) (disjoint_symm hf.disj)

-- A word of the struct header.
theorem inside_hdr {k : Nat} (hk : k < 3) :
    ∀ x, Mem.Blocks.Inside x 1 [(wordAt (rdi s) k, 8)] → Mem.Blocks.Inside x 1 (writable s.dmem (rdi s)) :=
  Kit.inside_bytes (inside_writable (Or.inl (by simp only [wordAt]; bv_omega)))

-- Blocks in the frame and `writable` do not overlap `readable`.
theorem disj_rd (hf : FrameOk finishF s) (hw : Wf s.dmem (rdi s)) (hA : finishA s)
    {l : List (Addr × Nat)}
    (h : ∀ x, Mem.Blocks.Inside x 1 l → Mem.Blocks.Inside x 1 (frame finishF s :: writable s.dmem (rdi s))) :
    Mem.Blocks.Disjoint (readable s.dmem (rdi s)) l :=
  disjoint_symm (disjoint_mono h (disjoint_symm (Pre.disj ⟨hw, hf, hA⟩)))

-- `rbx` plus an offset in the body of `permuteDestinations`.
theorem rbx_add (hfr : Fr s ra t) {c : Int64} {k : Nat} (hk : c.toInt = ((8 * k : Nat) : Int)) :
    t.regs.rbx.toBitVec + BitVec.ofInt 64 c.toInt = wordAt (rdi s) k := by
  have := hfr.hrbx
  simp only [Reg64s.get64_rbx] at this
  rw [this, hk, BitVec.ofInt_natCast]

-- The state after `movq (%rdi), %rdi` in the prologue.
theorem entry_next (hf : FrameOk finishF s) (hw : Wf s.dmem (rdi s)) {t : MachineData} {P : Prop}
    {a1 a2 a3 : Addr} (e1 : a1 = rsp s - 8#64) (e2 : a2 = rsp s - 16#64) (e3 : a3 = rdi s)
    (hrsp : rsp t = rsp s - 4128#64) (hrbx : t.regs.get64 .rbx = rdi s)
    (hrbp : t.regs.get64 .rbp = s.regs.get64 .rbp) (h12 : t.regs.get64 .r12 = s.regs.get64 .r12)
    (h13 : t.regs.get64 .r13 = s.regs.get64 .r13) (h14 : t.regs.get64 .r14 = s.regs.get64 .r14)
    (h15 : t.regs.get64 .r15 = s.regs.get64 .r15)
    (hm : t.dmem = (s.dmem.storeInt a1 8 ra.toBitVec.toInt).storeInt a2 8 (s.regs.get64 .rbx).toInt)
    (hrdi : rdi t = rd t.dmem a3) (hP : P) :
    Fr s ra t ∧ Mem.UnchangedOutside [frame finishF s] s.dmem t.dmem
      ∧ rdi t = rd s.dmem (wordAt (rdi s) 0) ∧ P := by
  subst e1 e2 e3
  obtain ⟨h1, h2⟩ := Fr.entry hf hw hrsp hrbx hrbp h12 h13 h14 h15 hm
  refine ⟨h1, h2, ?_, hP⟩
  have := rd_congr h2 (disj_frame hf (inside_hdr (k := 0) (by omega)))
  simp only [wordAt, Nat.mul_zero, BitVec.add_zero] at this
  rw [hrdi, this]
  simp [wordAt]

-- `movq (%rdi), %rdi` in the prologue reads the length.
theorem entry_val (hf : FrameOk finishF s) {a1 a2 : Addr}
    (e1 : a1 = rsp s - 8#64) (e2 : a2 = rsp s - 16#64) (x y : Int) :
    rd ((s.dmem.storeInt a1 8 x).storeInt a2 8 y) (rdi s) = rd s.dmem (wordAt (rdi s) 0) := by
  subst e1 e2
  have hle := hf.le
  simp only [finishF_eq] at hle
  have u0 : Mem.UnchangedOutside [frame finishF s] s.dmem s.dmem := fun _ _ => rfl
  have u := (u0.storeInt (Or.inl (by simp only [finishF_eq]; bv_omega) :
      Mem.Blocks.Inside (rsp s - 8#64) 8 [frame finishF s]) x).storeInt
    (Or.inl (by simp only [finishF_eq]; bv_omega) : Mem.Blocks.Inside (rsp s - 16#64) 8 [frame finishF s]) y
  have := rd_congr u (disj_frame hf (inside_hdr (k := 0) (by omega)))
  simpa [wordAt] using this


theorem len_eq {p0 : Perm} (hp0 : p0.toList = (st s).slots.map Slot.dest) :
    p0.toList.length = (rd s.dmem (wordAt (rdi s) 0)).toNat := by
  rw [hp0]; simp [stOf]

theorem get_eq {p0 : Perm} (hp0 : p0.toList = (st s).slots.map Slot.dest) {i : Nat}
    (hi : i < p0.toList.length) : p0.toList[i] = (rd s.dmem (wordAt (rdi s) (DEST + i))).toNat := by
  have hl := len_eq hp0
  simp only [hp0, stOf, List.getElem_map, List.getElem_range, slotOf]

-- `Contains` survives a change outside its bytes.
theorem contains_of_uo {l : List (Addr × Nat)} {m m' : Mem 64} {a : Addr} {bs : List UInt8}
    (h : Mem.Contains m a bs) (hu : Mem.UnchangedOutside l m m')
    (hd : Mem.Blocks.Disjoint [(a, bs.length)] l) : Mem.Contains m' a bs := fun i hi => by
  rw [hu _ (hd _ ((Mem.Blocks.Inside.base (bs := []) (Nat.le_refl _)).add_ofNat hi))]
  exact h i hi

-- The ops buffer has room for the swaps of `permute p0`.
theorem ops_room (hA : finishA s) {p0 : Perm} (hp0 : p0.toList = (st s).slots.map Slot.dest) :
    (st s).trace.length + 2 * p0.toList.length ≤ 6 * nOf s.dmem (rdi s) := by
  have h1 := hA.2
  have h3 : p0.toList.length = (st s).len := by rw [hp0]; simp [St.len]
  simp only [cap] at h1
  omega

-- A change in `writable` keeps `Fr`.
theorem Fr.of_uo (hf : FrameOk finishF s) (h : Fr s ra t) (hr : FrameRegs t t')
    {l : List (Addr × Nat)}
    (hl : ∀ x, Mem.Blocks.Inside x 1 l → Mem.Blocks.Inside x 1 (writable s.dmem (rdi s)))
    (hu : Mem.UnchangedOutside l t.dmem t'.dmem)
    (hm : Mem.Mapped (frame finishF s :: writable s.dmem (rdi s)) t'.dmem) : Fr s ra t' := by
  have hle := hf.le
  simp only [finishF_eq] at hle
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := h
  simp only [FrameRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hr
  refine ⟨e1.trans h1, e2.trans h2, e3.trans h3, e4.trans h4, e5.trans h5, e6.trans h6, e7.trans h7,
    contains_of_uo h8 hu fun x hx hx' => hf.disj x ?_ (inside_append.mpr (Or.inl (hl x hx'))),
    contains_of_uo h9 hu fun x hx hx' => hf.disj x ?_ (inside_append.mpr (Or.inl (hl x hx'))), hm⟩
  · simp only [Mem.Blocks.Inside, or_false, Int.toBytes_length, finishF_eq] at hx ⊢; bv_omega
  · simp only [Mem.Blocks.Inside, or_false, Int.toBytes_length, finishF_eq] at hx ⊢; bv_omega

theorem rd_of_contains {m : Mem 64} {a : Addr} {x : Word} (h : Mem.Contains m a (Int.toBytes 8 x.toInt)) :
    rd m a = x := by
  rw [rd, h.loadInt_eq (Int.toBytes_length _ _), Option.get!_some]
  exact BitVec.ofInt_ofBytes_toBytes 64 8 rfl x

-- `finishR` depends on `rax` and the memory.
theorem finishR_congr (hm : t'.dmem = t.dmem) (hax : rax t' = rax t) (h : finishR s t) : finishR s t' := by
  unfold finishR Res at *
  generalize finish (st s) = r at *
  rcases r with (⟨p, x⟩ | _) | a
  · exact ⟨hax.trans h.1, hm ▸ h.2.1, hm ▸ h.2.2⟩
  · exact hax.trans h
  · exact ⟨hax.trans h.1, by simp only [st', hm]; exact h.2⟩

-- The `kvcgen` form of the stores of `.LB60`.
def lb60A (m : Mem 64) (x : Addr) : Addr :=
  BitVec.ofInt 64 (m.loadInt (x + BitVec.ofInt 64 (Int64.toInt 56)) 8).get!

def lb60V (m : Mem 64) (sp : Addr) (k : Int64) : Word :=
  BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 16 (m.loadInt (sp + BitVec.ofInt 64 k.toInt) 2).get!))

def lb60M1 (m : Mem 64) (x sp : Addr) : Mem 64 :=
  m.storeInt (lb60A m x + BitVec.ofInt 64 (Int64.toInt 0)) 8 (lb60V m sp 12).toInt

def lb60Mem (m : Mem 64) (x sp : Addr) : Mem 64 :=
  (lb60M1 m x sp).storeInt (lb60A (lb60M1 m x sp) x + BitVec.ofInt 64 (Int64.toInt 8)) 8
    (lb60V (lb60M1 m x sp) sp 14).toInt


-- `finish` in terms of `permute p0`.
theorem finish_eq {p0 : Perm} {st0 : St} (hp0 : p0.toList = st0.slots.map Slot.dest) :
    finish st0 = (match permute p0 with
      | .ok L => .ok (L.foldl swapTop st0)
      | .error b => .error (.blocked b.offset b.excess)) := by
  obtain ⟨l, lt, inj⟩ := p0
  simp only at hp0
  subst hp0
  unfold finish
  rw [dite_eq_left_of_eq_true (eq_true ⟨lt, fun i hi j hj => inj i j hi hj⟩)]
  rfl

-- `Mid` from `Fr` and a change in the frame and `writable`.
theorem mid_of (hfr : Fr s ra t) {l : List (Addr × Nat)} (hu : Mem.UnchangedOutside l s.dmem t.dmem)
    (hl : ∀ x, Mem.Blocks.Inside x 1 l → Mem.Blocks.Inside x 1 (frame finishF s :: writable s.dmem (rdi s))) :
    Kit.Mid finishF s ra t.dmem :=
  ⟨rd_of_contains hfr.cra, hfr.map, uo_mono hu hl⟩

-- The count, the working stack and the ops buffer lie in `writable`.
theorem w3_sub : ∀ x, Mem.Blocks.Inside x 1 [(wordAt (rdi s) 2, 8),
    (dataOf s.dmem (rdi s), 8 * nOf s.dmem (rdi s)), (opsOf s.dmem (rdi s), 72 * nOf s.dmem (rdi s))] →
    Mem.Blocks.Inside x 1 (writable s.dmem (rdi s)) := by
  intro x hx
  rcases hx with hx | hx | hx | hx
  · exact inside_hdr (k := 2) (by decide) x (Or.inl hx)
  · exact Or.inr (Or.inr (Or.inl hx))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
  · exact hx.elim

-- The blocks that the swap loop changes.
theorem sw_sub : ∀ x, Mem.Blocks.Inside x 1 [frame finishF s, (wordAt (rdi s) 2, 8),
    (dataOf s.dmem (rdi s), 8 * nOf s.dmem (rdi s)), (opsOf s.dmem (rdi s), 72 * nOf s.dmem (rdi s))] →
    Mem.Blocks.Inside x 1 (frame finishF s :: writable s.dmem (rdi s)) :=
  fun x hx => hx.imp_right (w3_sub x)

-- The byte at `rsp s - 4112 + j` lies in the frame.
theorem inside_T (hf : FrameOk finishF s) {a : Addr} {j n : Nat} (ha : a = rsp s - 4112#64 + BitVec.ofNat 64 j)
    (hj : j + n ≤ 2048) : ∀ x, Mem.Blocks.Inside x 1 [(a, n)] → Mem.Blocks.Inside x 1 [frame finishF s] := by
  have hle := hf.le
  simp only [finishF_eq] at hle
  intro x hx
  subst ha
  simp only [Mem.Blocks.Inside, or_false, finishF_eq] at hx ⊢
  bv_omega

-- The facts of `SwHyp` at `.LB55`.
theorem lb55_hyp (hf : FrameOk finishF s) (hw : Wf s.dmem (rdi s)) (hA : finishA s) {p0 : Perm}
    (hp0 : p0.toList = (st s).slots.map Slot.dest) (hfr : Fr s ra t) {L : List Nat}
    (hL : permute p0 = .ok L) {j : Nat} (hj : j < L.length)
    (hrdx : rdx t = rsp s - 4112#64 + BitVec.ofNat 64 j) (h : SwInv s L j t) :
    SwHyp t.dmem (rdi s) (t.regs.get64 .r10) (rsi t) (rdx t) L[j]
      ∧ Mem.Mapped ((rdx t, 1) :: (writable t.dmem (rdi s) ++ readable t.dmem (rdi s))) t.dmem := by
  obtain ⟨-, h10, hsi, hc, hst, hu⟩ := h
  have hpre : Pre finishF finishA s := ⟨hw, hf, hA⟩
  have hmid := mid_of hfr hu sw_sub
  obtain ⟨-, hrd, hwr⟩ := hmid.keeps hpre
  have hn := hmid.n hpre
  have hl := len_eq hp0
  have hLb := permute_ok_bound hL
  have hroom := ops_room hA hp0
  have hlw := hw.len_le
  have hnw := hw.n_le
  simp only [MAX_N] at hnw
  have e1 := congrArg St.len hst
  have e2 := congrArg (fun x => x.trace.length) hst
  simp only [st', st, len_foldl, len_stOf] at e1
  simp only [st', st, trace_foldl, nops_stOf, List.length_take] at e2
  simp only [st, nops_stOf] at hroom
  have hlen : rd t.dmem (wordAt (rdi s) 0) = rd s.dmem (wordAt (rdi s) 0) := BitVec.eq_of_toNat_eq e1
  have hwt : Wf t.dmem (rdi s) := hmid.wf hpre (by omega) (by omega)
  have hd := permute_depth hL L[j] (List.getElem_mem hj)
  have hv : L[j] < 256 := by
    have := hLb.2 _ (List.getElem_mem hj)
    simp only [PermuteKraken.MAX_SWAP_DEPTH] at this
    omega
  have hT := inside_T hf hrdx (n := 1) (by omega)
  refine ⟨⟨hwt, by rw [h10, hlen], hsi.trans (by rw [h10]), hd.1, by omega, by rw [hn]; omega, ?_, ?_⟩,
    fun x hx => hx.elim (fun hx => hfr.map x (Or.inl ((hT x (Or.inl hx)).elim id False.elim)))
      fun hx => hwt.mapped x hx⟩
  · have hLj : L[j]! = L[j] := getElem!_pos L j hj
    rw [swD, hrdx, hc.load_byte hj (by rw [hLj]; exact hv) (by omega), Option.get!_some, hLj]
    exact zeroExtend_ofInt_byte _ hv
  · rw [hwr]
    exact fun x h1 h2 => hf.disj x (hT x h1) (inside_append.mpr (Or.inl h2))

-- One iteration of `.LB55`.
theorem lb55_step (hf : FrameOk finishF s) (hw : Wf s.dmem (rdi s)) (hA : finishA s) {p0 : Perm}
    (hp0 : p0.toList = (st s).slots.map Slot.dest) (h : FInv s ra p0 (.label ".LB55") t)
    (hr : FrameRegs t t')
    (hm : t'.dmem = swMem t.dmem (t.regs.get64 .rbx) (t.regs.get64 .r10) (rsi t) (rdx t))
    (hrdx : rdx t' = 1#64 + rdx t) (h9 : t'.regs.get64 .r9 = t.regs.get64 .r9)
    (h10 : t'.regs.get64 .r10 = t.regs.get64 .r10) (hsi : rsi t' = rsi t) :
    (rdx t' ≠ t.regs.get64 .r9 → FInv s ra p0 (.label ".LB55") t')
      ∧ (rdx t' = t.regs.get64 .r9 → rax t' = 0#64 → FInv s ra p0 (.label ".LB50") t') := by
  obtain ⟨hfr, L, hL, j, hj, hrdx0, hsw⟩ := h
  obtain ⟨H, -⟩ := lb55_hyp hf hw hA hp0 hfr hL hj hrdx0 hsw
  obtain ⟨h9', h10', hsi', hc, hst, hu⟩ := hsw
  have hle := hf.le
  simp only [finishF_eq] at hle
  have hpre : Pre finishF finishA s := ⟨hw, hf, hA⟩
  have hl := len_eq hp0
  have hLb := permute_ok_bound hL
  have hroom := ops_room hA hp0
  have hlw := hw.len_le
  have hnw := hw.n_le
  simp only [MAX_N] at hnw
  rw [hfr.hrbx] at hm
  -- The blocks of `t` and `s`.
  have hdr := hdr_congr' hu (disj_rd hf hw hA sw_sub)
  have h3 : ∀ x, Mem.Blocks.Inside x 1 [(wordAt (dataOf t.dmem (rdi s)) ((rd t.dmem (wordAt (rdi s) 0)).toNat - 1 - L[j]), 8),
      (wordAt (dataOf t.dmem (rdi s)) ((rd t.dmem (wordAt (rdi s) 0)).toNat - 1), 8),
      (opAt t.dmem (rdi s) (rd t.dmem (wordAt (rdi s) 2)).toNat, 12), (wordAt (rdi s) 2, 8)] →
      Mem.Blocks.Inside x 1 [(wordAt (rdi s) 2, 8),
        (dataOf s.dmem (rdi s), 8 * nOf s.dmem (rdi s)), (opsOf s.dmem (rdi s), 72 * nOf s.dmem (rdi s))] := by
    intro x hx
    have := H.inW3 x hx
    rwa [hdr.1, hdr.2.2.2.1, hdr.2.2.2.2.2] at this
  have hU : Mem.UnchangedOutside [(wordAt (rdi s) 2, 8),
      (dataOf s.dmem (rdi s), 8 * nOf s.dmem (rdi s)), (opsOf s.dmem (rdi s), 72 * nOf s.dmem (rdi s))]
      t.dmem t'.dmem := hm ▸ uo_mono H.uoAll h3
  have hmap : Mem.Mapped (frame finishF s :: writable s.dmem (rdi s)) t'.dmem := hm ▸ mapped_swMem hfr.map
  have hfr' : Fr s ra t' := Fr.of_uo hf hfr hr w3_sub hU hmap
  have hu' : Mem.UnchangedOutside [frame finishF s, (wordAt (rdi s) 2, 8),
      (dataOf s.dmem (rdi s), 8 * nOf s.dmem (rdi s)), (opsOf s.dmem (rdi s), 72 * nOf s.dmem (rdi s))]
      s.dmem t'.dmem := uo_trans hu (uo_mono hU fun x hx => Or.inr hx)
  have hst' : st' s t' = (L.take (j + 1)).foldl swapTop (st s) := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append,
      List.foldl_cons, List.foldl_nil, ← hst]
    simp only [st']
    rw [hm, H.st]
  have hrdx' : rdx t' = rsp s - 4112#64 + BitVec.ofNat 64 (j + 1) := by rw [hrdx, hrdx0]; bv_omega
  have hL2048 : L.length ≤ 2048 := by omega
  refine ⟨fun hne => ⟨hfr', L, hL, j + 1, ?_, hrdx', h9.trans h9', h10.trans h10', hsi.trans hsi',
    contains_of_uo hc hU ?_, hst', hu'⟩, fun he hrax => ?_⟩
  · have : j + 1 ≠ L.length := fun h => hne (by rw [hrdx', h9', h])
    omega
  · have hT := inside_T hf (a := rsp s - 4112#64) (j := 0) (n := (bytes L).length) (by simp)
      (by rw [length_bytes]; omega)
    exact fun x h1 h2 => hf.disj x (hT x h1) (inside_append.mpr (Or.inl (w3_sub x h2)))
  · have hjL : j + 1 = L.length := by rw [hrdx', h9'] at he; bv_omega
    rw [hjL, List.take_length] at hst'
    have hmid := mid_of hfr' hu' sw_sub
    have e1 := congrArg St.len hst'
    have e2 := congrArg (fun x => x.trace.length) hst'
    simp only [st', st, len_foldl, len_stOf] at e1
    simp only [st', st, trace_foldl, nops_stOf] at e2
    simp only [st, nops_stOf] at hroom
    refine ⟨hfr', hmid.wf hpre (by omega) (by omega), ?_, uo_mono hu' sw_sub⟩
    simp only [finishR, finish_eq hp0, hL, Res]
    exact ⟨hrax, hst'⟩

-- A word of `m_destinationOf` or `m_positionOf`.
theorem inside_dest {k : Nat} (hk : DEST ≤ k) (hk2 : k < WORDS) :
    ∀ x, Mem.Blocks.Inside x 1 [(wordAt (rdi s) k, 8)] → Mem.Blocks.Inside x 1 (writable s.dmem (rdi s)) :=
  Kit.inside_bytes (inside_writable (Or.inr (Or.inl (by
    simp only [wordAt, DEST_eq, WORDS_eq] at hk hk2 ⊢; bv_omega))))

-- One iteration of the copy loop `.LB52`.
theorem lb52_step (hf : FrameOk finishF s) (hw : Wf s.dmem (rdi s)) {p0 : Perm}
    (hp0 : p0.toList = (st s).slots.map Slot.dest) (hfr : Fr s ra t)
    (hu : Mem.UnchangedOutside [frame finishF s] s.dmem t.dmem) (hi : (rax t).toNat < p0.toList.length)
    (hc : Mem.Contains t.dmem (rsp s - 2064#64) (words (p0.toList.take (rax t).toNat)))
    {a b : Addr} (ea : a = wordAt (rdi s) (DEST + (rax t).toNat))
    (eb : b = rsp s - 2064#64 + BitVec.ofNat 64 (2 * (rax t).toNat))
    (hr : FrameRegs t t') (hm : t'.dmem = t.dmem.storeInt b 2 ((rd t.dmem a).take 16).toInt) :
    Fr s ra t' ∧ Mem.UnchangedOutside [frame finishF s] s.dmem t'.dmem
      ∧ Mem.Contains t'.dmem (rsp s - 2064#64) (words (p0.toList.take ((rax t).toNat + 1))) := by
  have hle := hf.le
  simp only [finishF_eq] at hle
  have hn := hw.n_le
  have hl := hw.len_le
  simp only [MAX_N] at hn
  have h1024 : (rax t).toNat < 1024 := by rw [len_eq hp0] at hi; omega
  have hin : Mem.Blocks.Inside b 2 [frame finishF s] := Or.inl (by subst eb; simp only [finishF_eq]; bv_omega)
  refine ⟨Fr.store hfr hr ?_ hm, ?_, ?_⟩
  · intro x h1 h2
    subst eb
    simp only [Mem.Blocks.Inside, or_false] at h1 h2
    bv_omega
  · rw [hm]; exact hu.storeInt hin _
  · have hv : rd t.dmem a = rd s.dmem a := by
      subst ea
      exact rd_congr hu (disj_frame hf (inside_dest (by simp only [DEST_eq]; omega)
        (by simp only [WORDS_eq, DEST_eq]; omega)))
    have hb : Int.toBytes 2 ((rd t.dmem a).take 16).toInt
        = [p0.toList[(rax t).toNat].toUInt8, (p0.toList[(rax t).toNat] / 256).toUInt8] := by
      rw [toBytes_two_take, hv, ea, get_eq hp0 hi]
    have hlen : (words (p0.toList.take (rax t).toNat)).length = 2 * (rax t).toNat := by
      simp only [length_words, List.length_take]; omega
    have := hc.append_word (by omega) ((rd t.dmem a).take 16).toInt
    rw [hlen, ← eb, ← hm, hb] at this
    rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
      show ∀ l x, words (l ++ [x]) = words l ++ [x.toUInt8, (x / 256).toUInt8] from fun l x => by simp [words]]
    exact this

-- The end of an iteration of `.LB52`: `addq $1, %rax; cmpq %rdi, %rax; jne .LB52`.
theorem lb52_next (hf : FrameOk finishF s) (hw : Wf s.dmem (rdi s)) {p0 : Perm}
    (hp0 : p0.toList = (st s).slots.map Slot.dest)
    (h : FInv s ra p0 (.label ".LB52") t)
    {a b : Addr} (ea : a = wordAt (rdi s) (DEST + (rax t).toNat))
    (eb : b = rsp s - 2064#64 + BitVec.ofNat 64 (2 * (rax t).toNat))
    (hr : FrameRegs t t') (hm : t'.dmem = t.dmem.storeInt b 2 ((rd t.dmem a).take 16).toInt)
    (hrax : rax t' = 1#64 + rax t) (hrdi : rdi t' = rdi t) :
    (rax t' ≠ rdi t → FInv s ra p0 (.label ".LB52") t')
      ∧ (rax t' = rdi t → FInv s ra p0 (.label ".LB51") t') := by
  obtain ⟨hfr, hu, hrdi0, hi, hc⟩ := h
  obtain ⟨h1, h2, h3⟩ := lb52_step hf hw hp0 hfr hu hi hc ea eb hr hm
  have hl := len_eq hp0
  have hn := hw.n_le
  have hle := hw.len_le
  simp only [MAX_N] at hn
  have hx : (rax t').toNat = (rax t).toNat + 1 := by rw [hrax]; bv_omega
  rw [← hx] at h3
  refine ⟨fun hne => ⟨h1, h2, hrdi.trans hrdi0, ?_, h3⟩, fun he => ⟨h1, h2, hrdi.trans hrdi0, ?_⟩⟩
  · have : (rax t').toNat ≠ p0.toList.length := by
      rw [hl, ← hrdi0]; exact fun h => hne (BitVec.eq_of_toNat_eq h)
    omega
  · rwa [show (rax t').toNat = p0.toList.length by rw [hl, ← hrdi0, he], List.take_length] at h3

-- `call permute` at `.LB51`, in the state `c`.
theorem lb51_call (hf : FrameOk finishF s) (hw : Wf s.dmem (rdi s)) {p0 : Perm}
    (hp0 : p0.toList = (st s).slots.map Slot.dest) (h : FInv s ra p0 (.label ".LB51") t)
    {c : MachineData} (hS : State.S c = rsp s - 4128#64) (hN : State.N c = rdi t)
    (hP : State.P c = rsp s - 2064#64) (hT : State.T c = rsp s - 4112#64)
    (hB : State.B c = rsp s - 4116#64) (hm : c.dmem = t.dmem) (hr : FrameRegs t c) :
    PermHyp c p0 ∧ ∀ u, PermPost c u → (PermMod c).Agree c u →
      Fr s ra u ∧ Mem.UnchangedOutside [frame finishF s] s.dmem u.dmem
        ∧ State.Result c p0 (rax u) u := by
  obtain ⟨hfr, hu, hrdi, hc⟩ := h
  have hle := hf.le
  simp only [finishF_eq] at hle
  have hl := len_eq hp0
  have hn := hw.n_le
  have hl1024 := hw.len_le
  simp only [MAX_N] at hn
  have hN' : (State.N c).toNat = p0.toList.length := by rw [hN, hrdi, hl]
  -- The blocks of `permute` lie in the frame, below the saved `rbx`.
  have hsub : ∀ x, Mem.Blocks.Inside x 1 (State.blocks c) → Mem.Blocks.Inside x 1 [frame finishF s] := by
    intro x hx
    simp only [Mem.Blocks.Inside, or_false, hS, hP, hT, hB, hN'] at hx
    simp only [Mem.Blocks.Inside, or_false, finishF_eq]
    rcases hx with hx | hx | hx | hx <;> bv_omega
  have hsv : Mem.Blocks.Disjoint [(rsp s - 16#64, 16)] (State.blocks c) := by
    intro x h1 h2
    simp only [Mem.Blocks.Inside, or_false, hS, hP, hT, hB, hN'] at h1 h2
    rcases h2 with h2 | h2 | h2 | h2 <;> bv_omega
  have hhyp : PermHyp c p0 := by
    refine ⟨hN'.symm, by simp only [Bbu.MAX_N]; omega, ?_, ?_, ?_, ?_⟩
    · rw [hm, hP]; exact hc
    · intro x hx; rw [hm]; exact hfr.map x (Or.inl ((hsub x hx).resolve_right id))
    · intro x h1 h2
      simp only [Mem.Blocks.Inside, or_false, hS, hP, hT, hB, hN'] at h1 h2
      rcases h1 with h1 | h1 | h1 <;> bv_omega
    · intro x h1 h2
      simp only [Mem.Blocks.Inside, or_false, hP, hT, hB, hN'] at h1 h2
      rcases h2 with h2 | h2 <;> bv_omega
  refine ⟨hhyp, fun u hpost hag => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hfr
  simp only [FrameRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hr
  have hreg : ∀ r, r ∉ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] →
      u.regs.get64 r = t.regs.get64 r := fun r hr' => (hag.1 r hr').trans (by
    cases r <;> simp_all)
  have hum : Mem.UnchangedOutside (State.blocks c) t.dmem u.dmem := hm ▸ hag.2
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [rsp, hreg .rsp (by simp)]; exact h1
  · rw [hreg .rbx (by simp)]; exact h2
  · rw [hreg .rbp (by simp)]; exact h3
  · rw [hreg .r12 (by simp)]; exact h4
  · rw [hreg .r13 (by simp)]; exact h5
  · rw [hreg .r14 (by simp)]; exact h6
  · rw [hreg .r15 (by simp)]; exact h7
  · refine contains_of_uo h8 hum (disjoint_mono (fun x hx => ?_) hsv)
    simp only [Mem.Blocks.Inside, or_false, Int.toBytes_length] at hx ⊢; bv_omega
  · refine contains_of_uo h9 hum (disjoint_mono (fun x hx => ?_) hsv)
    simp only [Mem.Blocks.Inside, or_false, Int.toBytes_length] at hx ⊢; bv_omega
  · exact Mapped.of_unchanged h10 hum hpost.1
  · exact uo_trans hu (uo_mono hum hsub)
  · exact hpost.2 p0 hhyp

-- The state after `call permute` and `testq %rax, %rax` at `.LB51`.
theorem lb51_ret (hf : FrameOk finishF s) (hw : Wf s.dmem (rdi s)) {p0 : Perm}
    (hp0 : p0.toList = (st s).slots.map Slot.dest) {u : MachineData} (hfr : Fr s ra u)
    (hu : Mem.UnchangedOutside [frame finishF s] s.dmem u.dmem) {c : MachineData}
    (hT : State.T c = rsp s - 4112#64) (hB : State.B c = rsp s - 4116#64)
    (hres : State.Result c p0 (rax u) u) (hr : FrameRegs u t) (hm : t.dmem = u.dmem) :
    ((rax u).msb = true → FInv s ra p0 (.label ".LB60") t)
      ∧ ((rax u).msb = false → rax u = 0#64 → FInv s ra p0 (.label ".LB56") t)
      ∧ ((rax u).msb = false → rax u ≠ 0#64
        → t.regs.get64 .r10 = rd u.dmem (u.regs.get64 .rbx) + -1#64
        → rsi t = (rd u.dmem (u.regs.get64 .rbx) + -1#64) * 8#64
        → rdx t = rsp u + 16#64 → t.regs.get64 .r9 = rax u + rsp u + 16#64
        → FInv s ra p0 (.label ".LB55") t) := by
  have hfr' := hfr.congr hr hm
  have hu' : Mem.UnchangedOutside [frame finishF s] s.dmem t.dmem := hm ▸ hu
  have hl := len_eq hp0
  have hlw := hw.len_le
  have hnw := hw.n_le
  simp only [MAX_N] at hnw
  have hrsp := hfr.hrsp
  rcases hp : permute p0 with b | L
  · simp only [State.Result, hp] at hres
    refine ⟨fun _ => ⟨hfr', hu', b, hp, by rw [hm, ← hB]; exact hres.2⟩, fun hs => ?_, fun hs => ?_⟩
    · rw [hres.1] at hs; exact absurd hs (by decide)
    · rw [hres.1] at hs; exact absurd hs (by decide)
  · simp only [State.Result, hp] at hres
    have hL := (permute_ok_bound hp).1
    have hc : Mem.Contains t.dmem (rsp s - 4112#64) (bytes L) := by rw [hm, ← hT]; exact hres.2
    refine ⟨fun hs => ?_, fun _ hz => ⟨hfr', hu', ?_⟩,
      fun _ hnz h10 hsi hrdx h9 => ⟨hfr', L, hp, 0, ?_, ?_, ?_⟩⟩
    · rw [hres.1, BitVec.msb_eq_toNat] at hs
      simp only [BitVec.toNat_ofNat, decide_eq_true_eq] at hs
      rw [Nat.mod_eq_of_lt (by omega)] at hs
      omega
    · have h0 : L.length = 0 := by
        have := hres.1.symm.trans hz
        bv_omega
      rw [List.eq_nil_of_length_eq_zero h0] at hp; exact hp
    · have : L.length ≠ 0 := fun h0 => hnz (by rw [hres.1, h0])
      omega
    · rw [hrdx, hrsp]; bv_omega
    · have hv : rd u.dmem (u.regs.get64 .rbx) = rd s.dmem (wordAt (rdi s) 0) := by
        rw [hfr.hrbx, ← rd_congr hu (disj_frame hf (inside_hdr (k := 0) (by omega)))]
        simp [wordAt]
      refine ⟨?_, ?_, ?_, hc, ?_, uo_mono hu' fun x hx => hx.imp_right False.elim⟩
      · rw [h9, hres.1, hrsp]; bv_omega
      · rw [h10, hv, BitVec.sub_eq_add_neg]
      · rw [hsi, hv, BitVec.sub_eq_add_neg]
      · simp only [List.take_zero, List.foldl_nil]
        exact stOf_congr hu' hw (disjoint_symm hf.disj)

-- `.LB56`: `permute` gives no swap; return 0.
theorem lb56_done (hf : FrameOk finishF s) (hw : Wf s.dmem (rdi s)) (hA : finishA s) {p0 : Perm}
    (hp0 : p0.toList = (st s).slots.map Slot.dest) (h : FInv s ra p0 (.label ".LB56") t)
    (hr : FrameRegs t t') (hm : t'.dmem = t.dmem) (hrax : rax t' = 0#64) :
    FInv s ra p0 (.label ".LB50") t' := by
  obtain ⟨hfr, hu, hL⟩ := h
  have hfr' := hfr.congr hr hm
  have hu' : Mem.UnchangedOutside [frame finishF s] s.dmem t'.dmem := hm ▸ hu
  have hsub : ∀ x, Mem.Blocks.Inside x 1 [frame finishF s] →
      Mem.Blocks.Inside x 1 (frame finishF s :: writable s.dmem (rdi s)) :=
    fun x hx => hx.imp_right False.elim
  have hst : st' s t' = st s := stOf_congr hu' hw (disjoint_symm hf.disj)
  have e1 := congrArg St.len hst
  have e2 := congrArg (fun x => x.trace.length) hst
  simp only [st', st, len_stOf] at e1
  simp only [st', st, nops_stOf] at e2
  have hlw := hw.len_le
  have hnw := hw.nops_le
  refine ⟨hfr', (mid_of hfr' hu' hsub).wf ⟨hw, hf, hA⟩ (by omega) (by omega), ?_, uo_mono hu' hsub⟩
  simp only [finishR, finish_eq hp0, hL, Res, List.foldl_nil]
  exact ⟨hrax, hst⟩

-- `.LB60` reads the pointer to `blocked` from word 7 of the struct.
theorem lb60_blk (hf : FrameOk finishF s) (hw : Wf s.dmem (rdi s)) (hA : finishA s) (hfr : Fr s ra t)
    (hu : Mem.UnchangedOutside [frame finishF s] s.dmem t.dmem) :
    lb60A t.dmem t.regs.rbx.toBitVec = blkOf s.dmem (rdi s)
      ∧ ∀ v : Int, lb60A (t.dmem.storeInt (blkOf s.dmem (rdi s)) 8 v) t.regs.rbx.toBitVec
        = blkOf s.dmem (rdi s) := by
  have hB : rd t.dmem (wordAt (rdi s) 7) = blkOf s.dmem (rdi s) :=
    hdr_congr hu (disj_rd hf hw hA fun x hx => hx.imp_right False.elim) (k := 7) (by decide) (by decide)
  simp only [lb60A, rbx_add hfr (c := 56) (k := 7) (by decide), ← rd.eq_1]
  refine ⟨hB, fun v => ?_⟩
  rw [rd_storeInt_of_disjoint fun x h1 h2 => hw.blk_disj (k := 7) (by decide) x h2 (by
    simp only [Mem.Blocks.Inside, or_false] at h1 ⊢; bv_omega)]
  exact hB

-- `.LB60`: `permute` is blocked; write `blocked` and return -1.
theorem lb60_next (hf : FrameOk finishF s) (hw : Wf s.dmem (rdi s)) (hA : finishA s) {p0 : Perm}
    (hp0 : p0.toList = (st s).slots.map Slot.dest) (h : FInv s ra p0 (.label ".LB60") t)
    (hr : FrameRegs t t') (hm : t'.dmem = lb60Mem t.dmem t.regs.rbx.toBitVec t.regs.rsp.toBitVec)
    (hrax : rax t' = -1#64) :
    FInv s ra p0 (.label ".LB50") t' := by
  obtain ⟨hfr, hu, b, hb, hc⟩ := h
  have hrsp : t.regs.rsp.toBitVec = rsp s - 4128#64 := by simpa [rsp] using hfr.hrsp
  have hsl := hw.struct_lt
  simp only [WORDS_eq] at hsl
  have hbl := hw.blk_lt
  have hle := hf.le
  simp only [finishF_eq] at hle
  have hlt := permute_err_bound hb
  have hlen := len_eq hp0
  have hwl := hw.len_le
  have hnw := hw.n_le
  simp only [MAX_N] at hnw
  -- The words of `b`.
  have hv : ∀ (m : Mem 64) (i : Nat) (k : Int64) (v : Nat),
      Mem.Contains m (rsp s - 4116#64) (words [b.offset, b.excess]) → i < 2 → k.toInt = 12 + 2 * i →
      [b.offset, b.excess][i]! = v → lb60V m t.regs.rsp.toBitVec k = BitVec.ofNat 64 v := by
    intro m i k v hc hi hk hv
    have hl : [b.offset, b.excess][i]! < 65536 := by
      rcases i with _ | _ | _ <;> simp at hi ⊢ <;> omega
    simp only [lb60V]
    rw [hk, show t.regs.rsp.toBitVec + BitVec.ofInt 64 (12 + 2 * (i : Int))
      = rsp s - 4116#64 + BitVec.ofNat 64 (2 * i) by rw [hrsp]; bv_omega,
      hc.load_word (by simp; omega) hl, Option.get!_some, ← hv]
    exact zeroExtend_ofInt_word _ hl
  have hv12 := hv _ 0 12 b.offset hc (by omega) (by decide) rfl
  -- `blocked`.
  obtain ⟨hA0, hA1⟩ := lb60_blk hf hw hA hfr hu
  have hM1 : lb60M1 t.dmem t.regs.rbx.toBitVec t.regs.rsp.toBitVec
      = t.dmem.storeInt (blkOf s.dmem (rdi s)) 8 (BitVec.ofNat 64 b.offset).toInt := by
    simp only [lb60M1]
    rw [hA0, hv12]
    simp
  -- The store to `blocked[0]` keeps the words of `b` in the frame.
  have hc1 : Mem.Contains (t.dmem.storeInt (blkOf s.dmem (rdi s)) 8 (BitVec.ofNat 64 b.offset).toInt)
      (rsp s - 4116#64) (words [b.offset, b.excess]) :=
    contains_of_uo hc (Mem.UnchangedOutside.storeInt (fun _ _ => rfl)
      (Mem.Blocks.Inside.base (bs := []) (Nat.le_refl 8)) _) fun x h2 h1 => hf.disj x (Or.inl (by
        simp only [Mem.Blocks.Inside, or_false, PermuteKraken.length_words, List.length_cons,
          List.length_nil, finishF_eq] at h2 ⊢; bv_omega))
      (inside_append.mpr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
        simp only [Mem.Blocks.Inside, or_false] at h1; bv_omega))))))))
  have hv14 := hv _ 1 14 b.excess hc1 (by omega) (by decide) rfl
  have hm' : t'.dmem = (t.dmem.storeInt (blkOf s.dmem (rdi s)) 8 (BitVec.ofNat 64 b.offset).toInt).storeInt
      (blkOf s.dmem (rdi s) + 8#64) 8 (BitVec.ofNat 64 b.excess).toInt := by
    rw [hm, lb60Mem, hM1, hA1, hv14]
    simp
  -- The memory that `.LB60` writes.
  have hU2 : Mem.UnchangedOutside [(blkOf s.dmem (rdi s), 8), (blkOf s.dmem (rdi s) + 8#64, 8)]
      t.dmem t'.dmem := by
    rw [hm']
    exact Mem.UnchangedOutside.storeInt (Mem.UnchangedOutside.storeInt (fun _ _ => rfl)
      (Mem.Blocks.Inside.base (Nat.le_refl 8)) _) (Mem.Blocks.Inside.base (Nat.le_refl 8)).tail _
  have hWl : ∀ x, Mem.Blocks.Inside x 1 [(blkOf s.dmem (rdi s), 8), (blkOf s.dmem (rdi s) + 8#64, 8)] →
      Mem.Blocks.Inside x 1 (writable s.dmem (rdi s)) := by
    intro x hx
    rcases hx with hx | hx | hx
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by bv_omega)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by bv_omega)))))
    · exact hx.elim
  have hmB : Mem.Mapped [(blkOf s.dmem (rdi s), 8)] t.dmem := fun x hx =>
    hfr.map x (Or.inr (hWl x (Or.inl (by simp only [Mem.Blocks.Inside, or_false] at hx; bv_omega))))
  have hmB8 : Mem.Mapped [(blkOf s.dmem (rdi s) + 8#64, 8)] t.dmem := fun x hx =>
    hfr.map x (Or.inr (hWl x (Or.inr (Or.inl (by simp only [Mem.Blocks.Inside, or_false] at hx; bv_omega)))))
  have hmap' : Mem.Mapped (frame finishF s :: writable s.dmem (rdi s)) t'.dmem := by
    rw [hm']; exact (hfr.map.storeInt _ _ _).storeInt _ _ _
  have hfr' : Fr s ra t' := Fr.of_uo hf hfr hr hWl hU2 hmap'
  have hUs : Mem.UnchangedOutside [frame finishF s, (blkOf s.dmem (rdi s), 16)] s.dmem t'.dmem := by
    refine uo_trans (uo_mono hu fun x hx => hx.imp_right False.elim) (uo_mono hU2 fun x hx => ?_)
    rcases hx with hx | hx | hx
    · exact Or.inr (Or.inl (by bv_omega))
    · exact Or.inr (Or.inl (by bv_omega))
    · exact hx.elim
  have hdl : Mem.Blocks.Disjoint (readable s.dmem (rdi s)) [frame finishF s, (blkOf s.dmem (rdi s), 16)] :=
    disj_rd hf hw hA fun x hx => hx.imp_right fun hx =>
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hx.resolve_right id)))))
  have hdw : ∀ k, k < 3 → Mem.Blocks.Disjoint [(wordAt (rdi s) k, 8)]
      [frame finishF s, (blkOf s.dmem (rdi s), 16)] := fun k hk x h1 h2 => h2.elim
    (fun h => disj_frame hf (inside_hdr hk) x h1 (Or.inl h))
    fun h => hw.blk_disj (by simp only [WORDS_eq]; omega) x h1 h
  have hwt : Wf t'.dmem (rdi s) :=
    Wf.congr hUs hw hdl (fun x hx => hmap' x (Or.inr hx))
      (by rw [rd_congr hUs (hdw 0 (by omega))]; exact hw.len_le)
      (by rw [rd_congr hUs (hdw 2 (by omega))]; exact hw.nops_le)
  have hB' : blkOf t'.dmem (rdi s) = blkOf s.dmem (rdi s) := hdr_congr hUs hdl (k := 7) (by omega) (by omega)
  refine ⟨hfr', hwt, ?_, uo_mono hUs fun x hx => ?_⟩
  · simp only [finishR, finish_eq hp0, hb, Res]
    refine ⟨hrax, ?_, ?_⟩
    · rw [hB', hm', rd_storeInt_of_disjoint (fun x h1 h2 => by
        simp only [Mem.Blocks.Inside, or_false] at h1 h2; bv_omega)]
      exact rd_storeInt_self _ hmB
    · rw [hB', hm', show wordAt (blkOf s.dmem (rdi s)) 1 = blkOf s.dmem (rdi s) + 8#64 by simp [wordAt]]
      exact rd_storeInt_self _ (hmB8.storeInt _ _ _)
  · rcases hx with hx | hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx)))))
    · exact hx.elim

-- The loads of `.LB60` succeed.
theorem lb60_some (hf : FrameOk finishF s) (hw : Wf s.dmem (rdi s)) (hA : finishA s) {p0 : Perm}
    (h : FInv s ra p0 (.label ".LB60") t) :
    (t.dmem.loadInt (t.regs.rbx.toBitVec + BitVec.ofInt 64 (Int64.toInt 56)) 8).isSome
      ∧ (t.dmem.loadInt (t.regs.rsp.toBitVec + BitVec.ofInt 64 (Int64.toInt 12)) 2).isSome
      ∧ (t.dmem.loadInt (lb60A t.dmem t.regs.rbx.toBitVec + BitVec.ofInt 64 (Int64.toInt 0)) 8).isSome
      ∧ ((lb60M1 t.dmem t.regs.rbx.toBitVec t.regs.rsp.toBitVec).loadInt
          (t.regs.rbx.toBitVec + BitVec.ofInt 64 (Int64.toInt 56)) 8).isSome
      ∧ ((lb60M1 t.dmem t.regs.rbx.toBitVec t.regs.rsp.toBitVec).loadInt
          (t.regs.rsp.toBitVec + BitVec.ofInt 64 (Int64.toInt 14)) 2).isSome
      ∧ ((lb60M1 t.dmem t.regs.rbx.toBitVec t.regs.rsp.toBitVec).loadInt
          (lb60A (lb60M1 t.dmem t.regs.rbx.toBitVec t.regs.rsp.toBitVec) t.regs.rbx.toBitVec
            + BitVec.ofInt 64 (Int64.toInt 8)) 8).isSome := by
  obtain ⟨hfr, hu, -⟩ := h
  have hrsp : t.regs.rsp.toBitVec = rsp s - 4128#64 := by simpa [rsp] using hfr.hrsp
  have hsl := hw.struct_lt
  simp only [WORDS_eq] at hsl
  have hbl := hw.blk_lt
  have hle := hf.le
  simp only [finishF_eq] at hle
  obtain ⟨hA0, hA1⟩ := lb60_blk hf hw hA hfr hu
  have hA0' : lb60A t.dmem t.regs.rbx.toBitVec + BitVec.ofInt 64 (Int64.toInt 0) = blkOf s.dmem (rdi s) := by
    rw [hA0]; simp
  have hA1' : lb60A (lb60M1 t.dmem t.regs.rbx.toBitVec t.regs.rsp.toBitVec) t.regs.rbx.toBitVec
      = blkOf s.dmem (rdi s) := by
    rw [lb60M1, hA0']; exact hA1 _
  have hmapT : Mem.Mapped (writable s.dmem (rdi s) ++ readable s.dmem (rdi s)) t.dmem :=
    Mapped.of_unchanged hw.mapped hu fun x hx => hfr.map x (hx.imp_right False.elim)
  have hM1 : Mem.Mapped (writable s.dmem (rdi s) ++ readable s.dmem (rdi s))
      (lb60M1 t.dmem t.regs.rbx.toBitVec t.regs.rsp.toBitVec) := hmapT.storeInt _ _ _
  have e56 := rbx_add hfr (c := 56) (k := 7) (by decide)
  refine ⟨?_, hfr.map.loadInt_isSome (Or.inl ?_), ?_, ?_,
    (hfr.map.storeInt _ _ _).loadInt_isSome (Or.inl ?_), ?_⟩
  · rw [e56]; exact hw.word_isSome hmapT (by decide)
  · simp only [finishF_eq, Int64.reduceToInt, BitVec.ofInt_ofNat]; rw [hrsp]; bv_omega
  · rw [hA0']; simpa [wordAt] using hw.blk_isSome hmapT (k := 0) (by decide)
  · rw [e56]; exact hw.word_isSome hM1 (by decide)
  · simp only [finishF_eq, Int64.reduceToInt, BitVec.ofInt_ofNat]; rw [hrsp]; bv_omega
  · rw [hA1']; simpa [wordAt] using hw.blk_isSome hM1 (k := 1) (by decide)

end
end FinishProof

open FinishProof in
theorem finish_body [Host] [FunDecls] (hperm : Program.WP.CallSpec "permute" PermPre PermPost PermMod) :
    Body finishAsm finishF finishA finishR := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨p0, hp0⟩ : ∃ p : Perm, p.toList = (st s).slots.map Slot.dest :=
    ⟨⟨_, hpre.2.2.1.1, fun i j hi hj => hpre.2.2.1.2 i hi j hj⟩, rfl⟩
  obtain ⟨hw, hf, hA⟩ := hpre
  have hle := hf.le
  simp only [finishF_eq] at hle
  refine Program.WP.cfg (FInv s ra p0) (FVar s) ?_ rfl
  cfg_cases
  case right.right.right.right.left t ht =>
    have ht0 := ht
    simp only [FInv] at ht
    obtain ⟨hfr, L, hL, j, hj, hrdx, hsw⟩ := ht
    have hrsp := hfr.hrsp
    have hL2 : L.length ≤ 2048 := by
      have := (permute_ok_bound hL).1; have := len_eq hp0; have := hw.len_le; have := hw.n_le
      simp only [MAX_N] at *; omega
    obtain ⟨H, hmap⟩ := lb55_hyp hf hw hA hp0 hfr hL hj hrdx hsw
    have hx : t.regs.rbx.toBitVec = rdi s := hfr.hrbx
    rw [← hx] at H hmap
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ := H.some hmap
    kvcgen64
    all_goals (try bbu_norm)
    case vc1 => exact c1
    case vc2 => exact c2
    case vc3 => exact c3
    case vc4 => exact c4
    case vc5 => exact c5
    case vc6 => exact c6
    case vc7 => exact c7
    case vc8 => (repeat apply loadInt_isSome_store); exact c1
    case vc9 => (repeat apply loadInt_isSome_store); exact c8
    case vc10 => (repeat apply loadInt_isSome_store); exact c9
    case vc11 => (repeat apply loadInt_isSome_store); exact c10
    case vc12 => (repeat apply loadInt_isSome_store); exact c2
    case vc13 => (repeat apply loadInt_isSome_store); exact c11
    case vc14 => (repeat apply loadInt_isSome_store); exact c12
    case vc15 => (repeat apply loadInt_isSome_store); exact c13
    case vc16 => (repeat apply loadInt_isSome_store); exact c14
    case vc17 => (repeat apply loadInt_isSome_store); exact c15
    case vc18 => (repeat apply loadInt_isSome_store); exact c16
    case vc19 => (repeat apply loadInt_isSome_store); exact c17
    case vc20 => (repeat apply loadInt_isSome_store); exact c11
    case vc21 =>
      rename_i hz
      have hne : ¬ (1#64 + t.regs.rdx.toBitVec = t.regs.r9.toBitVec) := by
        simp [CondCode.interp_nz, StatusFlags.zf_from_result] at hz
        bv_omega
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [MachineData.pushRa, Reg64s.get64_rsp, Reg64s.set64_rsp] at *
        bvo
      · refine (lb55_step hf hw hA hp0 ht0 ?_ ?_ ?_ ?_ ?_ ?_).1 hne
        · exact frameRegs_of rfl rfl rfl rfl rfl rfl rfl
        all_goals rfl
      · simp only [FVar]
        left
        show 2100 - (1#64 + rdx t - (rsp s - 4112#64)).toNat < 2100 - (rdx t - (rsp s - 4112#64)).toNat
        have e1 : (1#64 + rdx t - (rsp s - 4112#64)).toNat = j + 1 := by
          simp only [rdx, rsp] at hrdx ⊢; rw [hrdx]; bv_omega
        have e2 : (rdx t - (rsp s - 4112#64)).toNat = j := by
          simp only [rdx, rsp] at hrdx ⊢; rw [hrdx]; bv_omega
        omega
    case vc22 =>
      rename_i hz
      have he : 1#64 + t.regs.rdx.toBitVec = t.regs.r9.toBitVec := by
        simp [CondCode.interp_nz, StatusFlags.zf_from_result] at hz
        bv_omega
      refine (lb55_step hf hw hA hp0 ht0 ?_ ?_ ?_ ?_ ?_ ?_).2 he rfl
      · exact frameRegs_of rfl rfl rfl rfl rfl rfl rfl
      all_goals rfl
    case vc23 =>
      have e2 : (rdx t - (rsp s - 4112#64)).toNat = j := by
        simp only [rdx, rsp] at hrdx ⊢; rw [hrdx]; bv_omega
      simp only [FVar]
      left
      show 0 < 2100 - (rdx t - (rsp s - 4112#64)).toNat
      omega
  case left t ht =>
    simp only [FInv] at ht
    subst ht
    kvcgen64
    exact rfl
  case right.left t ht =>
    simp only [FInv] at ht
    have hrsp : t.regs.get64 .rsp = rsp s - 8#64 := by subst ht; simp [MachineData.pushRa]
    have hdm : t.dmem = s.dmem.storeInt (rsp s - 8#64) 8 ra.toBitVec.toInt := by
      subst ht; simp [MachineData.pushRa]
    have hregs : ∀ r ∈ [Reg64.rbx, .rbp, .rdi, .r12, .r13, .r14, .r15], t.regs.get64 r = s.regs.get64 r := by
      subst ht; simp [MachineData.pushRa]
    clear ht hperm
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Reg64s.get64_rbx, Reg64s.get64_rbp, Reg64s.get64_rdi, Reg64s.get64_r12, Reg64s.get64_r13,
      Reg64s.get64_r14, Reg64s.get64_r15] at hregs
    simp only [Reg64s.get64_rsp] at hrsp
    obtain ⟨hrbx, hrbp, hrdi, h12, h13, h14, h15⟩ := hregs
    have hmap0 := mapped_entry hf hw
    have hsl := hw.struct_lt
    simp only [WORDS_eq] at hsl
    have hlen := len_eq hp0
    have hv : rd (Mem.storeInt t.dmem (t.regs.rsp.toBitVec - 8#64) 8 t.regs.rbx.toBitVec.toInt)
        t.regs.rdi.toBitVec = rd s.dmem (wordAt (rdi s) 0) := by
      rw [hdm, hrdi]; exact entry_val hf rfl (by bvo) _ _
    kvcgen64
    · rw [hdm]
      exact (hmap0.storeInt _ _ _).loadInt_isSome (Or.inl (by bvo))
    · dsimp only; rw [hdm]
      refine Mem.Mapped.loadInt_isSome (((hmap0.storeInt _ _ _).storeInt _ _ _)) ?_
      exact Or.inr (Or.inl (by bvo))
    · rename_i hz
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [MachineData.pushRa, Reg64s.get64_rsp, Reg64s.set64_rsp] at *
        bvo
      · refine entry_next hf hw (a3 := t.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 0))
          rfl ?e2 ?e3 (by bvo) (by simp [hrdi]) (by simp [hrbp])
          (by simp [h12]) (by simp [h13]) (by simp [h14]) (by simp [h15])
          (by dsimp only; rw [hdm, hrbx]; rfl) rfl ?_
        case e2 => bvo
        case e3 => bvo
        simp [CondCode.interp_z, StatusFlags.zf_from_result] at hz
        have hz' : rd _ _ = 0#64 := hz
        rw [hv] at hz'
        rw [hz'] at hlen
        have : p0.toList = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
        rw [this]
        intro i hi
        simp [words] at hi
      · simp [FVar]
    · rename_i hz
      simp [CondCode.interp_z, StatusFlags.zf_from_result] at hz
      have hz' : ¬ rd _ _ = 0#64 := hz
      rw [hv] at hz'
      refine entry_next hf hw (a3 := t.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 0))
          rfl ?e2 ?e3 (by bvo) (by simp [hrdi]) (by simp [hrbp])
          (by simp [h12]) (by simp [h13]) (by simp [h14]) (by simp [h15])
          (by dsimp only; rw [hdm, hrbx]; rfl) rfl ⟨?_, ?_⟩
      case e2 => bvo
      case e3 => bvo
      · simp only [rax, Reg64s.get64_rax, BitVec.toNat_ofNat]
        rw [hlen]
        have : (rd s.dmem (wordAt (rdi s) 0)).toNat ≠ 0 := fun h => hz' (BitVec.eq_of_toNat_eq h)
        simp only [wordAt, rdi] at this
        omega
      · intro i hi
        simp [words] at hi
    · simp [FVar]
  case right.right.left t ht =>
    have ht0 := ht
    simp only [FInv] at ht
    obtain ⟨hfr, hu, hrdi, hi, hc⟩ := ht
    have hrbx := hfr.hrbx
    have hrsp := hfr.hrsp
    have hsl := hw.struct_lt
    simp only [WORDS_eq] at hsl
    have h1024 : (rax t).toNat < 1024 := by
      have := hw.len_le; have := hw.n_le; rw [len_eq hp0] at hi; simp only [MAX_N] at *; omega
    kvcgen64
    · exact hfr.map.loadInt_isSome (Or.inr (Or.inr (Or.inl (by simp only [DEST_eq, MAX_N]; bvo))))
    · exact hfr.map.loadInt_isSome (Or.inl (by bvo))
    · rename_i hz
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [MachineData.pushRa, Reg64s.get64_rsp, Reg64s.set64_rsp] at *
        bvo
      · refine (lb52_next hf hw hp0 ht0
          (a := t.regs.rbx.toBitVec + t.regs.rax.toBitVec * 8#64 + BitVec.ofInt 64 (Int64.toInt 72))
          (b := t.regs.rsp.toBitVec + t.regs.rax.toBitVec * 2#64 + BitVec.ofInt 64 (Int64.toInt 2064))
          ?_ ?_ ?_ ?_ ?_ ?_).1 ?_
        · simp only [DEST_eq]; bvo
        · bvo
        · exact frameRegs_of rfl rfl rfl rfl rfl rfl rfl
        · rfl
        · rfl
        · rfl
        · simp [CondCode.interp_nz, StatusFlags.zf_from_result] at hz
          bvo
      · simp only [FVar]
        left
        bvo
    · rename_i hz
      refine (lb52_next hf hw hp0 ht0
          (a := t.regs.rbx.toBitVec + t.regs.rax.toBitVec * 8#64 + BitVec.ofInt 64 (Int64.toInt 72))
          (b := t.regs.rsp.toBitVec + t.regs.rax.toBitVec * 2#64 + BitVec.ofInt 64 (Int64.toInt 2064))
          ?_ ?_ ?_ ?_ ?_ ?_).2 ?_
      · simp only [DEST_eq]; bvo
      · bvo
      · exact frameRegs_of rfl rfl rfl rfl rfl rfl rfl
      · rfl
      · rfl
      · rfl
      · simp [StatusFlags.zf_from_result] at hz
        bvo
    · simp [FVar]; bvo
  case right.right.right.left t ht =>
    have ht0 := ht
    simp only [FInv] at ht
    obtain ⟨hfr, hu, hrdi, hc⟩ := ht
    have hrsp := hfr.hrsp
    kvcgen64
    · exact hfr.map.loadInt_isSome (Or.inl (by bvo))
    · refine ⟨p0, (lb51_call hf hw hp0 ht0 ?_ ?_ ?_ ?_ ?_ ?_ ?_).1⟩
      · bvo
      · rfl
      · bvo
      · bvo
      · bvo
      · rfl
      · exact frameRegs_of rfl rfl rfl rfl rfl rfl rfl
    · rename_i u hpost hag af hs
      refine (fun hcall => ?_) ((lb51_call hf hw hp0 ht0 ?_ ?_ ?_ ?_ ?_ ?_
        ?_).2 u hpost hag)
      rotate_left 1
      · bvo
      · rfl
      · bvo
      · bvo
      · bvo
      · rfl
      · exact frameRegs_of rfl rfl rfl rfl rfl rfl rfl
      obtain ⟨hfr', hu', hres⟩ := hcall
      simp only [CondCode.interp, StatusFlags.from_result, BitVec.and_self] at hs
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        have := hfr'.hrsp
        simp only [MachineData.pushRa, Reg64s.get64_rsp, Reg64s.set64_rsp] at *
        bvo
      · refine (lb51_ret hf hw hp0 hfr' hu' ?_ ?_ hres ?_ ?_).1 hs
        · bvo
        · bvo
        · exact frameRegs_of rfl rfl rfl rfl rfl rfl rfl
        · rfl
      · simp [FVar]
    · rename_i u hpost hag af hs hz
      refine (fun hcall => ?_) ((lb51_call hf hw hp0 ht0 ?_ ?_ ?_ ?_ ?_ ?_
        ?_).2 u hpost hag)
      rotate_left 1
      · bvo
      · rfl
      · bvo
      · bvo
      · bvo
      · rfl
      · exact frameRegs_of rfl rfl rfl rfl rfl rfl rfl
      obtain ⟨hfr', hu', hres⟩ := hcall
      simp only [CondCode.interp, StatusFlags.from_result, BitVec.and_self] at hs hz
      have := hfr'.hrsp
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [MachineData.pushRa, Reg64s.get64_rsp, Reg64s.set64_rsp] at *
        bvo
      · refine (lb51_ret hf hw hp0 hfr' hu' ?_ ?_ hres ?_ ?_).2.1 hs ?_
        · bvo
        · bvo
        · exact frameRegs_of rfl rfl rfl rfl rfl rfl rfl
        · rfl
        · simpa [hs] using hz
      · simp [FVar]
    · rename_i u hpost hag af hs hz
      refine (fun hcall => ?_) ((lb51_call hf hw hp0 ht0 ?_ ?_ ?_ ?_ ?_ ?_
        ?_).2 u hpost hag)
      rotate_left 1
      · bvo
      · rfl
      · bvo
      · bvo
      · bvo
      · rfl
      · exact frameRegs_of rfl rfl rfl rfl rfl rfl rfl
      obtain ⟨hfr', -, -⟩ := hcall
      have h0 := hfr'.hrbx
      refine hfr'.map.loadInt_isSome (Or.inr (Or.inl ?_))
      simp only [Reg64s.get64_rbx] at h0 ⊢
      simp only [h0]
      bvo
    · rename_i u hpost hag af hs hz
      refine (fun hcall => ?_) ((lb51_call hf hw hp0 ht0 ?_ ?_ ?_ ?_ ?_ ?_
        ?_).2 u hpost hag)
      rotate_left 1
      · bvo
      · rfl
      · bvo
      · bvo
      · bvo
      · rfl
      · exact frameRegs_of rfl rfl rfl rfl rfl rfl rfl
      obtain ⟨hfr', hu', hres⟩ := hcall
      simp only [CondCode.interp, StatusFlags.from_result, BitVec.and_self] at hs hz
      refine (lb51_ret hf hw hp0 hfr' hu' ?_ ?_ hres ?_ ?_).2.2 hs ?_ ?_ ?_ ?_ ?_
      · bvo
      · bvo
      · exact frameRegs_of rfl rfl rfl rfl rfl rfl rfl
      · rfl
      · simpa [hs] using hz
      all_goals (simp only [rd, rsi, rdx, rax, rsp, Reg64s.get64_r10, Reg64s.get64_r9, Reg64s.get64_rbx, Reg64s.get64_rsi, Reg64s.get64_rdx, Reg64s.get64_rax, Reg64s.get64_rsp, Int64.reduceToInt, BitVec.ofInt_ofNat, BitVec.add_zero]) <;> rw [show BitVec.ofInt 64 (-1) = -1#64 by decide]
    · simp only [FVar]
      left
      omega
  case right.right.right.right.right.left t ht =>
    simp only [FInv] at ht
    obtain ⟨hfr, hwt, hR, hu⟩ := ht
    have hrsp := hfr.hrsp
    have hmid : Kit.Mid finishF s ra t.dmem := ⟨rd_of_contains hfr.cra, hfr.map, hu⟩
    have hcbx := rd_of_contains hfr.cbx
    kvcgen64
    · exact hfr.map.loadInt_isSome (Or.inl (by simp only [finishF_eq]; bvo))
    · refine Option.isSome_iff_exists.mpr ⟨ra, Kit.Mid.retAddr (by decide) ⟨hw, hf, hA⟩ hmid ?_⟩
      simp [rsp]
      bvo
    · refine Kit.Mid.ret (by decide) ⟨hw, hf, hA⟩ hmid ?_ rfl ?_ ?_ hwt (finishR_congr rfl rfl hR)
      · simp [rsp]
        bvo
      · simp [rsp]
        bvo
      · intro q hq
        cases q <;> simp at hq ⊢
        · rw [show 4112#64 + t.regs.rsp.toBitVec = rsp s - 16#64 by simp at hrsp; bvo]
          exact hcbx
        · exact hfr.hrbp
        · exact hfr.h12
        · exact hfr.h13
        · exact hfr.h14
        · exact hfr.h15
  case right.right.right.right.right.right.left t ht =>
    have ht0 := ht
    simp only [FInv] at ht
    obtain ⟨hfr, -⟩ := ht
    have hrsp := hfr.hrsp
    obtain ⟨s1, s2, s3, s4, s5, s6⟩ := lb60_some hf hw hA ht0
    kvcgen64
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
    · exact s6
    · cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [MachineData.pushRa, Reg64s.get64_rsp, Reg64s.set64_rsp] at *
        bvo
      · exact lb60_next hf hw hA hp0 ht0 (frameRegs_of rfl rfl rfl rfl rfl rfl rfl) rfl rfl
      · simp [FVar]
  case _ t ht =>
    have hrsp := ht.1.hrsp
    kvcgen64
    cfg_goto
    · apply MachineData.stackAtOrBelow_of_toNat_lt
      simp only [MachineData.pushRa, Reg64s.get64_rsp, Reg64s.set64_rsp] at *
      bvo
    · exact lb56_done hf hw hA hp0 ht (frameRegs_of rfl rfl rfl rfl rfl rfl rfl) rfl rfl
    · simp [FVar]

end Bbu
