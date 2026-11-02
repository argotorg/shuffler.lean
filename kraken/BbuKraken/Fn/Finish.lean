module

public import BbuKraken.Contracts
import all BbuKraken.Contracts
public import ProofKit.Memory
import all ProofKit.Memory
public import BbuKraken.Kit
import all BbuKraken.Kit
public import BbuKraken.Fn.FinishMem
import all BbuKraken.Fn.FinishMem

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open Bbu.Permutation

set_option experimental.vcgen true

namespace Bbu

open FinishMem

/-! ## Bounds of `permute` -/

theorem target_lt (q : Perm) {pos : Nat} (h : Bbu.Permutation.target q.toList = some pos) : pos < q.toList.length := by
  unfold Bbu.Permutation.target at h
  dsimp only at h
  split at h
  · cases h
    exact q.getElem!_lt (by
      rcases Nat.eq_zero_or_pos q.toList.length with h0 | h0
      · rename_i hne; simp [h0] at hne
      · omega)
  · exact (lastMisplaced_spec _ _ _ h).1

theorem step_blocked_lt (q : Perm) {b : Blocked} (h : Bbu.Permutation.step q.toList = .blocked b) :
    b.offset < q.toList.length ∧ b.excess < q.toList.length := by
  unfold Bbu.Permutation.step at h
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

theorem trace_le (p : Perm) : ∀ k ≤ steps p, ∀ x ∈ p.trace k, x ≤ Bbu.Permutation.MAX_SWAP_DEPTH := by
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
      exact (Bbu.Permutation.step_swap hs).2.1

theorem permute_ok_bound {p : Perm} {L : List Nat} (h : Bbu.Permutation.permute p = .ok L) :
    L.length ≤ 2 * p.toList.length ∧ ∀ x ∈ L, x ≤ Bbu.Permutation.MAX_SWAP_DEPTH := by
  rw [Perm.permute_eq] at h
  split at h
  · cases h
  · cases h
    refine ⟨?_, trace_le p _ (Nat.le_refl _)⟩
    rw [Perm.length_trace]
    rcases Nat.eq_zero_or_pos p.toList.length with h0 | h0
    · rw [p.steps_zero h0]; omega
    · have := p.steps_lt h0; omega

theorem permute_err_bound {p : Perm} {b : Blocked} (h : Bbu.Permutation.permute p = .error b) :
    b.offset < p.toList.length ∧ b.excess < p.toList.length := by
  rw [Perm.permute_eq] at h
  split at h
  · cases h
    rename_i hs
    have := step_blocked_lt _ hs
    rwa [Perm.length_state] at this
  · cases h

/-! ## The proof of `permuteDestinations` -/

-- Normalize the registers and close a goal on addresses.
local macro "bvo" : tactic => `(tactic| (
  simp only [Reg64s.get64_rsp, Reg64s.get64_rdi, Reg64s.get64_rax, Reg64s.get64_rbx,
    Reg64s.get64_rdx, Reg64s.get64_rsi, Reg64s.get64_rcx, finishF_eq, Mem.Blocks.Inside, or_false,
    Int64.reduceToInt, BitVec.ofInt_ofNat] at *
  bv_omega))

namespace FinishProof

-- The byte encodings of the swap depths and destination offsets in these invariants.
def bytes (l : List Nat) : List UInt8 := l.map Nat.toUInt8
def words (l : List Nat) : List UInt8 := l.flatMap fun x => [x.toUInt8, (x / 256).toUInt8]

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
  | .label ".LB.Emission.permute.0", t => Fr s ra t ∧ Mem.UnchangedOutside [frame finishF s] s.dmem t.dmem
      ∧ rdi t = rd s.dmem (wordAt (rdi s) 0) ∧ (rax t).toNat < p0.toList.length
      ∧ Mem.Contains t.dmem (rsp s - 2064#64) (words (p0.toList.take (rax t).toNat))
  | .label ".LB.Emission.permute.1", t => Fr s ra t ∧ Mem.UnchangedOutside [frame finishF s] s.dmem t.dmem
      ∧ rdi t = rd s.dmem (wordAt (rdi s) 0)
      ∧ Mem.Contains t.dmem (rsp s - 2064#64) (words p0.toList)
  | .label ".LB.Emission.permute.2", t => Fr s ra t ∧ ∃ L, Bbu.Permutation.permute p0 = .ok L ∧ ∃ j < L.length,
      rdx t = rsp s - 4112#64 + BitVec.ofNat 64 j ∧ SwInv s L j t
  | .label ".LB.Emission.permute.3", t => Fr s ra t ∧ Wf t.dmem (rdi s) ∧ finishR s t
      ∧ Mem.UnchangedOutside (frame finishF s :: writable s.dmem (rdi s)) s.dmem t.dmem
  | .label ".LB.Emission.permute.4", t => Fr s ra t ∧ Mem.UnchangedOutside [frame finishF s] s.dmem t.dmem
      ∧ ∃ b, Bbu.Permutation.permute p0 = .error b
        ∧ Mem.Contains t.dmem (rsp s - 4116#64) (words [b.offset, b.excess])
  | .label ".LB.Emission.permute.5", t => Fr s ra t ∧ Mem.UnchangedOutside [frame finishF s] s.dmem t.dmem
      ∧ Bbu.Permutation.permute p0 = .ok []
  | _, _ => False

def FVar (l : Label) (t : MachineData) : Nat :=
  match l with
  | "permuteDestinations" => 5000
  | ".LB.Emission.permute.0" => 3000 + (1024 - (rax t).toNat)
  | ".LB.Emission.permute.1" => 3000
  | ".LB.Emission.permute.2" => 2100 - (rdx t - (rsp s - 4112#64)).toNat
  | ".LB.Emission.permute.4" => 1
  | ".LB.Emission.permute.5" => 1
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

-- The `kvcgen` form of the stores of `.LB.Emission.permute.4`.
def lb60A (m : Mem 64) (x : Addr) : Addr :=
  BitVec.ofInt 64 (m.loadInt (x + BitVec.ofInt 64 (Int64.toInt 56)) 8).get!

def lb60V (m : Mem 64) (sp : Addr) (k : Int64) : Word :=
  BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 16 (m.loadInt (sp + BitVec.ofInt 64 k.toInt) 2).get!))

def lb60M1 (m : Mem 64) (x sp : Addr) : Mem 64 :=
  m.storeInt (lb60A m x + BitVec.ofInt 64 (Int64.toInt 0)) 8 (lb60V m sp 12).toInt

def lb60Mem (m : Mem 64) (x sp : Addr) : Mem 64 :=
  (lb60M1 m x sp).storeInt (lb60A (lb60M1 m x sp) x + BitVec.ofInt 64 (Int64.toInt 8)) 8
    (lb60V (lb60M1 m x sp) sp 14).toInt


-- `finishC` in terms of `permute p0`.
theorem finish_eq {p0 : Perm} {st0 : St} (hp0 : p0.toList = st0.slots.map Slot.dest) :
    finishC st0 = (match Bbu.Permutation.permute p0 with
      | .ok L => .ok (L.foldl swapTop st0)
      | .error b => .error (.blocked b.offset b.excess st0)) := by
  obtain ⟨l, lt, inj⟩ := p0
  simp only at hp0
  subst hp0
  unfold finishC
  simp only [St.all_destinationOf, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [dite_eq_left_of_eq_true (eq_true ⟨lt, fun i hi j hj => inj i j hi hj⟩)]
  rfl

-- `Mid` from `Fr` and a change in the frame and `writable`.
theorem mid_of (hfr : Fr s ra t) {l : List (Addr × Nat)} (hu : Mem.UnchangedOutside l s.dmem t.dmem)
    (hl : ∀ x, Mem.Blocks.Inside x 1 l → Mem.Blocks.Inside x 1 (frame finishF s :: writable s.dmem (rdi s))) :
    Kit.Mid finishF s ra t.dmem :=
  ⟨rd_of_contains hfr.cra, hfr.map, uo_mono hu hl⟩

-- The byte at `rsp s - 4112 + j` lies in the frame.
theorem inside_T (hf : FrameOk finishF s) {a : Addr} {j n : Nat} (ha : a = rsp s - 4112#64 + BitVec.ofNat 64 j)
    (hj : j + n ≤ 2048) : ∀ x, Mem.Blocks.Inside x 1 [(a, n)] → Mem.Blocks.Inside x 1 [frame finishF s] := by
  have hle := hf.le
  simp only [finishF_eq] at hle
  intro x hx
  subst ha
  simp only [Mem.Blocks.Inside, or_false, finishF_eq] at hx ⊢
  bv_omega

-- A word of `m_destinationOf` or `m_positionOf`.
theorem inside_dest {k : Nat} (hk : DEST ≤ k) (hk2 : k < WORDS) :
    ∀ x, Mem.Blocks.Inside x 1 [(wordAt (rdi s) k, 8)] → Mem.Blocks.Inside x 1 (writable s.dmem (rdi s)) :=
  Kit.inside_bytes (inside_writable (Or.inr (Or.inl (by
    simp only [wordAt, DEST_eq, WORDS_eq] at hk hk2 ⊢; bv_omega))))

end
end FinishProof

end Bbu
