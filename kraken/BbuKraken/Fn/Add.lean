import BbuKraken.Kit

/-!
The body triple of `add` (`c/bbu/add.S`). `add` saves five registers, calls
`position_of`, and then writes the operation and the new slot.
-/

open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Bbu

namespace AddFn

section
variable {s : MachineData} {ra : Int64}

-- The saved words, the struct and the frame in the memory `m` of `add`.
structure Fm (s : MachineData) (ra : Int64) (m : Mem 64) : Prop where
  ra : rd m (rsp s - 8#64) = ra.toBitVec
  r15 : rd m (rsp s - 16#64) = s.regs.r15.toBitVec
  r14 : rd m (rsp s - 24#64) = s.regs.r14.toBitVec
  r12 : rd m (rsp s - 32#64) = s.regs.r12.toBitVec
  rbp : rd m (rsp s - 40#64) = s.regs.rbp.toBitVec
  rbx : rd m (rsp s - 48#64) = s.regs.rbx.toBitVec
  wf : Wf m (rdi s)
  map : Mem.Mapped [frame 56 s] m
  un : Mem.UnchangedOutside (mod 56 s).mem s.dmem m

-- A change in the blocks of `add` keeps the environment and the regions.
theorem keeps {m : Mem 64} (hpre : Pre 56 addA s) (hu : Mem.UnchangedOutside (mod 56 s).mem s.dmem m) :
    envOf m (rdi s) = env s ∧ readable m (rdi s) = readable s.dmem (rdi s)
      ∧ writable m (rdi s) = writable s.dmem (rdi s) :=
  Post.env (t := { s with dmem := m }) hpre ⟨fun _ _ => rfl, hu⟩

-- The 8 bytes `k` bytes below `rsp s` lie in the frame.
theorem in_frame (_hle : 56 ≤ (rsp s).toNat) {k : Nat} (hk : 8 ≤ k) (hk' : k ≤ 56) :
    ∀ x, Mem.Blocks.Inside x 1 [(rsp s - BitVec.ofNat 64 k, 8)] → Mem.Blocks.Inside x 1 [frame 56 s] := by
  intro x hx
  simp only [Mem.Blocks.Inside, or_false] at hx ⊢
  bv_omega

-- The memory after the pushes of the entry block, as `kvcgen64` gives it.
def pushes (s : MachineData) (ra : Int64) : Mem 64 :=
  (((((s.dmem.storeInt (rsp s - 8#64) 8 ra.toBitVec.toInt).storeInt
    (rsp s - 8#64 - 8#64) 8 s.regs.r15.toBitVec.toInt).storeInt
    (rsp s - 8#64 - 8#64 - 8#64) 8 s.regs.r14.toBitVec.toInt).storeInt
    (rsp s - 8#64 - 8#64 - 8#64 - 8#64) 8 s.regs.r12.toBitVec.toInt).storeInt
    (rsp s - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8 s.regs.rbp.toBitVec.toInt).storeInt
    (rsp s - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8 s.regs.rbx.toBitVec.toInt

theorem unchanged_pushes : Mem.UnchangedOutside [frame 56 s] s.dmem (pushes s ra) := by
  have hin : ∀ a : Addr, (a - (rsp s - BitVec.ofNat 64 56)).toNat + 8 ≤ 56 →
      Mem.Blocks.Inside a 8 [frame 56 s] := fun a h => Or.inl h
  refine .storeInt (.storeInt (.storeInt (.storeInt (.storeInt (.storeInt
    (fun _ _ => rfl) (hin _ ?_) _) (hin _ ?_) _) (hin _ ?_) _) (hin _ ?_) _) (hin _ ?_) _) (hin _ ?_) _
  all_goals (simp only [rsp] at *; bv_omega)

theorem fm_pushes (hpre : Pre 56 addA s) : Fm s ra (pushes s ra) := by
  have hle := hpre.2.1.le
  have hu := unchanged_pushes (s := s) (ra := ra)
  have hd := disjoint_symm hpre.2.1.disj
  simp only [rsp] at hle
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Wf.congr_of_disjoint hu hpre.1 hd, ?_, ?_⟩
  all_goals try simp only [pushes]
  · rw [rd_store_other, rd_store_other, rd_store_other, rd_store_other, rd_store_other,
      rd_store_same _ rfl, BitVec.ofInt_toInt]
    all_goals bv_omega
  · rw [rd_store_other, rd_store_other, rd_store_other, rd_store_other,
      rd_store_same _ (by bv_omega), BitVec.ofInt_toInt]
    all_goals bv_omega
  · rw [rd_store_other, rd_store_other, rd_store_other, rd_store_same _ (by bv_omega),
      BitVec.ofInt_toInt]
    all_goals bv_omega
  · rw [rd_store_other, rd_store_other, rd_store_same _ (by bv_omega), BitVec.ofInt_toInt]
    all_goals bv_omega
  · rw [rd_store_other, rd_store_same _ (by bv_omega), BitVec.ofInt_toInt]
    all_goals bv_omega
  · rw [rd_store_same _ (by bv_omega), BitVec.ofInt_toInt]
  · exact hpre.2.1.mapped.storeInt _ _ _ |>.storeInt _ _ _ |>.storeInt _ _ _ |>.storeInt _ _ _
      |>.storeInt _ _ _ |>.storeInt _ _ _
  · intro x hx
    exact hu x fun h => hx (Or.inl (h.elim id False.elim))

-- A callee at `rsp s - 48` keeps the saved words and the blocks of `add`.
theorem Fm.call {m : Mem 64} {c t : MachineData} {R : MachineData → MachineData → Prop}
    (hpre : Pre 56 addA s) (h : Fm s ra m) (hc : c.dmem = m) (hrsp : rsp c = rsp s - 48#64)
    (hrdi : rdi c = rdi s) (hp : Post 8 R c t) (hag : (mod 8 c).Agree c t) : Fm s ra t.dmem := by
  have hfr := hpre.2.1
  have hle := hfr.le
  have hwr := (keeps hpre h.un).2.2
  have hu : Mem.UnchangedOutside (frame 8 c :: writable s.dmem (rdi s)) m t.dmem := by
    have := hag.2
    simp only [mod, hc, hrdi, hwr] at this
    exact this
  -- `writable` does not overlap the frame
  have hnw : ∀ x, Mem.Blocks.Inside x 1 [frame 56 s] → ¬ Mem.Blocks.Inside x 1 (writable s.dmem (rdi s)) :=
    fun x hx hw => hfr.disj x hx (inside_append.mpr (Or.inl hw))
  -- the frame of the callee lies in the frame
  have hcf : ∀ x, Mem.Blocks.Inside x 1 [frame 8 c] → Mem.Blocks.Inside x 1 [frame 56 s] := by
    intro x hx
    simp only [Mem.Blocks.Inside, or_false, hrsp] at hx ⊢
    bv_omega
  have hsv : ∀ {k}, 8 ≤ k → k ≤ 48 →
      rd t.dmem (rsp s - BitVec.ofNat 64 k) = rd m (rsp s - BitVec.ofNat 64 k) := fun hk hk' =>
    rd_congr hu fun x hx hl => by
      rcases hl with hl | hl
      · simp only [Mem.Blocks.Inside, or_false, hrsp] at hx hl
        bv_omega
      · exact hnw x (in_frame hle hk (by omega) x hx) hl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsv (k := 8) (by omega) (by omega)]; exact h.ra
  · rw [hsv (k := 16) (by omega) (by omega)]; exact h.r15
  · rw [hsv (k := 24) (by omega) (by omega)]; exact h.r14
  · rw [hsv (k := 32) (by omega) (by omega)]; exact h.r12
  · rw [hsv (k := 40) (by omega) (by omega)]; exact h.rbp
  · rw [hsv (k := 48) (by omega) (by omega)]; exact h.rbx
  · rw [← hrdi]; exact hp.1
  · intro x hx
    by_cases hx8 : Mem.Blocks.Inside x 1 [frame 8 c]
    · exact hp.2.1 x hx8
    · rw [hu x fun hl => hl.elim (fun hl => hx8 (Or.inl hl)) (hnw x hx)]
      exact h.map x hx
  · intro x hx
    have hx' : ¬ Mem.Blocks.Inside x 1 (frame 8 c :: writable s.dmem (rdi s)) := fun hl =>
      hl.elim (fun hl => hx (Or.inl (by
        simpa only [Mem.Blocks.Inside, or_false] using hcf x (Or.inl hl))))
        (fun hl => hx (Or.inr hl))
    rw [hu x hx']
    exact h.un x hx

-- The precondition of a callee at `rsp s - 48`.
theorem Fm.pre {m : Mem 64} {c : MachineData} {A : MachineData → Prop}
    (hpre : Pre 56 addA s) (h : Fm s ra m) (hc : c.dmem = m) (hrsp : rsp c = rsp s - 48#64)
    (hrdi : rdi c = rdi s) (hA : A c) : Pre 8 A c := by
  obtain ⟨-, hr, hwr⟩ := keeps hpre h.un
  refine ⟨by rw [hc, hrdi]; exact h.wf, ?_, hA⟩
  exact FrameOk.sub (k := 48) hpre.2.1 hpre.1 hrdi hrsp (by omega) (hc ▸ h.map) (hc ▸ hr) (hc ▸ hwr)

theorem st_pushes (hpre : Pre 56 addA s) : stOf (pushes s ra) (rdi s) = st s :=
  stOf_congr unchanged_pushes hpre.1 (disjoint_symm hpre.2.1.disj)

-- The state `c` after the call to `position_of` from the state `C`.
structure After (s : MachineData) (ra : Int64) (c : MachineData) : Prop where
  fm : Fm s ra c.dmem
  mst : stOf c.dmem (rdi s) = st s
  ax : c.regs.rax.toBitVec = encOpt (positionOf (st s) (rdx s).toNat)
  rsp : c.regs.rsp.toBitVec = rsp s - 48#64
  rbx : c.regs.rbx.toBitVec = s.regs.rdi.toBitVec
  rbp : c.regs.rbp.toBitVec = s.regs.rdx.toBitVec
  r12 : c.regs.r12.toBitVec = s.regs.rsi.toBitVec
  r13 : c.regs.r13 = s.regs.r13
  r14 : c.regs.r14.toBitVec = s.regs.rcx.toBitVec
  r15 : c.regs.r15.toBitVec = s.regs.r8.toBitVec

theorem after {C c : MachineData} (hp : Post 8 positionOfR C c) (hag : (mod 8 C).Agree C c)
    (hpre : Pre 56 addA s) (hm : C.dmem = pushes s ra)
    (hsp : C.regs.rsp.toBitVec = rsp s - 48#64) (hdi : C.regs.rdi = s.regs.rdi)
    (hsi : C.regs.rsi.toBitVec = s.regs.rdx.toBitVec)
    (hbx : C.regs.rbx.toBitVec = s.regs.rdi.toBitVec) (hbp : C.regs.rbp.toBitVec = s.regs.rdx.toBitVec)
    (h12 : C.regs.r12.toBitVec = s.regs.rsi.toBitVec) (h13 : C.regs.r13 = s.regs.r13)
    (h14 : C.regs.r14.toBitVec = s.regs.rcx.toBitVec) (h15 : C.regs.r15.toBitVec = s.regs.r8.toBitVec) :
    After s ra c := by
  have hrdi : rdi C = rdi s := by simp only [rdi, Reg64s.get64_rdi, hdi]
  have hreg : ∀ r, r ∉ (mod 8 C).regs → c.regs.get64 r = C.regs.get64 r := hag.1
  obtain ⟨-, -, hrax, hst⟩ := id hp
  simp only [st', st, hrdi, hm, st_pushes hpre] at hst
  simp only [rax, st, hrdi, hm, st_pushes hpre, rsi, Reg64s.get64_rsi, hsi] at hrax
  have g := fun r (h : r ∉ (mod 8 C).regs) => hreg r h
  refine ⟨Fm.call hpre (fm_pushes hpre) hm hsp hrdi hp hag, hst, hrax, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · have := g .rsp (by simp [mod]); simp only [Reg64s.get64_rsp] at this; rw [this, hsp]
  · have := g .rbx (by simp [mod]); simp only [Reg64s.get64_rbx] at this; rw [this, hbx]
  · have := g .rbp (by simp [mod]); simp only [Reg64s.get64_rbp] at this; rw [this, hbp]
  · have := g .r12 (by simp [mod]); simp only [Reg64s.get64_r12] at this; rw [this, h12]
  · have := g .r13 (by simp [mod]); simp only [Reg64s.get64_r13] at this
    rw [← h13]; exact UInt64.toBitVec_inj.mp this
  · have := g .r14 (by simp [mod]); simp only [Reg64s.get64_r14] at this; rw [this, h14]
  · have := g .r15 (by simp [mod]); simp only [Reg64s.get64_r15] at this; rw [this, h15]

end

section
variable (s : MachineData) (ra : Int64)

-- `.LB19`: `position_of` found a slot for the destination.
def At19 (t : MachineData) : Prop :=
  Fm s ra t.dmem ∧ t.regs.rsp.toBitVec = rsp s - 48#64 ∧ t.regs.r13 = s.regs.r13
    ∧ add (st s) (rsi s) (rdx s).toNat ⟨rcx s, r8 s⟩ = .error .assertion

-- `.LB17`: the result is in `rax` and in memory.
def At17 (t : MachineData) : Prop :=
  Fm s ra t.dmem ∧ t.regs.rsp.toBitVec = rsp s - 48#64 ∧ t.regs.r13 = s.regs.r13 ∧ addR s t

end

theorem shl4 (x : BitVec 64) : x <<< 4 = x * 16#64 := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]; rfl

section
variable {m : Mem 64} {S : Addr}

-- The struct before the stores of `add`.
structure Lay (m : Mem 64) (S : Addr) : Prop where
  wf : Wf m S
  len : (rd m S).toNat < 256
  nops : (rd m (S + 16#64)).toNat < 6 * nOf m S

theorem Lay.nat (h : Lay m S) :
    S.toNat + 4160 ≤ 2 ^ 64 ∧ (rd m (S + 48#64)).toNat + 96 * nOf m S ≤ 2 ^ 64
      ∧ 4160 ≤ (rd m (S + 48#64) - S).toNat ∧ 96 * nOf m S ≤ (S - rd m (S + 48#64)).toNat := by
  have hs : S.toNat + 4160 ≤ 2 ^ 64 := h.wf.struct_lt
  have ho : (rd m (S + 48#64)).toNat + 96 * nOf m S ≤ 2 ^ 64 := h.wf.ops_lt
  have hn := h.nops
  refine ⟨hs, ho, Nat.not_lt.mp fun hx => ?_, Nat.not_lt.mp fun hx => ?_⟩
  · refine h.wf.disj_struct (rd m (S + 48#64)) (Or.inl (show _ + 1 ≤ 4160 by omega)) (Or.inl ?_)
    show (rd m (S + 48#64) - rd m (S + 48#64)).toNat + 1 ≤ 96 * nOf m S
    simp only [BitVec.sub_self, BitVec.toNat_zero]; omega
  · refine h.wf.disj_struct S (Or.inl (show (S - S).toNat + 1 ≤ 4160 by simp)) (Or.inl ?_)
    show (S - rd m (S + 48#64)).toNat + 1 ≤ 96 * nOf m S
    omega


-- The address of the new operation.
abbrev opA (m : Mem 64) (S : Addr) : Addr := rd m (S + 48#64) + rd m (S + 16#64) * 16#64

theorem rd_st1a (h : Lay m S) (v : Int) :
    rd (m.storeInt (opA m S) 8 v) (S + 16#64) = rd m (S + 16#64) := by
  obtain ⟨h1, h2, h3, h4⟩ := h.nat
  have := h.nops
  rw [rd_store_other _ (by bv_omega)]

theorem rd_st1b (h : Lay m S) (v : Int) :
    rd (m.storeInt (opA m S) 8 v) (S + 48#64) = rd m (S + 48#64) := by
  obtain ⟨h1, h2, h3, h4⟩ := h.nat
  have := h.nops
  rw [rd_store_other _ (by bv_omega)]

theorem rd_st2 (h : Lay m S) (v w : Int) :
    rd ((m.storeInt (opA m S) 8 v).storeInt (opA m S + 8#64) 8 w) (S + 16#64) = rd m (S + 16#64) := by
  obtain ⟨h1, h2, h3, h4⟩ := h.nat
  have := h.nops
  rw [rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega)]

theorem rd_st3 (h : Lay m S) (v w x : Int) :
    rd (((m.storeInt (opA m S) 8 v).storeInt (opA m S + 8#64) 8 w).storeInt (S + 16#64) 8 x) S
      = rd m S := by
  obtain ⟨h1, h2, h3, h4⟩ := h.nat
  have := h.nops
  rw [rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega)]

-- The memory after the stores of `add`: the new operation, `nops + 1`, the new
-- slot and `len + 1`.
def stores (m : Mem 64) (S : Addr) (v d c r : Word) : Mem 64 :=
  (((((m.storeInt (opA m S) 8 c.toInt).storeInt (opA m S + 8#64) 8 r.toInt).storeInt (S + 16#64) 8
    (1#64 + rd m (S + 16#64)).toInt).storeInt (S + rd m S * 8#64 + 64#64) 8 v.toInt).storeInt
    (S + rd m S * 8#64 + 2112#64) 8 d.toInt).storeInt S 8 (1#64 + rd m S).toInt

theorem stores_un (h : Lay m S) (v d c r : Word) :
    Mem.UnchangedOutside (writable m S) m (stores m S v d c r) := by
  obtain ⟨h1, h2, h3, h4⟩ := h.nat
  have := h.nops
  have hl := h.len
  have h0 : Mem.UnchangedOutside (writable m S) m m := fun _ _ => rfl
  refine ((((((h0.storeInt ?_ _).storeInt ?_ _).storeInt ?_ _).storeInt ?_ _).storeInt ?_ _).storeInt ?_ _)
  all_goals simp only [writable, opsOf, wordAt, STACK, Mem.Blocks.Inside, Nat.reduceMul]
  · exact Or.inr (Or.inr (Or.inl (by bv_omega)))
  · exact Or.inr (Or.inr (Or.inl (by bv_omega)))
  · exact Or.inl (by bv_omega)
  · exact Or.inr (Or.inl (by bv_omega))
  · exact Or.inr (Or.inl (by bv_omega))
  · exact Or.inl (by bv_omega)

theorem stOf_stores (h : Lay m S) (v d c r : Word) :
    stOf (stores m S v d c r) S =
      { stOf m S with slots := (stOf m S).slots ++ [(⟨v, d.toNat⟩ : Slot)]
                      ops := (stOf m S).ops ++ [(⟨c, r⟩ : Op)] } := by
  obtain ⟨h1, h2, h3, h4⟩ := h.nat
  have hn := h.nops
  have hl := h.len
  have hlen : rd (stores m S v d c r) S = 1#64 + rd m S := by
    simp only [stores]
    rw [rd_store_same _ (by bv_omega), BitVec.ofInt_toInt]
  have hpend : rd (stores m S v d c r) (wordAt S 1) = rd m (wordAt S 1) := by
    simp only [stores]
    rw [rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega),
      rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega)]
  have hnops : rd (stores m S v d c r) (wordAt S 2) = 1#64 + rd m (S + 16#64) := by
    simp only [stores]
    rw [rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega),
      rd_store_same _ (by bv_omega), BitVec.ofInt_toInt]
  have hops : opsOf (stores m S v d c r) S = rd m (S + 48#64) := by
    simp only [stores, opsOf, wordAt, Nat.reduceMul]
    rw [rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega),
      rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega)]
  have hslot : ∀ i < (rd m S).toNat, slotOf (stores m S v d c r) S i = slotOf m S i := by
    intro i hi
    simp only [slotOf, stores, STACK, DEST]
    rw [rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega),
      rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega),
      rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega),
      rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega)]
  have hslotL : slotOf (stores m S v d c r) S (rd m S).toNat = ⟨v, d.toNat⟩ := by
    simp only [slotOf, stores, STACK, DEST]
    rw [rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega), rd_store_same _ (by bv_omega),
      rd_store_other _ (by bv_omega), rd_store_same _ (by bv_omega), BitVec.ofInt_toInt,
      BitVec.ofInt_toInt]
  have hop : ∀ i < (rd m (S + 16#64)).toNat, opOf (stores m S v d c r) S i = opOf m S i := by
    intro i hi
    have ho : opsOf m S = rd m (S + 48#64) := rfl
    simp only [opOf, hops, ho]
    simp only [stores]
    rw [rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega),
      rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega),
      rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega),
      rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega)]
  have hopN : opOf (stores m S v d c r) S (rd m (S + 16#64)).toNat = ⟨c, r⟩ := by
    simp only [opOf, hops]
    simp only [stores]
    rw [rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega),
      rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega), rd_store_same _ (by bv_omega),
      rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega), rd_store_other _ (by bv_omega),
      rd_store_other _ (by bv_omega), rd_store_same _ (by bv_omega), BitVec.ofInt_toInt,
      BitVec.ofInt_toInt]
  have hl1 : (1#64 + rd m S).toNat = (rd m S).toNat + 1 := by bv_omega
  have hn1 : (1#64 + rd m (S + 16#64)).toNat = (rd m (S + 16#64)).toNat + 1 := by bv_omega
  have hw0 : wordAt S 0 = S := by simp [wordAt]
  have hw2 : wordAt S 2 = S + 16#64 := rfl
  simp only [stOf, hlen, hpend, hnops, hl1, hn1, List.range_succ, List.map_append, List.map_cons,
    List.map_nil, hslotL, hopN, hw0, hw2]
  congr 2
  · exact List.map_congr_left fun i hi => hslot i (List.mem_range.mp hi)
  · exact List.map_congr_left fun i hi => hop i (List.mem_range.mp hi)

theorem ns_test (v : Word) (r) :
    CondCode.ns.interp (StatusFlags.from_result (v &&& v) r) = !v.msb := by
  simp [CondCode.interp, StatusFlags.from_result]

-- `jns` after `testq` of the result of `position_of`.
theorem pos_ns {st : St} {d : Nat} (hl : st.len ≤ 256) (r) :
    CondCode.ns.interp (StatusFlags.from_result (encOpt (positionOf st d) &&& encOpt (positionOf st d)) r)
      = (positionOf st d).isSome := by
  rw [ns_test]
  cases hp : positionOf st d with
  | none => simp [encOpt]; decide
  | some p =>
    have : p < st.len := by
      simp only [positionOf, List.findIdx?_eq_some_iff_getElem] at hp; exact hp.1
    simp only [encOpt, BitVec.msb_eq_decide, BitVec.toNat_ofNat, Option.isSome_some]
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Nat.not_le]
    omega

variable {s : MachineData} {ra : Int64}

theorem Fm.lay (hpre : Pre 56 addA s) (h : Fm s ra m) (hst : stOf m (rdi s) = st s) :
    Lay m (rdi s) := by
  have hn : nOf m (rdi s) = nOf s.dmem (rdi s) :=
    congrArg BitVec.toNat (hdr_congr h.un hpre.disj (k := 3) (by omega) (by omega))
  obtain ⟨-, -, hl, ho⟩ := hpre
  rw [← hst] at hl ho
  refine ⟨h.wf, ?_, ?_⟩
  · simpa [St.len, stOf, wordAt] using hl
  · rw [hn]; simpa [stOf, cap] using ho

theorem Fm.after_stores (hpre : Pre 56 addA s) (h : Fm s ra m) (hl : Lay m (rdi s)) (v d c r : Word) :
    Fm s ra (stores m (rdi s) v d c r) := by
  have hu := stores_un hl v d c r
  obtain ⟨-, hr, hwr⟩ := keeps hpre h.un
  have hfr := hpre.2.1
  have hle := hfr.le
  have hnw : ∀ x, Mem.Blocks.Inside x 1 [frame 56 s] → ¬ Mem.Blocks.Inside x 1 (writable m (rdi s)) :=
    fun x hx hw => hfr.disj x hx (inside_append.mpr (Or.inl (hwr ▸ hw)))
  have hsv : ∀ {k}, 8 ≤ k → k ≤ 56 → rd (stores m (rdi s) v d c r) (rsp s - BitVec.ofNat 64 k)
      = rd m (rsp s - BitVec.ofNat 64 k) := fun hk hk' =>
    rd_congr hu fun x hx hw => hnw x (in_frame hle hk hk' x hx) hw
  have hd : Mem.Blocks.Disjoint (readable m (rdi s)) (writable m (rdi s)) :=
    fun x hx hw => hpre.disj x (hr ▸ hx) (Or.inr (hwr ▸ hw))
  have hm0 : Mem.Mapped (writable m (rdi s)) m := fun x hx => h.wf.mapped x (inside_append.mpr (Or.inl hx))
  have hst := stOf_stores hl v d c r
  have hsl := congrArg (fun t => t.slots.length) hst
  have hop := congrArg (fun t => t.ops.length) hst
  simp only [stOf, List.length_map, List.length_range, List.length_append, List.length_cons,
    List.length_nil] at hsl hop
  have hlen := hl.len
  have hnops := hl.nops
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Wf.congr hu h.wf hd ?_ ?_ ?_, ?_, ?_⟩
  · rw [hsv (k := 8) (by omega) (by omega)]; exact h.ra
  · rw [hsv (k := 16) (by omega) (by omega)]; exact h.r15
  · rw [hsv (k := 24) (by omega) (by omega)]; exact h.r14
  · rw [hsv (k := 32) (by omega) (by omega)]; exact h.r12
  · rw [hsv (k := 40) (by omega) (by omega)]; exact h.rbp
  · rw [hsv (k := 48) (by omega) (by omega)]; exact h.rbx
  · exact ((((((hm0.storeInt _ _ _).storeInt _ _ _).storeInt _ _ _).storeInt _ _ _).storeInt _ _ _).storeInt _ _ _)
  · simp only [wordAt, Nat.reduceMul, BitVec.add_zero] at hsl hlen ⊢; omega
  · simp only [wordAt, Nat.reduceMul] at hop hnops ⊢; omega
  · exact ((((((h.map.storeInt _ _ _).storeInt _ _ _).storeInt _ _ _).storeInt _ _ _).storeInt _ _ _).storeInt _ _ _)
  · intro x hx
    rw [hu x fun hw => hx (Or.inr (hwr ▸ hw))]
    exact h.un x hx

-- A load from the struct regions after stores that keep them mapped.
theorem isSome_of {m m' : Mem 64} {a : Addr} (_hw : Wf m S)
    (hm : Mem.Mapped (writable m S ++ readable m S) m')
    (hin : Mem.Blocks.Inside a 8 (writable m S ++ readable m S)) : (m'.loadInt a 8).isSome = true :=
  hm.loadInt_isSome hin

theorem at17_ok {c t : MachineData} (hpre : Pre 56 addA s) (hA : After s ra c)
    (hnone : positionOf (st s) (rdx s).toNat = none)
    (hm : t.dmem = stores c.dmem (rdi s) (rsi s) (rdx s) (rcx s) (r8 s))
    (hax : t.regs.rax.toBitVec = 0#64) (hsp : t.regs.rsp.toBitVec = rsp s - 48#64)
    (h13 : t.regs.r13 = s.regs.r13) : At17 s ra t := by
  have hl := hA.fm.lay hpre hA.mst
  refine ⟨hm ▸ hA.fm.after_stores hpre hl _ _ _ _, hsp, h13, ?_⟩
  simp only [addR, add, hnone, Option.isSome_none, Bool.false_eq_true, ite_false, Res, Ok]
  refine ⟨by simpa [rax] using hax, ?_⟩
  simp only [st', hm, stOf_stores hl, hA.mst, id]

-- `Fm` gives the `Mid` of the Kit.
theorem Fm.mid (hpre : Pre 56 addA s) (h : Fm s ra m) : Kit.Mid 56 s ra m :=
  ⟨h.ra, fun x hx => hx.elim (fun h' => h.map x (Or.inl h'))
    (fun h' => h.wf.mapped x (inside_append.mpr (Or.inl ((keeps hpre h.un).2.2 ▸ h')))), h.un⟩


-- The pops of `.LB17` read the saved words.
theorem Fm.pops (h : Fm s ra m) {a : Addr} (ha : a = rsp s - 48#64) :
    rd m a = s.regs.rbx.toBitVec ∧ rd m (a + 8#64) = s.regs.rbp.toBitVec
      ∧ rd m (a + 8#64 + 8#64) = s.regs.r12.toBitVec
      ∧ rd m (a + 8#64 + 8#64 + 8#64) = s.regs.r14.toBitVec
      ∧ rd m (a + 8#64 + 8#64 + 8#64 + 8#64) = s.regs.r15.toBitVec := by
  subst ha
  refine ⟨h.rbx, ?_, ?_, ?_, ?_⟩
  · rw [show rsp s - 48#64 + 8#64 = rsp s - 40#64 by bv_omega]; exact h.rbp
  · rw [show rsp s - 48#64 + 8#64 + 8#64 = rsp s - 32#64 by bv_omega]; exact h.r12
  · rw [show rsp s - 48#64 + 8#64 + 8#64 + 8#64 = rsp s - 24#64 by bv_omega]; exact h.r14
  · rw [show rsp s - 48#64 + 8#64 + 8#64 + 8#64 + 8#64 = rsp s - 16#64 by bv_omega]; exact h.r15

-- `addR` depends on `rax` and the memory.
theorem addR_congr {t t' : MachineData} (hm : t'.dmem = t.dmem) (hax : rax t' = rax t)
    (h : addR s t) : addR s t' := by
  unfold addR Res at *
  generalize add (st s) (rsi s) (rdx s).toNat ⟨rcx s, r8 s⟩ = r at *
  rcases r with (⟨p, x⟩ | _) | a
  · exact ⟨hax.trans h.1, hm ▸ h.2.1, hm ▸ h.2.2⟩
  · exact hax.trans h
  · exact ⟨hax.trans h.1, by simp only [st', hm]; exact h.2⟩

-- `ret` from the state `u` gives the postcondition.
theorem ret [Host] {ls : List Label} {I' : CfgLabel → Nat → Unit → MachineData → Prop}
    {u : MachineData} (hpre : Pre 56 addA s) (hm : Fm s ra u.dmem)
    (hsp : u.regs.get64 .rsp = rsp s - 8#64)
    (hr : ∀ q, q ∉ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .rsp] →
      u.regs.get64 q = s.regs.get64 q)
    (hR : addR s u) :
    Program.Intercept ls (s.pushRa ra) I'
      (fun a t => a = ra ∧ Post addF addR s t ∧ (mod addF s).Agree s t) u.retAddr.get!
      { regs := u.regs.set64 Reg64.rsp (u.regs.get64 Reg64.rsp + 8#64), zmms := u.zmms,
        status := u.status, dmem := u.dmem } :=
  Kit.Mid.ret (by decide) hpre (hm.mid hpre) hsp rfl
    (by simp only [rsp, Reg64s.get64_set64, reduceIte, hsp, BitVec.sub_add_cancel])
    (fun q hq => by
      simp only [Reg64s.get64_set64]
      split
      · simp_all
      · exact hr q hq)
    hm.wf (addR_congr rfl (by simp [rax]) hR)
end
end AddFn

open AddFn

-- A jump to a label of the cfg: the stack, the invariant and the variant.
local macro "cfg_goto" : tactic => `(tactic| (
  apply Program.Intercept.intro_label
  · repeat ((fail_if_success (apply List.getElem?_cons_zero)); (apply List.getElem?_cons_succ_of))
    apply List.getElem?_cons_zero
  refine Or.inl ⟨?_, ?_, ?_⟩))

theorem add_body [Host] [FunDecls]
    (hpos : Spec "position_of" positionOfF positionOfA positionOfR) :
    Body addAsm addF addA addR := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  replace hpre : Pre 56 addA s := hpre
  refine Program.WP.cfg (fun
      | .entry, t | .label "add", t => t = s.pushRa ra
      | .label ".LB19", t => At19 s ra t
      | .label ".LB17", t => At17 s ra t
      | _, _ => False)
    (fun | "add", _ => 2 | ".LB19", _ => 1 | _, _ => 0) ?_ rfl
  cfg_cases
  case left t ht =>
    subst ht
    kvcgen64
  case right.left t ht =>
    subst ht
    have hle := hpre.2.1.le
    have hmap0 : Mem.Mapped [frame 56 s] (s.pushRa ra).dmem := hpre.2.1.mapped.storeInt _ _ _
    kvcgen64 [hpos]
    case vc1 | vc2 | vc3 | vc4 | vc5 | vc6 =>
      refine Mem.Mapped.loadInt_isSome (bs := [frame 56 s]) ?_ (Or.inl ?_)
      · repeat (first | (with_reducible exact hmap0) | apply Mem.Mapped.storeInt)
      · simp only [Reg64s.get64_rsp, MachineData.regs_pushRa, Reg64s.set64_rsp, rsp] at *
        bv_omega
    case vc7 =>
      refine Fm.pre hpre (fm_pushes hpre) rfl ?_ rfl trivial
      simp only [rsp, Reg64s.get64_rsp, MachineData.regs_pushRa, Reg64s.set64_rsp]
      bv_omega
    all_goals
      have hp := ‹Post positionOfF positionOfR _ _›
      have hag := ‹(mod positionOfF _).Agree _ _›
      have hA := after hp hag hpre rfl
        (by simp only [rsp, Reg64s.get64_rsp, MachineData.regs_pushRa, Reg64s.set64_rsp]; bv_omega)
        rfl rfl rfl rfl rfl rfl rfl rfl
      clear hp hag
      clear ‹Post positionOfF positionOfR _ _› ‹(mod positionOfF _).Agree _ _›
      have hl := hA.fm.lay hpre hA.mst
      have hw := hA.fm.wf
      have h256 : (st s).len ≤ 256 := Nat.le_of_lt hpre.2.2.1
      bbu_norm at *
      try simp only [hA.rbx, hA.rbp, hA.r12, hA.r13, hA.r14, hA.r15, hA.ax] at *
      simp only [pos_ns h256] at *
    case vc8 =>
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        have := hA.rsp
        simp only [MachineData.regs_pushRa, Reg64s.get64_rsp, Reg64s.set64_rsp, rsp] at *
        bv_omega
      · exact ⟨hA.fm, hA.rsp, hA.r13, by unfold add; simp only [‹(positionOf _ _).isSome = true›, ite_true]⟩
      · simp
    case vc10 | vc14 => decide
    all_goals try simp only [shl4, rd_st1a hl, rd_st1b hl, rd_st2 hl, rd_st3 hl]
    case vc22 =>
      refine at17_ok hpre hA ?_ rfl rfl hA.rsp rfl
      simpa using ‹(positionOf _ _).isSome = false›
    case vc23 => simp
    all_goals
      refine isSome_of hw ?_ ?_
      · repeat (first | exact hw.mapped | apply Mem.Mapped.storeInt)
      · obtain ⟨h1, h2, h3, h4⟩ := hl.nat
        have := hl.nops
        have := hl.len
        simp only [writable, readable, opsOf, wordAt, STACK, List.cons_append, Mem.Blocks.Inside,
          Nat.reduceMul]
        first
        | (left; bv_omega)
        | (right; left; bv_omega)
        | (right; right; left; bv_omega)
        | (right; right; right; right; left; bv_omega)
  case right.right.left t ht =>
    obtain ⟨hfm, hsp, h13, hR⟩ := ht
    have hle : 56 ≤ s.regs.rsp.toBitVec.toNat := hpre.2.1.le
    have hsp' : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 48#64 := hsp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hfm.pops hsp
    kvcgen64
    all_goals simp only [rd_def] at *
    case vc1 | vc2 | vc3 | vc4 | vc5 =>
      refine Mem.Mapped.loadInt_isSome hfm.map (Or.inl ?_)
      simp only [Reg64s.get64_rsp, rsp, hsp']
      bv_omega
    case vc6 =>
      simp only [MachineData.retAddr, Option.isSome_map]
      refine Mem.Mapped.loadInt_isSome hfm.map (Or.inl ?_)
      simp only [Reg64s.get64_rsp, rsp, hsp']
      bv_omega
    case vc7 =>
      refine ret hpre hfm ?_ ?_ hR
      · simp only [Reg64s.get64_rsp, rsp, hsp']
        bv_omega
      · intro q hq
        cases q <;> simp_all
  case right.right.right t ht =>
    obtain ⟨hfm, hsp, h13, hadd⟩ := ht
    kvcgen64
    cfg_goto
    · apply MachineData.stackAtOrBelow_of_toNat_lt
      simp only [MachineData.regs_pushRa, Reg64s.get64_rsp, Reg64s.set64_rsp, hsp] at *
      have := hpre.2.1.le
      bv_omega
    · exact ⟨hfm, hsp, h13, by simp only [addR, hadd, Res]; rfl⟩
    · simp

end Bbu
