import BbuKraken.Fn.Loop.Machine
import BbuKraken.Fn.Loop.Model

/-!
The exit blocks of `buildBottomUp`: `.LB65` (the pops and `ret`), `.LB66` (the end of
the loop), `.LB69` (`permuteDestinations`), the blocked labels `.LB107`, `.LB110` and
`.LB111`, and the labels that set `-2`.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

namespace Loop

section
variable {s : MachineData} {ra : Int64}

-- `-2` in `rax` gives the result of a failed assertion.
theorem atErr_out {t u : MachineData} (h : AtErr s ra t) (hm : u.dmem = t.dmem)
    (hsp : u.regs.rsp = t.regs.rsp) (hax : rax u = -2#64) : At65 s ra u := by
  refine ⟨hm ▸ h.1.fm, hsp ▸ h.1.rsp, ?_⟩
  unfold loopR
  rw [show loop (env s) (st s) 0 = R0 s from rfl, h.2]
  exact hax

end

section
variable {s : MachineData} {ra : Int64}

-- The callee-saved registers.
theorem saved_regs {t : MachineData} (hbx : t.regs.rbx.toBitVec = s.regs.rbx.toBitVec)
    (hbp : t.regs.rbp.toBitVec = s.regs.rbp.toBitVec)
    (h12 : t.regs.r12.toBitVec = s.regs.r12.toBitVec) (h13 : t.regs.r13.toBitVec = s.regs.r13.toBitVec)
    (h14 : t.regs.r14.toBitVec = s.regs.r14.toBitVec) (h15 : t.regs.r15.toBitVec = s.regs.r15.toBitVec) :
    ∀ q, q ∉ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .rsp] →
      t.regs.get64 q = s.regs.get64 q := by
  intro q hq
  cases q <;> simp_all

-- `loopR` reads only `rax` and the memory.
theorem loopR_congr {t u : MachineData} (h : loopR s t) (hm : u.dmem = t.dmem)
    (hax : rax u = rax t) : loopR s u := by
  unfold loopR at *
  generalize loop (env s) (st s) 0 = r at *
  rcases r with (⟨p, x⟩ | _) | a
  · exact ⟨hax.trans h.1, hm ▸ h.2.1, hm ▸ h.2.2⟩
  · exact hax.trans h
  · exact ⟨hax.trans h.1, by rw [st', hm]; exact h.2⟩

-- A word of the frame at `.LB65` is mapped.
theorem At65.isSome (hpre : Pre loopF loopA s) {t : MachineData} (h : At65 s ra t) {a : Addr}
    {k : Nat} (hk : 16 ≤ k ∧ k ≤ 56) (ha : a = rsp s - BitVec.ofNat 64 k) :
    (t.dmem.loadInt a 8).isSome = true := by
  have hle : 4224 ≤ (rsp s).toNat := hpre.2.1.le
  refine Mem.Mapped.loadInt_isSome h.1.map (Or.inl ?_)
  have : (BitVec.ofNat 64 k).toNat = k := by simp only [BitVec.toNat_ofNat]; omega
  simp only [ha, loopF_eq]
  bv_omega

theorem At65.sp {t u : MachineData} (h : At65 s ra t)
    (hsp : u.regs.rsp.toBitVec = 24#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) :
    rsp u = rsp s - 8#64 := by
  simp only [rsp, Reg64s.get64_rsp, hsp, h.2.1]; bv_omega

theorem At65.retSome (hpre : Pre loopF loopA s) {t u : MachineData} (h : At65 s ra t)
    (hu : u.dmem = t.dmem)
    (hsp : u.regs.rsp.toBitVec = 24#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) :
    u.retAddr.isSome = true := by
  rw [Kit.Mid.retAddr (by decide) hpre (hu ▸ h.1.toMid) (h.sp hsp)]; rfl

-- The pops and `ret` of `.LB65`.
theorem At65.ret [Host] {ls : List Label} {I' : CfgLabel → Nat → Unit → MachineData → Prop}
    (hpre : Pre loopF loopA s) {t u : MachineData} (h : At65 s ra t) (hu : u.dmem = t.dmem)
    (hsp : u.regs.rsp.toBitVec = 24#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64)
    (hbx : u.regs.rbx.toBitVec = rd t.dmem (24#64 + t.regs.rsp.toBitVec))
    (hbp : u.regs.rbp.toBitVec = rd t.dmem (24#64 + t.regs.rsp.toBitVec + 8#64))
    (h12 : u.regs.r12.toBitVec = rd t.dmem (24#64 + t.regs.rsp.toBitVec + 8#64 + 8#64))
    (h13 : u.regs.r13.toBitVec = rd t.dmem (24#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64))
    (h14 : u.regs.r14.toBitVec
      = rd t.dmem (24#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64))
    (h15 : u.regs.r15.toBitVec
      = rd t.dmem (24#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64 + 8#64))
    (hax : u.regs.rax = t.regs.rax) :
    Program.Intercept ls (s.pushRa ra) I'
      (fun a t => a = ra ∧ Post loopF loopR s t ∧ (mod loopF s).Agree s t) u.retAddr.get!
      { regs := u.regs.set64 Reg64.rsp (u.regs.get64 Reg64.rsp + 8#64), zmms := u.zmms,
        status := u.status, dmem := u.dmem } := by
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := h.1.pops
  have e := h.2.1
  refine Kit.Fm.ret (by decide) hpre (hu ▸ h.1) (h.sp hsp) (saved_regs ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · rw [hbx, e, show 24#64 + (rsp s - 80#64) = rsp s - 56#64 by bv_omega, p0]
  · rw [hbp, e, show 24#64 + (rsp s - 80#64) + 8#64 = rsp s - 48#64 by bv_omega, p1]
  · rw [h12, e, show 24#64 + (rsp s - 80#64) + 8#64 + 8#64 = rsp s - 40#64 by bv_omega, p2]
  · rw [h13, e, show 24#64 + (rsp s - 80#64) + 8#64 + 8#64 + 8#64 = rsp s - 32#64 by bv_omega, p3]
  · rw [h14, e, show 24#64 + (rsp s - 80#64) + 8#64 + 8#64 + 8#64 + 8#64 = rsp s - 24#64 by
      bv_omega, p4]
  · rw [h15, e, show 24#64 + (rsp s - 80#64) + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 = rsp s - 16#64 by
      bv_omega, p5]
  · intro t' hm hax'
    exact loopR_congr h.2.2 (hm.trans hu) (hax'.trans (by simp only [rax, Reg64s.get64_rax, hax]))

end

section
variable {s : MachineData} {ra : Int64} {t : MachineData}

/-! The blocked labels store `x` and `y` at `blocked` (the word 7 of the struct). -/

theorem Base.w7 (h : Base s ra t) : t.regs.rbp.toBitVec + 56#64 = wordAt (rdi s) 7 := by
  rw [h.rbp]

theorem blk0 (m : Mem 64) (S : Addr) : blkOf m S = wordAt (blkOf m S) 0 := by simp [wordAt]

theorem Base.blk_ld1 (h : Base s ra t) :
    (t.dmem.loadInt (t.regs.rbp.toBitVec + 56#64) 8).isSome = true := by
  rw [h.w7]; exact h.fm.wf.word_isSome h.fm.wf.mapped (by decide)

theorem Base.blk_ld2 (h : Base s ra t) :
    (t.dmem.loadInt (rd t.dmem (t.regs.rbp.toBitVec + 56#64)) 8).isSome = true := by
  rw [h.w7, blkOf_def, blk0]; exact h.fm.wf.blk_isSome h.fm.wf.mapped (by decide)

theorem Base.blk_ld3 (h : Base s ra t) (x : Word) :
    ((t.dmem.storeInt (rd t.dmem (t.regs.rbp.toBitVec + 56#64)) 8 x.toInt).loadInt
      (t.regs.rbp.toBitVec + 56#64) 8).isSome = true := by
  rw [h.w7]; exact h.fm.wf.word_isSome (h.fm.wf.mapped.storeInt _ _ _) (by decide)

theorem Base.blk_ld4 (h : Base s ra t) (x : Word) :
    ((t.dmem.storeInt (rd t.dmem (t.regs.rbp.toBitVec + 56#64)) 8 x.toInt).loadInt
      (rd (t.dmem.storeInt (rd t.dmem (t.regs.rbp.toBitVec + 56#64)) 8 x.toInt)
        (t.regs.rbp.toBitVec + 56#64) + 8#64) 8).isSome = true := by
  rw [h.w7, blkOf_def, blkOf_def, blk0 t.dmem, h.fm.wf.blkOf_store (by decide)]
  exact h.fm.wf.blk_isSome (h.fm.wf.mapped.storeInt _ _ _) (k := 1) (by decide)

-- The two stores of a blocked label give `At65`.
theorem Base.blk_out (hpre : Pre loopF loopA s) (h : Base s ra t) {u : MachineData} {c k : Nat}
    {x y : Word} (hx : x = BitVec.ofNat 64 c) (hy : y = BitVec.ofNat 64 k)
    (hR : R0 s = .error (.blocked c k))
    (hm : u.dmem = (t.dmem.storeInt (rd t.dmem (t.regs.rbp.toBitVec + 56#64)) 8 x.toInt).storeInt
      (rd (t.dmem.storeInt (rd t.dmem (t.regs.rbp.toBitVec + 56#64)) 8 x.toInt)
        (t.regs.rbp.toBitVec + 56#64) + 8#64) 8 y.toInt)
    (hsp : u.regs.rsp = t.regs.rsp) (hr : rax u = -1#64) : At65 s ra u := by
  subst hx hy
  rw [h.w7, blkOf_def, blkOf_def, blk0 t.dmem, h.fm.wf.blkOf_store (by decide)] at hm
  obtain ⟨hf, hres⟩ := Fm.blocked hpre h.fm hm hr
  refine ⟨hf, hsp ▸ h.rsp, ?_⟩
  unfold loopR
  rw [show loop (env s) (st s) 0 = R0 s from rfl, hR]
  exact hres

end

section
variable {s : MachineData} {ra : Int64} {t c t' : MachineData}

-- The precondition of `permuteDestinations` at `.LB69`.
theorem lb69_pre (hpre : Pre loopF loopA s) (hb : Base s ra t) (hc : c.dmem = t.dmem)
    (hsp : c.regs.rsp = t.regs.rsp) (hdi : rdi c = rdi s)
    (hperm : IsPerm ((st' s t).slots.map Slot.dest))
    (hops : (st' s t).trace.length + 2 * (st' s t).len ≤ 6 * (env s).n) :
    Pre finishF finishA c := by
  have hrsp : rsp c = rsp s - BitVec.ofNat 64 80 := by
    simp only [rsp, Reg64s.get64_rsp, hsp]; exact hb.rsp
  refine Kit.Fm.pre (by decide) hpre hb.fm hc hrsp hdi ?_
  unfold finishA
  rw [st_call hc hdi, cap_call hpre hb hc hdi]
  refine ⟨hperm, ?_⟩
  show _ ≤ 6 * nOf s.dmem (rdi s)
  rw [← n_envOf]; exact hops

-- The return of `permuteDestinations` gives `At65`.
theorem lb69_out [Host] (hpre : Pre loopF loopA s) (hb : Base s ra t) (hR : R0 s = finish (st' s t))
    (hc : c.dmem = t.dmem) (hsp : c.regs.rsp = t.regs.rsp) (hdi : rdi c = rdi s)
    (hbp : c.regs.rbp = t.regs.rbp) (hp : Post finishF finishR c t')
    (hag : (mod finishF c).Agree c t') : At65 s ra t' := by
  have hb' := Base.call (by decide) hpre hb hp hag hc hsp hdi hbp
  refine ⟨hb'.fm, hb'.rsp, ?_⟩
  unfold loopR
  rw [show loop (env s) (st s) 0 = R0 s from rfl, hR]
  exact finish_post hp hc hdi

end

set_option experimental.vcgen true

/-- The block `movq $-2, %rax; jmp .LB65`. -/
local macro "err_case" : tactic =>
  `(tactic|
    (loop_case
     intro t ht
     kvcgen64
     loop_goto
     · exact stack_of ht.1.rsp
     · exact atErr_out ht rfl rfl rfl
     · simp [V]))

variable [Host] [FunDecls] {s : MachineData} {ra : Int64}

theorem lb90 : OblAt s ra (.label ".LB90") := by err_case
theorem lb92 : OblAt s ra (.label ".LB92") := by err_case
theorem lb94 : OblAt s ra (.label ".LB94") := by err_case
theorem lb96 : OblAt s ra (.label ".LB96") := by err_case
theorem lb97 : OblAt s ra (.label ".LB97") := by err_case
theorem lb98 : OblAt s ra (.label ".LB98") := by err_case
theorem lb99 : OblAt s ra (.label ".LB99") := by err_case

-- The pops and `ret`.
theorem lb65 (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB65") := by
  loop_case
  intro t ht
  have h : At65 s ra t := ht
  clear ht
  kvcgen64
  all_goals bbu_norm at *
  case vc1 => exact h.isSome hpre (k := 56) (by decide) (by have := h.2.1; bv_omega)
  case vc2 => exact h.isSome hpre (k := 48) (by decide) (by have := h.2.1; bv_omega)
  case vc3 => exact h.isSome hpre (k := 40) (by decide) (by have := h.2.1; bv_omega)
  case vc4 => exact h.isSome hpre (k := 32) (by decide) (by have := h.2.1; bv_omega)
  case vc5 => exact h.isSome hpre (k := 24) (by decide) (by have := h.2.1; bv_omega)
  case vc6 => exact h.isSome hpre (k := 16) (by decide) (by have := h.2.1; bv_omega)
  case vc7 => exact h.retSome hpre rfl rfl
  case vc8 => exact h.ret hpre rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- The end of the loop: `0` if `len = n`, else `-2`.
theorem lb66 (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB66") := by
  loop_case
  intro t ht
  have h : At66 s ra t := ht
  clear ht
  kvcgen64
  all_goals bbu_norm at *
  all_goals have w0 : wordAt (rdi s) 0 = rdi s := by simp [wordAt]
  case vc1 =>
    rw [h.1.rbp, ← w0]
    exact h.1.fm.wf.word_isSome h.1.fm.wf.mapped (by decide)
  all_goals
    rename_i hc
    have hn : (env s).n ≤ 1024 := by rw [n_envOf]; exact hpre.1.n_le
    have hl : (st' s t).len < 2 ^ 64 := by rw [len_stOf]; exact BitVec.isLt _
    have e : rd t.dmem t.regs.rbp.toBitVec = BitVec.ofNat 64 (st' s t).len := by
      rw [len_stOf, BitVec.ofNat_toNat, BitVec.setWidth_eq, h.1.rbp, w0]
    rw [Kit.nz_sub, e, h.2.1] at hc
    loop_goto
    · exact stack_of h.1.rsp
    rotate_left
    · simp [V]
  case vc2 =>
    have hne : (st' s t).len ≠ (env s).n := fun h' => by simp [h'] at hc
    show AtErr s ra _
    exact ⟨⟨h.1.fm, h.1.rsp, h.1.rbp⟩, by rw [h.2.2]; simp [hne]⟩
  case vc3 =>
    have heq : (st' s t).len = (env s).n := ofNat_inj64 hl (by omega) (by simpa using hc)
    show At65 s ra _
    refine ⟨h.1.fm, h.1.rsp, ?_⟩
    unfold loopR
    rw [show loop (env s) (st s) 0 = R0 s from rfl, h.2.2]
    simp only [heq, ↓reduceIte]
    exact ⟨rfl, rfl⟩

-- No slot is pending: `permuteDestinations` if `len = n`, else `-2`.
theorem lb69 (hfin : Spec "permuteDestinations" finishF finishA finishR)
    (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB69") := by
  loop_case
  intro t ht
  have h : At69 s ra t := ht
  clear ht
  obtain ⟨hb, h13, h15, T, hctx, ho, hp⟩ := h
  obtain ⟨hR, hperm, hops⟩ := ctx_fin hctx ho hp
  -- No slot is pending, so `len = n`.
  have hlen : (st' s t).len = (env s).n := by have := (ctx_bounds hctx).1; omega
  simp only [hlen, ↓reduceIte] at hR
  kvcgen64
  all_goals bbu_norm at *
  case vc1 =>
    rename_i hc
    rw [Kit.nz_sub, h15, h13, hlen] at hc
    simp at hc
  case vc2 =>
    rw [hb.rsp]
    exact Kit.Mid.call_isSome (k := 80) (by decide) hpre hb.fm.toMid
  case vc3 => exact lb69_pre hpre hb rfl rfl hb.rbp hperm hops
  case vc4 =>
    rename_i t' hpost hag
    have h65 := lb69_out hpre hb hR (by rfl) (by rfl) (by exact hb.rbp) (by rfl) hpost hag
    loop_goto
    · exact stack_of h65.2.1
    · exact h65
    · simp [V]

-- A copy is out of reach for a dup: store the blocked slot and the excess, `-1`.
theorem lb107 (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB107") := by
  loop_case
  intro t ht
  have h : At107 s ra t := ht
  clear ht
  kvcgen64
  all_goals bbu_norm at *
  case vc1 => exact h.1.blk_ld1
  case vc2 => exact h.1.blk_ld2
  case vc3 => exact h.1.blk_ld3 _
  case vc4 => exact h.1.blk_ld4 _
  case vc5 =>
    obtain ⟨c, k, hc, hk, hR⟩ := h.2
    exact h.1.blk_out hpre hc hk hR rfl rfl rfl
  case vc6 => simp [V]

-- The slot at `rsi` is out of reach for a swap.
theorem lb110 (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB110") := by
  loop_case
  intro t ht
  have h : At110 s ra t := ht
  clear ht
  kvcgen64
  all_goals bbu_norm at *
  case vc1 => exact h.1.blk_ld1
  case vc2 => exact h.1.blk_ld2
  case vc3 => exact h.1.blk_ld3 _
  case vc4 => exact h.1.blk_ld4 _
  loop_goto
  · exact stack_of h.1.rsp
  · obtain ⟨c, k, hc, hk, hR⟩ := h.2
    exact h.1.blk_out hpre hc hk hR rfl rfl rfl
  · simp [V]

-- The slot at `r14` is out of reach for a swap.
theorem lb111 (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB111") := by
  loop_case
  intro t ht
  have h : At111 s ra t := ht
  clear ht
  kvcgen64
  all_goals bbu_norm at *
  case vc1 => exact h.1.blk_ld1
  case vc2 => exact h.1.blk_ld2
  case vc3 => exact h.1.blk_ld3 _
  case vc4 => exact h.1.blk_ld4 _
  loop_goto
  · exact stack_of h.1.rsp
  · obtain ⟨c, k, hc, hk, hR⟩ := h.2
    exact h.1.blk_out hpre hc hk hR rfl rfl rfl
  · simp [V]

end Loop

end Bbu
