import BbuKraken.Fn.Loop.Machine
import BbuKraken.Fn.Loop.Model

/-!
The entry of `buildBottomUp`: the prologue, then `.LB62` if `n = 0`, else the loop
head `.LB85` at offset `0`.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

namespace Loop

section
variable {s : MachineData} {ra : Int64}

-- The frame is mapped before the pushes.
theorem map0 (hpre : Pre loopF loopA s) : Mem.Mapped (mod loopF s).mem s.dmem := fun x hx =>
  hx.elim (fun h => hpre.2.1.mapped x (Or.inl h))
    (fun h => hpre.1.mapped x (inside_append.mpr (Or.inl h)))

-- A load of a pushed register.
theorem pro_ld (hpre : Pre loopF loopA s) {m : Mem 64} (hm : Mem.Mapped (mod loopF s).mem m)
    {a : Addr} (ha : 16 ≤ (s.regs.rsp.toBitVec - a).toNat ∧ (s.regs.rsp.toBitVec - a).toNat ≤ 56) :
    (m.loadInt a 8).isSome = true := by
  have hle : 4224 ≤ (rsp s).toNat := hpre.2.1.le
  refine Mem.Mapped.loadInt_isSome hm (Or.inl ?_)
  simp only [loopF_eq, rsp, Reg64s.get64_rsp] at *
  bv_omega

-- The memory after the pushes.
theorem fm0 (hpre : Pre loopF loopA s) : Fm s ra (Kit.pushes s ra regs) :=
  Kit.Fm.init (by decide) hpre

-- The word `n` after the pushes.
theorem n0 (hpre : Pre loopF loopA s) :
    rd (Kit.pushes s ra regs) (s.regs.rdi.toBitVec + 24#64) = BitVec.ofNat 64 (env s).n := by
  rw [n_envOf, ← Kit.Mid.n hpre (fm0 (ra := ra) hpre).toMid, nOf, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]
  rfl

-- The model state after the pushes.
theorem st0 (hpre : Pre loopF loopA s) {t : MachineData} (hm : t.dmem = Kit.pushes s ra regs) :
    st' s t = st s := by
  show stOf t.dmem (rdi s) = _
  rw [hm]
  exact Kit.st_pushes (by decide) hpre

-- The fixed registers after the prologue.
theorem pro_base (hpre : Pre loopF loopA s) {t : MachineData} (hm : t.dmem = Kit.pushes s ra regs)
    (hsp : t.regs.rsp.toBitVec
      = s.regs.rsp.toBitVec - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 24#64)
    (hbp : t.regs.rbp.toBitVec = s.regs.rdi.toBitVec) : Base s ra t :=
  ⟨hm ▸ fm0 hpre, by simp only [hsp, rsp, Reg64s.get64_rsp]; bv_omega, hbp⟩

-- `n = 0`: the loop ends at once.
theorem pro_62 (hpre : Pre loopF loopA s) {t : MachineData} (hm : t.dmem = Kit.pushes s ra regs)
    (hsp : t.regs.rsp.toBitVec
      = s.regs.rsp.toBitVec - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 24#64)
    (hbp : t.regs.rbp.toBitVec = s.regs.rdi.toBitVec)
    (h13 : t.regs.r13.toBitVec = rd (Kit.pushes s ra regs) (s.regs.rdi.toBitVec + 24#64))
    (hz : rd (Kit.pushes s ra regs) (s.regs.rdi.toBitVec + 24#64) = 0#64) : At62 s ra t := by
  have hi : Inv (env s) (st s) 0 := hpre.2.2
  have hn := congrArg BitVec.toNat (hz.symm.trans (n0 hpre))
  have := hi.n_le
  simp only [MAX_N, BitVec.toNat_ofNat] at hn this
  refine ⟨pro_base hpre hm hsp hbp, h13.trans (n0 hpre), ?_⟩
  rw [st0 hpre hm]
  exact loop_end (T := 0) (by omega) rfl

-- `n ≠ 0`: the loop head at offset `0`.
theorem pro_85 (hpre : Pre loopF loopA s) {t : MachineData} (hm : t.dmem = Kit.pushes s ra regs)
    (hsp : t.regs.rsp.toBitVec
      = s.regs.rsp.toBitVec - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 24#64)
    (hbp : t.regs.rbp.toBitVec = s.regs.rdi.toBitVec)
    (h13 : t.regs.r13.toBitVec = rd (Kit.pushes s ra regs) (s.regs.rdi.toBitVec + 24#64))
    (h14 : t.regs.r14.toBitVec = 0#64)
    (hz : ¬ rd (Kit.pushes s ra regs) (s.regs.rdi.toBitVec + 24#64) = 0#64) : At85 s ra t := by
  have hn : (env s).n ≠ 0 := fun h => hz (by rw [n0 hpre, h])
  refine ⟨pro_base hpre hm hsp hbp, h13.trans (n0 hpre), 0, h14, ?_⟩
  rw [st0 hpre hm]
  exact ⟨by omega, ⟨hpre.2.2, Nat.zero_le _⟩, rfl⟩

-- The variant at `.LB85` after the prologue.
theorem pro_v85 (hpre : Pre loopF loopA s) {t : MachineData} (hm : t.dmem = Kit.pushes s ra regs)
    (h14 : t.regs.r14.toBitVec = 0#64) (u : MachineData) :
    V s ".LB85" t < V s "buildBottomUp" u := by
  have hi : Inv (env s) (st s) 0 := hpre.2.2
  have h1 := hi.len_pending
  have h2 := hi.n_le
  simp only [MAX_N] at h2
  simp only [V, outer, st0 hpre hm, h14, W, BitVec.toNat_ofNat]
  omega

end

set_option experimental.vcgen true

variable [Host] [FunDecls] {s : MachineData} {ra : Int64}

-- The entry block.
theorem entry : OblAt s ra .entry := by
  loop_case
  intro t ht
  subst ht
  kvcgen64
  rfl

-- The prologue: the pushes, `n = 0` to `.LB62`, else `.LB85` at offset `0`.
theorem prologue (hpre : Pre loopF loopA s) : OblAt s ra (.label "buildBottomUp") := by
  loop_case
  intro t ht
  subst ht
  kvcgen64
  all_goals bbu_norm at *
  case vc1 | vc2 | vc3 | vc4 | vc5 | vc6 =>
    exact pro_ld hpre (by (repeat apply Mem.Mapped.storeInt); exact map0 hpre) (by bv_omega)
  case vc7 => exact (fm0 hpre).wf.word_isSome (fm0 hpre).wf.mapped (k := 3) (by decide)
  case vc8 =>
    rename_i hc
    have hz : rd (Kit.pushes s ra regs) (s.regs.rdi.toBitVec + 24#64) = 0#64 := by
      rw [Kit.z_test] at hc; exact beq_iff_eq.mp hc
    loop_goto
    · exact stack_of (pro_base (ra := ra) hpre (by rfl) (by rfl) (by rfl)).rsp
    · show At62 s ra _
      exact pro_62 hpre (by rfl) (by rfl) (by rfl) (by rfl) hz
    · simp [V]
  case vc9 =>
    rename_i hc
    have hz : ¬ rd (Kit.pushes s ra regs) (s.regs.rdi.toBitVec + 24#64) = 0#64 := by
      rw [Kit.z_test] at hc; exact fun h => Bool.false_ne_true (hc.symm.trans (beq_iff_eq.mpr h))
    loop_goto
    · exact stack_of (pro_base (ra := ra) hpre (by rfl) (by rfl) (by rfl)).rsp
    · show At85 s ra _
      exact pro_85 hpre (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) hz
    · exact Or.inl (pro_v85 hpre (by rfl) (by rfl) _)

end Loop

end Bbu
