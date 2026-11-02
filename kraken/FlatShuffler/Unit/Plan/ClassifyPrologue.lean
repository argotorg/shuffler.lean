module

public import FlatShuffler.Unit.Plan.ClassifyPrologueTail
import all FlatShuffler.Unit.Plan.ClassifyPrologueTail

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit.ClassifyU
open FlatShuffler.Sep

set_option maxRecDepth 4096 in
theorem b_fn [Host] [FunDecls]
    (P : Addr) (c : CG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (hok : c.Ok) (ha : classifyA c s) (hdi : rdi s = P)
    (xs : List Word) (hl : xs.length = 16)
    (hk : Kg (CView P c ∗ F) s ra xs (s.pushRa ra)) :
    classifyAsm.ForallBlocks fun blk => blk.label = .label Names.classify →
      Obl P c F s ra blk := by
  simp only [Names.classify]
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.classify, ↓reduceIte] at ht
  subst t
  obtain ⟨lo, w, q, hps, hb, _, _⟩ := prologue_frame hl hk
  simp only [pushRegs, PushOk] at hps
  rcases hps with ⟨k0, k1, k2, k3, k4, k5, _⟩
  vcgen (stepLimit := 14) simplifying_assumptions [Reg64s.set64_rsp,
    Reg64s.get64_rsp, Reg64s.get64_r15, Reg64s.get64_r14, Reg64s.get64_r13,
    Reg64s.get64_r12, Reg64s.get64_rbp, Reg64s.get64_rbx,
    MachineData.regs_mk, MachineData.dmem_mk, MachineData.zmms_mk,
    MachineData.status_mk, UInt64.toBitVec_ofBitVec, MachineState.data_mk,
    Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat]
  all_goals try symexec_norm at ⊢
  all_goals try rw [prologue_sp] at ⊢
  vc_by_shape
  | load => run_loads [k0, k1, k2, k3, k4, k5]
  | other =>
    apply prologue_tail P c F s ra hok ha _ lo w q
    · apply hb.next <;> rfl
    · exact hdi
    · exact ha.1.1
    · exact ha.1.2.1
    · rfl

end FlatShuffler.Unit.ClassifyU
