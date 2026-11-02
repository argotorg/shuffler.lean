module

public import FlatShuffler.Unit.Plan.Defs
import all FlatShuffler.Unit.Plan.Defs
public import FlatShuffler.Unit.IsSpilled
import all FlatShuffler.Unit.IsSpilled
public import FlatShuffler.Asm
import all FlatShuffler.Asm
public import ProofKit.Cfg
import all ProofKit.Cfg

@[expose] public section

/-!
# `Planner::isRetained`

`Names.isRetained` in `build/kraken/c/build_bottom_up.S`: no frame, no call, no store. `cmpq $-1, (%rdi,%rsi,8)` reads
`m_destinationOf[rsi]` of the `Mapping` at `rdi`, and `setne %al` gives the result bit.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit

open FlatShuffler.Sep

def isRetainedA (_ : Flat.Mapping) (s : MachineData) : Prop := (rsi s).toNat < MAX_N

def isRetainedQ (M M' : Flat.Mapping) (s t : MachineData) : Prop :=
  M' = M ∧ al t = if Flat.isRetained M (rsi s) then 1#8 else 0#8

theorem isRetained_unit [Host] [FunDecls] :
    VThm MapM (fun _ => True) isRetainedAsm isRetainedA 0 isRetainedQ := by
  intro S M F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨fr, hfr, hk0⟩ := hpre.kg ra
  obtain rfl : fr = [] := List.eq_nil_of_length_eq_zero hfr
  have hrdi : (s.pushRa ra).regs.rdi.toBitVec = S := by
    simpa [MachineData.pushRa] using hpre.rdi
  refine Program.WP.cfg (fun
      | .entry, t => t = s.pushRa ra
      | .label l, t => if l = Names.isRetained then t = s.pushRa ra else False
      | .exit, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_blocks
  case entry t ht =>
    subst ht
    kvcgen64
    simp only [Names.isRetained, ↓reduceIte]
  case «_ZN12_GLOBAL__N_17Planner10isRetainedERKNS_7MappingE11StackOffset» t ht =>
    simp only [Names.isRetained, ↓reduceIte] at ht
    subst ht
    have hp : (rsi s).toNat < MAX_N := hpre.args
    have hm := hk0.vmem
    kvcgen64
    all_goals try symexec_norm
    all_goals try simp only [hrdi, fold_slot, sub_beq_zero, neg_one_eq_none]
    vc_by_shape
    | closed => decide
    | load => exact MapM.isSome_dest hm hp
    | retAddr =>
      exact Option.isSome_iff_exists.mpr ⟨ra, (hk0.next rfl rfl rfl rfl rfl rfl rfl rfl).retAddr⟩
    | ret =>
      refine Kg.vret (ok := fun _ => True) (hk0.next rfl rfl rfl rfl rfl rfl rfl rfl) rfl trivial
        fun t' _ hax => ⟨rfl, ?_⟩
      show (rax t').setWidth 8 = _
      rw [hax]
      simp only [rax, Reg64s.get64_rax, setne_bit]
      have hd : rd (s.pushRa ra).dmem (slotAt S (s.pushRa ra).regs.rsi.toBitVec.toNat) = _ :=
        MapM.rd_dest hm hp
      unfold rd at hd
      rw [hd]
      rfl

end FlatShuffler.Unit
