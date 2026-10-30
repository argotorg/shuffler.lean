import BbuKraken.Unit.Defs
import BbuKraken.Sep.Stores
import ProofKit.Cfg

/-!
# `isSpilled`

`c/bbu/<Names.isSpilled>.S`: no frame, no call, no store. It tests the kind byte and the opcode
byte of the slot, and reads the byte `m_spills[payload]` for a variable.

The callers are `produce` (the slot `m_target[t]`) and `buildBottomUp` (a target slot). The slot
is a target word, so its id is in `splIds` (`isSpilledA`), and the view holds the byte: as a
`Spl` atom, or as a byte of a target word when the byte is in the target (`Sep.splOut`).
`Sep.View.isSome_spl` and `Sep.View.rdb_spl` with `Pre.ok` give the load in both cases.
The callers use `g' = g` and the result bit in `al`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit

open Bbu.Sep

namespace IsSpilled

/-! ## The slot bytes and the flags (after `symexec_norm`) -/

-- `shrq $32`: byte 4 of the slot word is the kind.
theorem kind_byte (w : Word) :
    BitVec.extractLsb' 0 8 (w.ushiftRight 32) = (StackSlot.ofWord w).kind := by
  ext i hi; simp [StackSlot.ofWord]

-- `shrq $40`: byte 5 of the slot word is the opcode.
theorem op_byte (w : Word) :
    BitVec.extractLsb' 0 8 (w.ushiftRight 40) = (StackSlot.ofWord w).valueOpcode := by
  ext i hi; simp [StackSlot.ofWord]

-- `testb %dl, %dl` on the kind byte: `zf` is set iff the slot is a value.
theorem kind_flag (w : Word) :
    (BitVec.extractLsb' 0 8 (w.ushiftRight 32) &&& BitVec.extractLsb' 0 8 (w.ushiftRight 32)
      == BitVec.zero 8) = ((StackSlot.ofWord w).kind == Value) := by
  rw [BitVec.and_self, kind_byte]; rfl

-- `testb %dl, %dl` on the opcode byte: `zf` is set iff the slot is a literal.
theorem op_flag (w : Word) :
    (BitVec.extractLsb' 0 8 (w.ushiftRight 40) &&& BitVec.extractLsb' 0 8 (w.ushiftRight 40)
      == BitVec.zero 8) = ((StackSlot.ofWord w).valueOpcode == Const) := by
  rw [BitVec.and_self, op_byte]; rfl

-- `movl %esi, %esi`: the payload.
theorem payload_word (w : Word) :
    BitVec.setWidth 64 (BitVec.extractLsb' 0 32 w)
      = BitVec.ofNat 64 (StackSlot.ofWord w).payload.toNat := by
  rw [BitVec.ofNat_toNat]; rfl

-- `setne %al` writes the low byte of `rax`.
theorem setWidth_replaceLow (x : Word) (v : BitVec 8) : BitVec.setWidth 8 (x.replaceLow v) = v := by
  conv => rhs; rw [← BitVec.take_replaceLow_8 x v]
  ext i hi
  simp [BitVec.take]

-- `cmpb $0, b; setne %al`: `al` is the bit `b != 0`.
theorem setne_al (x : Word) (b : BitVec 8) :
    BitVec.setWidth 8 (x.replaceLow (BitVec.ofNat 8 (!(b - 0#8 == BitVec.zero 8)).toNat))
      = if (b != 0#8) = true then 1#8 else 0#8 := by
  rw [setWidth_replaceLow, BitVec.sub_zero, BitVec.zero_eq]
  cases h : (b == 0#8) <;> simp [bne, h]

/-! ## `Flat.isSpilled` -/

theorem isSpilled_flat (g : G) (x : StackSlot) :
    Flat.isSpilled (flat g) x
      = (x.kind == Value && !(x.valueOpcode == Const) && g.spl x.payload != 0) := rfl

-- The jump of `jne` (not a value) or of `je` (a literal) to `.LB1`: not spilled.
theorem not_spilled {fs : Flat.St} {x : StackSlot}
    (h : (!(x.kind == Value)) = true ∨ (x.valueOpcode == Const) = true) :
    Flat.isSpilled fs x = false := by
  unfold Flat.isSpilled isLiteralValue
  rcases h with h | h <;> simp_all

-- Both jumps fall through: the slot is a variable, and its id is the payload.
theorem spillId_eq {x : StackSlot} (hk : (!(x.kind == Value)) = false)
    (ho : (x.valueOpcode == Const) = false) : spillId x = some x.payload.toNat := by
  simp only [Bool.not_eq_eq_eq_not, Bool.not_false, beq_iff_eq, beq_eq_false_iff_ne] at hk ho
  simp [spillId, hk, ho]

-- The result of the fall-through: the byte of the payload.
theorem al_spilled {g : G} {x : StackSlot} (hk : (!(x.kind == Value)) = false)
    (ho : (x.valueOpcode == Const) = false) :
    (if (g.spl (BitVec.ofNat 32 x.payload.toNat) != 0#8) = true then 1#8 else 0#8)
      = if Flat.isSpilled (flat g) x then 1#8 else 0#8 := by
  simp only [Bool.not_eq_eq_eq_not, Bool.not_false, beq_iff_eq, beq_eq_false_iff_ne] at hk ho
  rw [isSpilled_flat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp [hk, ho]

/-! ## The word `m_spills` -/

variable {S : Addr} {g : G} {F : MProp 64} {m : Mem 64}

theorem rd_spills (h : (View S g ∗ F).get m) : rd m (Fld.spills S) = g.h.spl :=
  rd_of_eq h (by unfold View Em; ecancel)

theorem isSome_spills (h : (View S g ∗ F).get m) : (m.loadInt (Fld.spills S) 8).isSome = true :=
  isSome_of_eq g.h.spl h (by unfold View Em; ecancel)

-- The address of the byte that `cmpb $0, (%rax,%rsi)` reads.
theorem spl_addr (h : (View S g ∗ F).get m) (w : Word) :
    BitVec.ofInt 64 (m.loadInt (Fld.spills S) 8).get!
        + BitVec.setWidth 64 (BitVec.extractLsb' 0 32 w)
      = g.h.spl + BitVec.ofNat 64 (StackSlot.ofWord w).payload.toNat := by
  rw [payload_word]; exact congrArg (· + _) (rd_spills h)

end IsSpilled

open IsSpilled in
theorem isSpilled_unit [Host] [FunDecls] : UnitThm isSpilledAsm isSpilledA 0 isSpilledQ := by
  intro S g F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨fr, v, hfr, hm⟩ := hpre.mem
  obtain rfl : fr = [] := List.eq_nil_of_length_eq_zero hfr
  have hk0 : Kp S g F s ra [] (s.pushRa ra) := Kp.init hm
  have hS : (s.pushRa ra).regs.rdi.toBitVec + 16#64 = Fld.spills S := by
    rw [show (s.pushRa ra).regs.rdi.toBitVec = S by simpa [MachineData.pushRa] using hpre.rdi]; rfl
  refine Program.WP.cfg (fun
      | .entry, t => t = s.pushRa ra
      | .label l, t =>
        if l = Names.isSpilled then t = s.pushRa ra
        else if l = ".LB1" then Kp S g F s ra [] t
          ∧ al t = if Flat.isSpilled (flat g) (StackSlot.ofWord (rsi s)) then 1#8 else 0#8
        else False
      | .exit, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_blocks
  case entry t ht =>
    subst ht
    kvcgen64
    simp only [Names.isSpilled, ↓reduceIte]
  case «.LB1» t ht =>
    simp only [Names.isSpilled, String.reduceEq, ↓reduceIte] at ht
    obtain ⟨hk, hal⟩ := ht
    kvcgen64
    vc_by_shape
    | retAddr => simp [hk.retAddr]
    | ret =>
      exact Kp.ret hk rfl hpre.ok fun t' _ hax =>
        ⟨rfl, by show (rax t').setWidth 8 = _; rw [hax]; exact hal⟩
  case «_ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot» t ht =>
    simp only [Names.isSpilled, ↓reduceIte] at ht
    subst ht
    kvcgen64
    all_goals try symexec_norm
    all_goals try simp only [kind_flag, op_flag] at *
    all_goals try simp only [hS]
    vc_by_shape
    | closed => decide
    | goto ".LB1" =>
      -- `jne` (not a value) or `je` (a literal): `al = 0`.
      have hn : Flat.isSpilled (flat g) (StackSlot.ofWord s.regs.rsi.toBitVec) = false :=
        not_spilled (by first | exact Or.inl ‹_› | exact Or.inr ‹_›)
      cfg_goto
      · exact (hk0.next rfl rfl rfl rfl rfl rfl rfl rfl).stack
      · simp only [Names.isSpilled, String.reduceEq, ↓reduceIte]
        refine ⟨hk0.next rfl rfl rfl rfl rfl rfl rfl rfl, ?_⟩
        simp only [hn, Bool.false_eq_true, ↓reduceIte]
        rfl
      · simp
    | load =>
      -- `cmpb $0, (%rax,%rsi)` reads `m_spills[payload]`; `movq 16(%rdi), %rax` reads `m_spills`.
      first
      | rw [spl_addr hk0.mem]
        exact View.isSome_spl hk0.mem hpre.ok (hpre.args _ (spillId_eq ‹_› ‹_›))
      | exact isSome_spills hk0.mem
    | other =>
      -- The fall-through to `.LB1`: `al` is the byte `m_spills[payload] != 0`.
      have hi := hpre.args _ (spillId_eq ‹_› ‹_›)
      simp only [Names.isSpilled, String.reduceEq, ↓reduceIte]
      refine ⟨hk0.next rfl rfl rfl rfl rfl rfl rfl rfl, ?_⟩
      rw [setne_al, spl_addr hk0.mem]
      exact (congrArg (fun b => if (b != 0#8) = true then 1#8 else 0#8)
        (View.rdb_spl hk0.mem hpre.ok hi)).trans (al_spilled ‹_› ‹_›)

end Bbu.Unit
