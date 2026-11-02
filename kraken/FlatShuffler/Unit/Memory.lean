module

public import FlatShuffler.Unit.SpillDefs
import all FlatShuffler.Unit.SpillDefs
public import FlatShuffler.Sep.Stores
import all FlatShuffler.Sep.Stores

@[expose] public section

namespace FlatShuffler.Unit
open FlatShuffler.Sep

theorem rd32_b32 {m : Mem 64} {a : Addr} {v : BitVec 32} {F : MProp 64}
    (h : (B32 a v ∗ F).get m) : BitVec.ofInt 32 (m.loadInt a 4).get! = v := by
  unfold B32 at h
  simp only [Mem.loadInt_eq_of_AtM h (Int.toBytes_length _ _) (by decide), Option.get!_some,
    BitVec.ofInt_ofBytes_toBytes 32 4 rfl]

theorem Bs.focus (a : Addr) (bs : List (BitVec 8)) {i : Nat} (hi : i < bs.length)
    (v : BitVec 8) :
    ∃ R, Bs a bs = B8 (a + BitVec.ofNat 64 i) bs[i] ∗ R
      ∧ Bs a (bs.set i v) = B8 (a + BitVec.ofNat 64 i) v ∗ R := by
  induction bs generalizing a i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons b bs ih =>
    cases i with
    | zero => exact ⟨Bs (a + 1#64) bs, by simp [Bs], by simp [Bs]⟩
    | succ i =>
      obtain ⟨R, e1, e2⟩ := ih (a + 1#64) (i := i) (by simpa using hi)
      have ha : a + 1#64 + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (i + 1) := by bv_omega
      refine ⟨B8 a b ∗ R, ?_, ?_⟩
      · simp only [Bs, List.getElem_cons_succ]; rw [e1, ha, sep_lc]
      · simp only [Bs, List.set_cons_succ]; rw [e2, ha, sep_lc]

section
variable {a : Addr} {bs : List (BitVec 8)} {F : MProp 64} {m : Mem 64} {x : Word}

theorem Bs.isSome_word (h : (Bs a bs ∗ F).get m) (hx : x.toNat < bs.length) :
    (m.loadInt (a + x) 1).isSome = true := by
  obtain ⟨R, e1, -⟩ := Bs.focus a bs hx 0#8
  rw [e1, MProp.sep_assoc, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  exact B8.isSome h

theorem Bs.store (h : (Bs a bs ∗ F).get m) (hx : x.toNat < bs.length) (z : Int) :
    (Bs a (bs.set x.toNat (BitVec.ofInt 8 z)) ∗ F).get (m.storeInt (a + x) 1 z) := by
  obtain ⟨R, e1, e2⟩ := Bs.focus a bs hx (BitVec.ofInt 8 z)
  rw [e1, MProp.sep_assoc, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  rw [e2, MProp.sep_assoc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact B8.store h z
end

section
open Std.WP Lean.Order
open scoped Program.WP
variable [Host] [FunDecls] {Q : PUnit → MachineData → Prop} {E : Int64 → MachineData → Prop}

-- `movl disp(%b, %i, 8), %r32`: the write clears the upper half.
theorem movl_idx8_spec (rd b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i * 8#64 + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 4).isSome = true
        ∧ Q () { s with
            regs := s.regs.set64 rd ((BitVec.ofInt 32 (Mem.loadInt s.dmem a 4).get!).zeroExtend 64) } ⦄
      (Directive.instr (.regular .W64 .W32
          (.mov (.reg (.low rd .W32))
            (.regOrMem (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.set_low_W32, AddrExpr.zeroExtend_interp_base_idx8, Width.bytes, hload, Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

end

end FlatShuffler.Unit
