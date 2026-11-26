module

public import Kraken.X64.WP.Instance
public import Kraken.SeparationMem
public import Kraken.Specs
public import Kraken.Blocks

open Std.WP
open Lean.Order

@[expose] public section

/-! ## Calls -/

def MachineData.push64 (s : MachineData) (v : Int64) : MachineData :=
  { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64),
           dmem := Mem.storeInt s.dmem (s.regs.get64 .rsp - 8#64) 8 v.toBitVec.toInt }

@[grind =] theorem MachineData.regs_push64 (s : MachineData) (v : Int64) :
    (s.push64 v).regs = s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64) := rfl

@[grind =] theorem MachineData.dmem_push64 (s : MachineData) (v : Int64) :
    (s.push64 v).dmem = Mem.storeInt s.dmem (s.regs.get64 .rsp - 8#64) 8 v.toBitVec.toInt := rfl

@[grind =] theorem Int64.ofBitVec_ofBytes_toBytes (ra : Int64) :
    Int64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 ra.toBitVec.toInt))) = ra := by
  rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_toInt, Int64.ofBitVec_toBitVec]

@[grind =] theorem MachineData.retAddr_push64 (s : MachineData) (ra : Int64) :
    (s.push64 ra).retAddr = some ra := by
  simp only [MachineData.retAddr, MachineData.push64, Reg64s.get64_set64, reduceIte,
    Mem.loadInt_storeInt_64, Option.map_some,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_toInt, Int64.ofBitVec_toBitVec]

namespace Program.WP

variable [Host] [FunDecls]

theorem MachineData.stackBelow_push64 (s : MachineData) (ra : Int64) : (s.push64 ra).StackBelow s := by
  simp only [MachineData.StackBelow, MachineData.push64, Reg64s.set64_rsp, Reg64s.get64_rsp, Reg64s.rsp_mk,
    UInt64.toBitVec_ofBitVec]
  exact BitVec.serialLt_sub _ _ (by decide)

def _root_.FunDecls.body (f : Label) : Program := ((FunDecls.at (label f)).map Fragment.prog).getD []

theorem _root_.FunDecls.body_eq {f : Label} {g : Fragment} (hg : FunDecls.at (label f) = some g) :
    FunDecls.body f = g.prog := by
  simp [FunDecls.body, hg]

open Classical in
theorem wp_call_iff {f : Label} {g : Fragment} (hg : FunDecls.at (label f) = some g) {asz osz : Width}
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData} :
    WP.wp (Directive.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction))))) Q E s ↔
      ∀ [h : Embeds [Directive.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction))))]],
        (Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true ∧
        WP.wp (FunDecls.body f) (fun _ _ => False)
          (fun a s' => if a = h.embedding.endAddr then Q () s' else E a s') (s.push64 h.embedding.endAddr) := by
  rw [FunDecls.body_eq hg]
  have nd := Program.noInternal_of_noLabels
    (p := [Directive.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction))))]) rfl
  constructor
  · intro hw H
    have hw : Program.wp _ (fun st => Q () st.data) (fun st => E st.pc st.data) s := hw
    rw [Program.wp_eq] at hw
    have hw := @hw H
    simp only [Program.continueOnInternalExit_of_noInternal nd] at hw
    have hk := H.embedding.isInfixAt
    have hd := Host.exe_getElem? H.embedding.start
    rw [hk.cons.1, Option.map_some] at hd
    have hz : 0 < Kraken.Layout.size Directive H.embedding.start :=
      Host.instr_size_pos _ _ hk.cons.1 (by rintro ⟨⟩)
    have hft : Host.exe.fallthrough H.embedding.startAddr = H.embedding.endAddr :=
      Host.fallthrough_addrOf hd hz
    have hne : H.embedding.startAddr ≠ H.embedding.endAddr := Host.addrOf_succ_ne hd hz
    unfold While at hw
    cases hw with
    | done _ h => exact absurd hne h.1
    | step _ mid ht hrest =>
      have hst := ht.2
      let probe : Prop → Effects := fun c => if c then .done ⟨s, 0⟩ else .unimplemented ""
      have hprobe : ∀ c, (probe c).All (fun _ => True) ↔ c := fun c => by
        by_cases hc : c <;> simp [probe, hc, Effects.All]
      have t := Host.stepIn_elim hd hz hst (P := fun _ => True) (ret := fun u => probe (mid u))
        (jmp := fun u => probe (Host.exe.StepOut (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
          ⟨s, H.embedding.startAddr⟩ mid (fun st => E st.pc st.data) u))
        (fun _ h => (hprobe _).mpr h) (fun _ h => (hprobe _).mpr h)
      cases hload : Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8 with
      | none =>
        simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
          ConstExpr.interp, MachineData.store, hload, Effects.All] at t
      | some i =>
        refine ⟨rfl, ?_⟩
        simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
          ConstExpr.interp, MachineData.store, hload, Effects.All] at t
        rw [Int64.ofBitVec_toBitVec, Int64.add_sub_self_left] at t
        have t := (hprobe (Host.exe.StepOut (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
          ⟨s, H.embedding.startAddr⟩ mid (fun st => E st.pc st.data)
          ⟨s.push64 H.embedding.endAddr, label f⟩)).mp t
        unfold Executable.StepOut at t
        simp only [hg, Option.map_some, MachineData.stackBelow_push64, ite_true] at t
        rw [hft] at t
        refine Program.wp_mono (fun _ h => h) ?_ t
        intro u hu
        by_cases hpc : u.pc = H.embedding.endAddr
        · simp only [hpc, ite_true] at hu ⊢
          have hr := hrest u hu
          unfold While at hr
          cases hr with
          | done _ h => exact h.2
          | step _ _ ht' _ => exact absurd hpc ht'.1
        · simp only [hpc, ite_false] at hu ⊢
          exact hu
  · intro hr
    refine Program.wp_single fun h _ _ _ _ hj => ?_
    obtain ⟨hmapped, hbody⟩ := @hr h
    obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
    simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
      ConstExpr.interp, MachineData.store, hload, Effects.All]
    rw [Int64.ofBitVec_toBitVec, Int64.add_sub_self_left]
    refine hj (label f) (s.push64 h.embedding.endAddr) ?_
    unfold Executable.StepOut
    simp only [hg, Option.map_some, MachineData.stackBelow_push64, ite_true]
    have hk := h.embedding.isInfixAt
    have hd := Host.exe_getElem? h.embedding.start
    rw [hk.cons.1, Option.map_some] at hd
    have hz : 0 < Kraken.Layout.size Directive h.embedding.start :=
      Host.instr_size_pos _ _ hk.cons.1 (by rintro ⟨⟩)
    have hft : Host.exe.fallthrough h.embedding.startAddr = h.embedding.endAddr :=
      Host.fallthrough_addrOf hd hz
    rw [hft]
    refine Program.wp_mono (fun _ h => h) ?_ hbody
    intro u hu
    by_cases hpc : u.pc = h.embedding.endAddr
    · simp only [hpc, ite_true] at hu ⊢
      exact ⟨trivial, hu⟩
    · simp only [hpc, ite_false] at hu ⊢
      exact hu

end Program.WP

end

namespace Program.WP

public theorem MachineData.not_stackBelow_self (s : MachineData) : ¬ s.StackBelow s :=
  BitVec.not_serialLt_self _

public theorem MachineData.not_stackBelow_pop (s : MachineData) :
    ¬ ({ s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64) } : MachineData).StackBelow s := by
  simp only [MachineData.StackBelow, Reg64s.set64_rsp, Reg64s.get64_rsp, Reg64s.rsp_mk, UInt64.toBitVec_ofBitVec]
  exact (BitVec.serialLt_add _ _ (by decide)).asymm

end Program.WP

public def Program.cfg (p : Program) : Program := p

public theorem Program.cfg_eq (p : Program) : Program.cfg p = p := by
  unfold Program.cfg; rfl

namespace Program.WP.Spec

variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

@[spec] public theorem nil : ⦃ fun s => Q () s ⦄ ([] : Program) ⦃ Q; E ⦄ :=
  Triple.intro fun _ hq => Program.wp_nil fun _ => hq

@[spec] public theorem cons (d : Directive) (p : Program) :
    ⦃ fun s => (Program.labels (d :: p) = [] → WP.wp (Program.straight (d :: p)) Q E s)
               ∧ (Program.labels (d :: p) ≠ [] → WP.wp (Program.cfg (d :: p)) Q E s) ⦄ (d :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun _ ⟨hl, hc⟩ => by
    by_cases h : Program.labels (d :: p) = []
    · rw [← Program.straight_eq_self_of_labels h]
      exact hl h
    · rw [← Program.cfg_eq (d :: p)]
      exact hc h

@[spec] public theorem straight_nil : ⦃ fun s => Q () s ⦄ Program.straight [] ⦃ Q; E ⦄ :=
  Triple.intro fun _ hq => Program.wp_nil fun _ => hq

@[spec] public theorem straight_instr (i : Instr) (p : Program) :
    ⦃ fun s => WP.wp (Directive.instr i) (fun _ => WP.wp (Program.straight p) Q E) E s ⦄
      Program.straight (Directive.instr i :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun _ hw => by
    rw [Program.straight_cons_instr]
    exact Program.wp_cons (by rw [Program.labels_cons_instr]; exact Program.labels_straight p) hw

@[spec] public theorem straight_label (l : Label) (p : Program) :
    ⦃ fun s => WP.wp (Program.straight p) Q E s ⦄ Program.straight (Directive.label l :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun _ hw => by
    rw [Program.straight_cons_label]
    exact hw

@[spec] public theorem straight_byteArray (a : ByteArray) (p : Program) :
    ⦃ fun s => WP.wp (Directive.byteArray a) (fun _ => WP.wp (Program.straight p) Q E) E s ⦄
      Program.straight (Directive.byteArray a :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun _ hw => by
    rw [Program.straight_cons_byteArray]
    exact Program.wp_cons (by rw [Program.labels_cons_byteArray]; exact Program.labels_straight p) hw

@[spec] public theorem append (p q : Program) :
    ⦃ fun s => WP.wp (Program.cfg (p ++ q)) Q E s ⦄ (p ++ q) ⦃ Q; E ⦄ :=
  Triple.intro fun _ hw => by rwa [Program.cfg_eq] at hw

@[spec] public theorem mov_reg_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r (BitVec.setWidth 64 i.toBitVec) } ⦄
      (Directive.instr (.regular asz .W64 (.mov (.reg (.low r .W64)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    MachineData.set, MachineData.setReg, Reg64s.set_low_W64, Effects.All, ite_true]
  exact hn _ hpre

@[spec] public theorem mov_mem_reg (b : Reg64) (d : Int64) (rs : Reg64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8).isSome = true
        ∧ Q () { s with
            dmem := Mem.storeInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8
              (s.regs.get64 rs).toInt } ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩)
            (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store, Reg64s.get_low_W64,
    AddrExpr.zeroExtend_interp_base_disp, hload, Effects.All, ite_true]
  exact hn _ hpre

@[spec] public theorem add_reg_mem (rd b : Reg64) (d : Int64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8).isSome = true ∧
          let a := BitVec.ofInt 64 (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8).get!
          Q () { s with regs := s.regs.set64 rd (a + s.regs.get64 rd), status := StatusFlags.ofAdd a (s.regs.get64 rd) } ⦄
      (Directive.instr (.regular .W64 .W64
          (.add (.reg (.low rd .W64))
            (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.get_low_W64, Reg64s.set_low_W64, AddrExpr.zeroExtend_interp_base_disp,
    hload, Effects.All, ite_true]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

@[spec] public theorem mov_reg_sib8 (r b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 8).isSome = true
          ∧ Q () { s with regs := s.regs.set64 r (BitVec.ofInt 64 (Mem.loadInt s.dmem a 8).get!) } ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg, Reg64s.set_low_W64,
    AddrExpr.zeroExtend_interp_sib, hv, Effects.All, ite_true]
  exact hn _ (by rwa [hv, Option.get!_some] at hq)

@[spec] public theorem mov_sib8_reg (b i : Reg64) (d : Int64) (rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 8).isSome = true
          ∧ Q () { s with dmem := Mem.storeInt s.dmem a 8 (s.regs.get64 rs).toInt } ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store, Reg64s.get_low_W64,
    AddrExpr.zeroExtend_interp_sib, hv, Effects.All, ite_true]
  exact hn _ hq

@[spec] public theorem add_reg_sib8 (rd b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 8).isSome = true ∧
          let x := BitVec.ofInt 64 (Mem.loadInt s.dmem a 8).get!
          Q () { s with regs := s.regs.set64 rd (x + s.regs.get64 rd), status := StatusFlags.ofAdd x (s.regs.get64 rd) } ⦄
      (Directive.instr (.regular .W64 .W64
          (.add (.reg (.low rd .W64)) (.regOrMem (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.get_low_W64, Reg64s.set_low_W64, AddrExpr.zeroExtend_interp_sib,
    hv, Effects.All, ite_true]
  exact hn _ (by rwa [hv, Option.get!_some] at hq)

local macro "run_step" : tactic =>
  `(tactic| simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
      RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp, MachineData.set, MachineData.setReg,
      Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All, ite_true])

@[spec] public theorem label_directive (l : Label) :
    ⦃ fun s => Q () s ⦄ (Directive.label l) ⦃ Q; E ⦄ :=
  Triple.intro fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by run_step; exact hn _ hq

@[spec] public theorem nop (asz osz : Width) (n : Nat) :
    ⦃ fun s => Q () s ⦄ (Directive.instr (.regular asz osz (.nop n))) ⦃ Q; E ⦄ :=
  Triple.intro fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by run_step; exact hn _ hq

@[spec] public theorem sub_reg_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := BitVec.setWidth 64 i.toBitVec
        Q () { s with regs := s.regs.set64 r (s.regs.get64 r - a), status := StatusFlags.ofSub (s.regs.get64 r) a } ⦄
      (Directive.instr (.regular asz .W64 (.sub (.reg (.low r .W64)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  exact hn _ hpre

@[spec] public theorem mulx_reg_reg_reg (asz : Width) (hi lo rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rs).unsigned * (s.regs.get64 .rdx).unsigned
        Q () { s with regs :=
          (s.regs.set64 lo (BitVec.ofInt 64 v)).set64 hi (BitVec.ofInt 64 (v >>> 64)) } ⦄
      (Directive.instr (.regular asz .W64 (.mulx (.low hi .W64) (.low lo .W64) (.reg (.low rs .W64)))))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by run_step; exact hn _ hq

@[spec] public theorem add_reg_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := BitVec.setWidth 64 i.toBitVec
        Q () { s with regs := s.regs.set64 r (a + s.regs.get64 r), status := StatusFlags.ofAdd a (s.regs.get64 r) } ⦄
      (Directive.instr (.regular asz .W64 (.add (.reg (.low r .W64)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  exact hn _ hpre

@[spec] public theorem adc_reg_reg (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := s.regs.get64 rs + s.regs.get64 rd + BitVec.ofNat 64 s.status.cf.toNat
        Q () { s with
          regs := s.regs.set64 rd v
          status := StatusFlags.from_result v
            { cf := BitVec.carry 64 (s.regs.get64 rs) (s.regs.get64 rd) s.status.cf,
              af := BitVec.carry 4 (s.regs.get64 rs) (s.regs.get64 rd) s.status.cf,
              of := BitVec.saddcOverflow (s.regs.get64 rs) (s.regs.get64 rd) s.status.cf } } ⦄
      (Directive.instr (.regular asz .W64
          (.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  rw [BitVec.unsigned_add_add_bne, BitVec.unsigned_take_add_add_bne _ _ _ (by decide),
    BitVec.signed_add_add_bne]
  exact hn _ hpre

@[spec] public theorem add_reg_reg (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        Q () { s with regs := s.regs.set64 rd (s.regs.get64 rs + s.regs.get64 rd), status := StatusFlags.ofAdd (s.regs.get64 rs) (s.regs.get64 rd) } ⦄
      (Directive.instr (.regular asz .W64
          (.add (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  exact hn _ hpre

@[spec] public theorem mov_reg_reg (asz : Width) (rd rs : Reg64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 rd (s.regs.get64 rs) } ⦄
      (Directive.instr (.regular asz .W64 (.mov (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  exact hn _ hpre

@[spec] public theorem lea_reg_label (rd : Reg64) (l : Label) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 rd (label l).toBitVec } ⦄
      (Directive.instr (.regular .W64 .W64 (.lea (.low rd .W64)
        { base := some .rip, idx := none, disp := .sub (.label l) .after_current_instruction })))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  simp only [AddrExpr.interp, ConstExpr.interp, Int.add_zero]
  rw [show BitVec.zeroExtend Width.W64.bits (BitVec.ofInt Width.W64.bits
      (Embeds.embedding.endAddr.toInt + (label l - Embeds.embedding.endAddr).toInt)) = (label l).toBitVec by
    simp only [Int64.toInt, BitVec.ofInt_add, BitVec.ofInt_toInt, Int64.toBitVec_sub]
    show BitVec.setWidth 64 _ = _
    rw [BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]]
  exact hn _ hpre

@[spec] public theorem cmp_reg_reg (asz : Width) (ra rb : Reg64) :
    ⦃ fun s =>
        Q () { s with status := StatusFlags.ofSub (s.regs.get64 ra) (s.regs.get64 rb) } ⦄
      (Directive.instr (.regular asz .W64
          (.cmp (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  exact hn _ hpre

@[spec] public theorem test_reg_reg (asz : Width) (ra rb : Reg64) :
    ⦃ fun s =>
        ∀ af : Bool, Q () { s with
          status := StatusFlags.ofLogic (s.regs.get64 ra &&& s.regs.get64 rb) af } ⦄
      (Directive.instr (.regular asz .W64
          (.test (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  intro af
  exact hn _ (hpre af)

@[spec] public theorem mov_reg8_mem (r b : Reg64) (d : Int64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 1).isSome = true
        ∧ Q () { s with regs := s.regs.set (.low r .W8)
                              (BitVec.ofInt 8 (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 1).get!) } ⦄
      (Directive.instr (.regular .W64 .W8
          (.mov (.reg (.low r .W8)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All, ite_true]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

@[spec] public theorem mov_mem_reg8 (b : Reg64) (d : Int64) (r : Reg64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 1).isSome = true
        ∧ Q () { s with
            dmem := Mem.storeInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 1
              (BitVec.toInt (n := 8) (s.regs.get (.low r .W8))) } ⦄
      (Directive.instr (.regular .W64 .W8
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low r .W8))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All, ite_true]
  exact hn _ hpre

@[spec] public theorem mov_reg16_mem (r b : Reg64) (d : Int64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 2).isSome = true
        ∧ Q () { s with regs := s.regs.set (.low r .W16)
                              (BitVec.ofInt 16 (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 2).get!) } ⦄
      (Directive.instr (.regular .W64 .W16
          (.mov (.reg (.low r .W16)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

@[spec] public theorem mov_mem_reg16 (b : Reg64) (d : Int64) (r : Reg64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 2).isSome = true
        ∧ Q () { s with
            dmem := Mem.storeInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 2
              (BitVec.toInt (n := 16) (s.regs.get (.low r .W16))) } ⦄
      (Directive.instr (.regular .W64 .W16
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low r .W16))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All]
  exact hn _ hpre

@[spec] public theorem mov_reg32_mem (r b : Reg64) (d : Int64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 4).isSome = true
        ∧ Q () { s with regs := s.regs.set (.low r .W32)
                              (BitVec.ofInt 32 (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 4).get!) } ⦄
      (Directive.instr (.regular .W64 .W32
          (.mov (.reg (.low r .W32)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

@[spec] public theorem mov_mem_reg32 (b : Reg64) (d : Int64) (r : Reg64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 4).isSome = true
        ∧ Q () { s with
            dmem := Mem.storeInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 4
              (BitVec.toInt (n := 32) (s.regs.get (.low r .W32))) } ⦄
      (Directive.instr (.regular .W64 .W32
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low r .W32))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All]
  exact hn _ hpre

@[spec] public theorem xor_reg_reg (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := s.regs.get64 rd ^^^ s.regs.get64 rs
        ∀ af : Bool, Q () { s with regs := s.regs.set64 rd v, status := StatusFlags.ofLogic v af } ⦄
      (Directive.instr (.regular asz .W64
          (.xor (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  intro af
  exact hn _ (hpre af)

@[spec] public theorem dec_reg (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        Q () { s with regs := s.regs.set64 r (s.regs.get64 r - 1), status := StatusFlags.ofDec (s.regs.get64 r) s.status.cf } ⦄
      (Directive.instr (.regular asz .W64 (.dec (.reg (.low r .W64)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  exact hn _ hpre

@[spec] public theorem inc_reg (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        Q () { s with regs := s.regs.set64 r (s.regs.get64 r + 1), status := StatusFlags.ofInc (s.regs.get64 r) s.status.cf } ⦄
      (Directive.instr (.regular asz .W64 (.inc (.reg (.low r .W64)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  exact hn _ hpre

@[spec] public theorem xor_reg32_reg32 (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rd).take 32 ^^^ (s.regs.get64 rs).take 32
        ∀ af : Bool,
          Q () { s with regs := s.regs.set64 rd (v.zeroExtend 64), status := StatusFlags.ofLogic v af } ⦄
      (Directive.instr (.regular asz .W32
          (.xor (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  simp only [Reg64s.get_low_W32, Reg64s.set_low_W32]
  intro af
  exact hn _ (hpre af)

@[spec] public theorem cmp_reg_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        Q () { s with status := StatusFlags.ofSub (s.regs.get64 r) (BitVec.setWidth 64 i.toBitVec) } ⦄
      (Directive.instr (.regular asz .W64 (.cmp (.reg (.low r .W64)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by run_step; exact hn _ hq

@[spec] public theorem and_reg_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := s.regs.get64 r &&& BitVec.setWidth 64 i.toBitVec
        ∀ af : Bool, Q () { s with regs := s.regs.set64 r v, status := StatusFlags.ofLogic v af } ⦄
      (Directive.instr (.regular asz .W64 (.and (.reg (.low r .W64)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by run_step; exact fun af => hn _ (hq af)

@[spec] public theorem shl_reg32_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let n := i.toBitVec.toNat % 32
        n ≠ 0 ∧ ∀ st : StatusFlags, Q () { s with
          regs := s.regs.set64 r ((((s.regs.get64 r).take 32) <<< n).zeroExtend 64)
          status := st } ⦄
      (Directive.instr (.regular asz .W32 (.shl (.reg (.low r .W32)) (.imm8 (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hz, hq⟩ => Program.wp_single fun _ _ _ _ hn _ => ?_
  have hc : ∀ (L : Labels) rng,
      @ShiftCountExpr.interpMasked L (.imm8 (.int64 i)) s rng Width.W32
        = i.toBitVec.toNat % 32 := fun _ _ => by
    show (i.toBitVec.take 8).toNat &&& (2 ^ 5 - 1) = _
    rw [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (by decide)]
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W32, Reg64s.set_low_W32, hc, hz,
    beq_iff_eq, ite_false, Effects.All]
  repeat (first | exact hn _ (hq _) | intro _ | split | simp only [Effects.All])

local macro "run_avx" : tactic =>
  `(tactic| simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
      MachineData.setAvx, MachineData.setAvxReg, Effects.All, ite_true])

@[spec] public theorem vxorps_vreg_vreg_vreg {w : AvxWidth} (asz : Width) (dst src1 src2 : AvxReg w) :
    ⦃ fun s => Q () { s with zmms := s.zmms.set dst (s.zmms.get src1 ^^^ s.zmms.get src2) } ⦄
      (Directive.instr (.avx asz w (.vxorps dst src1 (.avx src2))))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by run_avx; exact hn _ hq

@[spec] public theorem vaddps_vreg_vreg_vreg {w : AvxWidth} (asz : Width) (dst src1 src2 : AvxReg w) :
    ⦃ fun s => Q () { s with zmms := (s.zmms.set dst
        (BitVec.packedBinOp 32 (sseBinOp (· + ·)) (s.zmms.get src1) (s.zmms.get src2))) } ⦄
      (Directive.instr (.avx asz w (.vaddps dst src1 (.avx src2))))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by run_avx; exact hn _ hq

@[spec] public theorem vshufps_vreg_vreg_vreg_imm {w : AvxWidth} (asz : Width) (dst src1 src2 : AvxReg w)
    (imm : UInt8) :
    ⦃ fun s => Q () { s with zmms := (s.zmms.set dst
        (BitVec.packedBinOp 128 (BitVec.shufps128 imm) (s.zmms.get src1) (s.zmms.get src2))) } ⦄
      (Directive.instr (.avx asz w (.vshufps dst src1 (.avx src2) imm)))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by run_avx; exact hn _ hq

@[spec] public theorem vextractf128_vreg_vreg_imm {w : AvxWidth} (asz : Width) (dst : AvxReg .W128)
    (src : AvxReg .W256) (imm : UInt8) :
    ⦃ fun s => Q () { s with zmms := (s.zmms.set dst
        ((s.zmms.get src).extractLsb' (128 * (imm.toNat % 2)) 128)) } ⦄
      (Directive.instr (.avx asz w (.vextractf128 dst src imm)))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by run_avx; exact hn _ hq

@[spec] public theorem vmovhlps_vreg_vreg_vreg {w : AvxWidth} (asz : Width) (dst src1 src2 : AvxReg .W128) :
    ⦃ fun s => Q () { s with zmms := (s.zmms.set dst
        ((s.zmms.get src1).extractLsb' 64 64 ++ (s.zmms.get src2).extractLsb' 64 64)) } ⦄
      (Directive.instr (.avx asz w (.vmovhlps dst src1 src2)))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by run_avx; exact hn _ hq

@[spec] public theorem vmovss_vreg_vreg_vreg {w : AvxWidth} (asz : Width) (dst src1 src2 : AvxReg .W128) :
    ⦃ fun s => Q () { s with zmms := (s.zmms.set dst
        ((s.zmms.get src1).extractLsb' 32 96 ++ (s.zmms.get src2).extractLsb' 0 32)) } ⦄
      (Directive.instr (.avx asz w (.vmovss dst src1 src2)))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by run_avx; exact hn _ hq

@[spec] public theorem vaddss_vreg_vreg_vreg {w : AvxWidth} (asz : Width) (dst src1 src2 : AvxReg .W128) :
    ⦃ fun s => Q () { s with zmms := (s.zmms.set dst
        ((s.zmms.get src1).extractLsb' 32 96
          ++ sseBinOp (· + ·) ((s.zmms.get src1).extractLsb' 0 32)
            ((s.zmms.get src2).extractLsb' 0 32))) } ⦄
      (Directive.instr (.avx asz w (.vaddss dst src1 src2)))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by run_avx; exact hn _ hq

@[spec] public theorem vzeroupper {w : AvxWidth} (asz : Width) :
    ⦃ fun s => Q () { s with zmms := s.zmms.zeroUpper } ⦄
      (Directive.instr (.avx asz w .vzeroupper))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by run_avx; exact hn _ hq

@[spec] public theorem vmovups_vreg_sib1 (y : AvxReg .W256) (b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 32).isSome = true
          ∧ Q () { s with zmms := s.zmms.set y (BitVec.ofInt 256 (Mem.loadInt s.dmem a 32).get!) } ⦄
      (Directive.instr (.avx .W64 .W256
          (.vmovups (.avx y) (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvx, MachineData.setAvxReg, MachineData.loadAvx,
    AddrExpr.zeroExtend_interp_sib1, hv, Bool.false_and, Bool.false_eq_true, ite_false,
    Effects.All]
  exact hn _ (by rwa [hv, Option.get!_some] at hq)

@[spec] public theorem vfmadd231ps_vreg_vreg_sib1 (dst src1 : AvxReg .W256) (b i : Reg64)
    (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 32).isSome = true
          ∧ Q () { s with zmms := (s.zmms.set dst
              (BitVec.packedTernOp 32 (sseTernOp Kraken.Float32.fma)
                (s.zmms.get src1) (BitVec.ofInt 256 (Mem.loadInt s.dmem a 32).get!) (s.zmms.get dst))) } ⦄
      (Directive.instr (.avx .W64 .W256
          (.vfmadd231ps dst src1 (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvxReg, MachineData.loadAvx, AddrExpr.zeroExtend_interp_sib1, hv,
    Bool.false_and, Bool.false_eq_true, ite_false, Effects.All]
  exact hn _ (by rwa [hv, Option.get!_some] at hq)

@[spec] public theorem vmovaps_vreg_sib1 (x : AvxReg .W128) (b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt
        isAligned 16 a = true ∧ (Mem.loadInt s.dmem a 16).isSome = true
          ∧ Q () { s with zmms := s.zmms.set x (BitVec.ofInt 128 (Mem.loadInt s.dmem a 16).get!) } ⦄
      (Directive.instr (.avx .W64 .W128
          (.vmovaps (.avx x) (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hal, hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvx, MachineData.setAvxReg, MachineData.loadAvx,
    AddrExpr.zeroExtend_interp_sib1, hal, hv, AvxWidth.bytes, Bool.not_true, Bool.and_false,
    Bool.false_eq_true, ite_false, Effects.All]
  exact hn _ (by rwa [hv, Option.get!_some] at hq)

@[spec] public theorem vmulps_vreg_vreg_sib1 (dst src1 : AvxReg .W128) (b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 16).isSome = true
          ∧ Q () { s with zmms := (s.zmms.set dst
              (BitVec.packedBinOp 32 (sseBinOp (· * ·)) (s.zmms.get src1)
                (BitVec.ofInt 128 (Mem.loadInt s.dmem a 16).get!))) } ⦄
      (Directive.instr (.avx .W64 .W128
          (.vmulps dst src1 (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvxReg, MachineData.loadAvx, AddrExpr.zeroExtend_interp_sib1, hv,
    Bool.false_and, Bool.false_eq_true, ite_false, Effects.All]
  exact hn _ (by rwa [hv, Option.get!_some] at hq)

@[spec] public theorem jmp_label (asz osz : Width) (l : Label) :
    ⦃ fun s => E (label l) s ⦄
      (Directive.instr (.regular asz osz (.jmp (.rel (.sub (.label l) .after_current_instruction)))))
    ⦃ Q; E ⦄ :=
  Triple.intro fun s hq => Program.wp_single fun _ _ _ _ _ hj => by
    run_step
    rw [Int64.ofBitVec_toBitVec, Int64.add_sub_self_left]
    refine hj (label l) s ?_
    rw [Executable.StepOut.of_not_below_data (MachineData.not_stackBelow_self s)]
    exact hq

attribute [grind =] Int64.ofBitVec_toBitVec

@[spec] public theorem jmp_reg (asz osz : Width) (r : Reg64) :
    ⦃ fun s => E (Int64.ofBitVec (s.regs.get64 r)) s ⦄
      (Directive.instr (.regular asz osz (.jmp (.reg (.low r .W64)))))
    ⦃ Q; E ⦄ :=
  Triple.intro fun s hq => Program.wp_single fun _ _ _ _ _ hj => by
    run_step
    refine hj _ s ?_
    rw [Executable.StepOut.of_not_below_data (MachineData.not_stackBelow_self s)]
    exact hq

@[spec] public theorem jcc_label (asz osz : Width) (cc : CondCode) (l : Label) :
    ⦃ fun s => (cc.interp s.status = true → E (label l) s) ∧ (cc.interp s.status = false → Q () s) ⦄
      (Directive.instr (.regular asz osz (.jcc cc l)))
    ⦃ Q; E ⦄ :=
  Triple.intro fun s ⟨hjmp, hfall⟩ => Program.wp_single fun _ _ _ _ hn hj => by
    run_step
    cases hc : CondCode.interp cc s.status <;> simp only [Bool.false_eq_true, ite_true, ite_false]
    · exact hn _ (hfall hc)
    · refine hj (label l) s ?_
      rw [Executable.StepOut.of_not_below_data (MachineData.not_stackBelow_self s)]
      exact hjmp hc

@[spec] public theorem push_reg (rs : Reg64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true
        ∧ Q () { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64),
                        dmem := Mem.storeInt s.dmem (s.regs.get64 .rsp - 8#64) 8 (s.regs.get64 rs).toInt } ⦄
      (Directive.instr (.regular .W64 .W64 (.push (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.store, Reg64s.get_low_W64, Width.bytes, hload, Effects.All]
  exact hn _ hpre

@[spec] public theorem pop_reg (rd : Reg64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 .rsp) 8).isSome = true
        ∧ Q () { s with
            regs := (s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64)).set64 rd
              (BitVec.ofInt 64 (Mem.loadInt s.dmem (s.regs.get64 .rsp) 8).get!) } ⦄
      (Directive.instr (.regular .W64 .W64 (.pop (.reg (.low rd .W64)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.load, MachineData.set,
    MachineData.setReg, Reg64s.set_low_W64, Width.bytes, hload, Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

@[spec] public theorem ret (asz osz : Width) :
    ⦃ fun s => s.retAddr.isSome = true
        ∧ E s.retAddr.get! { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64) } ⦄
      (Directive.instr (.regular asz osz .ret))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  obtain ⟨hmapped, hexit⟩ := hpre
  obtain ⟨ra, hra⟩ := Option.isSome_iff_exists.mp hmapped
  rw [hra, Option.get!_some] at hexit
  obtain ⟨i, hi, hval⟩ : ∃ i, Mem.loadInt s.dmem (s.regs.get64 .rsp) 8 = some i
      ∧ Int64.ofBitVec (BitVec.ofInt 64 i) = ra := by
    unfold MachineData.retAddr at hra
    cases hl : Mem.loadInt s.dmem (s.regs.get64 .rsp) 8 with
    | none => rw [hl] at hra; exact absurd hra (by simp)
    | some i => exact ⟨i, rfl, by rw [hl] at hra; simpa using hra⟩
  refine Program.wp_single fun _ _ _ _ _ hj => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.load, hi,
    Effects.All, hval]
  refine hj ra { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64) } ?_
  rw [Executable.StepOut.of_not_below_data (MachineData.not_stackBelow_pop s)]
  exact hexit

@[spec] public theorem call_label {f : Label} (asz osz : Width)
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} :
    ⦃ fun s => Mem.Mapped [(s.regs.rsp.toBitVec - 8#64, 8)] s.dmem
        ∧ ∀ ra, WP.wp (FunDecls.body f) (fun _ _ => False)
          (fun a s' => (a = ra → Q () s') ∧ (a ≠ ra → E a s')) (s.push64 ra) ⦄
      (Directive.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction)))))
    ⦃ Q; E ⦄ := by
  cases hg : FunDecls.at (label f) with
  | none =>
    refine Triple.intro fun s ⟨_, hbody⟩ => ?_
    have hw := hbody 0
    simp only [FunDecls.body, hg, Option.map_none, Option.getD_none] at hw
    exact (Program.wp_nil_elim hw ⟨0, List.nil_isInfixAt _ _⟩).elim
  | some g =>
    refine Triple.intro fun s ⟨hmapped, hbody⟩ => (wp_call_iff hg).mpr fun [h : Embeds _] =>
      ⟨Mem.Mapped.loadInt_isSome hmapped (Mem.Blocks.Inside.base (Nat.le_refl _)), ?_⟩
    refine Program.wp_mono (fun _ h => h) (fun u hu => ?_) (hbody h.embedding.endAddr)
    by_cases hpc : u.pc = h.embedding.endAddr
    · simp only [hpc, ite_true]
      exact hu.1 hpc
    · simp only [hpc, ite_false]
      exact hu.2 hpc

end Program.WP.Spec
