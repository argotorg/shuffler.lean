module

public import BbuKraken.Unit.SpillAdd
import all BbuKraken.Unit.SpillAdd
public import BbuKraken.Unit.SpillSetLemmas
import all BbuKraken.Unit.SpillSetLemmas
public import ProofKit.CfgBlock
import all ProofKit.CfgBlock

@[expose] public section

/-!
# `spill_set`

`c/bbu/spill_set.S`: 6 pushes and 40 bytes of locals. `8(%rsp)` holds `spilled`, and `24(%rsp)`
is the `SpillSet` object that `SpillSet::add` gets in `rdi`. The four loops are:

- `.LB.spill_set.1`: the check of the adds (an id of a variable is below `idCount`);
- `.LB.spill_set.3`: the check of the queries;
- `.LB.spill_set.6`: the adds, with a call of `SpillSet::add` for each;
- `.LB.spill_set.9`: the queries, with a store of the result byte for each.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true
set_option autoImplicit false

namespace Bbu.Unit

open Bbu.Sep

namespace SpillSetProof

def Inv (f : BitVec 32 → BitVec 8) (adds queries : List Word) (r : Addr)
    (res : List (BitVec 8)) (F : MProp 64) (s : MachineData) (ra : Int64) (A Q : List StackSlot) :
    CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .label l, t =>
    if l = Names.spill_set then t = s.pushRa ra
    else if l = ".LB.spill_set.1" then ∃ y o x2, Sb s ra adds queries r F f res y o x2 t
      ∧ t.regs.rbx.toBitVec = rdx s ∧ rdi t = rdi s ∧ (rax t).toNat < (rcx s).toNat
      ∧ (A.take (rax t).toNat).all (Flat.idOk (rdi s)) = true
    else if l = ".LB.spill_set.0" then ∃ y o x2, Sb s ra adds queries r F f res y o x2 t
      ∧ t.regs.rbx.toBitVec = rdx s ∧ rdi t = rdi s ∧ (rax t).toNat < (rcx s).toNat
      ∧ (A.take ((rax t).toNat + 1)).all (Flat.idOk (rdi s)) = true
    else if l = ".LB.spill_set.15" then ∃ y o x2, Sb s ra adds queries r F f res y o x2 t
      ∧ t.regs.rbx.toBitVec = rdx s ∧ rdi t = rdi s ∧ (rcx s).toNat ≠ 0
      ∧ A.all (Flat.idOk (rdi s)) = true
    else if l = ".LB.spill_set.14" then ∃ y o x2, Sb s ra adds queries r F f res y o x2 t
      ∧ t.regs.rbx.toBitVec = rdx s ∧ rdi t = rdi s ∧ rcx s = 0#64 ∧ rcx t = 0#64
      ∧ r9 t = r9 s
    else if l = ".LB.spill_set.3" then ∃ y o x2, Sb s ra adds queries r F f res y o x2 t
      ∧ t.regs.rbx.toBitVec = rdx s ∧ rdi t = rdi s ∧ (rax t).toNat < (r9 s).toNat
      ∧ A.all (Flat.idOk (rdi s)) = true
      ∧ (Q.take (rax t).toNat).all (Flat.idOk (rdi s)) = true
    else if l = ".LB.spill_set.2" then ∃ y o x2, Sb s ra adds queries r F f res y o x2 t
      ∧ t.regs.rbx.toBitVec = rdx s ∧ rdi t = rdi s ∧ (rax t).toNat < (r9 s).toNat
      ∧ A.all (Flat.idOk (rdi s)) = true
      ∧ (Q.take ((rax t).toNat + 1)).all (Flat.idOk (rdi s)) = true
    else if l = ".LB.spill_set.4" then ∃ y o x2, Sb s ra adds queries r F f res y o x2 t
      ∧ t.regs.rbx.toBitVec = rdx s ∧ (r9 s).toNat ≠ 0
      ∧ A.all (Flat.idOk (rdi s)) = true ∧ Q.all (Flat.idOk (rdi s)) = true
    else if l = ".LB.spill_set.5" then ∃ y x2, Sb s ra adds queries r F f res y (rsi s) x2 t
      ∧ t.regs.rbx.toBitVec = rdx s ∧ (rcx s).toNat ≠ 0
      ∧ A.all (Flat.idOk (rdi s)) = true ∧ Q.all (Flat.idOk (rdi s)) = true
    else if l = ".LB.spill_set.6" then ∃ f' y x2, Sb s ra adds queries r F f' res y (rsi s) x2 t
      ∧ t.regs.rbx.toBitVec = rdx s + t.regs.r14.toBitVec * 8#64
      ∧ t.regs.r14.toBitVec.toNat < (rcx s).toNat ∧ t.regs.r15.toBitVec = rsp s - 72#64
      ∧ Flat.spillAddAll f (A.take t.regs.r14.toBitVec.toNat) = (.done, f')
      ∧ A.all (Flat.idOk (rdi s)) = true ∧ Q.all (Flat.idOk (rdi s)) = true
    else if l = ".LB.spill_set.7" then ∃ f' y x2, Sb s ra adds queries r F f' res y (rsi s) x2 t
      ∧ (r9 s).toNat ≠ 0 ∧ Q.all (Flat.idOk (rdi s)) = true
      ∧ setRes s f adds queries res = (0, f', Q.map (g f'))
    else if l = ".LB.spill_set.9" then ∃ f' y x2, Sb s ra adds queries r F f'
        ((Q.take (rax t).toNat).map (g f') ++ res.drop (rax t).toNat) y (rsi s) x2 t
      ∧ (rax t).toNat < (r9 s).toNat ∧ Q.all (Flat.idOk (rdi s)) = true
      ∧ setRes s f adds queries res = (0, f', Q.map (g f'))
    else if l = ".LB.spill_set.8" then ∃ f' y x2, Sb s ra adds queries r F f'
        ((Q.take (rax t).toNat).map (g f') ++ res.drop (rax t).toNat) y (rsi s) x2 t
      ∧ (rax t).toNat < (r9 s).toNat ∧ Q.all (Flat.idOk (rdi s)) = true
      ∧ setRes s f adds queries res = (0, f', Q.map (g f'))
      ∧ ∃ q, Q[(rax t).toNat]? = some q ∧ t.regs.rdx.toBitVec.setWidth 8 = g f' q
    else if l = ".LB.spill_set.10" ∨ l = ".LB.spill_set.13" then ∃ f' res' y o x2,
      Sb s ra adds queries r F f' res' y o x2 t ∧ setRes s f adds queries res = (0, f', res')
    else if l = ".LB.spill_set.11" then ∃ f' res' y o x2,
      Sb s ra adds queries r F f' res' y o x2 t ∧ setRes s f adds queries res = (-2, f', res')
    else if l = ".LB.spill_set.12" then ∃ f' res' y o x2,
      Sb s ra adds queries r F f' res' y o x2 t ∧ setRes s f adds queries res = (rax t, f', res')
    else False
  | .exit, _ => False

def E [Labels] (f : BitVec 32 → BitVec 8) (adds queries : List Word) (r : Addr)
    (res : List (BitVec 8)) (F : MProp 64) (s : MachineData) (ra : Int64) :
    Int64 → MachineData → Prop :=
  fun a t => (a = ra ∧ SetPost f adds queries r res F s t ∧ Sep.mod.Agree s t) ∨
    (a = label "exit" ∧ t.regs.get64 .rdi = 1#64 ∧ SetExit f adds queries r res F s t)

def Obl [Host] [FunDecls] (f : BitVec 32 → BitVec 8) (adds queries : List Word) (r : Addr)
    (res : List (BitVec 8)) (F : MProp 64) (s : MachineData) (ra : Int64) (A Q : List StackSlot) (blk : Program.Block) : Prop :=
  ∀ t, Inv f adds queries r res F s ra A Q blk.label t →
    let I' (c : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      Inv f adds queries r res F s ra A Q c u ∧ Program.Decreases
        (var (rcx s).toNat (r9 s).toNat) blk.label blk.idx t c j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels spillSetAsm) (s.pushRa ra) I'
        (E f adds queries r res F s ra)) t

def labels : List CfgLabel :=
  [.entry,
    .label Names.spill_set,
    .label ".LB.spill_set.12",
    .label ".LB.spill_set.1",
    .label ".LB.spill_set.0",
    .label ".LB.spill_set.15",
    .label ".LB.spill_set.14",
    .label ".LB.spill_set.3",
    .label ".LB.spill_set.2",
    .label ".LB.spill_set.4",
    .label ".LB.spill_set.5",
    .label ".LB.spill_set.6",
    .label ".LB.spill_set.7",
    .label ".LB.spill_set.9",
    .label ".LB.spill_set.8",
    .label ".LB.spill_set.10",
    .label ".LB.spill_set.13",
    .label ".LB.spill_set.11"]

theorem labels_cover : spillSetAsm.ForallBlocks fun blk => blk.label ∈ labels := by
  simp only [labels, Names.spill_set]
  cfg_labels

section
variable [Host] [FunDecls] (f : BitVec 32 → BitVec 8) (adds queries : List Word) (r : Addr)
    (res : List (BitVec 8)) (F : MProp 64) (s : MachineData) (ra : Int64) (A Q : List StackSlot)

set_option linter.unusedSimpArgs false in
theorem b_entry
    : spillSetAsm.ForallBlocks fun blk =>
      blk.label = .entry → Obl f adds queries r res F s ra A Q blk := by
  cfg_block [Obl, Names.spill_set]
  intro t ht
  simp only [Inv] at ht
  subst ht
  kvcgen64
  simp only [Inv, Names.spill_set, ↓reduceIte]

set_option linter.unusedSimpArgs false in
theorem b_fn
    (hpre : SetPre f adds queries r res F s)
    : spillSetAsm.ForallBlocks fun blk =>
      blk.label = .label Names.spill_set → Obl f adds queries r res F s ra A Q blk := by
  cfg_block [Obl, Names.spill_set]
  intro t ht
  simp only [Inv, Names.spill_set, ↓reduceIte] at ht
  subst ht
  obtain ⟨fr, v, hfr, hm⟩ := hpre.mem
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, rfl⟩ := split14 hfr
  rw [setMem_eq] at hm
  have hk0 : Kg (Rest s adds queries r F f res) s ra _ (s.pushRa ra) := Kg.init hm
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, hm7⟩ := pushes (q := (s.pushRa ra).regs.rsp.toBitVec)
    (a := (s.pushRa ra).regs.r15.toBitVec) (b := (s.pushRa ra).regs.r14.toBitVec)
    (c := (s.pushRa ra).regs.r13.toBitVec) (d := (s.pushRa ra).regs.r12.toBitVec)
    (e := (s.pushRa ra).regs.rbp.toBitVec) (k := (s.pushRa ra).regs.rbx.toBitVec)
    (z := (s.pushRa ra).regs.rsi.toBitVec)
    hk0.mem (by simp [MachineData.pushRa]) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl
  let temp : Temps := ⟨x0, x1, x2, x3, x7⟩
  change (Mb s ra adds queries r F f res temp x6 x5).get _ at hm7
  have hsp0 : (s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 40#64
      = rsp s - 96#64 := by
    rw [show (s.pushRa ra).regs.rsp.toBitVec = rsp s - 8#64 by simp [MachineData.pushRa]]
    bv_omega
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | load =>
    first
    | with_reducible exact p1 | with_reducible exact p2 | with_reducible exact p3
    | with_reducible exact p4 | with_reducible exact p5 | with_reducible exact p6
    | with_reducible exact p7
  | goto ".LB.spill_set.14" =>
    rename_i _ hz
    have h0 := ShallowestCopy.zf_true hz
    cfg_goto
    · exact (Sb.stack (s := s) (ra := ra) (adds := adds) (queries := queries) (r := r) (F := F)
        (f := f) (res := res) (y := temp) (o := x6) (x2 := x5) ⟨hm7, hsp0, rfl, rfl, rfl⟩)
    · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte]
      exact ⟨temp, x6, x5, ⟨hm7, hsp0, rfl, rfl, rfl⟩, rfl, rfl, h0, h0, rfl⟩
    · left; simp only [var, String.reduceEq, ↓reduceIte]; omega
  | goto ".LB.spill_set.1" =>
    rename_i _ hz
    have h0 := ShallowestCopy.zf_false hz
    cfg_goto
    · exact (Sb.stack (s := s) (ra := ra) (adds := adds) (queries := queries) (r := r) (F := F)
        (f := f) (res := res) (y := temp) (o := x6) (x2 := x5) ⟨hm7, hsp0, rfl, rfl, rfl⟩)
    · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte]
      refine ⟨temp, x6, x5, ⟨hm7, hsp0, rfl, rfl, rfl⟩, rfl, rfl, ?_, by simp⟩
      change 0 < (rcx s).toNat
      have h1 : rcx s ≠ 0#64 := h0
      exact Nat.pos_of_ne_zero fun h => h1 (BitVec.eq_of_toNat_eq h)
    · left; simp only [var, String.reduceEq, ↓reduceIte]; omega

set_option linter.unusedSimpArgs false in
theorem b_12
    : spillSetAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.spill_set.12" → Obl f adds queries r res F s ra A Q blk := by
  cfg_block [Obl, Names.spill_set]
  intro t ht
  simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte, or_self] at ht
  obtain ⟨f', res', y, o, x2, hsb, hres⟩ := ht
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hsb.isSome_pops
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | load =>
    first
    | with_reducible exact p1 | with_reducible exact p2 | with_reducible exact p3
    | with_reducible exact p4 | with_reducible exact p5 | with_reducible exact p6
  | retAddr =>
    refine (congrArg Option.isSome (hsb.pop ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).retAddr).trans rfl
    all_goals rfl
  | ret =>
    refine ProofKit.intercept_mono_exit
      (E := fun a t => a = ra ∧ SetPost f adds queries r res F s t ∧ Sep.mod.Agree s t)
      ?_ (fun h => Or.inl h)
    refine Kg.ret (hsb.pop ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) fun t' hm' hax => hsb.post hres hm' hax
    all_goals rfl

set_option linter.unusedSimpArgs false in
theorem b_1
    (hpre : SetPre f adds queries r res F s)
    (hA : adds.map StackSlot.ofWord = A)
    : spillSetAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.spill_set.1" → Obl f adds queries r res F s ra A Q blk := by
  cfg_block [Obl, Names.spill_set]
  intro t ht
  simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨y, o, x2, hsb, hbx, hdi, hlt, hall⟩ := ht
  obtain ⟨R, hR⟩ := hsb.addsArr
  have hR' : (Arr t.regs.rbx.toBitVec adds ∗ R).get t.dmem := by rw [hbx]; exact hR
  have hx : t.regs.rax.toBitVec.toNat < adds.length := by rw [hpre.hadds]; exact hlt
  have hxA : t.regs.rax.toBitVec.toNat < A.length := by rw [← hA, List.length_map]; exact hx
  have hAi : A[t.regs.rax.toBitVec.toNat] = StackSlot.ofWord adds[t.regs.rax.toBitVec.toNat] := by
    subst hA; simp
  obtain ⟨o1, o2⟩ := arr_op hR' hx
  obtain ⟨k1, k2⟩ := arr_kind hR' hx
  obtain ⟨w1, w2⟩ := arr_pay hR' hx
  have hpl := (StackSlot.ofWord adds[t.regs.rax.toBitVec.toNat]).payload.isLt
  kvcgen64 [movl_idx8_spec]
  all_goals try symexec_norm
  vc_by_shape
  | load => first | exact o1 | exact k1 | exact w1
  | goto ".LB.spill_set.0" =>
    have hok : Flat.idOk s.regs.rdi.toBitVec A[t.regs.rax.toBitVec.toNat] = true := by
      rw [hAi]
      first
      | (rename_i hz
         rw [o2, ProduceProof.sub_beq8] at hz
         exact idOk_op (by simpa using hz))
      | (rename_i hz
         rw [k2, ProduceProof.sub_beq8] at hz
         exact idOk_kind (by simpa using hz))
      | (rename_i hz
         rw [Idioms.cf_sub, w2, decide_eq_true_eq, BitVec.toNat_setWidth] at hz
         exact idOk_lt (by rw [← hdi]; omega))
    cfg_goto
    · exact (hsb.next rfl rfl rfl rfl rfl).stack
    · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte]
      exact ⟨y, o, x2, hsb.next rfl rfl rfl rfl rfl, hbx, hdi, hlt, all_take_succ hxA hall hok⟩
    · left; simp only [var, rax, Reg64s.get64_rax, String.reduceEq, ↓reduceIte]; omega
  | goto ".LB.spill_set.12" =>
    rename_i ho hk hc
    rw [o2, ProduceProof.sub_beq8] at ho
    rw [k2, ProduceProof.sub_beq8] at hk
    rw [Idioms.cf_sub, w2, decide_eq_false_iff_not, BitVec.toNat_setWidth] at hc
    have hbad : Flat.idOk (rdi s) A[t.regs.rax.toBitVec.toNat] = false := by
      rw [hAi]
      exact idOk_false (by simpa using hk) (by simpa using ho) (by show s.regs.rdi.toBitVec.toNat ≤ _; rw [← hdi]; omega)
    have hres : setRes s f adds queries res = (-2#64, f, res) :=
      setRes_bad (by rw [hA, all_false hxA hbad, Bool.false_and])
    cfg_goto
    · exact (hsb.next rfl rfl rfl rfl rfl).stack
    · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte, or_self]
      exact ⟨f, res, y, o, x2, hsb.next rfl rfl rfl rfl rfl, hres⟩
    · left; simp only [var, rax, Reg64s.get64_rax, String.reduceEq, ↓reduceIte, or_self]; omega

set_option linter.unusedSimpArgs false in
theorem b_0
    (hpre : SetPre f adds queries r res F s)
    (hA : adds.map StackSlot.ofWord = A)
    : spillSetAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.spill_set.0" → Obl f adds queries r res F s ra A Q blk := by
  cfg_block [Obl, Names.spill_set]
  intro t ht
  simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨y, o, x2, hsb, hbx, hdi, hlt, hall⟩ := ht
  have hc := s.regs.rcx.toBitVec.isLt
  have hlt' : t.regs.rax.toBitVec.toNat < s.regs.rcx.toBitVec.toNat := hlt
  have e12 : t.regs.r12.toBitVec = s.regs.rcx.toBitVec := hsb.r12
  have hr1 : (1#64 + t.regs.rax.toBitVec).toNat = t.regs.rax.toBitVec.toNat + 1 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have hlen : A.length = s.regs.rcx.toBitVec.toNat := by
    rw [← hA, List.length_map]; exact hpre.hadds
  have hne : (t.regs.r12.toBitVec - (1#64 + t.regs.rax.toBitVec) == BitVec.zero 64) = false →
      (1#64 + t.regs.rax.toBitVec).toNat < s.regs.rcx.toBitVec.toNat := by
    intro hz
    have he := ProduceProof.ne_of_z hz
    rw [e12] at he
    have h2 : (1#64 + t.regs.rax.toBitVec).toNat ≠ s.regs.rcx.toBitVec.toNat :=
      fun e => he (BitVec.eq_of_toNat_eq e).symm
    omega
  have hall' : (A.take (1#64 + t.regs.rax.toBitVec).toNat).all (Flat.idOk (rdi s)) = true := by
    rw [hr1]; exact hall
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.spill_set.15" =>
    have hz : (t.regs.r12.toBitVec - (1#64 + t.regs.rax.toBitVec) == BitVec.zero 64) = true := by
      with_reducible assumption
    have he := ProduceProof.eq_of_z hz
    rw [e12] at he
    have hn : t.regs.rax.toBitVec.toNat + 1 = A.length := by rw [hlen, he, hr1]
    cfg_goto
    · exact (hsb.next rfl rfl rfl rfl rfl).stack
    · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte]
      refine ⟨y, o, x2, hsb.next rfl rfl rfl rfl rfl, hbx, hdi,
        show s.regs.rcx.toBitVec.toNat ≠ 0 by omega, ?_⟩
      rw [hn, List.take_length] at hall
      exact hall
    · left; simp only [var, rax, Reg64s.get64_rax, String.reduceEq, ↓reduceIte]; omega
  · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte]
    exact ⟨y, o, x2, hsb.next rfl rfl rfl rfl rfl, hbx, hdi, hne (by assumption), hall'⟩
  · left; simp only [var, rax, Reg64s.get64_rax, String.reduceEq, ↓reduceIte]
    have := hne (by assumption)
    omega

set_option linter.unusedSimpArgs false in
theorem b_15
    (hpre : SetPre f adds queries r res F s)
    (hQ : queries.map StackSlot.ofWord = Q)
    : spillSetAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.spill_set.15" → Obl f adds queries r res F s ra A Q blk := by
  cfg_block [Obl, Names.spill_set]
  intro t ht
  simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨y, o, x2, hsb, hbx, hdi, hc0, hall⟩ := ht
  have hld := hsb.ld_sp
  have hio := hsb.isSome_o
  have hc9 := s.regs.r9.toBitVec.isLt
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | load => first | exact hld.1 | exact hio
  | goto ".LB.spill_set.3" =>
    rename_i _ hz
    have h9 := nz_true hz
    rw [hsb.r13] at h9
    have h1 : s.regs.r9.toBitVec ≠ 0#64 := h9
    have hq0 : (0#64).toNat < s.regs.r9.toBitVec.toNat := by bv_omega
    cfg_goto
    · exact (hsb.next rfl rfl rfl rfl rfl).stack
    · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte]
      exact ⟨y, o, x2, hsb.next rfl rfl rfl rfl rfl, hbx, hdi, hq0, hall, rfl⟩
    · left
      simp only [var, rax, Reg64s.get64_rax, String.reduceEq, ↓reduceIte, BitVec.toNat_ofNat]
      omega
  | goto ".LB.spill_set.5" =>
    rename_i _ hz
    have h9 := nz_false hz
    rw [hsb.r13] at h9
    have hQ0 : Q = [] := by
      rw [← hQ]; apply List.eq_nil_of_length_eq_zero
      rw [List.length_map, hpre.hqueries, h9]; rfl
    cfg_goto
    · exact hsb.stack' rfl
    · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte]
      exact ⟨y, x2, hsb.st_o rfl rfl rfl rfl rfl, hbx, hc0, hall, by rw [hQ0]; rfl⟩
    · left; simp only [var, String.reduceEq, ↓reduceIte]; omega

set_option linter.unusedSimpArgs false in
theorem b_14
    (hpre : SetPre f adds queries r res F s)
    (hA : adds.map StackSlot.ofWord = A)
    (hQ : queries.map StackSlot.ofWord = Q)
    : spillSetAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.spill_set.14" → Obl f adds queries r res F s ra A Q blk := by
  cfg_block [Obl, Names.spill_set]
  intro t ht
  simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨y, o, x2, hsb, hbx, hdi, hc0, hc0', h9⟩ := ht
  have hc0'' : t.regs.rcx.toBitVec = 0#64 := hc0'
  have h9' : t.regs.r9.toBitVec = s.regs.r9.toBitVec := h9
  have hc9 := s.regs.r9.toBitVec.isLt
  have hA0 : A = [] := by
    rw [← hA]; apply List.eq_nil_of_length_eq_zero
    rw [List.length_map, hpre.hadds, hc0]; rfl
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.spill_set.3" =>
    rename_i _ hz
    have hn := nz_true hz
    rw [h9'] at hn
    have h1 : s.regs.r9.toBitVec ≠ 0#64 := hn
    have hq0 : t.regs.rcx.toBitVec.toNat < s.regs.r9.toBitVec.toNat := by rw [hc0'']; bv_omega
    have hq1 : (Q.take t.regs.rcx.toBitVec.toNat).all (Flat.idOk (rdi s)) = true := by
      rw [hc0'']; rfl
    cfg_goto
    · exact (hsb.next rfl rfl rfl rfl rfl).stack
    · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte]
      exact ⟨y, o, x2, hsb.next rfl rfl rfl rfl rfl, hbx, hdi, hq0, by rw [hA0]; rfl, hq1⟩
    · left; simp only [var, rax, Reg64s.get64_rax, String.reduceEq, ↓reduceIte]; omega
  | goto ".LB.spill_set.12" =>
    rename_i _ hz
    have hn := nz_false hz
    rw [h9'] at hn
    have hn' : r9 s = 0#64 := hn
    have hQ0 : Q = [] := by
      rw [← hQ]; apply List.eq_nil_of_length_eq_zero
      rw [List.length_map, hpre.hqueries, hn']; rfl
    have hr0 : res = [] := List.eq_nil_of_length_eq_zero (by rw [hpre.hres, hn']; rfl)
    have hres : setRes s f adds queries res = (0#64, f, res) := by
      rw [setRes_done (f' := f) (by rw [hA, hA0]; rfl) (by rw [hQ, hQ0]; rfl)
        (by rw [hA, hA0]; rfl), hQ, hQ0, hr0]
      rfl
    cfg_goto
    · exact (hsb.next rfl rfl rfl rfl rfl).stack
    · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte, or_self]
      exact ⟨f, res, y, o, x2, hsb.next rfl rfl rfl rfl rfl, hres⟩
    · left; simp only [var, String.reduceEq, ↓reduceIte, or_self]; omega

set_option linter.unusedSimpArgs false in
theorem b_3
    (hpre : SetPre f adds queries r res F s)
    (hA : adds.map StackSlot.ofWord = A)
    (hQ : queries.map StackSlot.ofWord = Q)
    : spillSetAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.spill_set.3" → Obl f adds queries r res F s ra A Q blk := by
  cfg_block [Obl, Names.spill_set]
  intro t ht
  simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨y, o, x2, hsb, hbx, hdi, hlt, hallA, hall⟩ := ht
  obtain ⟨R, hR⟩ := hsb.queriesArr
  have hR' : (Arr t.regs.rbp.toBitVec queries ∗ R).get t.dmem := by rw [hsb.bp]; exact hR
  have hx : t.regs.rax.toBitVec.toNat < queries.length := by rw [hpre.hqueries]; exact hlt
  have hxQ : t.regs.rax.toBitVec.toNat < Q.length := by rw [← hQ, List.length_map]; exact hx
  have hQi : Q[t.regs.rax.toBitVec.toNat] = StackSlot.ofWord queries[t.regs.rax.toBitVec.toNat] := by
    subst hQ; simp
  obtain ⟨o1, o2⟩ := arr_op hR' hx
  obtain ⟨k1, k2⟩ := arr_kind hR' hx
  obtain ⟨w1, w2⟩ := arr_pay hR' hx
  have hpl := (StackSlot.ofWord queries[t.regs.rax.toBitVec.toNat]).payload.isLt
  kvcgen64 [movl_idx8_spec]
  all_goals try symexec_norm
  vc_by_shape
  | load => first | exact o1 | exact k1 | exact w1
  | goto ".LB.spill_set.2" =>
    have hok : Flat.idOk s.regs.rdi.toBitVec Q[t.regs.rax.toBitVec.toNat] = true := by
      rw [hQi]
      first
      | (rename_i hz
         rw [o2, ProduceProof.sub_beq8] at hz
         exact idOk_op (by simpa using hz))
      | (rename_i hz
         rw [k2, ProduceProof.sub_beq8] at hz
         exact idOk_kind (by simpa using hz))
      | (rename_i hz
         rw [Idioms.cf_sub, w2, decide_eq_true_eq, BitVec.toNat_setWidth] at hz
         exact idOk_lt (by rw [← hdi]; omega))
    cfg_goto
    · exact (hsb.next rfl rfl rfl rfl rfl).stack
    · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte]
      exact ⟨y, o, x2, hsb.next rfl rfl rfl rfl rfl, hbx, hdi, hlt, hallA,
        all_take_succ hxQ hall hok⟩
    · left; simp only [var, rax, Reg64s.get64_rax, String.reduceEq, ↓reduceIte]; omega
  | goto ".LB.spill_set.12" =>
    rename_i ho hk hc
    rw [o2, ProduceProof.sub_beq8] at ho
    rw [k2, ProduceProof.sub_beq8] at hk
    rw [Idioms.cf_sub, w2, decide_eq_false_iff_not, BitVec.toNat_setWidth] at hc
    have hbad : Flat.idOk (rdi s) Q[t.regs.rax.toBitVec.toNat] = false := by
      rw [hQi]
      exact idOk_false (by simpa using hk) (by simpa using ho)
        (by show s.regs.rdi.toBitVec.toNat ≤ _; rw [← hdi]; omega)
    have hres : setRes s f adds queries res = (-2#64, f, res) :=
      setRes_bad (by rw [hA, hQ, all_false hxQ hbad, Bool.and_false])
    cfg_goto
    · exact (hsb.next rfl rfl rfl rfl rfl).stack
    · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte, or_self]
      exact ⟨f, res, y, o, x2, hsb.next rfl rfl rfl rfl rfl, hres⟩
    · left; simp only [var, rax, Reg64s.get64_rax, String.reduceEq, ↓reduceIte, or_self]; omega

set_option linter.unusedSimpArgs false in
theorem b_2
    (hpre : SetPre f adds queries r res F s)
    (hQ : queries.map StackSlot.ofWord = Q)
    : spillSetAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.spill_set.2" → Obl f adds queries r res F s ra A Q blk := by
  cfg_block [Obl, Names.spill_set]
  intro t ht
  simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨y, o, x2, hsb, hbx, hdi, hlt, hallA, hall⟩ := ht
  have hc := s.regs.r9.toBitVec.isLt
  have hlt' : t.regs.rax.toBitVec.toNat < s.regs.r9.toBitVec.toNat := hlt
  have e13 : t.regs.r13.toBitVec = s.regs.r9.toBitVec := hsb.r13
  have hr1 : (1#64 + t.regs.rax.toBitVec).toNat = t.regs.rax.toBitVec.toNat + 1 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have hlen : Q.length = s.regs.r9.toBitVec.toNat := by
    rw [← hQ, List.length_map]; exact hpre.hqueries
  have hne : (t.regs.r13.toBitVec - (1#64 + t.regs.rax.toBitVec) == BitVec.zero 64) = false →
      (1#64 + t.regs.rax.toBitVec).toNat < s.regs.r9.toBitVec.toNat := by
    intro hz
    have he := ProduceProof.ne_of_z hz
    rw [e13] at he
    have h2 : (1#64 + t.regs.rax.toBitVec).toNat ≠ s.regs.r9.toBitVec.toNat :=
      fun e => he (BitVec.eq_of_toNat_eq e).symm
    omega
  have hall' : (Q.take (1#64 + t.regs.rax.toBitVec).toNat).all (Flat.idOk (rdi s)) = true := by
    rw [hr1]; exact hall
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.spill_set.4" =>
    have hz : (t.regs.r13.toBitVec - (1#64 + t.regs.rax.toBitVec) == BitVec.zero 64) = true := by
      with_reducible assumption
    have he := ProduceProof.eq_of_z hz
    rw [e13] at he
    have hn : t.regs.rax.toBitVec.toNat + 1 = Q.length := by rw [hlen, he, hr1]
    cfg_goto
    · exact (hsb.next rfl rfl rfl rfl rfl).stack
    · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte]
      refine ⟨y, o, x2, hsb.next rfl rfl rfl rfl rfl, hbx,
        show s.regs.r9.toBitVec.toNat ≠ 0 by omega, hallA, ?_⟩
      rw [hn, List.take_length] at hall
      exact hall
    · left; simp only [var, rax, Reg64s.get64_rax, String.reduceEq, ↓reduceIte]; omega
  · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte]
    exact ⟨y, o, x2, hsb.next rfl rfl rfl rfl rfl, hbx, hdi, hne (by assumption), hallA, hall'⟩
  · left; simp only [var, rax, Reg64s.get64_rax, String.reduceEq, ↓reduceIte]
    have := hne (by assumption)
    omega

set_option linter.unusedSimpArgs false in
theorem b_4
    (hpre : SetPre f adds queries r res F s)
    (hA : adds.map StackSlot.ofWord = A)
    (hQ : queries.map StackSlot.ofWord = Q)
    : spillSetAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.spill_set.4" → Obl f adds queries r res F s ra A Q blk := by
  cfg_block [Obl, Names.spill_set]
  intro t ht
  simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨y, o, x2, hsb, hbx, h9, hallA, hallQ⟩ := ht
  have hld := hsb.ld_sp
  have hio := hsb.isSome_o
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | load => first | exact hld.1 | exact hio
  | goto ".LB.spill_set.7" =>
    rename_i _ hz
    have h12 := ShallowestCopy.zf_true hz
    rw [hsb.r12] at h12
    have hA0 : A = [] := by
      rw [← hA]; apply List.eq_nil_of_length_eq_zero
      rw [List.length_map, hpre.hadds, h12]; rfl
    have hres : setRes s f adds queries res = (0#64, f, Q.map (g f)) := by
      rw [setRes_done (f' := f) (by rw [hA]; exact hallA) (by rw [hQ]; exact hallQ)
        (by rw [hA, hA0]; rfl), hQ]
    cfg_goto
    · exact hsb.stack' rfl
    · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte]
      exact ⟨f, y, x2, hsb.st_o rfl rfl rfl rfl rfl, h9, hallQ, hres⟩
    · left; simp only [var, String.reduceEq, ↓reduceIte]; omega
  · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte]
    have h12 : t.regs.r12.toBitVec ≠ 0#64 := ShallowestCopy.zf_false (by with_reducible assumption)
    have e12 : t.regs.r12.toBitVec = s.regs.rcx.toBitVec := hsb.r12
    rw [e12] at h12
    have hc0 : s.regs.rcx.toBitVec.toNat ≠ 0 := by bv_omega
    exact ⟨y, x2, hsb.st_o rfl rfl rfl rfl rfl, hbx, hc0, hallA, hallQ⟩
  · left; simp only [var, String.reduceEq, ↓reduceIte]; omega

set_option linter.unusedSimpArgs false in
theorem b_5
    : spillSetAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.spill_set.5" → Obl f adds queries r res F s ra A Q blk := by
  cfg_block [Obl, Names.spill_set]
  intro t ht
  simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨y, x2, hsb, hbx, hc0, hallA, hallQ⟩ := ht
  have hc := s.regs.rcx.toBitVec.isLt
  have hb : t.regs.rbx.toBitVec = rdx s + 0#64 * 8#64 := by rw [hbx]; bv_omega
  have hc0' : s.regs.rcx.toBitVec.toNat ≠ 0 := hc0
  have h14 : (0#64 : Word).toNat < s.regs.rcx.toBitVec.toNat := by
    simp only [BitVec.toNat_ofNat]; omega
  have h15 : t.regs.rsp.toBitVec + 24#64 = rsp s - 72#64 := by rw [hsb.sp]; bv_omega
  have hd : Flat.spillAddAll f (A.take (0#64 : Word).toNat) = (.done, f) := by
    simp [Flat.spillAddAll]
  kvcgen64
  all_goals try symexec_norm
  · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte]
    exact ⟨f, y, x2, hsb.next rfl rfl rfl rfl rfl, hb, h14, h15, hd, hallA, hallQ⟩
  · left; simp only [var, String.reduceEq, ↓reduceIte, BitVec.toNat_ofNat]; omega

set_option linter.unusedSimpArgs false in
theorem b_6
    (hpre : SetPre f adds queries r res F s)
    (hA : adds.map StackSlot.ofWord = A)
    (hQ : queries.map StackSlot.ofWord = Q)
    (hadd : AddSpec)
    (hout : ∀ l ∈ Program.labels spillSetAsm, label l ≠ label "exit")
    : spillSetAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.spill_set.6" → Obl f adds queries r res F s ra A Q blk := by
  simp only [AddSpec, Names.spillSetAdd] at hadd
  cfg_block [Obl, Names.spill_set]
  intro t ht
  simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨f', y, x2, hsb, hbx, hlt, h15, hdone, hallA, hallQ⟩ := ht
  have hc := s.regs.rcx.toBitVec.isLt
  have hc9 := s.regs.r9.toBitVec.isLt
  have hlt' : t.regs.r14.toBitVec.toNat < s.regs.rcx.toBitVec.toNat := hlt
  obtain ⟨R, hR⟩ := hsb.addsArr
  have hx : t.regs.r14.toBitVec.toNat < adds.length := by rw [hpre.hadds]; exact hlt
  have hxA : t.regs.r14.toBitVec.toNat < A.length := by rw [← hA, List.length_map]; exact hx
  have hlenA : A.length = s.regs.rcx.toBitVec.toNat := by
    rw [← hA, List.length_map]; exact hpre.hadds
  have hAi : A[t.regs.r14.toBitVec.toNat] = StackSlot.ofWord adds[t.regs.r14.toBitVec.toNat] := by
    subst hA; simp
  obtain ⟨R', hW⟩ := arr_wd hR hx
  have hW' : (Wd t.regs.rbx.toBitVec adds[t.regs.r14.toBitVec.toNat] ∗ R').get t.dmem := by
    rw [hbx]; exact hW
  have hld := Wd.isSome hW'
  have hrd := Wd.rd hW'
  have hok : Flat.idOk (rdi s) (StackSlot.ofWord adds[t.regs.r14.toBitVec.toNat]) = true := by
    rw [← hAi]; exact idOk_of_all hxA hallA
  have hstep : Flat.spillAddAll f (A.take (t.regs.r14.toBitVec.toNat + 1))
      = Flat.spillAdd f' (StackSlot.ofWord adds[t.regs.r14.toBitVec.toNat]) := by
    rw [addAll_step hxA hdone, hAi]
  have hr1 : (1#64 + t.regs.r14.toBitVec).toNat = t.regs.r14.toBitVec.toNat + 1 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  obtain ⟨w, hw⟩ : ∃ w, adds[t.regs.r14.toBitVec.toNat] = w := ⟨_, rfl⟩
  rw [hw] at hrd hok hstep
  kvcgen64 [hadd]
  all_goals try symexec_norm
  vc_by_shape
  | load => exact hld
  | other =>
    refine Sb.call (w := w) (hsb.next rfl rfl rfl rfl rfl) h15 hrd (fun hv => lt_ids hok hv) ?normal ?abort
    case normal =>
      intro t2 v hsb2 hal hag
      have k14 : t2.regs.r14 = t.regs.r14 := mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r14
      have kbx : t2.regs.rbx = t.regs.rbx := mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbx
      have k15 : t2.regs.r15 = t.regs.r15 := mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r15
      have e12 : t2.regs.r12.toBitVec = s.regs.rcx.toBitVec := hsb2.r12
      have e13 : t2.regs.r13.toBitVec = s.regs.r9.toBitVec := hsb2.r13
      have hr2 : (1#64 + t2.regs.r14.toBitVec).toNat = t.regs.r14.toBitVec.toNat + 1 := by
        rw [k14]; exact hr1
      have h15' : t2.regs.r15.toBitVec = rsp s - 72#64 := by rw [k15]; exact h15
      kvcgen64
      all_goals try symexec_norm
      vc_by_shape
      | goto ".LB.spill_set.11" =>
        have hal0 := ProduceProof.al_ne (by with_reducible assumption)
        have hst : (Flat.spillAdd f' (StackSlot.ofWord w)).1 ≠ .done :=
          ProduceProof.code_ne_zero (fun e => hal0 (hal.trans e))
        have hfail : Flat.spillAddAll f A = Flat.spillAdd f' (StackSlot.ofWord w) :=
          (addAll_fail (l := A) (i := t.regs.r14.toBitVec.toNat + 1)
            (by rw [hstep]; exact hst)).trans hstep
        have hres : setRes s f adds queries res
            = (-2#64, (Flat.spillAdd f' (StackSlot.ofWord w)).2, res) :=
          setRes_fail (st := (Flat.spillAdd f' (StackSlot.ofWord w)).1)
            (by rw [hA]; exact hallA) (by rw [hQ]; exact hallQ) (by rw [hA, hfail]) hst
        cfg_goto
        · exact hsb2.stack' rfl
        · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte, or_self]
          exact ⟨_, res, v, rsi s, x2, hsb2.next rfl rfl rfl rfl rfl, hres⟩
        · left; simp only [var, String.reduceEq, ↓reduceIte, or_true]; omega
      | goto ".LB.spill_set.6" =>
        have hal0 := ProduceProof.al_zero (by with_reducible assumption)
        have hd := ProduceProof.code_eq_zero (hal.symm.trans hal0)
        have hlt2 : (1#64 + t2.regs.r14.toBitVec).toNat < t2.regs.r12.toBitVec.toNat :=
          lt_of_cfb (by with_reducible assumption)
        rw [e12] at hlt2
        have hbx' : t.regs.rbx.toBitVec = s.regs.rdx.toBitVec + t.regs.r14.toBitVec * 8#64 := hbx
        have hb2 : 8#64 + t2.regs.rbx.toBitVec = rdx s + (1#64 + t2.regs.r14.toBitVec) * 8#64 := by
          show 8#64 + t2.regs.rbx.toBitVec = s.regs.rdx.toBitVec + (1#64 + t2.regs.r14.toBitVec) * 8#64
          rw [kbx, k14, hbx']; bv_omega
        have hdone2 : Flat.spillAddAll f (A.take (1#64 + t2.regs.r14.toBitVec).toNat)
            = (.done, (Flat.spillAdd f' (StackSlot.ofWord w)).2) := by
          rw [hr2, hstep]; exact Prod.ext hd rfl
        cfg_goto
        · exact hsb2.stack' rfl
        · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte]
          exact ⟨_, v, x2, hsb2.next rfl rfl rfl rfl rfl, hb2, hlt2, h15', hdone2, hallA, hallQ⟩
        · left; simp only [var, String.reduceEq, ↓reduceIte]; omega
      | goto ".LB.spill_set.13" =>
        have hal0 := ProduceProof.al_zero (by with_reducible assumption)
        have hd := ProduceProof.code_eq_zero (hal.symm.trans hal0)
        have hge : t2.regs.r12.toBitVec.toNat ≤ (1#64 + t2.regs.r14.toBitVec).toNat :=
          ge_of_cfb (by with_reducible assumption)
        have h13z : t2.regs.r13.toBitVec = 0#64 := ShallowestCopy.zf_true (by with_reducible assumption)
        rw [e12, hr2] at hge
        rw [e13] at h13z
        have hn' : r9 s = 0#64 := h13z
        have hQ0 : Q = [] := by
          rw [← hQ]; apply List.eq_nil_of_length_eq_zero
          rw [List.length_map, hpre.hqueries, hn']; rfl
        have hr0 : res = [] := List.eq_nil_of_length_eq_zero (by rw [hpre.hres, hn']; rfl)
        have hdoneA : Flat.spillAddAll f A = (.done, (Flat.spillAdd f' (StackSlot.ofWord w)).2) :=
          ((addAll_all (f := f) (l := A) (i := t.regs.r14.toBitVec.toNat + 1)
            (by omega)).symm.trans hstep).trans (Prod.ext hd rfl)
        have hres : setRes s f adds queries res
            = (0#64, (Flat.spillAdd f' (StackSlot.ofWord w)).2, res) := by
          rw [setRes_done (by rw [hA]; exact hallA) (by rw [hQ]; exact hallQ)
            (by rw [hA]; exact hdoneA), hQ, hQ0, List.map_nil, hr0]
        cfg_goto
        · exact hsb2.stack' rfl
        · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte, or_true, true_or, or_false,
            false_or, or_self]
          exact ⟨_, res, v, rsi s, x2, hsb2.next rfl rfl rfl rfl rfl, hres⟩
        · left
          simp only [var, String.reduceEq, ↓reduceIte, or_true, true_or, or_false, false_or]
          omega
      · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte]
        have hal0 := ProduceProof.al_zero (by with_reducible assumption)
        have hd := ProduceProof.code_eq_zero (hal.symm.trans hal0)
        have hge : t2.regs.r12.toBitVec.toNat ≤ (1#64 + t2.regs.r14.toBitVec).toNat :=
          ge_of_cfb (by with_reducible assumption)
        have h13 : t2.regs.r13.toBitVec ≠ 0#64 := ShallowestCopy.zf_false (by with_reducible assumption)
        rw [e12, hr2] at hge
        rw [e13] at h13
        have h9 : s.regs.r9.toBitVec.toNat ≠ 0 := by bv_omega
        have hdoneA : Flat.spillAddAll f A = (.done, (Flat.spillAdd f' (StackSlot.ofWord w)).2) :=
          ((addAll_all (f := f) (l := A) (i := t.regs.r14.toBitVec.toNat + 1)
            (by omega)).symm.trans hstep).trans (Prod.ext hd rfl)
        have hres : setRes s f adds queries res = (0#64, (Flat.spillAdd f' (StackSlot.ofWord w)).2,
            Q.map (g (Flat.spillAdd f' (StackSlot.ofWord w)).2)) := by
          rw [setRes_done (by rw [hA]; exact hallA) (by rw [hQ]; exact hallQ)
            (by rw [hA]; exact hdoneA), hQ]
        exact ⟨_, v, x2, hsb2.next rfl rfl rfl rfl rfl, h9, hallQ, hres⟩
      · left; simp only [var, String.reduceEq, ↓reduceIte]; omega
    case abort =>
      intro t2 v hm2 hf harg
      have hfail : Flat.spillAddAll f A = (.assertionFailed, f') := by
        have hbad : (Flat.spillAddAll f (A.take (t.regs.r14.toBitVec.toNat + 1))).1 ≠ .done := by
          rw [hstep, hf]
          change Flat.Status.assertionFailed ≠ Flat.Status.done
          decide
        exact (addAll_fail (l := A) (i := t.regs.r14.toBitVec.toNat + 1) hbad).trans
          (hstep.trans hf)
      have hres : setRes s f adds queries res = (-2#64, f', res) :=
        setRes_fail (st := .assertionFailed) (by rw [hA]; exact hallA)
          (by rw [hQ]; exact hallQ) (by rw [hA]; exact hfail) (by decide)
      refine Or.inr ⟨Or.inr ⟨rfl, harg, ?_⟩, ?_⟩
      · refine ⟨?_, by rw [hres], frm s v (rsi s) x2, ra.toBitVec, rfl, ?_⟩
        · rw [hA, hfail]
        · rw [hres, setMem_eq, ← mb_eq]
          exact hm2
      · intro l hl ha
        exact False.elim (hout l hl ha)

set_option linter.unusedSimpArgs false in
theorem b_7
    : spillSetAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.spill_set.7" → Obl f adds queries r res F s ra A Q blk := by
  cfg_block [Obl, Names.spill_set]
  intro t ht
  simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨f', y, x2, hsb, h9, hallQ, hres⟩ := ht
  have hc9 := s.regs.r9.toBitVec.isLt
  have h9' : s.regs.r9.toBitVec.toNat ≠ 0 := h9
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.spill_set.9" =>
    cfg_goto
    · exact (hsb.next rfl rfl rfl rfl rfl).stack
    · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte]
      refine ⟨f', y, x2, hsb.next rfl rfl rfl rfl rfl, ?_, hallQ, hres⟩
      change 0 < (r9 s).toNat
      exact Nat.pos_of_ne_zero h9'
    · left
      simp only [var, rax, Reg64s.get64_rax, String.reduceEq, ↓reduceIte, BitVec.toNat_ofNat]
      omega

set_option linter.unusedSimpArgs false in
theorem b_9
    (hpre : SetPre f adds queries r res F s)
    (hQ : queries.map StackSlot.ofWord = Q)
    : spillSetAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.spill_set.9" → Obl f adds queries r res F s ra A Q blk := by
  cfg_block [Obl, Names.spill_set]
  intro t ht
  simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨f', y, x2, hsb, hlt, hallQ, hres⟩ := ht
  obtain ⟨R, hR⟩ := hsb.queriesArr
  have hR' : (Arr t.regs.rbp.toBitVec queries ∗ R).get t.dmem := by rw [hsb.bp]; exact hR
  have hc9 := s.regs.r9.toBitVec.isLt
  have hlt' : t.regs.rax.toBitVec.toNat < s.regs.r9.toBitVec.toNat := hlt
  have hx : t.regs.rax.toBitVec.toNat < queries.length := by rw [hpre.hqueries]; exact hlt
  have hxQ : t.regs.rax.toBitVec.toNat < Q.length := by rw [← hQ, List.length_map]; exact hx
  obtain ⟨q, hq⟩ : ∃ q, StackSlot.ofWord queries[t.regs.rax.toBitVec.toNat] = q := ⟨_, rfl⟩
  have hQi : Q[t.regs.rax.toBitVec.toNat] = q := by rw [← hq]; subst hQ; simp
  have hQs : Q[t.regs.rax.toBitVec.toNat]? = some q := by
    rw [List.getElem?_eq_getElem hxQ, hQi]
  obtain ⟨o1, o2⟩ := arr_op hR' hx
  obtain ⟨k1, k2⟩ := arr_kind hR' hx
  obtain ⟨w1, w2⟩ := arr_pay hR' hx
  rw [hq] at o2 k2 w2
  have hld := hsb.ld_sp
  have hok : Flat.idOk (rdi s) q = true := by rw [← hQi]; exact idOk_of_all hxQ hallQ
  have ea : BitVec.ofInt 64 (t.dmem.loadInt (t.regs.rsp.toBitVec + 8#64) 8).get!
      + BitVec.setWidth 64
        (BitVec.ofInt 32 (t.dmem.loadInt (t.regs.rbp.toBitVec + t.regs.rax.toBitVec * 8#64) 4).get!)
      = rsi s + BitVec.ofNat 64 q.payload.toNat := by
    rw [w2, BitVec.ofNat_toNat]; exact congrArg (· + BitVec.setWidth 64 q.payload) hld.2
  have hspl : Flat.isVariable q = true →
      (t.dmem.loadInt (rsi s + BitVec.ofNat 64 q.payload.toNat) 1).isSome = true
      ∧ BitVec.ofInt 8 (t.dmem.loadInt (rsi s + BitVec.ofNat 64 q.payload.toNat) 1).get!
        = f' q.payload := by
    intro hv
    have hl := lt_ids hok hv
    refine ⟨hsb.isSome_spl hl, ?_⟩
    have h2 := hsb.rdb_spl hl
    have e32 : BitVec.ofNat 32 q.payload.toNat = q.payload := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [e32] at h2
    exact h2
  kvcgen64 [movl_idx8_spec, andb_spec]
  all_goals try symexec_norm
  vc_by_shape
  | load =>
    first
    | exact o1 | exact k1 | exact w1 | exact hld.1
    | (rw [ea]; exact (hspl (var_of_andb o2 k2 (by with_reducible assumption))).1)
  | goto ".LB.spill_set.8" =>
    first
    | (have hv := notvar_of_andb o2 k2 (by with_reducible assumption)
       cfg_goto
       · exact hsb.stack' rfl
       · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte]
         refine ⟨f', y, x2, hsb.next rfl rfl rfl rfl rfl, hlt, hallQ, hres, q, hQs, ?_⟩
         rw [setWidth_replaceLow, andb_byte, o2, k2, ← isVariable_eq, g_not_var hv]
       · left; simp only [var, rax, Reg64s.get64_rax, String.reduceEq, ↓reduceIte]; omega)
    | (have hv := var_of_andb o2 k2 (by with_reducible assumption)
       cfg_goto
       · exact hsb.stack' rfl
       · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte]
         refine ⟨f', y, x2, hsb.next rfl rfl rfl rfl rfl, hlt, hallQ, hres, q, hQs, ?_⟩
         rw [setWidth_replaceLow, ea, (hspl hv).2, setne_byte, g_var hv]
       · left; simp only [var, rax, Reg64s.get64_rax, String.reduceEq, ↓reduceIte]; omega)

set_option linter.unusedSimpArgs false in
theorem b_8
    (hpre : SetPre f adds queries r res F s)
    (hQ : queries.map StackSlot.ofWord = Q)
    : spillSetAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.spill_set.8" → Obl f adds queries r res F s ra A Q blk := by
  cfg_block [Obl, Names.spill_set]
  intro t ht
  simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨f', y, x2, hsb, hlt, hallQ, hres, q, hqs, hdl⟩ := ht
  have hc9 := s.regs.r9.toBitVec.isLt
  have hlt' : t.regs.rax.toBitVec.toNat < s.regs.r9.toBitVec.toNat := hlt
  have e13 : t.regs.r13.toBitVec = s.regs.r9.toBitVec := hsb.r13
  have hr1 : (1#64 + t.regs.rax.toBitVec).toNat = t.regs.rax.toBitVec.toNat + 1 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have hlenQ : Q.length = s.regs.r9.toBitVec.toNat := by
    rw [← hQ, List.length_map]; exact hpre.hqueries
  have hlenR : Q.length = res.length := hlenQ.trans hpre.hres.symm
  have hxQ : t.regs.rax.toBitVec.toNat < Q.length := by rw [hlenQ]; exact hlt'
  have hqi : Q[t.regs.rax.toBitVec.toNat] = q :=
    Option.some.inj ((List.getElem?_eq_getElem hxQ).symm.trans hqs)
  have hlr := hsb.ld_res
  have er : BitVec.ofInt 64 (t.dmem.loadInt (t.regs.rsp.toBitVec + 96#64) 8).get! = r := hlr.2
  have hxr : t.regs.rax.toBitVec.toNat
      < ((Q.take t.regs.rax.toBitVec.toNat).map (g f') ++ res.drop t.regs.rax.toBitVec.toNat).length := by
    simp only [List.length_append, List.length_map, List.length_take, List.length_drop]; omega
  have hne : (t.regs.r13.toBitVec - (1#64 + t.regs.rax.toBitVec) == BitVec.zero 64) = false →
      (1#64 + t.regs.rax.toBitVec).toNat < s.regs.r9.toBitVec.toNat := by
    intro hz
    have he := ProduceProof.ne_of_z hz
    rw [e13] at he
    have h2 : (1#64 + t.regs.rax.toBitVec).toNat ≠ s.regs.r9.toBitVec.toNat :=
      fun e => he (BitVec.eq_of_toNat_eq e).symm
    omega
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | load => first | exact hlr.1 | (rw [er]; exact hsb.isSome_res hxr)
  | goto ".LB.spill_set.10" =>
    have hz : (t.regs.r13.toBitVec - (1#64 + t.regs.rax.toBitVec) == BitVec.zero 64) = true := by
      with_reducible assumption
    have he := ProduceProof.eq_of_z hz
    rw [e13] at he
    have hn : t.regs.rax.toBitVec.toNat + 1 = Q.length := by rw [hlenQ, he, hr1]
    cfg_goto
    · exact hsb.stack' rfl
    · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte, or_true, true_or, or_false,
        false_or, or_self]
      refine ⟨f', Q.map (g f'), y, rsi s, x2, ?_, hres⟩
      exact hsb.st_res hxr (BitVec.extractLsb' 0 8 t.regs.rdx.toBitVec).toInt (by rw [er])
        (by rw [ofInt_extract8, hdl, ← hqi, res_step hxQ hlenR]; exact res_end hn hlenR)
        rfl rfl rfl rfl
    · left
      simp only [var, String.reduceEq, ↓reduceIte, or_true, true_or, or_false, false_or]
      omega
  · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte]
    refine ⟨f', y, x2, ?_, hne (by assumption), hallQ, hres⟩
    exact hsb.st_res hxr (BitVec.extractLsb' 0 8 t.regs.rdx.toBitVec).toInt (by rw [er])
      (by
        simp only [rax, Reg64s.get64_rax]
        rw [hr1, ofInt_extract8, hdl, ← hqi]
        exact res_step (f := f') hxQ hlenR) rfl rfl rfl rfl
  · left; simp only [var, rax, Reg64s.get64_rax, String.reduceEq, ↓reduceIte]
    have := hne (by assumption)
    omega

set_option linter.unusedSimpArgs false in
theorem b_10
    : spillSetAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.spill_set.10" → Obl f adds queries r res F s ra A Q blk := by
  cfg_block [Obl, Names.spill_set]
  intro t ht
  simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte, or_true, true_or, or_false,
    false_or, or_self] at ht
  obtain ⟨f', res', y, o, x2, hsb, hres⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.spill_set.12" =>
    cfg_goto
    · exact (hsb.next rfl rfl rfl rfl rfl).stack
    · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte, or_self]
      exact ⟨f', res', y, o, x2, hsb.next rfl rfl rfl rfl rfl, hres⟩
    · left
      simp only [var, String.reduceEq, ↓reduceIte, or_true, true_or, or_false, false_or, or_self]
      omega

set_option linter.unusedSimpArgs false in
theorem b_13
    : spillSetAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.spill_set.13" → Obl f adds queries r res F s ra A Q blk := by
  cfg_block [Obl, Names.spill_set]
  intro t ht
  simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte, or_true, true_or, or_false,
    false_or, or_self] at ht
  obtain ⟨f', res', y, o, x2, hsb, hres⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.spill_set.12" =>
    cfg_goto
    · exact (hsb.next rfl rfl rfl rfl rfl).stack
    · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte, or_self]
      exact ⟨f', res', y, o, x2, hsb.next rfl rfl rfl rfl rfl, hres⟩
    · left
      simp only [var, String.reduceEq, ↓reduceIte, or_true, true_or, or_false, false_or, or_self]
      omega

set_option linter.unusedSimpArgs false in
theorem b_11
    : spillSetAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.spill_set.11" → Obl f adds queries r res F s ra A Q blk := by
  cfg_block [Obl, Names.spill_set]
  intro t ht
  simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte, or_self] at ht
  obtain ⟨f', res', y, o, x2, hsb, hres⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  · simp only [Inv, Names.spill_set, String.reduceEq, ↓reduceIte, or_self]
    exact ⟨f', res', y, o, x2, hsb.next rfl rfl rfl rfl rfl, hres⟩
  · left; simp only [var, String.reduceEq, ↓reduceIte, or_self, or_true, false_or]; omega

end
end SpillSetProof

open SpillSetProof in
theorem spill_set_unit [Host] [FunDecls] (hadd : AddSpec)
    (hout : ∀ l ∈ Program.labels spillSetAsm, label l ≠ label "exit") :
    ∀ f adds queries r res F,
      BodyWithExit spillSetAsm (SetPre f adds queries r res F)
        (SetPost f adds queries r res F) (SetExit f adds queries r res F) := by
  intro f adds queries r res F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨A, hA⟩ : ∃ A, adds.map StackSlot.ofWord = A := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, queries.map StackSlot.ofWord = Q := ⟨_, rfl⟩
  refine Program.WP.cfg (SpillSetProof.Inv f adds queries r res F s ra A Q)
    (SpillSetProof.var (rcx s).toNat (r9 s).toNat) ?_ rfl
  refine forallBlocks_cases SpillSetProof.labels SpillSetProof.labels_cover ?_
  intro l hl
  simp only [SpillSetProof.labels, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SpillSetProof.b_entry f adds queries r res F s ra A Q
  · exact SpillSetProof.b_fn f adds queries r res F s ra A Q hpre
  · exact SpillSetProof.b_12 f adds queries r res F s ra A Q
  · exact SpillSetProof.b_1 f adds queries r res F s ra A Q hpre hA
  · exact SpillSetProof.b_0 f adds queries r res F s ra A Q hpre hA
  · exact SpillSetProof.b_15 f adds queries r res F s ra A Q hpre hQ
  · exact SpillSetProof.b_14 f adds queries r res F s ra A Q hpre hA hQ
  · exact SpillSetProof.b_3 f adds queries r res F s ra A Q hpre hA hQ
  · exact SpillSetProof.b_2 f adds queries r res F s ra A Q hpre hQ
  · exact SpillSetProof.b_4 f adds queries r res F s ra A Q hpre hA hQ
  · exact SpillSetProof.b_5 f adds queries r res F s ra A Q
  · exact SpillSetProof.b_6 f adds queries r res F s ra A Q hpre hA hQ hadd hout
  · exact SpillSetProof.b_7 f adds queries r res F s ra A Q
  · exact SpillSetProof.b_9 f adds queries r res F s ra A Q hpre hQ
  · exact SpillSetProof.b_8 f adds queries r res F s ra A Q hpre hQ
  · exact SpillSetProof.b_10 f adds queries r res F s ra A Q
  · exact SpillSetProof.b_13 f adds queries r res F s ra A Q
  · exact SpillSetProof.b_11 f adds queries r res F s ra A Q

end Bbu.Unit
