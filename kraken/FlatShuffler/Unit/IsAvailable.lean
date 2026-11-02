module

public import FlatShuffler.Unit.Plan.Emission
import all FlatShuffler.Unit.Plan.Emission
public import FlatShuffler.Unit.IsSpilled
import all FlatShuffler.Unit.IsSpilled
public import FlatShuffler.Unit.ShallowestCopy
import all FlatShuffler.Unit.ShallowestCopy
public import ProofKit.CfgBlock
import all ProofKit.CfgBlock

@[expose] public section

/-! `Emission::isAvailable` reads a target slot and tests whether it can be generated,
is spilled, or has a copy on the working stack. It pushes `rbp` and `rbx` and calls
`isSpilled` and `shallowestCopyPosition`. -/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit
open FlatShuffler.Sep

def isAvailableA (g : G) (s : MachineData) : Prop := (rsi s).toNat < g.h.n.toNat

def isAvailableQ (g g' : G) (s t : MachineData) : Prop :=
  g' = g ∧ al t = if Flat.isAvailable (flat g) (rsi s) then 1#8 else 0#8

namespace AvailableU

def fr (s : MachineData) (w : Word) : List Word :=
  [w, s.regs.rbx.toBitVec, s.regs.rbp.toBitVec]

def slot (g : G) (s : MachineData) : Word := g.tgt[(rsi s).toNat]!
def res (g : G) (s : MachineData) : Bool := Flat.isAvailable (flat g) (rsi s)

theorem get_target {g : G} {i : Word} (hok : g.Ok) (hi : i.toNat < g.h.n.toNat) :
    Flat.get (flat g).target i = StackSlot.ofWord g.tgt[i.toNat] := by
  simp [Flat.get, flat, vec, hi, Nat.lt_of_lt_of_le hi hok.n]

theorem target_slot {g : G} {s : MachineData} (hok : g.Ok)
    (hi : (rsi s).toNat < g.h.n.toNat) :
    Flat.get (flat g).target (rsi s) = StackSlot.ofWord (slot g s) := by
  rw [get_target hok hi]
  simp only [slot, getElem!_pos g.tgt (rsi s).toNat hi]

-- The compiler tests `kind - 1 <= 1` to recognize the two free kinds.
theorem kind_low (k : BitVec 8) :
    BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (BitVec.setWidth 32 k - 1#32)) = k - 1#8 := by
  bv_decide

theorem kind_test (k : BitVec 8) :
    (decide ((k - 1#8).toNat < 1) || (k - 1#8 == 1#8)) = (k == Junk || k == FunctionCallReturnLabel) := by
  unfold Junk FunctionCallReturnLabel
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  bv_omega

theorem free_test (w : Word) :
    (decide ((w.extractLsb' 32 8 - 1#8).toNat < 1) ||
      (w.extractLsb' 32 8 - 1#8 == 1#8) || (w.extractLsb' 40 8 == 0#8)) =
      canBeFreelyGenerated (StackSlot.ofWord w) := by
  rw [kind_test]
  simp only [canBeFreelyGenerated, isLiteralValue, StackSlot.ofWord, Const,
    Bool.or_comm, Bool.or_left_comm, BitVec.ofNat_eq_ofNat]

structure Bd (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)
    (w : Word) (t : MachineData) : Prop where
  kb : Kb (View S g ∗ F) s ra (fr s w) 16#64 t
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15

section
variable {S : Addr} {g : G} {F : MProp 64} {s t t' : MachineData} {ra : Int64} {w : Word}

theorem Bd.next (h : Bd S g F s ra w t) (hm : t'.dmem = t.dmem)
    (hsp : t'.regs.rsp = t.regs.rsp) (h12 : t'.regs.r12 = t.regs.r12)
    (h13 : t'.regs.r13 = t.regs.r13) (h14 : t'.regs.r14 = t.regs.r14)
    (h15 : t'.regs.r15 = t.regs.r15) : Bd S g F s ra w t' :=
  ⟨h.kb.next hm hsp, h12.trans h.r12, h13.trans h.r13, h14.trans h.r14, h15.trans h.r15⟩

theorem Bd.afterCall {u : MachineData} {w' : Word} (h : Bd S g F s ra w t)
    (hkb : Kb (View S g ∗ F) s ra (fr s w') 16#64 u) (hag : Sep.mod.Agree t u) :
    Bd S g F s ra w' u :=
  ⟨hkb,
    (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r12).trans h.r12,
    (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r13).trans h.r13,
    (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r14).trans h.r14,
    (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r15).trans h.r15⟩

theorem Bd.pop (h : Bd S g F s ra w t) (hm : t'.dmem = t.dmem)
    (hsp : t'.regs.rsp.toBitVec = t.regs.rsp.toBitVec + 8#64 + 8#64)
    (hbx : t'.regs.rbx.toBitVec = rd t.dmem t.regs.rsp.toBitVec)
    (hbp : t'.regs.rbp.toBitVec = rd t.dmem (t.regs.rsp.toBitVec + 8#64))
    (h12 : t'.regs.r12 = t.regs.r12) (h13 : t'.regs.r13 = t.regs.r13)
    (h14 : t'.regs.r14 = t.regs.r14) (h15 : t'.regs.r15 = t.regs.r15) :
    Kg (View S g ∗ F) s ra (fr s w) t' := by
  have rd0 := h.kb.rd_hi (lo := [w]) (hi := [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec]) rfl
    (i := 0) (by simp)
  have rd1 := h.kb.rd_hi (lo := [w]) (hi := [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec]) rfl
    (i := 1) (by simp)
  simp only [Nat.mul_zero, Nat.mul_one, BitVec.add_zero,
    List.getElem_cons_zero, List.getElem_cons_succ] at rd0 rd1
  exact h.kb.kg hm (by rw [hsp, h.kb.sp]; bv_omega)
    (UInt64.toBitVec_inj.mp (hbx.trans rd0)) (UInt64.toBitVec_inj.mp (hbp.trans rd1))
    (h12.trans h.r12) (h13.trans h.r13) (h14.trans h.r14) (h15.trans h.r15)
end

def Inv (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) :
    CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .label l, t =>
    if l = Names.isAvailable then t = s.pushRa ra
    else if l = ".LB.Emission.isAvailable.0" then
      ∃ w, Bd S g F s ra w t
        ∧ al t = if res g s then 1#8 else 0#8
    else if l = ".LB.Emission.isAvailable.1" then
      ∃ w, Bd S g F s ra w t
        ∧ rdi t = S ∧ t.regs.rbp.toBitVec = slot g s
        ∧ canBeFreelyGenerated (StackSlot.ofWord (slot g s)) = false
    else False
  | .exit, _ => False

def V (l : Label) (_ : MachineData) : Nat :=
  if l = Names.isAvailable then 2 else if l = ".LB.Emission.isAvailable.1" then 1 else 0

def E (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) :
    Int64 → MachineData → Prop :=
  fun a t => a = ra ∧ VPost View G.Ok S F 3 (fun g' t => isAvailableQ g g' s t) s t
    ∧ Sep.mod.Agree s t

def Obl [Host] [FunDecls] (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)
    (blk : Program.Block) : Prop :=
  ∀ t, Inv S g F s ra blk.label t →
    let I' (c : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      Inv S g F s ra c u ∧ Program.Decreases V blk.label blk.idx t c j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels isAvailableAsm) (s.pushRa ra) I' (E S g F s ra)) t

section
variable [Host] [FunDecls] (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)

theorem b_entry : isAvailableAsm.ForallBlocks fun blk =>
    blk.label = .entry → Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  kvcgen64
  simp only [Inv, Names.isAvailable, ↓reduceIte]
  exact ht

theorem b_fn (hp : VPre View G.Ok S g F isAvailableA 3 s) (w x y : Word)
    (hk0 : Kg (View S g ∗ F) s ra [w, x, y] (s.pushRa ra)) :
    isAvailableAsm.ForallBlocks fun blk =>
      blk.label = .label Names.isAvailable → Obl S g F s ra blk := by
  cfg_block [Obl, Names.isAvailable]
  intro t ht
  simp only [Inv, Names.isAvailable, ↓reduceIte] at ht
  subst ht
  have ⟨hpush, hm⟩ := hk0.pushes (xs := [(s.pushRa ra).regs.rbp.toBitVec, (s.pushRa ra).regs.rbx.toBitVec]) (by simp)
  simp only [PushOk, pushes, List.length_cons, List.length_nil, List.take_succ_cons,
    List.take_zero, List.reverse_cons, List.reverse_nil, List.nil_append] at hpush hm
  obtain ⟨hp0, hp1, -⟩ := hpush
  have hm' := (sep_lc _ _ _) ▸ hm
  have hi : (rsi s).toNat < g.h.n.toNat := hp.args
  have hrdi : (s.pushRa ra).regs.rdi.toBitVec = S := hp.rdi
  have hrsi : (s.pushRa ra).regs.rsi.toBitVec = rsi s := rfl
  have hrd : rd _ S = g.h.tgt := rd_of_eq hm' (by unfold View Em; ecancel)
  have hword := View.rd_tgt hm' hi
  have hkind := View.rdb_tgt_byte hm' hi (j := 4) (by decide)
  have hop := View.rdb_tgt_byte hm' hi (j := 5) (by decide)
  unfold rd at hrd hword
  unfold rdb at hkind hop
  have lm0 : (_ : Option Int).isSome = true := isSome_of_eq g.h.tgt hm' (a := S)
    (by unfold View Em; ecancel)
  have lm1 := View.isSome_tgt hm' hi
  obtain ⟨_, hb4⟩ := View.b8_tgt hm' hi (j := 4) (by decide)
  obtain ⟨_, hb5⟩ := View.b8_tgt hm' hi (j := 5) (by decide)
  have lm2 := B8.isSome hb4
  have lm3 := B8.isSome hb5
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hrdi, hrsi, hrd, fold_slot, hword, hkind, hop] at ⊢
  vc_by_shape
  | load => first
    | with_reducible exact hp0
    | with_reducible exact hp1
    | with_reducible exact lm0
    | with_reducible exact lm1
    | with_reducible exact lm2
    | with_reducible exact lm3
  | other => skip
  | goto ".LB.Emission.isAvailable.1" =>
    rename_i af hj
    symexec_norm at hj
    simp only [hrdi, hrsi, hrd, fold_slot, hkind, hop] at hj
    try simp only [kind_low] at hj
    idioms at hj
    simp only [Nat.reduceMul, free_test] at hj
    cfg_goto
    · apply MachineData.stackAtOrBelow_of_toNat_lt
      change ((s.pushRa ra).regs.rsp.toBitVec -
        ((s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64)).toNat < 2^63
      have e : ∀ q : Word, q - (q - 8#64 - 8#64) = 16#64 := by intro q; bv_omega
      rw [e]; decide
    · simp only [Inv, Names.isAvailable, String.reduceEq, ↓reduceIte]
      refine ⟨w, ⟨⟨?_, ?_⟩, rfl, rfl, rfl, rfl⟩, hrdi, ?_, ?_⟩
      · simpa only [fr, rsp, List.cons_append, List.nil_append, MachineData.pushRa, Reg64s.set64_rsp] using hm
      · have hsp := hk0.sp64
        change (s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64 = rsp s - 8#64 - 16#64
        rw [← Reg64s.get64_rsp, hsp]; bv_omega
      · simp only [slot, getElem!_pos g.tgt (rsi s).toNat hi]
      · simpa only [slot, getElem!_pos g.tgt (rsi s).toNat hi] using hj
    · simp only [V, Names.isAvailable, String.reduceEq, ↓reduceIte, Nat.reduceLT, true_or]
  all_goals try simp only [V, Names.isAvailable, String.reduceEq, ↓reduceIte, Nat.reduceLT, true_or]
  rename_i af hj
  symexec_norm at hj
  simp only [hrdi, hrsi, hrd, fold_slot, hkind, hop, kind_low] at hj
  idioms at hj
  simp only [Nat.reduceMul] at hj
  have hf : canBeFreelyGenerated (StackSlot.ofWord g.tgt[(rsi s).toNat]) = true := by
    rw [← free_test]
    simpa only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] using hj
  have hr : res g s = true := by
    simp only [res, Flat.isAvailable, get_target hp.ok hi, hf, Bool.true_or]
  simp only [Inv, Names.isAvailable, String.reduceEq, ↓reduceIte]
  refine ⟨w, ⟨⟨?_, ?_⟩, rfl, rfl, rfl, rfl⟩, ?_⟩
  · simpa only [fr, rsp, List.cons_append, List.nil_append, MachineData.pushRa,
      Reg64s.set64_rsp] using hm
  · have hsp := hk0.sp64
    change (s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64 = rsp s - 8#64 - 16#64
    rw [← Reg64s.get64_rsp, hsp]; bv_omega
  · simp only [al, rax, Reg64s.get64_rax, IsSpilled.setWidth_replaceLow]
    simp only [kind_low]
    idioms
    simp only [Nat.reduceMul, free_test, hf, hr]
    rfl


theorem b_0 (hok : g.Ok) : isAvailableAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Emission.isAvailable.0" → Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.isAvailable, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨w, hk, hres⟩ := ht
  have hp0 := hk.kb.isSome_hi (lo := [w]) (hi := [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec]) rfl
    (i := 0) (by simp)
  have hp1 := hk.kb.isSome_hi (lo := [w]) (hi := [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec]) rfl
    (i := 1) (by simp)
  simp only [Nat.mul_zero, Nat.mul_one, BitVec.add_zero] at hp0 hp1
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | load => first | exact hp0 | exact hp1
  | retAddr =>
    apply Option.isSome_iff_exists.mpr
    refine ⟨ra, ?_⟩
    apply Kg.retAddr
    apply hk.pop <;> rfl
  | ret =>
    refine Kg.vret (ok := G.Ok) (a' := g) (fr := fr s w) ?_ (by simp [fr]) hok ?_
    · apply hk.pop <;> rfl
    · intro t' _ hax
      exact ⟨rfl, by show (rax t').setWidth 8 = _; rw [hax]; exact hres⟩

theorem b_1 (hp : VPre View G.Ok S g F isAvailableA 3 s)
    (hspill : VSpec View G.Ok Names.isSpilled isSpilledA 0 isSpilledQ)
    (hcopy : VSpec View G.Ok Names.shallowestCopyPosition shallowestCopyA 0 shallowestCopyQ) :
    isAvailableAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.isAvailable.1" → Obl S g F s ra blk := by
  simp only [Names.isSpilled, Names.shallowestCopyPosition] at hspill hcopy
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.isAvailable, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨w, hk, hdi, hbp, hfree⟩ := ht
  kvcgen64 [hspill, hcopy]
  all_goals try symexec_norm
  refine Kb.vcall (V := View) (ok := G.Ok) (lo := [])
    (hi := [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec]) (w := w) (d := 16#64)
    (hk.kb.next rfl rfl) rfl rfl hdi hp.ok ?_ ?_
  · show ∀ i, spillId (StackSlot.ofWord t.regs.rbp.toBitVec) = some i → _
    rw [hbp, slot, getElem!_pos g.tgt (rsi s).toNat hp.args]
    exact fun _ h => List.mem_eraseDups.mpr
      (List.mem_filterMap.mpr ⟨_, by simp, h⟩)
  · intro u g' lo' w' hkb hl hq hok hag
    have hnil : lo' = [] := List.length_eq_zero_iff.mp hl
    subst lo'
    obtain ⟨he, hq⟩ := hq
    subst g'
    have hq' : al u = if Flat.isSpilled (flat g) (StackSlot.ofWord (slot g s)) then 1#8 else 0#8 := by
      simpa only [rsi, Reg64s.get64_rsi, hbp] using hq
    have hku : Bd S g F s ra w' u := by
      apply Bd.afterCall (hkb := hkb) (hag := hag)
      apply hk.next <;> rfl
    have hbu : u.regs.rbp.toBitVec = slot g s := by
      rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbp]
      exact hbp
    have hxu : u.regs.rbx.toBitVec = S := by
      rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbx]
      exact hdi
    kvcgen64 [hcopy]
    all_goals try symexec_norm at ⊢
    vc_by_shape
    | goto ".LB.Emission.isAvailable.0" =>
      rename_i hj
      have hn := al_ne hj
      have hs : Flat.isSpilled (flat g) (StackSlot.ofWord (slot g s)) = true := by
        cases he : Flat.isSpilled (flat g) (StackSlot.ofWord (slot g s)) <;>
          simp only [he, Bool.false_eq_true, ↓reduceIte] at hq' ⊢
        exact False.elim (hn hq')
      have hr : res g s = true := by
        simp only [res, Flat.isAvailable, target_slot hp.ok hp.args,
          hfree, hs, Bool.false_or, Bool.true_or]
      cfg_goto
      · exact (hku.kb.next rfl rfl).stack (by decide)
      · simp only [Inv, Names.isAvailable, String.reduceEq, ↓reduceIte]
        refine ⟨w', ?_, ?_⟩
        · apply hku.next <;> rfl
        · simpa only [al, rax, Reg64s.get64_rax, hr, hs, ↓reduceIte] using hq'
      · simp only [V, Names.isAvailable, String.reduceEq, ↓reduceIte, Nat.reduceLT, true_or]
    | other =>
      rename_i hj
      have hz := al_zero hj
      have hs : Flat.isSpilled (flat g) (StackSlot.ofWord (slot g s)) = false := by
        cases he : Flat.isSpilled (flat g) (StackSlot.ofWord (slot g s)) <;>
          simp only [he, Bool.false_eq_true, ↓reduceIte] at hq' ⊢
        change al u = 1#8 at hq'
        rw [hz] at hq'
        contradiction
      refine Kb.vcall (V := View) (ok := G.Ok) (lo := [])
        (hi := [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec]) (w := w') (d := 16#64)
        (hku.kb.next rfl rfl) rfl rfl hxu hp.ok trivial ?_
      intro v g' lo' w'' hkb hl hq hok hag'
      have hnil : lo' = [] := List.length_eq_zero_iff.mp hl
      subst lo'
      obtain ⟨he, hq⟩ := hq
      subst g'
      have hq'' : rax v = Flat.shallowestCopyPosition (flat g) (StackSlot.ofWord (slot g s)) := by
        simpa only [rsi, Reg64s.get64_rsi, hbu] using hq
      have hkv : Bd S g F s ra w'' v := by
        apply Bd.afterCall (hkb := hkb) (hag := hag')
        apply hku.next <;> rfl
      kvcgen64
      all_goals try symexec_norm at ⊢
      cfg_goto
      · exact (hkv.kb.next rfl rfl).stack (by decide)
      · simp only [Inv, Names.isAvailable, String.reduceEq, ↓reduceIte]
        refine ⟨w'', ?_, ?_⟩
        · apply hkv.next <;> rfl
        · simp only [al, rax, Reg64s.get64_rax, IsSpilled.setWidth_replaceLow]
          idioms
          simp only [res, Flat.isAvailable, target_slot hp.ok hp.args,
            hfree, hs, Bool.false_or]
          have heq : v.regs.rax.toBitVec =
              Flat.shallowestCopyPosition (flat g) (StackSlot.ofWord (slot g s)) := hq''
          rw [heq, neg_one_eq_none]
          by_cases he : Flat.shallowestCopyPosition (flat g) (StackSlot.ofWord (slot g s)) = Flat.NONE
          · simp only [he, beq_self_eq_true, Bool.not_true, Bool.toNat_false, ne_eq,
              not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
          · simp only [beq_eq_false_iff_ne.mpr he, Bool.not_false, Bool.toNat_true,
              decide_eq_true he, ↓reduceIte]

      · simp only [V, Names.isAvailable, String.reduceEq, ↓reduceIte, Nat.reduceLT, true_or]
end

theorem isAvailable_vthm [Host] [FunDecls]
    (hspill : VSpec View G.Ok Names.isSpilled isSpilledA 0 isSpilledQ)
    (hcopy : VSpec View G.Ok Names.shallowestCopyPosition shallowestCopyA 0 shallowestCopyQ) :
    VThm View G.Ok isAvailableAsm isAvailableA 3 isAvailableQ := by
  intro S g F s ra
  refine ⟨fun t ⟨ht, hp⟩ => ?_⟩
  subst ht
  obtain ⟨fr₀, hfr, hk0⟩ := hp.kg ra
  match fr₀, hfr, hk0 with
  | [w, x, y], _, hk0 =>
  refine Program.WP.cfg (Inv S g F s ra) V ?_ rfl
  refine forallBlocks_cases [.entry, .label Names.isAvailable,
    .label ".LB.Emission.isAvailable.0", .label ".LB.Emission.isAvailable.1"]
    (by simp only [Names.isAvailable]; cfg_labels) ?_
  intro l hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · exact b_entry S g F s ra
  · exact b_fn S g F s ra hp w x y hk0
  · exact b_0 S g F s ra hp.ok
  · exact b_1 S g F s ra hp hspill hcopy

end AvailableU

theorem isAvailable_unit [Host] [FunDecls]
    (hspill : Sep.Spec Names.isSpilled isSpilledA 0 isSpilledQ)
    (hcopy : Sep.Spec Names.shallowestCopyPosition shallowestCopyA 0 shallowestCopyQ) :
    UnitThm isAvailableAsm isAvailableA 3 isAvailableQ :=
  emissionUnit (AvailableU.isAvailable_vthm (emissionVSpec hspill) (emissionVSpec hcopy))

end FlatShuffler.Unit
