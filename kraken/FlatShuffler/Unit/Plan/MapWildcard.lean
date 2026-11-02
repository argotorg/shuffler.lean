module

public import FlatShuffler.Unit.Plan.MapClosest
import all FlatShuffler.Unit.Plan.MapClosest

@[expose] public section

/-!
# `MappingBuilder::mapWildcardSlotCopies`

`Names.mapWildcardSlotCopies` in `build/kraken/c/build_bottom_up.S`: if `n = 0` it returns `DONE` at once. Else it pushes
`r13`, `r12`, `rbp`, `rbx` and runs the loop over the targets `rbx < n`. `rbp` is the builder and
`r12` the kind of target `rbx`. Each turn of the loop is one unfold of `Flat.wildcardFrom`: for a
target with no source that is not a wildcard, `closestCopy` gives a copy in a wildcard slot. A
return label is mapped at once. For other kinds the unit sets `m_sawWildcardCopy` (byte 56) and
maps the copy only if the strategy (byte 40) is `TakeWildcardCopies`. The unit never clears
byte 56, thus the flat result `false` keeps the byte. The frame of the loop is the four free words
of `closestCopy`, the return slot of the callees and the saved `rbx`, `rbp`, `r12`, `r13`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit

open FlatShuffler.Sep

-- Byte 56 of the builder after the flat `saw`.
def sawB (b : BG) (sw : Bool) : BitVec 8 := bif sw then 1#8 else b.saw

def mapWildA (_ : BG) (_ : MachineData) : Prop := True

def mapWildQ (b b' : BG) (_ t : MachineData) : Prop :=
  al t = code (Flat.mapWildcardSlotCopies b.fl b.M false).1
    ∧ b' = { b with M := (Flat.mapWildcardSlotCopies b.fl b.M false).2.1,
                    saw := sawB b (Flat.mapWildcardSlotCopies b.fl b.M false).2.2 }

def mapWildX (b b' : BG) (_s _t : MachineData) : Prop :=
  (Flat.mapWildcardSlotCopies b.fl b.M false).1 = .assertionFailed ∧
    b' = { b with M := (Flat.mapWildcardSlotCopies b.fl b.M false).2.1,
                    saw := sawB b (Flat.mapWildcardSlotCopies b.fl b.M false).2.2 }

/-! ## The members `m_strategy` and `m_sawWildcardCopy` -/

section
variable {B : Addr} {b : BG} {F : MProp 64} {m : Mem 64}

theorem BView.rdb_strat (h : (BView B b ∗ F).get m) : rdb m (B + 40#64) = b.strat :=
  B8.rdb ((by unfold BView; ecancel : BView B b ∗ F = B8 (B + 40#64) b.strat ∗ _) ▸ h)

theorem BView.isSome_strat (h : (BView B b ∗ F).get m) :
    (m.loadInt (B + 40#64) 1).isSome = true :=
  B8.isSome ((by unfold BView; ecancel : BView B b ∗ F = B8 (B + 40#64) b.strat ∗ _) ▸ h)

theorem BView.isSome_saw (h : (BView B b ∗ F).get m) :
    (m.loadInt (B + 56#64) 1).isSome = true :=
  B8.isSome ((by unfold BView; ecancel : BView B b ∗ F = B8 (B + 56#64) b.saw ∗ _) ▸ h)

-- `movb $1, 56(%rbp)`
theorem BView.store_saw (h : (BView B b ∗ F).get m) {x : Int} (hx : BitVec.ofInt 8 x = 1#8) :
    (BView B { b with saw := 1#8 } ∗ F).get (m.storeInt (B + 56#64) 1 x) := by
  obtain ⟨R, e⟩ : ∃ R, ∀ v, BView B { b with saw := v } ∗ F = B8 (B + 56#64) v ∗ R :=
    ⟨_, fun v => by simp only [BView]; ecancel⟩
  rw [e, ← hx]
  exact B8.store ((e b.saw) ▸ h) x
end

namespace WildU

-- The frame of the body: the free words of `closestCopy`, the return slot of the callees, then
-- the saved `rbx`, `rbp`, `r12` and `r13`.
def fr (s : MachineData) (lo : List Word) (w : CopiesU.CallWords) : List Word :=
  lo ++ w.ret :: [w.pad, s.regs.rbx.toBitVec, s.regs.rbp.toBitVec, s.regs.r12.toBitVec, s.regs.r13.toBitVec]

-- The view in the loop: the `Mapping` so far and the flat `saw` so far.
abbrev bv (b : BG) (M : Flat.Mapping) (sw : Bool) : BG := { b with M := M, saw := sawB b sw }

-- The registers in the loop.
structure LI (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (M : Flat.Mapping) (sw : Bool) (lo : List Word) (w : CopiesU.CallWords) (t : MachineData) : Prop where
  kb : Kb (BView B (bv b M sw) ∗ F) s ra (fr s lo w) 40#64 t
  hl : lo.length = 4
  rbp : t.regs.rbp.toBitVec = B
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15

/-! ### One turn of the loop -/

-- The map of target `j` to the copy `c`, then the rest of the loop.
def step (fb : Flat.Builder) (M : Flat.Mapping) (sw : Bool) (c j : Word) :
    Flat.Status × Flat.Mapping × Bool :=
  let r := Flat.mbMap fb M c j
  if r.1 ≠ .done then (r.1, r.2, sw) else Flat.wildcardFrom fb r.2 sw (j + 1)

section
variable {fb : Flat.Builder} {M : Flat.Mapping} {sw : Bool} {j c : Word}

theorem from_ge (h : ¬ j < fb.n) : Flat.wildcardFrom fb M sw j = (.done, M, sw) := by
  rw [Flat.wildcardFrom, dite_eq_right h]

theorem skip_pos (h : j < fb.n) (hp : (!(Flat.get M.pos j == Flat.NONE)) = true) :
    Flat.wildcardFrom fb M sw j = Flat.wildcardFrom fb M sw (j + 1) := by
  rw [Flat.wildcardFrom, dite_eq_left h]
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hp
  simp [Flat.hasSourceAssigned, hp]

theorem skip_junk (h : j < fb.n) (hw : Flat.isWildcardTarget fb j = true) :
    Flat.wildcardFrom fb M sw j = Flat.wildcardFrom fb M sw (j + 1) := by
  rw [Flat.wildcardFrom, dite_eq_left h]
  simp [hw]

theorem skip_none (h : j < fb.n) (hc : Flat.closestCopy fb M j true = Flat.NONE) :
    Flat.wildcardFrom fb M sw j = Flat.wildcardFrom fb M sw (j + 1) := by
  rw [Flat.wildcardFrom, dite_eq_left h]
  simp [hc]

-- A return label: `map` at once.
theorem from_ret (h : j < fb.n) (hp : (!(Flat.get M.pos j == Flat.NONE)) = false)
    (hw : Flat.isWildcardTarget fb j = false) (hc : Flat.closestCopy fb M j true ≠ Flat.NONE)
    (hk : (Flat.get fb.target j).kind = FunctionReturnLabel) :
    Flat.wildcardFrom fb M sw j = step fb M sw (Flat.closestCopy fb M j true) j := by
  rw [Flat.wildcardFrom, dite_eq_left h]
  simp only [Bool.not_eq_false', beq_iff_eq] at hp
  simp [Flat.hasSourceAssigned, hp, hw, hc, hk, step]

-- Another kind with `TakeWildcardCopies`.
theorem from_take (h : j < fb.n) (hp : (!(Flat.get M.pos j == Flat.NONE)) = false)
    (hw : Flat.isWildcardTarget fb j = false) (hc : Flat.closestCopy fb M j true ≠ Flat.NONE)
    (hk : (Flat.get fb.target j).kind ≠ FunctionReturnLabel) (ht : fb.take = true) :
    Flat.wildcardFrom fb M sw j = step fb M true (Flat.closestCopy fb M j true) j := by
  rw [Flat.wildcardFrom, dite_eq_left h]
  simp only [Bool.not_eq_false', beq_iff_eq] at hp
  simp [Flat.hasSourceAssigned, hp, hw, hc, hk, ht, step]

-- Another kind without `TakeWildcardCopies`.
theorem from_skip (h : j < fb.n) (hp : (!(Flat.get M.pos j == Flat.NONE)) = false)
    (hw : Flat.isWildcardTarget fb j = false) (hc : Flat.closestCopy fb M j true ≠ Flat.NONE)
    (hk : (Flat.get fb.target j).kind ≠ FunctionReturnLabel) (ht : fb.take = false) :
    Flat.wildcardFrom fb M sw j = Flat.wildcardFrom fb M true (j + 1) := by
  rw [Flat.wildcardFrom, dite_eq_left h]
  simp only [Bool.not_eq_false', beq_iff_eq] at hp
  simp [Flat.hasSourceAssigned, hp, hw, hc, hk, ht]

theorem step_done (hd : (Flat.mbMap fb M c j).1 = .done) :
    step fb M sw c j = Flat.wildcardFrom fb (Flat.mbMap fb M c j).2 sw (j + 1) := by
  simp [step, hd]

theorem step_fail (hd : (Flat.mbMap fb M c j).1 ≠ .done) :
    step fb M sw c j = ((Flat.mbMap fb M c j).1, (Flat.mbMap fb M c j).2, sw) := by
  simp [step, hd]

-- `cmpb $3, %r12b`: the kind is a return label.
theorem ret_flag {x : BitVec 8} (hk : x = (Flat.get fb.target j).kind) :
    (x - 3#8 == BitVec.zero 8) = ((Flat.get fb.target j).kind == FunctionReturnLabel) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← hk]
  unfold FunctionReturnLabel
  constructor <;> intro h <;> bv_decide

-- `cmpb $1, 40(%rbp)`: the strategy is `TakeWildcardCopies`.
theorem take_flag (b : BG) : (b.strat - 1#8 == BitVec.zero 8) = b.fl.take := by
  rw [Bool.eq_iff_iff, beq_iff_eq]
  show _ ↔ (b.strat == 1#8) = true
  rw [beq_iff_eq]
  constructor <;> intro h <;> bv_decide
end

/-! ### The registers -/

section
variable {B : Addr} {b : BG} {F : MProp 64} {s t t' : MachineData} {ra : Int64}
  {M : Flat.Mapping} {sw : Bool} {lo : List Word} {w : CopiesU.CallWords}

theorem LI.next (h : LI B b F s ra M sw lo w t) (hm : t'.dmem = t.dmem)
    (hsp : t'.regs.rsp = t.regs.rsp) (hbp : t'.regs.rbp = t.regs.rbp)
    (h14 : t'.regs.r14 = t.regs.r14) (h15 : t'.regs.r15 = t.regs.r15) :
    LI B b F s ra M sw lo w t' :=
  ⟨h.kb.next hm hsp, h.hl, by rw [hbp]; exact h.rbp, h14 ▸ h.r14, h15 ▸ h.r15⟩

theorem LI.stk (h : LI B b F s ra M sw lo w t) (hm : t'.dmem = t.dmem)
    (hsp : t'.regs.rsp = t.regs.rsp) : t'.StackAtOrBelow (s.pushRa ra) :=
  (h.kb.next hm hsp).stack (by decide)

-- `movb $1, 56(%rbp)`: the flat `saw` is `true`.
theorem LI.saw (h : LI B b F s ra M sw lo w t) {x : Int} (hx : BitVec.ofInt 8 x = 1#8)
    (hm : t'.dmem = t.dmem.storeInt (B + 56#64) 1 x)
    (hsp : t'.regs.rsp = t.regs.rsp) (hbp : t'.regs.rbp = t.regs.rbp)
    (h14 : t'.regs.r14 = t.regs.r14) (h15 : t'.regs.r15 = t.regs.r15) :
    LI B b F s ra M true lo w t' := by
  have hb := h.kb.mem
  rw [sep_lc] at hb
  have hs := BView.store_saw hb hx
  rw [sep_lc, ← hm] at hs
  exact ⟨⟨hs, hsp ▸ h.kb.sp⟩, h.hl, by rw [hbp]; exact h.rbp, h14 ▸ h.r14, h15 ▸ h.r15⟩

-- The state after a call: the callees keep `rbx`, `rbp` and `r12`…`r15`.
theorem LI.after {c : MachineData} {M' : Flat.Mapping} {a' : BG} {xs lo' : List Word} {w' : Word}
    (hag : Sep.mod.Agree c t) (h : LI B b F s ra M sw lo w c)
    (hkb : Kb (BView B a' ∗ F) s ra (xs ++ lo' ++ w' ::
      [w.pad, s.regs.rbx.toBitVec, s.regs.rbp.toBitVec, s.regs.r12.toBitVec, s.regs.r13.toBitVec]) 40#64 t)
    (hl : (xs ++ lo').length = 4) (ha : a' = bv b M' sw) :
    LI B b F s ra M' sw (xs ++ lo') ⟨w', w.pad⟩ t ∧ t.regs.rbx = c.regs.rbx ∧ t.regs.r12 = c.regs.r12 := by
  subst ha
  refine ⟨⟨by rw [fr]; exact hkb, hl, ?_, ?_, ?_⟩,
    mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbx,
    mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r12⟩
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbp]; exact h.rbp
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r14]; exact h.r14
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r15]; exact h.r15

theorem pop_addr (a : Word) :
    8#64 + a = a + BitVec.ofNat 64 (8 * 1) ∧
      8#64 + a + 8#64 = a + BitVec.ofNat 64 (8 * 2) ∧
      8#64 + a + 8#64 + 8#64 = a + BitVec.ofNat 64 (8 * 3) ∧
      8#64 + a + 8#64 + 8#64 + 8#64 = a + BitVec.ofNat 64 (8 * 4) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_omega

theorem LI.kb' (h : LI B b F s ra M sw lo w t) :
    Kb (BView B (bv b M sw) ∗ F) s ra ((lo ++ [w.ret]) ++
      [w.pad, s.regs.rbx.toBitVec, s.regs.rbp.toBitVec, s.regs.r12.toBitVec, s.regs.r13.toBitVec])
      40#64 t := by
  simpa [fr] using h.kb

theorem LI.pop_isSome (h : LI B b F s ra M sw lo w t) :
    (t.dmem.loadInt (8#64 + t.regs.rsp.toBitVec) 8).isSome = true
      ∧ (t.dmem.loadInt (8#64 + t.regs.rsp.toBitVec + 8#64) 8).isSome = true
      ∧ (t.dmem.loadInt (8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64) 8).isSome = true
      ∧ (t.dmem.loadInt (8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64) 8).isSome = true := by
  obtain ⟨e0, e1, e2, e3⟩ := pop_addr t.regs.rsp.toBitVec
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e0]; exact Kb.isSome_hi h.kb' rfl (by simp)
  · rw [e1]; exact Kb.isSome_hi h.kb' rfl (by simp)
  · rw [e2]; exact Kb.isSome_hi h.kb' rfl (by simp)
  · rw [e3]; exact Kb.isSome_hi h.kb' rfl (by simp)

theorem LI.pop_kg (h : LI B b F s ra M sw lo w t) (hm : t'.dmem = t.dmem)
    (hsp : t'.regs.rsp.toBitVec = t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64 + 8#64)
    (hbx : t'.regs.rbx.toBitVec = rd t.dmem (8#64 + t.regs.rsp.toBitVec))
    (hbp : t'.regs.rbp.toBitVec = rd t.dmem (8#64 + t.regs.rsp.toBitVec + 8#64))
    (h12 : t'.regs.r12.toBitVec = rd t.dmem (8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64))
    (h13 : t'.regs.r13.toBitVec = rd t.dmem (8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64))
    (h14 : t'.regs.r14 = t.regs.r14) (h15 : t'.regs.r15 = t.regs.r15) :
    Kg (BView B (bv b M sw) ∗ F) s ra (fr s lo w) t' := by
  obtain ⟨e0, e1, e2, e3⟩ := pop_addr t.regs.rsp.toBitVec
  refine h.kb.kg hm ?_ ?_ ?_ ?_ ?_ (h14.trans h.r14) (h15.trans h.r15)
    <;> (try apply UInt64.toBitVec_inj.mp)
  · rw [hsp, h.kb.sp]; bv_omega
  · rw [hbx, e0]; exact Kb.rd_hi h.kb' rfl (i := 1) (by simp)
  · rw [hbp, e1]; exact Kb.rd_hi h.kb' rfl (i := 2) (by simp)
  · rw [h12, e2]; exact Kb.rd_hi h.kb' rfl (i := 3) (by simp)
  · rw [h13, e3]; exact Kb.rd_hi h.kb' rfl (i := 4) (by simp)
end

/-! ### The invariant, the variant and the obligation of a block -/

-- The result of the unit.
abbrev res (b : BG) : Flat.Status × Flat.Mapping × Bool :=
  Flat.mapWildcardSlotCopies b.fl b.M false

def Inv (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64) (fr₀ : List Word) :
    CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .exit, _ => False
  | .label l, t =>
    if l = Names.mapWildcardSlotCopies then t = s.pushRa ra
    else if l = ".LB.MappingBuilder.mapWildcardSlotCopies.0" then
      ∃ M sw lo w, LI B b F s ra M sw lo w t
      ∧ t.regs.rbx.toBitVec.toNat < b.n.toNat ∧ t.regs.rax.toBitVec.toNat < b.m.toNat
      ∧ step b.fl M sw t.regs.rax.toBitVec t.regs.rbx.toBitVec = res b
    else if l = ".LB.MappingBuilder.mapWildcardSlotCopies.1" then
      ∃ M sw lo w, LI B b F s ra M sw lo w t
      ∧ t.regs.rbx.toBitVec.toNat < b.n.toNat
      ∧ Flat.wildcardFrom b.fl M sw (t.regs.rbx.toBitVec + 1#64) = res b
    else if l = ".LB.MappingBuilder.mapWildcardSlotCopies.2" then
      ∃ M sw lo w, LI B b F s ra M sw lo w t
      ∧ t.regs.rbx.toBitVec.toNat < b.n.toNat
      ∧ Flat.wildcardFrom b.fl M sw t.regs.rbx.toBitVec = res b
    else if l = ".LB.MappingBuilder.mapWildcardSlotCopies.3" then
      ∃ M sw lo w, LI B b F s ra M sw lo w t ∧ res b = (.done, M, sw)
    else if l = ".LB.MappingBuilder.mapWildcardSlotCopies.4" then
      ∃ M sw lo w, LI B b F s ra M sw lo w t ∧ al t = code (res b).1 ∧ (res b).2 = (M, sw)
    else if l = ".LB.MappingBuilder.mapWildcardSlotCopies.5" then
      Kg (BView B b ∗ F) s ra fr₀ t ∧ res b = (.done, b.M, false)
    else False

-- The variant. A turn of the loop decreases `n - rbx`.
def V (b : BG) (l : Label) (t : MachineData) : Nat :=
  if l = Names.mapWildcardSlotCopies then 2 ^ 70
  else if l = ".LB.MappingBuilder.mapWildcardSlotCopies.0" then
    3 * (b.n.toNat - t.regs.rbx.toBitVec.toNat)
  else if l = ".LB.MappingBuilder.mapWildcardSlotCopies.1" then
    3 * (b.n.toNat - t.regs.rbx.toBitVec.toNat) - 1
  else if l = ".LB.MappingBuilder.mapWildcardSlotCopies.2" then
    3 * (b.n.toNat - t.regs.rbx.toBitVec.toNat) + 1
  else 0

def E [Labels] (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64) :
    Int64 → MachineData → Prop :=
  fun a t => a = ra ∧ VPost BView BG.Ok B F 10 (fun a' t => mapWildQ b a' s t) s t
    ∧ Sep.mod.Agree s t
    ∨ a = label "exit" ∧ t.regs.get64 .rdi = 1#64 ∧
      VPost BView BG.Ok B F 10 (fun a' t => mapWildX b a' s t) s t

def Obl [Host] [FunDecls] (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (fr₀ : List Word) (blk : Program.Block) : Prop :=
  ∀ t, Inv B b F s ra fr₀ blk.label t →
    let I' (c : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      Inv B b F s ra fr₀ c u ∧ Program.Decreases (V b) blk.label blk.idx t c j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels mapWildcardSlotCopiesAsm) (s.pushRa ra) I'
        (E B b F s ra)) t

def labels : List CfgLabel :=
  [.entry, .label Names.mapWildcardSlotCopies,
    .label ".LB.MappingBuilder.mapWildcardSlotCopies.0",
    .label ".LB.MappingBuilder.mapWildcardSlotCopies.1",
    .label ".LB.MappingBuilder.mapWildcardSlotCopies.2",
    .label ".LB.MappingBuilder.mapWildcardSlotCopies.3",
    .label ".LB.MappingBuilder.mapWildcardSlotCopies.4",
    .label ".LB.MappingBuilder.mapWildcardSlotCopies.5"]

theorem labels_cover : mapWildcardSlotCopiesAsm.ForallBlocks fun blk => blk.label ∈ labels := by
  simp only [labels, Names.mapWildcardSlotCopies]
  cfg_labels

macro "mw_inv" : tactic => `(tactic|
  simp only [Inv, Names.mapWildcardSlotCopies, String.reduceEq, ↓reduceIte])
macro "mw_inv" "at" h:ident : tactic => `(tactic|
  simp only [Inv, Names.mapWildcardSlotCopies, String.reduceEq, ↓reduceIte] at $h:ident)
macro "mw_var" : tactic => `(tactic|
  simp only [V, Names.mapWildcardSlotCopies, String.reduceEq, ↓reduceIte])

/-! ### The blocks -/

open ShallowestCopy CopiesU

section
variable [Host] [FunDecls] (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64)
  (fr₀ : List Word)

set_option maxHeartbeats 100000 in
theorem b_entry : mapWildcardSlotCopiesAsm.ForallBlocks fun blk =>
    blk.label = .entry → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  kvcgen64
  mw_inv
  exact ht

set_option maxHeartbeats 100000 in
theorem b_fn (hpre : VPre BView BG.Ok B b F mapWildA 10 s) (w₀ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ : Word)
    (hk0 : Kg (BView B b ∗ F) s ra [w₀, w₁, w₂, w₃, w₄, w₅, w₆, w₇, w₈, w₉] (s.pushRa ra)) :
    mapWildcardSlotCopiesAsm.ForallBlocks fun blk =>
      blk.label = .label Names.mapWildcardSlotCopies
        → Obl B b F s ra [w₀, w₁, w₂, w₃, w₄, w₅, w₆, w₇, w₈, w₉] blk := by
  cfg_block [Obl, Names.mapWildcardSlotCopies]
  intro t ht
  mw_inv at ht
  subst ht
  have hrdi : (s.pushRa ra).regs.rdi.toBitVec = B := by
    simpa [MachineData.pushRa] using hpre.rdi
  have hm0 := hk0.vmem
  have hq : (s.pushRa ra).regs.rsp.toBitVec = rsp s - 8#64 := by
    rw [← Reg64s.get64_rsp, hk0.sp64]
  have hsp4 : (s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 = rsp s - 8#64 - 40#64 := by
    rw [hq]; bv_omega
  obtain ⟨hpo, hpm⟩ := hk0.pushes (xs := [(s.pushRa ra).regs.r13.toBitVec,
    (s.pushRa ra).regs.r12.toBitVec, (s.pushRa ra).regs.rbp.toBitVec,
    (s.pushRa ra).regs.rbx.toBitVec]) (by simp)
  simp only [pushes] at hpm
  change (Stk (rsp s) (fr s [w₀, w₁, w₂, w₃] ⟨w₄, w₅⟩) ra.toBitVec ∗ BView B b ∗ F).get _ at hpm
  simp only [PushOk] at hpo
  obtain ⟨p1, p2, p3, p4, -⟩ := hpo
  have h_n := BView.rd_n hm0
  unfold rd at h_n
  have k_n := BView.isSome_n hm0
  clear hm0
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [hrdi, h_n, sub_beq_zero] at *
  vc_by_shape
  | load =>
    first
    | with_reducible exact k_n
    | with_reducible exact p1
    | with_reducible exact p2
    | with_reducible exact p3
    | with_reducible exact p4
  | goto ".LB.MappingBuilder.mapWildcardSlotCopies.5" =>
    rename_i hc
    have h0 := beq_iff_eq.mp hc
    cfg_goto
    · exact (hk0.next rfl rfl rfl rfl rfl rfl rfl rfl).stack
    · mw_inv
      exact ⟨hk0.next rfl rfl rfl rfl rfl rfl rfl rfl,
        from_ge (by show ¬ (0 : Word) < b.n; rw [h0]; decide)⟩
    · simp [V, Names.mapWildcardSlotCopies]
  | goto ".LB.MappingBuilder.mapWildcardSlotCopies.2" =>
    rename_i hc
    have h0 : b.n ≠ 0#64 := by simpa using hc
    have hpos : 0 < b.n.toNat := Nat.pos_of_ne_zero fun h => h0 (BitVec.eq_of_toNat_eq h)
    cfg_goto
    · exact Kb.stack ⟨hpm, hsp4⟩ (by decide)
    · mw_inv
      exact ⟨b.M, false, [w₀, w₁, w₂, w₃], ⟨w₄, w₅⟩, ⟨⟨hpm, hsp4⟩, rfl,
        by simpa [MachineData.pushRa] using hpre.rdi, rfl, rfl⟩, hpos, rfl⟩
    · left; have := b.n.isLt; simp [V, Names.mapWildcardSlotCopies]; omega

set_option maxHeartbeats 100000 in
theorem b_0 (hout : ∀ l ∈ Program.labels mapWildcardSlotCopiesAsm, label l ≠ label "exit")
    (hmap : BSpecWithExit Names.map mapA 2 mapQ mapX) (hok : b.Ok) :
    mapWildcardSlotCopiesAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.mapWildcardSlotCopies.0" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  mw_inv at ht
  obtain ⟨M, sw, lo, w, hli, hlt, hcm, hrest⟩ := ht
  have hokM : BG.Ok (bv b M sw) := ⟨hok.m, hok.n, hok.sw, hok.tw, hok.db⟩
  simp only [Names.map] at hmap
  kvcgen64 [hmap]
  all_goals try symexec_norm
  vc_by_shape
  | other =>
    refine Kb.vcallWithExit_above (V := BView) (A := mapA) (Q := mapQ) (X := mapX) (S := B) (s := s) (ra := ra)
      (F := F) (a := bv b M sw) (xs := lo.take 2) (lo := lo.drop 2) (w := w.ret)
      (hi := [w.pad, s.regs.rbx.toBitVec, s.regs.rbp.toBitVec, s.regs.r12.toBitVec, s.regs.r13.toBitVec])
      (k := 2) ?kb rfl (by simp [hli.hl]) ?rdi hokM ?A ?normal ?abort
    case kb => rw [List.take_append_drop]; exact Kb.next hli.kb rfl rfl
    case rdi => exact hli.rbp
    case A => exact ⟨hcm, hlt⟩
    case normal =>
      intro t3 a'' lo'' w'' hkb3 hl3 hQ3 hok3 hag3
      obtain ⟨hli3, hbx3, -⟩ := LI.after (xs := lo.take 2) hag3 (hli.next rfl rfl rfl rfl rfl) hkb3
        (by simp [List.length_append, hl3, hli.hl]) hQ3.2
      have hal : al t3 = code (Flat.mbMap b.fl M t.regs.rax.toBitVec t.regs.rbx.toBitVec).1 := hQ3.1
      clear hQ3 hkb3
      kvcgen64
      all_goals try symexec_norm
      vc_by_shape
      | goto ".LB.MappingBuilder.mapWildcardSlotCopies.4" =>
        have hd := code_ne_zero fun e =>
          al_ne (by with_reducible assumption) (hal.trans e)
        have hf := hrest.symm.trans (step_fail hd)
        cfg_goto
        · exact hli3.stk rfl rfl
        · mw_inv
          exact ⟨_, sw, _, ⟨w'', w.pad⟩, hli3.next rfl rfl rfl rfl rfl, by simp only [res, hf]; exact hal,
            by simp only [res, hf]; rfl⟩
        · left; mw_var; omega
      | other =>
        have hd := code_eq_zero (hal.symm.trans
          (al_zero (by with_reducible assumption)))
        first
        | (left; mw_var; rw [hbx3]; omega)
        | (mw_inv
           refine ⟨_, sw, _, ⟨w'', w.pad⟩, hli3.next rfl rfl rfl rfl rfl, ?_, ?_⟩
           · show t3.regs.rbx.toBitVec.toNat < _; rw [hbx3]; exact hlt
           · show Flat.wildcardFrom _ _ _ (t3.regs.rbx.toBitVec + 1#64) = _
             rw [hbx3]
             exact (step_done hd).symm.trans hrest)
    case abort =>
      intro t3 a'' free v hmem hfree hrel hok3 harg
      obtain ⟨ha'', hf⟩ := hrel
      subst a''
      change Flat.mbMap b.fl M t.regs.rax.toBitVec t.regs.rbx.toBitVec =
        (.assertionFailed, M) at hf
      have hd : (Flat.mbMap b.fl M t.regs.rax.toBitVec t.regs.rbx.toBitVec).1 ≠ .done := by
        rw [hf]
        change Flat.Status.assertionFailed ≠ Flat.Status.done
        decide
      have hmodel : res b = (.assertionFailed, M, sw) := by
        change Flat.mapWildcardSlotCopies b.fl b.M false = _
        rw [← hrest, step_fail hd, hf]
      refine Or.inr ⟨Or.inr ⟨rfl, harg, ?_⟩, ?_⟩
      · refine ⟨bv b M sw, ?_, hokM,
          lo.take 2 ++ free ++ v :: [w.pad, s.regs.rbx.toBitVec, s.regs.rbp.toBitVec,
            s.regs.r12.toBitVec, s.regs.r13.toBitVec], ra.toBitVec,
          by simp [hfree, hli.hl], ?_⟩
        · change (res b).1 = .assertionFailed ∧ bv b M sw =
            { b with M := (res b).2.1, saw := sawB b (res b).2.2 }
          rw [hmodel]
          exact ⟨rfl, rfl⟩
        · simpa only [MProp.sep_assoc] using hmem
      · intro l hl ha
        exact False.elim (hout l hl ha)

set_option maxHeartbeats 100000 in
theorem b_1 : mapWildcardSlotCopiesAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.mapWildcardSlotCopies.1" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  mw_inv at ht
  obtain ⟨M, sw, lo, w, hli, hlt, hrest⟩ := ht
  have hb := hli.kb.mem
  rw [sep_lc] at hb
  have hbp := hli.rbp
  have h_n := BView.rd_n hb
  unfold rd at h_n
  have k_n := BView.isSome_n hb
  clear hb
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [hbp, h_n] at *
  vc_by_shape
  | load => with_reducible exact k_n
  | goto ".LB.MappingBuilder.mapWildcardSlotCopies.3" =>
    have hge := InPlaceU.jnb_true _ _ (by assumption)
    rw [BitVec.add_comm] at hge
    cfg_goto
    · exact hli.stk rfl rfl
    · mw_inv
      exact ⟨M, sw, lo, w, hli.next rfl rfl rfl rfl rfl,
        hrest.symm.trans (from_ge fun h => absurd (BitVec.lt_def.1 h) (Nat.not_lt.2 hge))⟩
    · left; mw_var; omega
  | other =>
    have hlt' := InPlaceU.jnb_false _ _ (by assumption)
    first
    | (left
       mw_var
       have e : (1#64 + t.regs.rbx.toBitVec).toNat = t.regs.rbx.toBitVec.toNat + 1 := by bv_omega
       omega)
    | (mw_inv
       refine ⟨M, sw, lo, w, hli.next rfl rfl rfl rfl rfl, hlt', ?_⟩
       rw [BitVec.add_comm]
       exact hrest)

set_option maxHeartbeats 100000 in
theorem b_2 (hout : ∀ l ∈ Program.labels mapWildcardSlotCopiesAsm, label l ≠ label "exit")
    (hcc : BSpec Names.closestCopy closestA 4 closestQ) (hmap : BSpecWithExit Names.map mapA 2 mapQ mapX)
    (hok : b.Ok) : mapWildcardSlotCopiesAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.mapWildcardSlotCopies.2" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  mw_inv at ht
  obtain ⟨M, sw, lo, w, hli, hlt, hrest⟩ := ht
  have hokM : BG.Ok (bv b M sw) := ⟨hok.m, hok.n, hok.sw, hok.tw, hok.db⟩
  have hb := hli.kb.mem
  rw [sep_lc] at hb
  have hbp := hli.rbp
  have hmax : t.regs.rbx.toBitVec.toNat < MAX_N := Nat.lt_of_lt_of_le hlt hok.n
  obtain ⟨_, hM⟩ := BView.mapM hb
  have h_tgt := BView.rd_tgt hb
  have h_mp := BView.rd_mp hb
  have h_pos := MapM.rd_pos hM hmax
  have h_kind := BView.rdb_kind hb hokM hlt
  unfold rd at h_tgt h_mp h_pos
  unfold rdb at h_kind
  have k_tgt := BView.isSome_tgt hb
  have k_mp := BView.isSome_mp hb
  have k_pos := MapM.isSome_pos hM hmax
  have k_kind := BView.isSome_kind hb hokM hlt
  clear hb hM
  simp only [Names.closestCopy] at hcc
  kvcgen64 [hcc]
  all_goals try symexec_norm
  all_goals try simp only [hbp, h_tgt, h_mp, fold_slot, slot_8192, h_pos, sub_beq_zero,
    neg_one_eq_none, zext_byte] at *
  vc_by_shape
  | load =>
    first
    | with_reducible exact k_mp
    | with_reducible exact k_pos
    | with_reducible exact k_tgt
    | with_reducible exact k_kind
  | goto ".LB.MappingBuilder.mapWildcardSlotCopies.1" =>
    have hskip : Flat.wildcardFrom b.fl M sw t.regs.rbx.toBitVec
        = Flat.wildcardFrom b.fl M sw (t.regs.rbx.toBitVec + 1#64) := by
      first
      | (refine skip_pos (BitVec.lt_def.2 hlt) ?_; with_reducible assumption)
      | (refine skip_junk (BitVec.lt_def.2 hlt) ?_
         exact (junk_flag (fb := b.fl) hlt h_kind).symm.trans ‹_›)
    cfg_goto
    · exact hli.stk rfl rfl
    · mw_inv
      exact ⟨M, sw, lo, w, hli.next rfl rfl rfl rfl rfl, hlt, hskip.symm.trans hrest⟩
    · left; mw_var; omega
  | other =>
    rename_i hp hj
    have hw : Flat.isWildcardTarget b.fl t.regs.rbx.toBitVec = false :=
      (junk_flag (fb := b.fl) hlt h_kind).symm.trans hj
    clear hj
    refine Kb.vcall_above (V := BView) (A := closestA) (Q := closestQ) (S := B) (s := s) (ra := ra)
      (F := F) (a := bv b M sw) (xs := []) (lo := lo) (w := w.ret)
      (hi := [w.pad, s.regs.rbx.toBitVec, s.regs.rbp.toBitVec, s.regs.r12.toBitVec, s.regs.r13.toBitVec])
      (k := 4) ?kb rfl hli.hl ?rdi hokM ?A ?_
    case kb => exact Kb.next hli.kb rfl rfl
    case rdi => exact hli.rbp
    case A => exact hlt
    intro t2 a' lo' w' hkb hl hQ hok' hag
    obtain ⟨hli2, hbx, h12⟩ := LI.after (xs := []) hag (hli.next rfl rfl rfl rfl rfl) hkb
      (by simpa using hl) hQ.1
    have hrax : t2.regs.rax.toBitVec = Flat.closestCopy b.fl M t.regs.rbx.toBitVec true := hQ.2
    have hk12 : BitVec.extractLsb' 0 8 t2.regs.r12.toBitVec
        = (Flat.get b.fl.target t.regs.rbx.toBitVec).kind := by
      rw [h12]; exact (zext_byte _).trans h_kind
    clear hQ hkb h12 h_kind
    have hbp2 := hli2.rbp
    have hb2 := hli2.kb.mem
    rw [sep_lc] at hb2
    have k_saw := BView.isSome_saw hb2
    have hs := BView.store_saw hb2 (x := 1) rfl
    have k_strat := BView.isSome_strat hs
    have h_strat : BitVec.ofInt 8 ((t2.dmem.storeInt (B + 56#64) 1 1).loadInt (B + 40#64) 1).get!
        = b.strat := (BView.rdb_strat hs :)
    clear hb2 hs
    have hlis := LI.saw hli2 (x := 1) (t' := { t2 with dmem := t2.dmem.storeInt (B + 56#64) 1 1 })
      rfl rfl rfl rfl rfl rfl
    have hokT : BG.Ok (bv b M true) := ⟨hok.m, hok.n, hok.sw, hok.tw, hok.db⟩
    simp only [Names.map] at hmap
    kvcgen64 [hmap]
    all_goals try symexec_norm
    all_goals try simp only [hbp2, h_strat, take_flag, ret_flag hk12, sub_beq_zero,
      neg_one_eq_none] at *
    vc_by_shape
    | load =>
      first
      | with_reducible exact k_saw
      | with_reducible exact k_strat
    | goto ".LB.MappingBuilder.mapWildcardSlotCopies.0" =>
      have hc : (t2.regs.rax.toBitVec == Flat.NONE) = false := by assumption
      have hk : (Flat.get b.fl.target t.regs.rbx.toBitVec).kind = FunctionReturnLabel := by
        exact beq_iff_eq.mp (by assumption)
      have hne : Flat.closestCopy b.fl M t.regs.rbx.toBitVec true ≠ Flat.NONE := by
        rw [← hrax]; exact fun e => by simp [e] at hc
      cfg_goto
      · exact hli2.stk rfl rfl
      · mw_inv
        refine ⟨M, sw, _, ⟨w', w.pad⟩, hli2.next rfl rfl rfl rfl rfl, ?_, ?_, ?_⟩
        · show t2.regs.rbx.toBitVec.toNat < _; rw [hbx]; exact hlt
        · show t2.regs.rax.toBitVec.toNat < _; rw [hrax]; exact BitVec.lt_def.1 (closestCopy_lt hne)
        · show step _ _ _ t2.regs.rax.toBitVec t2.regs.rbx.toBitVec = _
          rw [hrax, hbx]
          exact (from_ret (BitVec.lt_def.2 hlt) hp hw hne hk).symm.trans hrest
      · left; mw_var; rw [hbx]; omega
    | goto ".LB.MappingBuilder.mapWildcardSlotCopies.1" =>
      first
      | (have hn : Flat.closestCopy b.fl M t.regs.rbx.toBitVec true = Flat.NONE := by
           rw [← hrax]; exact beq_iff_eq.mp (by assumption)
         cfg_goto
         · exact hli2.stk rfl rfl
         · mw_inv
           refine ⟨M, sw, _, ⟨w', w.pad⟩, hli2.next rfl rfl rfl rfl rfl, ?_, ?_⟩
           · show t2.regs.rbx.toBitVec.toNat < _; rw [hbx]; exact hlt
           · show Flat.wildcardFrom _ _ _ (t2.regs.rbx.toBitVec + 1#64) = _
             rw [hbx]
             exact (skip_none (BitVec.lt_def.2 hlt) hn).symm.trans hrest
         · left; mw_var; rw [hbx]; omega)
      | (have hc : (t2.regs.rax.toBitVec == Flat.NONE) = false := by assumption
         have hr : ((Flat.get b.fl.target t.regs.rbx.toBitVec).kind == FunctionReturnLabel)
           = false := by assumption
         have ht : b.fl.take = false := by simpa using (by assumption : (!b.fl.take) = true)
         have hne : Flat.closestCopy b.fl M t.regs.rbx.toBitVec true ≠ Flat.NONE := by
           rw [← hrax]; exact fun e => by simp [e] at hc
         have hk : (Flat.get b.fl.target t.regs.rbx.toBitVec).kind ≠ FunctionReturnLabel :=
           fun e => by simp [e] at hr
         cfg_goto
         · exact hlis.stk rfl rfl
         · mw_inv
           refine ⟨M, true, _, ⟨w', w.pad⟩, hlis.next rfl rfl rfl rfl rfl, ?_, ?_⟩
           · show t2.regs.rbx.toBitVec.toNat < _; rw [hbx]; exact hlt
           · show Flat.wildcardFrom _ _ _ (t2.regs.rbx.toBitVec + 1#64) = _
             rw [hbx]
             exact (from_skip (BitVec.lt_def.2 hlt) hp hw hne hk ht).symm.trans hrest
         · left; mw_var; rw [hbx]; omega)
    | other =>
      have hc : (t2.regs.rax.toBitVec == Flat.NONE) = false := by assumption
      have hr : ((Flat.get b.fl.target t.regs.rbx.toBitVec).kind == FunctionReturnLabel)
        = false := by assumption
      have ht : b.fl.take = true := by simpa using (by assumption : (!b.fl.take) = false)
      have hne : Flat.closestCopy b.fl M t.regs.rbx.toBitVec true ≠ Flat.NONE := by
        rw [← hrax]; exact fun e => by simp [e] at hc
      have hk : (Flat.get b.fl.target t.regs.rbx.toBitVec).kind ≠ FunctionReturnLabel :=
        fun e => by simp [e] at hr
      have hstep := (from_take (BitVec.lt_def.2 hlt) hp hw hne hk ht).symm.trans hrest
      refine Kb.vcallWithExit_above (V := BView) (A := mapA) (Q := mapQ) (X := mapX) (S := B) (s := s) (ra := ra)
        (F := F) (a := bv b M true) (xs := lo'.take 2) (lo := lo'.drop 2) (w := w')
        (hi := [w.pad, s.regs.rbx.toBitVec, s.regs.rbp.toBitVec, s.regs.r12.toBitVec, s.regs.r13.toBitVec])
        (k := 2) ?kb rfl (by simp [hl]) ?rdi hokT ?A ?normal ?abort
      case kb => rw [List.take_append_drop]; exact Kb.next hlis.kb rfl rfl
      case rdi => exact hli2.rbp
      case A =>
        exact ⟨by show t2.regs.rax.toBitVec.toNat < _; rw [hrax]; exact BitVec.lt_def.1 (closestCopy_lt hne),
          by show t2.regs.rbx.toBitVec.toNat < _; rw [hbx]; exact hlt⟩
      case normal =>
        intro t3 a'' lo'' w'' hkb3 hl3 hQ3 hok3 hag3
        obtain ⟨hli3, hbx3, -⟩ := LI.after (xs := lo'.take 2) hag3 (hlis.next rfl rfl rfl rfl rfl) hkb3
          (by simp [List.length_append, hl3, hl]) hQ3.2
        have hal : al t3 = code (Flat.mbMap b.fl M t2.regs.rax.toBitVec t2.regs.rbx.toBitVec).1 := hQ3.1
        rw [hrax, hbx] at hal
        clear hQ3 hkb3
        kvcgen64
        all_goals try symexec_norm
        vc_by_shape
        | goto ".LB.MappingBuilder.mapWildcardSlotCopies.1" =>
          have hd := code_eq_zero (hal.symm.trans (al_zero (by
            first
            | with_reducible assumption
            | (rw [Bool.not_eq_false']; with_reducible assumption))))
          cfg_goto
          · exact hli3.stk rfl rfl
          · mw_inv
            refine ⟨_, true, _, ⟨w'', w.pad⟩, hli3.next rfl rfl rfl rfl rfl, ?_, ?_⟩
            · show t3.regs.rbx.toBitVec.toNat < _; rw [hbx3, hbx]; exact hlt
            · show Flat.wildcardFrom _ _ _ (t3.regs.rbx.toBitVec + 1#64) = _
              rw [hbx3, hbx, hrax]
              exact (step_done hd).symm.trans hstep
          · left; mw_var; rw [hbx3, hbx]; omega
        | goto ".LB.MappingBuilder.mapWildcardSlotCopies.4" =>
          have hd := code_ne_zero fun e => al_ne (by
            first
            | with_reducible assumption
            | (rw [Bool.not_eq_true']; with_reducible assumption)) (hal.trans e)
          have hf := hstep.symm.trans (step_fail hd)
          cfg_goto
          · exact hli3.stk rfl rfl
          · mw_inv
            exact ⟨_, true, _, ⟨w'', w.pad⟩, hli3.next rfl rfl rfl rfl rfl, by simp only [res, hf]; exact hal,
              by rw [hrax, hbx]; simp only [res, hf]; try rfl⟩
          · left; mw_var; omega
      case abort =>
        intro t3 a'' free v hmem hfree hrel hok3 harg
        obtain ⟨ha'', hf⟩ := hrel
        subst a''
        change Flat.mbMap b.fl M t2.regs.rax.toBitVec t2.regs.rbx.toBitVec =
          (.assertionFailed, M) at hf
        have hf' : Flat.mbMap b.fl M (Flat.closestCopy b.fl M t.regs.rbx.toBitVec true)
            t.regs.rbx.toBitVec = (.assertionFailed, M) := by
          simpa only [hrax, hbx] using hf
        have hd : (Flat.mbMap b.fl M (Flat.closestCopy b.fl M t.regs.rbx.toBitVec true)
            t.regs.rbx.toBitVec).1 ≠ .done := by
          rw [hf']
          change Flat.Status.assertionFailed ≠ Flat.Status.done
          decide
        have hmodel : res b = (.assertionFailed, M, true) := by
          change Flat.mapWildcardSlotCopies b.fl b.M false = _
          rw [← hstep, step_fail hd, hf']
        refine Or.inr ⟨Or.inr ⟨rfl, harg, ?_⟩, ?_⟩
        · refine ⟨bv b M true, ?_, hokT,
            lo'.take 2 ++ free ++ v :: [w.pad, s.regs.rbx.toBitVec, s.regs.rbp.toBitVec,
              s.regs.r12.toBitVec, s.regs.r13.toBitVec], ra.toBitVec,
            by simp [hfree, hl], ?_⟩
          · change (res b).1 = .assertionFailed ∧ bv b M true =
              { b with M := (res b).2.1, saw := sawB b (res b).2.2 }
            rw [hmodel]
            exact ⟨rfl, rfl⟩
          · simpa only [MProp.sep_assoc] using hmem
        · intro l hl ha
          exact False.elim (hout l hl ha)

set_option maxHeartbeats 100000 in
theorem b_3 : mapWildcardSlotCopiesAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.mapWildcardSlotCopies.3" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  mw_inv at ht
  obtain ⟨M, sw, lo, w, hli, hd⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | other =>
    first
    | (right; exact ⟨by mw_var, Nat.lt_succ_self _⟩)
    | (mw_inv
       exact ⟨M, sw, lo, w, hli.next rfl rfl rfl rfl rfl, by simp only [res, hd]; rfl,
         by simp only [res, hd]⟩)

set_option maxHeartbeats 100000 in
theorem b_4 (hok : b.Ok) : mapWildcardSlotCopiesAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.mapWildcardSlotCopies.4" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  mw_inv at ht
  obtain ⟨M, sw, lo, w, hli, hal, hM⟩ := ht
  obtain ⟨p0, p1, p2, p3⟩ := hli.pop_isSome
  have hokM : BG.Ok (bv b M sw) := ⟨hok.m, hok.n, hok.sw, hok.tw, hok.db⟩
  have hfl : (fr s lo w).length = 10 := by simp [fr, hli.hl]
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | load =>
    first
    | with_reducible exact p0
    | with_reducible exact p1
    | with_reducible exact p2
    | with_reducible exact p3
  | retAddr =>
    refine Option.isSome_iff_exists.mpr
      ⟨ra, Kg.retAddr (P := BView B (bv b M sw) ∗ F) (s := s) (fr := fr s lo w) ?_⟩
    exact hli.pop_kg rfl (by bv_omega) rfl rfl rfl rfl rfl rfl
  | ret =>
    refine ProofKit.intercept_mono_exit
      (E := fun a t => a = ra ∧
        VPost BView BG.Ok B F 10 (fun a' t => mapWildQ b a' s t) s t ∧
          Sep.mod.Agree s t) ?_ (fun h => Or.inl h)
    refine Kg.vret (ok := BG.Ok) (a' := bv b M sw)
      (hli.pop_kg rfl (by bv_omega) rfl rfl rfl rfl rfl rfl) hfl hokM
      fun t' _ hax => ⟨?_, by rw [hM]⟩
    simp only [al] at hal ⊢
    rw [hax]
    exact hal

set_option maxHeartbeats 100000 in
theorem b_5 (hok : b.Ok) (hfr : fr₀.length = 10) : mapWildcardSlotCopiesAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.mapWildcardSlotCopies.5" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  mw_inv at ht
  obtain ⟨hk, hd⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | retAddr =>
    exact Option.isSome_iff_exists.mpr ⟨ra, (hk.next rfl rfl rfl rfl rfl rfl rfl rfl).retAddr⟩
  | ret =>
    refine ProofKit.intercept_mono_exit
      (E := fun a t => a = ra ∧
        VPost BView BG.Ok B F 10 (fun a' t => mapWildQ b a' s t) s t ∧
          Sep.mod.Agree s t) ?_ (fun h => Or.inl h)
    refine Kg.vret (ok := BG.Ok) (a' := b) (hk.next rfl rfl rfl rfl rfl rfl rfl rfl) hfr hok
      fun t' _ hax => ⟨?_, by rw [hd]; rfl⟩
    simp only [al]
    rw [hax, hd]
    rfl

end

end WildU

open WildU in
theorem mapWildcardSlotCopies_unit [Host] [FunDecls]
    (hout : ∀ l ∈ Program.labels mapWildcardSlotCopiesAsm, label l ≠ label "exit")
    (hcc : BSpec Names.closestCopy closestA 4 closestQ) (hmap : BSpecWithExit Names.map mapA 2 mapQ mapX) :
    BThmWithExit mapWildcardSlotCopiesAsm mapWildA 10 mapWildQ mapWildX := by
  intro B b F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨fr₀, hfr, hk0⟩ := hpre.kg ra
  match fr₀, hfr, hk0 with
  | [w₀, w₁, w₂, w₃, w₄, w₅, w₆, w₇, w₈, w₉], hfr, hk0 =>
  refine Program.WP.cfg (WildU.Inv B b F s ra [w₀, w₁, w₂, w₃, w₄, w₅, w₆, w₇, w₈, w₉]) (WildU.V b)
    ?_ rfl
  refine forallBlocks_cases labels labels_cover fun l hl => ?_
  simp only [labels, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact b_entry B b F s ra _
  · exact b_fn B b F s ra hpre w₀ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ hk0
  · exact b_0 B b F s ra _ hout hmap hpre.ok
  · exact b_1 B b F s ra _
  · exact b_2 B b F s ra _ hout hcc hmap hpre.ok
  · exact b_3 B b F s ra _
  · exact b_4 B b F s ra _ hpre.ok
  · exact b_5 B b F s ra _ hpre.ok hfr

end FlatShuffler.Unit
