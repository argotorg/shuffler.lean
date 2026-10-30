import BbuKraken.Unit.Defs
import BbuKraken.Sep.Stores
import ProofKit.Cfg
import ProofKit.Idioms

/-!
# `generate`

`c/bbu/<Names.generate>.S`: 2 `pushq`, so 11 free words (2, and 9 for the call of `produce`).
It asserts `t < n`, calls `produce`, and then, if `t + 1 < size` and `t` is not final, swaps the
destinations of `t` and of the top slot (equal slots) or calls `swapWith(t)`.

The preconditions of the callees: `produceA` from the check `t < n` and `generateA`; after
`produce` the trace has one more record (`nops + 1 < 6n`) and the new slot is bound to `t < n`
(`DestOk`, `swapWithA`). The caller is `buildBottomUp`: `Inv.lt` gives `len < n` and
`nops + 3 ≤ 6n`, and `Inv.pos` gives `DestOk`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit
open Bbu.Sep

namespace Generate
/-! ## Loads of the struct -/

section
variable {S : Addr} {g : G} {F : MProp 64} {m : Mem 64}

theorem rd_n (h : (View S g ∗ F).get m) : rd m (Fld.targetSize S) = g.h.n :=
  rd_of_eq h (by unfold View Em; ecancel)

theorem isSome_n (h : (View S g ∗ F).get m) : (m.loadInt (Fld.targetSize S) 8).isSome = true :=
  isSome_of_eq g.h.n h (by unfold View Em; ecancel)

theorem rd_dest (h : (View S g ∗ F).get m) {i : Nat} (hi : i < MAX_N) :
    rd m (Fld.mapping_destinationOf S i) = g.h.dest[i] := by
  obtain ⟨R, h'⟩ := View.arr_dest h
  exact (Arr.rd h' (by simpa using hi)).trans (by simp)

theorem rd_stk (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat) :
    rd m (slotAt g.h.data i) = g.stk[i] :=
  let ⟨_, h⟩ := View.arr_stk h; (Arr.rd h (by simpa using hi)).trans (by simp)

end

/-! ## The stack: the two pushed registers -/

-- The frame of the callees: the pushed `rbx` and `rbp`, the return address and `F`.
def Fr (s : MachineData) (ra : Int64) (F : MProp 64) : MProp 64 :=
  Wd (rsp s - 24#64) s.regs.rbx.toBitVec ∗ Wd (rsp s - 16#64) s.regs.rbp.toBitVec
    ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F

-- The three top free words: the return address of a callee, `rbx` and `rbp`.
theorem stk3 (P : MProp 64) (sp : Addr) (fr : List Word) (w x y v : Word) (F : MProp 64) :
    P ∗ Stk sp (fr ++ [w, x, y]) v ∗ F
      = P ∗ Stk (sp - 24#64) fr w ∗ (Wd (sp - 24#64) x ∗ Wd (sp - 16#64) y ∗ Wd (sp - 8#64) v ∗ F) := by
  have e : fr ++ [w, x, y] = fr ++ [w] ++ [x] ++ [y] := by simp
  rw [e, Stk.call, Stk.call, Stk.call, show sp - 8#64 - 8#64 - 8#64 = sp - 24#64 by bv_omega,
    show sp - 8#64 - 8#64 = sp - 16#64 by bv_omega]

-- No free word for the callee: the free words go to the frame.
theorem stk_nil (P : MProp 64) (sp : Addr) (fr : List Word) (v : Word) (F : MProp 64) :
    P ∗ Stk sp fr v ∗ F
      = P ∗ Stk sp [] v ∗ (Arr (sp - 8#64 - BitVec.ofNat 64 (8 * fr.length)) fr ∗ F) := by
  unfold Stk
  simp only [Arr, MProp.emp_sep]
  ecancel

-- A state between the pushes and the pops: `rbx` is the argument, `rbp` is the struct, and the
-- stack holds 8 free words, the return address slot `w` of a callee, and `Fr`.
structure Mid (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) (fr : List Word)
    (w : Word) (t : MachineData) : Prop where
  len : fr.length = 8
  mem : (View S g ∗ Stk (rsp s - 24#64) fr w ∗ Fr s ra F).get t.dmem
  sp : t.regs.rsp.toBitVec = rsp s - 24#64
  bx : t.regs.rbx = s.regs.rsi
  bp : t.regs.rbp.toBitVec = S
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15

section
variable {S : Addr} {g : G} {F : MProp 64} {s : MachineData} {ra : Int64} {fr : List Word}
  {w : Word}

-- `pushq %rbp; pushq %rbx` from the entry stack (`r` is `rsp` after the call).
theorem Mid.push {m₀ : Mem 64} {x y : Word} {c : MachineData}
    (hm : (View S g ∗ Stk (rsp s) (fr ++ [w, x, y]) ra.toBitVec ∗ F).get m₀) (hfr : fr.length = 8)
    {r : Addr} (hr : r = rsp s - 8#64)
    (hc : c.dmem = (m₀.storeInt (r - 8#64) 8 s.regs.rbp.toBitVec.toInt).storeInt
      (r - 8#64 - 8#64) 8 s.regs.rbx.toBitVec.toInt)
    (hsp : c.regs.rsp.toBitVec = r - 8#64 - 8#64) (hbx : c.regs.rbx = s.regs.rsi)
    (hbp : c.regs.rbp.toBitVec = S) (h12 : c.regs.r12 = s.regs.r12)
    (h13 : c.regs.r13 = s.regs.r13) (h14 : c.regs.r14 = s.regs.r14)
    (h15 : c.regs.r15 = s.regs.r15) : Mid S g F s ra fr w c := by
  have e1 : r - 8#64 = rsp s - 16#64 := by subst hr; bv_omega
  have e2 : r - 8#64 - 8#64 = rsp s - 24#64 := by subst hr; bv_omega
  rw [e2, e1] at hc
  rw [e2] at hsp
  refine ⟨hfr, ?_, hsp, hbx, hbp, h12, h13, h14, h15⟩
  rw [stk3] at hm
  have h1 : (Wd (rsp s - 16#64) y ∗ (Wd (rsp s - 24#64) x ∗ View S g ∗ Stk (rsp s - 24#64) fr w
      ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F)).get m₀ := by
    have e : View S g ∗ Stk (rsp s - 24#64) fr w ∗ (Wd (rsp s - 24#64) x ∗ Wd (rsp s - 16#64) y
        ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F)
        = Wd (rsp s - 16#64) y ∗ (Wd (rsp s - 24#64) x ∗ View S g ∗ Stk (rsp s - 24#64) fr w
          ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F) := by ecancel
    exact e ▸ hm
  have h2 := Wd.store h1 s.regs.rbp.toBitVec
  have h3 : (Wd (rsp s - 24#64) x ∗ (Wd (rsp s - 16#64) s.regs.rbp.toBitVec ∗ View S g
      ∗ Stk (rsp s - 24#64) fr w ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F)).get
      (m₀.storeInt (rsp s - 16#64) 8 s.regs.rbp.toBitVec.toInt) := by
    have e : Wd (rsp s - 16#64) s.regs.rbp.toBitVec ∗ (Wd (rsp s - 24#64) x ∗ View S g
        ∗ Stk (rsp s - 24#64) fr w ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F)
        = Wd (rsp s - 24#64) x ∗ (Wd (rsp s - 16#64) s.regs.rbp.toBitVec ∗ View S g
          ∗ Stk (rsp s - 24#64) fr w ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F) := by ecancel
    exact e ▸ h2
  have h4 := Wd.store h3 s.regs.rbx.toBitVec
  rw [hc]
  have e : Wd (rsp s - 24#64) s.regs.rbx.toBitVec ∗ (Wd (rsp s - 16#64) s.regs.rbp.toBitVec
      ∗ View S g ∗ Stk (rsp s - 24#64) fr w ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F)
      = View S g ∗ Stk (rsp s - 24#64) fr w ∗ Fr s ra F := by unfold Fr; ecancel
  exact e ▸ h4

-- The precondition of a callee with 8 free words.
theorem Mid.pre {A : G → MachineData → Prop} {c : MachineData} (h : Mid S g F s ra fr w c)
    (hdi : rdi c = S) (hok : g.Ok) (hA : A g c) : Sep.Pre S g (Fr s ra F) A 8 c :=
  ⟨hdi, hok, ⟨fr, w, h.len, by simpa only [rsp, Reg64s.get64_rsp, h.sp] using h.mem⟩, hA⟩

-- The precondition of a callee with no free word.
theorem Mid.pre0 {A : G → MachineData → Prop} {c : MachineData} (h : Mid S g F s ra fr w c)
    (hdi : rdi c = S) (hok : g.Ok) (hA : A g c) :
    Sep.Pre S g (Arr (rsp s - 24#64 - 8#64 - BitVec.ofNat 64 (8 * fr.length)) fr ∗ Fr s ra F) A 0 c :=
  ⟨hdi, hok, ⟨[], w, rfl, by
    simpa only [rsp, Reg64s.get64_rsp, h.sp, ← stk_nil] using h.mem⟩, hA⟩

-- After a callee with 8 free words.
theorem Mid.agree {c t : MachineData} {g' : G} {fr' : List Word} {w' : Word}
    (h : Mid S g F s ra fr w c) (hag : Sep.mod.Agree c t) (hl : fr'.length = 8)
    (hm : (View S g' ∗ Stk (rsp c) fr' w' ∗ Fr s ra F).get t.dmem) : Mid S g' F s ra fr' w' t where
  len := hl
  mem := by simpa only [rsp, Reg64s.get64_rsp, h.sp] using hm
  sp := by rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp]; exact h.sp
  bx := (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbx).trans h.bx
  bp := by rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbp]; exact h.bp
  r12 := (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r12).trans h.r12
  r13 := (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r13).trans h.r13
  r14 := (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r14).trans h.r14
  r15 := (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r15).trans h.r15

-- After a callee with no free word.
theorem Mid.agree0 {c t : MachineData} {g' : G} {fr' : List Word} {w' : Word}
    (h : Mid S g F s ra fr w c) (hag : Sep.mod.Agree c t) (hl : fr'.length = 0)
    (hm : (View S g' ∗ Stk (rsp c) fr' w'
      ∗ (Arr (rsp s - 24#64 - 8#64 - BitVec.ofNat 64 (8 * fr.length)) fr ∗ Fr s ra F)).get t.dmem) :
    Mid S g' F s ra fr w' t := by
  obtain rfl := List.eq_nil_of_length_eq_zero hl
  refine h.agree hag h.len ?_
  rw [stk_nil (fr := fr)]
  simpa only [rsp, Reg64s.get64_rsp, h.sp] using hm


theorem Mid.isSome_bx {t : MachineData} (h : Mid S g F s ra fr w t) :
    (t.dmem.loadInt t.regs.rsp.toBitVec 8).isSome = true := by
  rw [h.sp]; exact isSome_of_eq _ h.mem (by unfold Fr; ecancel)

theorem Mid.isSome_bp {t : MachineData} (h : Mid S g F s ra fr w t) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + 8#64) 8).isSome = true := by
  rw [h.sp, show rsp s - 24#64 + 8#64 = rsp s - 16#64 by bv_omega]
  exact isSome_of_eq _ h.mem (by unfold Fr; ecancel)

-- `popq %rbx; popq %rbp`: the state `P` before the `ret` is a `Kp` state with 3 more free words.
theorem Mid.pop {t P : MachineData} (h : Mid S g F s ra fr w t) (hm : P.dmem = t.dmem)
    (hsp : P.regs.rsp.toBitVec = t.regs.rsp.toBitVec + 8#64 + 8#64)
    (hbx : P.regs.rbx.toBitVec = rd t.dmem t.regs.rsp.toBitVec)
    (hbp : P.regs.rbp.toBitVec = rd t.dmem (t.regs.rsp.toBitVec + 8#64))
    (h12 : P.regs.r12 = t.regs.r12) (h13 : P.regs.r13 = t.regs.r13)
    (h14 : P.regs.r14 = t.regs.r14) (h15 : P.regs.r15 = t.regs.r15) :
    Kp S g F s ra (fr ++ [w, s.regs.rbx.toBitVec, s.regs.rbp.toBitVec]) P where
  mem := by rw [hm, stk3]; exact h.mem
  sp := by
    apply UInt64.toBitVec_inj.mp
    rw [hsp, h.sp]
    show _ = rsp s - 8#64
    bv_omega
  bx := by
    apply UInt64.toBitVec_inj.mp
    rw [hbx, h.sp]
    exact rd_of_eq h.mem (by unfold Fr; ecancel)
  bp := by
    apply UInt64.toBitVec_inj.mp
    rw [hbp, h.sp, show rsp s - 24#64 + 8#64 = rsp s - 16#64 by bv_omega]
    exact rd_of_eq h.mem (by unfold Fr; ecancel)
  r12 := h12.trans h.r12
  r13 := h13.trans h.r13
  r14 := h14.trans h.r14
  r15 := h15.trans h.r15

-- A step that keeps the stack registers: the struct is now `g'`.
theorem Mid.step {t P : MachineData} {g' : G} (h : Mid S g F s ra fr w t)
    (hm : (View S g' ∗ Stk (rsp s - 24#64) fr w ∗ Fr s ra F).get P.dmem)
    (hsp : P.regs.rsp = t.regs.rsp) (hbx : P.regs.rbx = t.regs.rbx)
    (hbp : P.regs.rbp = t.regs.rbp) (h12 : P.regs.r12 = t.regs.r12)
    (h13 : P.regs.r13 = t.regs.r13) (h14 : P.regs.r14 = t.regs.r14)
    (h15 : P.regs.r15 = t.regs.r15) : Mid S g' F s ra fr w P :=
  ⟨h.len, hm, by rw [hsp]; exact h.sp, hbx.trans h.bx, by rw [hbp]; exact h.bp, h12.trans h.r12,
    h13.trans h.r13, h14.trans h.r14, h15.trans h.r15⟩

-- A step that keeps the memory and the stack registers.
theorem Mid.next {t P : MachineData} (h : Mid S g F s ra fr w t) (hm : P.dmem = t.dmem)
    (hsp : P.regs.rsp = t.regs.rsp) (hbx : P.regs.rbx = t.regs.rbx)
    (hbp : P.regs.rbp = t.regs.rbp) (h12 : P.regs.r12 = t.regs.r12)
    (h13 : P.regs.r13 = t.regs.r13) (h14 : P.regs.r14 = t.regs.r14)
    (h15 : P.regs.r15 = t.regs.r15) : Mid S g F s ra fr w P :=
  h.step (hm ▸ h.mem) hsp hbx hbp h12 h13 h14 h15

theorem Mid.stack {t : MachineData} (h : Mid S g F s ra fr w t) : t.StackAtOrBelow (s.pushRa ra) :=
  MachineData.stackAtOrBelow_of_toNat_lt (by
    rw [Reg64s.get64_rsp, Reg64s.get64_rsp, h.sp]
    simp only [MachineData.pushRa, rsp, Reg64s.get64_rsp, Reg64s.set64_rsp]
    bv_omega)

end

/-! ## Loads and stores of the struct at `rbp` -/

section
variable {S : Addr} {g : G} {R : MProp 64} {m : Mem 64}

theorem rd_len' (h : (View S g ∗ R).get m) : BitVec.ofInt 64 (m.loadInt (S + 32#64) 8).get! = g.h.len := by
  rw [Fld.fold_stack_size]; exact View.rd_len h
theorem isSome_len' (h : (View S g ∗ R).get m) : (m.loadInt (S + 32#64) 8).isSome = true := by
  rw [Fld.fold_stack_size]; exact View.isSome_len h
theorem rd_data' (h : (View S g ∗ R).get m) : BitVec.ofInt 64 (m.loadInt (S + 24#64) 8).get! = g.h.data := by
  rw [Fld.fold_stack_data]; exact View.rd_data h
theorem isSome_data' (h : (View S g ∗ R).get m) : (m.loadInt (S + 24#64) 8).isSome = true := by
  rw [Fld.fold_stack_data]; exact View.isSome_data h

theorem rd_dest' (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < MAX_N) :
    BitVec.ofInt 64 (m.loadInt (S + x * 8#64 + 56#64) 8).get! = g.h.dest[x.toNat] := by
  rw [Fld.fold_mapping_destinationOf]; exact rd_dest h hx
theorem isSome_dest' (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < MAX_N) :
    (m.loadInt (S + x * 8#64 + 56#64) 8).isSome = true := by
  rw [Fld.fold_mapping_destinationOf]; exact View.isSome_dest h hx
theorem isSome_pos' (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < MAX_N) :
    (m.loadInt (S + x * 8#64 + 8248#64) 8).isSome = true := by
  rw [Fld.fold_mapping_positionOf]; exact View.isSome_pos h hx

theorem rd_slot' (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < g.h.n.toNat) :
    BitVec.ofInt 64 (m.loadInt (g.h.data + x * 8#64) 8).get! = g.stk[x.toNat] := by
  rw [fold_slot]; exact rd_stk h hx
theorem isSome_slot' (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < g.h.n.toNat) :
    (m.loadInt (g.h.data + x * 8#64) 8).isSome = true := by
  rw [fold_slot]; exact View.isSome_slot h hx

theorem store_dest' (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < MAX_N) (v : Word) :
    (View S { g with h := { g.h with dest := g.h.dest.set x.toNat v } } ∗ R).get
      (m.storeInt (S + x * 8#64 + 56#64) 8 v.toInt) := by
  rw [Fld.fold_mapping_destinationOf]; exact View.store_dest h hx v
theorem store_pos' (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < MAX_N) (v : Word) :
    (View S { g with h := { g.h with pos := g.h.pos.set x.toNat v } } ∗ R).get
      (m.storeInt (S + x * 8#64 + 8248#64) 8 v.toInt) := by
  rw [Fld.fold_mapping_positionOf]; exact View.store_pos h hx v

end

section
variable {S : Addr} {g : G} {F : MProp 64} {s : MachineData} {ra : Int64} {fr : List Word}
  {w : Word}

-- The call rule of a callee with 8 free words (`produce`), from a `Mid` state.
theorem Mid.call {A : G → MachineData → Prop} {Q : G → G → MachineData → MachineData → Prop}
    {c : MachineData} {K : MachineData → Prop} (h : Mid S g F s ra fr w c) (hdi : rdi c = S)
    (hok : g.Ok) (hA : A g c)
    (hK : ∀ t g' fr' w', Mid S g' F s ra fr' w' t → Q g g' c t → g'.Ok → K t) :
    ∃ S' g' F', Sep.Pre S' g' F' A 8 c
      ∧ ∀ s', Sep.Post S' F' 8 (fun g'' t => Q g' g'' c t) c s' → Sep.mod.Agree c s' → K s' :=
  ⟨S, g, Fr s ra F, h.pre hdi hok hA, fun s' ⟨g', fr', v', hQ, hok', hl, hm⟩ hag =>
    hK s' g' fr' v' (h.agree hag hl hm) hQ hok'⟩

-- The call rule of a callee with no free word (`swapWith`), from a `Mid` state.
theorem Mid.call0 {A : G → MachineData → Prop} {Q : G → G → MachineData → MachineData → Prop}
    {c : MachineData} {K : MachineData → Prop} (h : Mid S g F s ra fr w c) (hdi : rdi c = S)
    (hok : g.Ok) (hA : A g c)
    (hK : ∀ t g' w', Mid S g' F s ra fr w' t → Q g g' c t → g'.Ok → K t) :
    ∃ S' g' F', Sep.Pre S' g' F' A 0 c
      ∧ ∀ s', Sep.Post S' F' 0 (fun g'' t => Q g' g'' c t) c s' → Sep.mod.Agree c s' → K s' :=
  ⟨S, g, _, h.pre0 hdi hok hA, fun s' ⟨g', _, v', hQ, hok', hl, hm⟩ hag =>
    hK s' g' v' (h.agree0 hag hl hm) hQ hok'⟩

end


/-! ## The flat model -/

open Flat in
-- The state after an action of `produce` that is done: one more slot, one more operation, and
-- the new slot has the destination `t`.
structure Grow (st st' : Flat.St) (t : Word) : Prop where
  size : st'.size = st.size + 1
  trace : ∃ op, st'.trace = st.trace ++ [op]
  dest : st'.dest = put st.dest st.size t
  tsize : st'.targetSize = st.targetSize

section
variable {st : Flat.St} {t : Word}

theorem push_grow {x : StackSlot} (h : (Flat.push st x t).1 = .done) : Grow st (Flat.push st x t).2 t := by
  unfold Flat.push at *
  dsimp only at h ⊢
  split at h
  · simp at h
  · rename_i hp
    simp only [hp, ↓reduceIte]
    exact ⟨rfl, ⟨_, rfl⟩, by simp [Flat.bind, Flat.stackPush, BitVec.add_sub_cancel], rfl⟩

theorem dup_grow {c : Word} (h : (Flat.dup st c t).1 = .done) : Grow st (Flat.dup st c t).2 t := by
  unfold Flat.dup at *
  dsimp only at h ⊢
  split at h
  · simp at h
  · rename_i hk
    split at h
    · simp at h
    · rename_i hp
      simp only [hk, hp, ↓reduceIte]
      exact ⟨rfl, ⟨_, rfl⟩, by simp [Flat.bind, Flat.stackDup, BitVec.add_sub_cancel], rfl⟩

theorem produce_grow (h : (Flat.produce st t).1 = .done) : Grow st (Flat.produce st t).2 t := by
  unfold Flat.produce at *
  dsimp only at h ⊢
  generalize hr : (if isJunk (Flat.get st.target t) then Flat.push st (Flat.get st.target t) t
      else if Flat.shallowestCopyPosition st (Flat.get st.target t) ≠ Flat.NONE ∧
          Flat.isDupReachable st (Flat.shallowestCopyPosition st (Flat.get st.target t)) = true then
        Flat.dup st (Flat.shallowestCopyPosition st (Flat.get st.target t)) t
      else if (canBeFreelyGenerated (Flat.get st.target t) ||
          Flat.isSpilled st (Flat.get st.target t)) = true then
        Flat.push st (Flat.get st.target t) t
      else if Flat.shallowestCopyPosition st (Flat.get st.target t) ≠ Flat.NONE then
        Flat.blockDupUnreachable st (Flat.shallowestCopyPosition st (Flat.get st.target t))
      else (Flat.Status.assertionFailed, st)) = r at h ⊢
  have key : r.1 = .done → Grow st r.2 t := by
    subst hr
    split
    · exact push_grow
    split
    · exact dup_grow
    split
    · exact push_grow
    split
    · intro h'
      unfold Flat.blockDupUnreachable Flat.block at h'
      split at h' <;> simp at h'
    · simp
  by_cases h1 : r.1 = .done
  · have g := key h1
    simp only [h1, ne_eq, not_true_eq_false, ↓reduceIte] at h ⊢
    split at h
    · simp at h
    · rename_i h2
      simp only [h2, ↓reduceIte]
      exact ⟨g.size, g.trace, g.dest, g.tsize⟩
  · simp [h1] at h

theorem gen_fail (h : ¬t < st.targetSize) : Flat.generate st t = (.assertionFailed, st) := by
  simp [Flat.generate, h]

theorem gen_prod (h : t < st.targetSize) (hp : (Flat.produce st t).1 ≠ .done) :
    Flat.generate st t = Flat.produce st t := by
  simp [Flat.generate, h, hp]

-- `produce` is done: `generate` is the branch after `produce`.
theorem gen_after (h : t < st.targetSize) (hp : (Flat.produce st t).1 = .done) :
    Flat.generate st t =
      if t + 1 < (Flat.produce st t).2.size ∧ ¬Flat.isFinal (Flat.produce st t).2 t then
        if Flat.get (Flat.produce st t).2.data t
            = Flat.get (Flat.produce st t).2.data ((Flat.produce st t).2.size - 1) then
          (.done, Flat.swapDestinations (Flat.produce st t).2 t ((Flat.produce st t).2.size - 1))
        else if Flat.isSwapReachable (Flat.produce st t).2 t then
          Flat.swapWith (Flat.produce st t).2 t
        else (.done, (Flat.produce st t).2)
      else (.done, (Flat.produce st t).2) := by
  unfold Flat.generate
  dsimp only
  rw [ite_eq_right (Decidable.not_not.mpr h), ite_eq_right (Decidable.not_not.mpr hp)]

-- No swap: `t` is the top slot or it is final.
theorem gen_done {X : Flat.St} (h : t < st.targetSize) (hp : (Flat.produce st t).1 = .done)
    (hf : X = (Flat.produce st t).2) (hc : ¬(t + 1 < X.size ∧ ¬Flat.isFinal X t)) :
    Flat.generate st t = (.done, X) := by
  subst hf; rw [gen_after h hp, ite_eq_right hc]

-- Equal slots: swap the destinations.
theorem gen_eq {X : Flat.St} (h : t < st.targetSize) (hp : (Flat.produce st t).1 = .done)
    (hf : X = (Flat.produce st t).2) (hc : t + 1 < X.size ∧ ¬Flat.isFinal X t)
    (he : Flat.get X.data t = Flat.get X.data (X.size - 1)) :
    Flat.generate st t = (.done, Flat.swapDestinations X t (X.size - 1)) := by
  subst hf; rw [gen_after h hp, ite_eq_left hc, ite_eq_left he]

-- Different slots, in reach of a swap.
theorem gen_swap {X : Flat.St} (h : t < st.targetSize) (hp : (Flat.produce st t).1 = .done)
    (hf : X = (Flat.produce st t).2) (hc : t + 1 < X.size ∧ ¬Flat.isFinal X t)
    (he : Flat.get X.data t ≠ Flat.get X.data (X.size - 1))
    (hr : Flat.isSwapReachable X t = true) :
    Flat.generate st t = Flat.swapWith X t := by
  subst hf; rw [gen_after h hp, ite_eq_left hc, ite_eq_right he, ite_eq_left hr]

-- Different slots, out of reach of a swap.
theorem gen_far {X : Flat.St} (h : t < st.targetSize) (hp : (Flat.produce st t).1 = .done)
    (hf : X = (Flat.produce st t).2) (hc : t + 1 < X.size ∧ ¬Flat.isFinal X t)
    (he : Flat.get X.data t ≠ Flat.get X.data (X.size - 1))
    (hr : ¬Flat.isSwapReachable X t = true) :
    Flat.generate st t = (.done, X) := by
  subst hf; rw [gen_after h hp, ite_eq_left hc, ite_eq_right he, ite_eq_right hr]

end

/-! ## The entry: the two pushes -/

theorem split11 {fr : List Word} (h : fr.length = 11) :
    ∃ fr8 w x y, fr = fr8 ++ [w, x, y] ∧ fr8.length = 8 :=
  match fr, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7, w, x, y], _ =>
    ⟨[a0, a1, a2, a3, a4, a5, a6, a7], w, x, y, rfl, rfl⟩

section
variable {S : Addr} {g : G} {F : MProp 64} {s : MachineData} {fr : List Word} {w x y v : Word}
  {m : Mem 64}

-- The address of `pushq %rbp` (`r` is `rsp` after the call).
theorem push_isSome1 (hm : (View S g ∗ Stk (rsp s) (fr ++ [w, x, y]) v ∗ F).get m) {r : Addr}
    (hr : r = rsp s - 8#64) : (m.loadInt (r - 8#64) 8).isSome = true := by
  rw [stk3] at hm
  rw [show r - 8#64 = rsp s - 16#64 by subst hr; bv_omega]
  exact isSome_of_eq y hm (by ecancel)

-- The address of `pushq %rbx`, after the store of `pushq %rbp`.
theorem push_isSome2 (hm : (View S g ∗ Stk (rsp s) (fr ++ [w, x, y]) v ∗ F).get m) {r : Addr}
    (hr : r = rsp s - 8#64) (z : Word) :
    ((m.storeInt (r - 8#64) 8 z.toInt).loadInt (r - 8#64 - 8#64) 8).isSome = true := by
  rw [stk3] at hm
  rw [show r - 8#64 = rsp s - 16#64 by subst hr; bv_omega,
    show rsp s - 16#64 - 8#64 = rsp s - 24#64 by bv_omega]
  have e : View S g ∗ Stk (rsp s - 24#64) fr w ∗ (Wd (rsp s - 24#64) x ∗ Wd (rsp s - 16#64) y
      ∗ Wd (rsp s - 8#64) v ∗ F)
      = Wd (rsp s - 16#64) y ∗ (Wd (rsp s - 24#64) x ∗ View S g ∗ Stk (rsp s - 24#64) fr w
        ∗ Wd (rsp s - 8#64) v ∗ F) := by ecancel
  exact isSome_of_eq x (Wd.store (e ▸ hm) z) (by ecancel)

end

/-! ## `Keep` -/

theorem Keep.refl (g : G) : Keep g g := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {g g1 g2 : G} (h1 : Keep g g1) (h2 : Keep g1 g2) : Keep g g2 :=
  ⟨h2.tgtp.trans h1.tgtp, h2.n.trans h1.n, h2.splp.trans h1.splp, h2.data.trans h1.data,
    h2.ops.trans h1.ops, h2.tgt.trans h1.tgt, h2.spl.trans h1.spl⟩

/-! ## Flags -/

-- `cmpq n, a; jnb`: the jump is not taken.
theorem lt_of_cf {a n : Word}
    (h : (!(((a - n).toNat : Int) != (a.toNat : Int) - (n.toNat : Int))) = false) : a < n := by
  rw [Idioms.cf_sub] at h
  simpa [BitVec.lt_def] using h

-- `cmpq n, a; jnb`: the jump is taken.
theorem not_lt_of_cf {a n : Word}
    (h : (!(((a - n).toNat : Int) != (a.toNat : Int) - (n.toNat : Int))) = true) : ¬a < n := by
  rw [Idioms.cf_sub] at h
  simpa [BitVec.lt_def] using h

-- `al` reads only `rax`. A step that does not write `rax` keeps `al`.
theorem al_eq {t t' : MachineData} (h : t'.regs.rax = t.regs.rax) : al t' = al t := by
  rw [al, al, rax, rax, Reg64s.get64_rax, Reg64s.get64_rax, h]

-- `testb %al, %al; jne`: the jump is not taken.
theorem al_zero {t : MachineData}
    (h : (!(BitVec.extractLsb' 0 8 t.regs.rax.toBitVec &&& BitVec.extractLsb' 0 8 t.regs.rax.toBitVec
      == BitVec.zero 8)) = false) : al t = 0#8 := by
  simp only [Bool.not_eq_false', beq_iff_eq, BitVec.and_self] at h
  rw [al, rax, Reg64s.get64_rax, BitVec.setWidth_eq_extractLsb' (by decide)]
  exact h

-- `testb %al, %al; jne`: the jump is taken.
theorem al_ne {t : MachineData}
    (h : (!(BitVec.extractLsb' 0 8 t.regs.rax.toBitVec &&& BitVec.extractLsb' 0 8 t.regs.rax.toBitVec
      == BitVec.zero 8)) = true) : al t ≠ 0#8 := by
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, BitVec.and_self] at h
  rw [al, rax, Reg64s.get64_rax, BitVec.setWidth_eq_extractLsb' (by decide)]
  exact h

-- `cmpq b, a; je`.
theorem eq_of_z {a b : Word} (h : (a - b == BitVec.zero 64) = true) : a = b := by
  simp only [beq_iff_eq] at h
  have : a - b = 0#64 := h
  bv_omega

theorem ne_of_z {a b : Word} (h : (a - b == BitVec.zero 64) = false) : a ≠ b := by
  intro e
  simp [e] at h

-- `cmpq $-1, d; je`: the immediate is `NONE`.
theorem none_of_z {d : Word} (h : (d - 18446744073709551615#64 == BitVec.zero 64) = true) :
    d = Flat.NONE :=
  eq_of_z h

theorem ne_none_of_z {d : Word} (h : (d - 18446744073709551615#64 == BitVec.zero 64) = false) :
    d ≠ Flat.NONE :=
  ne_of_z h

-- `cmpq $16, d; jbe`: the jump is taken.
theorem le_of_be {d : Word}
    (h : (((((d - 16#64).toNat : Int) != (d.toNat : Int) - 16)) || (d - 16#64 == BitVec.zero 64)) = true) :
    d ≤ 16#64 := by
  rw [Idioms.cf_sub_imm d 16 (by decide)] at h
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with h | h
  · bv_omega
  · have : d - 16#64 = 0#64 := h
    bv_omega

-- `cmpq $16, d; jbe`: the jump is not taken.
theorem not_le_of_be {d : Word}
    (h : (((((d - 16#64).toNat : Int) != (d.toNat : Int) - 16)) || (d - 16#64 == BitVec.zero 64)) = false) :
    ¬d ≤ 16#64 := by
  rw [Idioms.cf_sub_imm d 16 (by decide)] at h
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne] at h
  have : d - 16#64 ≠ 0#64 := h.2
  bv_omega

-- `xorq; salq $16; je`: the low 6 bytes of the two words are equal.
theorem slot_eq_iff {a b : Word} :
    (((a ^^^ b).shiftLeft 16 == BitVec.zero 64) = true) ↔ StackSlot.ofWord b = StackSlot.ofWord a := by
  rw [beq_iff_eq, show BitVec.zero 64 = 0#64 from rfl,
    show (a ^^^ b).shiftLeft 16 = (a ^^^ b) <<< 16 from rfl, Idioms.slot_eq_iff]
  simp only [StackSlot.ofWord, StackSlot.mk.injEq]
  constructor <;> (rintro ⟨h1, h2, h3⟩; exact ⟨h1.symm, h2.symm, h3.symm⟩)

theorem code_eq_zero {st : Flat.Status} (h : code st = 0#8) : st = .done := by
  cases st <;> revert h <;> decide

/-! ## `get` and `put` -/

theorem get_eq {α : Type} [Inhabited α] (v : Vector α MAX_N) {i : Word} (hi : i.toNat < MAX_N) :
    Flat.get v i = v[i.toNat] := by
  simp [Flat.get, hi]

theorem put_eq {α : Type} (v : Vector α MAX_N) {i : Word} (hi : i.toNat < MAX_N) (x : α) :
    Flat.put v i x = v.set i.toNat x hi := by
  ext j hj; simp [Flat.put, Vector.getElem_set, Vector.getElem_setIfInBounds]

theorem get_put_self {α : Type} [Inhabited α] (v : Vector α MAX_N) {i : Word} (hi : i.toNat < MAX_N)
    (x : α) : Flat.get (Flat.put v i x) i = x := by
  simp [Flat.get, Flat.put, hi]

theorem get_put_ne {α : Type} [Inhabited α] (v : Vector α MAX_N) {i j : Word} (x : α) (h : j ≠ i) :
    Flat.get (Flat.put v i x) j = Flat.get v j := by
  unfold Flat.get Flat.put
  split
  · next hj =>
    rw [Vector.getElem_setIfInBounds_ne]
    exact fun e => h (BitVec.eq_of_toNat_eq e.symm)
  · rfl

theorem get_data {g : G} (hok : g.Ok) {i : Word} (hi : i.toNat < g.h.n.toNat) :
    Flat.get (flat g).data i = StackSlot.ofWord g.stk[i.toNat] := by
  simp [Flat.get, flat, vec, Nat.lt_of_lt_of_le hi hok.n, hi]

/-! ## The state after `produce` -/

-- `produce` is done: one more slot, room for one more operation, and the destinations of the
-- slots are none or in the target.
theorem after_prod {g g1 : G} {T : Word} {s : MachineData} (hok : g.Ok) (hok1 : g1.Ok) (hK : Keep g g1)
    (hA : generateA g s) (hT : T < (flat g).targetSize) (hp : (Flat.produce (flat g) T).1 = .done)
    (hf : flat g1 = (Flat.produce (flat g) T).2) :
    g1.h.len = g.h.len + 1#64 ∧ g1.h.len.toNat = g.h.len.toNat + 1
      ∧ g1.h.nops.toNat < 6 * g1.h.n.toNat ∧ DestOk (flat g1) := by
  have gr := produce_grow hp
  rw [← hf] at gr
  have hl : g1.h.len = g.h.len + 1#64 := gr.size
  have hA1 := hA.1
  have hn := hok.n
  have hln : g1.h.len.toNat = g.h.len.toNat + 1 := by rw [hl]; simp [MAX_N] at hn; bv_omega
  refine ⟨hl, hln, ?_, ?_⟩
  · obtain ⟨op, htr⟩ := gr.trace
    have e := congrArg List.length htr
    simp only [flat, List.length_map, List.length_take, Vector.length_toList, List.length_append,
      List.length_singleton] at e
    have := hok.nops
    have := hok1.nops
    have := hA.2.1
    rw [hK.n] at e ⊢
    omega
  · intro i hi
    have hs : (flat g1).size = g1.h.len := rfl
    have ht : (flat g1).targetSize = g.h.n := gr.tsize
    rw [hs, hln] at hi
    rw [ht, gr.dest]
    have hlm : g.h.len.toNat < MAX_N := by have := hok.len; omega
    by_cases e : i = g.h.len.toNat
    · right
      rw [show BitVec.ofNat 64 i = (flat g).size by subst e; simp [flat],
        get_put_self _ (show (flat g).size.toNat < MAX_N from hlm)]
      exact BitVec.lt_def.mp hT
    · have hne : BitVec.ofNat 64 i ≠ (flat g).size := fun h => e (by
        have h' : BitVec.ofNat 64 i = g.h.len := h
        rw [← h']; simp; omega)
      rw [get_put_ne _ _ hne]
      exact (hA.2.2 i (by show i < g.h.len.toNat; omega))


-- The result of `generate` from the result `r` of the flat model.
theorem genQ {g g1 : G} {s t : MachineData} {r : Flat.Status × Flat.St} (hK : Keep g g1)
    (hgen : Flat.generate (flat g) (rsi s) = r) (hf : flat g1 = r.2) (hal : al t = code r.1) :
    generateQ g g1 s t :=
  by subst hgen; exact ⟨hK, hf, hal⟩

-- The post of `swapWith` reads `rsi` of the call state. `generate` passes its own `rsi`.
theorem swapQ_of {g1 g2 : G} {c s t : MachineData} (h : swapWithQ g1 g2 c t) (hc : rsi c = rsi s) :
    swapWithQ g1 g2 s t := by
  unfold swapWithQ at *; rw [← hc]; exact h

theorem add_neg_one (x : Word) : x + BitVec.ofInt 64 (-1) = x - 1#64 := by
  rw [show BitVec.ofInt 64 (-1) = -1#64 from rfl]
  bv_omega

-- The top slot is a slot of the stack.
theorem top_lt {g1 : G} (hok : g1.Ok) {x : Word} (h : x + 1#64 < g1.h.len) :
    (g1.h.len - 1#64).toNat < g1.h.n.toNat := by
  have := hok.len
  bv_omega


/-! ## The branches after `produce` -/

section
variable {g1 : G} {T : Word}

-- `t + 1 < size` and `t` is not final.
theorem cond_of (hT : T.toNat < MAX_N) (h1 : T + 1#64 < g1.h.len) (hfin : g1.h.dest[T.toNat] ≠ T) :
    T + 1 < (flat g1).size ∧ ¬Flat.isFinal (flat g1) T = true :=
  ⟨h1, by simp [Flat.isFinal, flat, get_eq _ hT, hfin]⟩

-- `t` is final.
theorem not_cond_of (hT : T.toNat < MAX_N) (hfin : g1.h.dest[T.toNat] = T) :
    ¬(T + 1 < (flat g1).size ∧ ¬Flat.isFinal (flat g1) T = true) :=
  fun h => h.2 (by simp [Flat.isFinal, flat, get_eq _ hT, hfin])

theorem reach_iff (X : Flat.St) (t : Word) :
    Flat.isSwapReachable X t = true ↔ X.size - t - 1#64 ≤ 16#64 := by
  simp only [Flat.isSwapReachable, decide_eq_true_eq]
  simp only [Flat.depthOf, Flat.maxSwapDepth]
  constructor <;> intro h <;> bv_omega

variable {S : Addr} {R : MProp 64} {m : Mem 64}

-- `xorq; salq $16; je`: the slots `a` and `b` of the stack.
theorem data_eq (hm : (View S g1 ∗ R).get m) (hok : g1.Ok) {a b : Word}
    (ha : a.toNat < g1.h.n.toNat) (hb : b.toNat < g1.h.n.toNat)
    (h : ((BitVec.ofInt 64 (m.loadInt (g1.h.data + b * 8#64) 8).get!
      ^^^ BitVec.ofInt 64 (m.loadInt (g1.h.data + a * 8#64) 8).get!).shiftLeft 16
      == BitVec.zero 64) = true) :
    Flat.get (flat g1).data a = Flat.get (flat g1).data b := by
  rw [rd_slot' hm ha, rd_slot' hm hb, slot_eq_iff] at h
  rw [get_data hok ha, get_data hok hb, h]

theorem data_ne (hm : (View S g1 ∗ R).get m) (hok : g1.Ok) {a b : Word}
    (ha : a.toNat < g1.h.n.toNat) (hb : b.toNat < g1.h.n.toNat)
    (h : ((BitVec.ofInt 64 (m.loadInt (g1.h.data + b * 8#64) 8).get!
      ^^^ BitVec.ofInt 64 (m.loadInt (g1.h.data + a * 8#64) 8).get!).shiftLeft 16
      == BitVec.zero 64) = false) :
    Flat.get (flat g1).data a ≠ Flat.get (flat g1).data b := by
  rw [rd_slot' hm ha, rd_slot' hm hb] at h
  rw [get_data hok ha, get_data hok hb]
  intro e
  rw [slot_eq_iff.mpr e] at h
  cases h

end

/-! ## The swap of two destinations -/

-- `m_positionOf[dest[i]] = i` if `dest[i]` is not none: one half of `swapDestinations`.
def posAt (st : Flat.St) (i : Word) : Flat.St :=
  { st with pos := if Flat.get st.dest i ≠ Flat.NONE then Flat.put st.pos (Flat.get st.dest i) i
      else st.pos }

-- The swap of `dest[a]` and `dest[b]`.
def dsw (st : Flat.St) (a b : Word) : Flat.St :=
  { st with dest := Flat.put (Flat.put st.dest a (Flat.get st.dest b)) b (Flat.get st.dest a) }

theorem swapDestinations_eq (st : Flat.St) (a b : Word) :
    Flat.swapDestinations st a b = posAt (posAt (dsw st a b) a) b := rfl

theorem posAt_none {st : Flat.St} {i : Word} (h : Flat.get st.dest i = Flat.NONE) :
    posAt st i = st := by
  simp [posAt, h]

theorem posAt_some {st : Flat.St} {i : Word} (h : Flat.get st.dest i ≠ Flat.NONE) :
    posAt st i = { st with pos := Flat.put st.pos (Flat.get st.dest i) i } := by
  simp [posAt, h]

-- The ghost with other destinations, or other positions.
def withDest (g : G) (d : Vector Word MAX_N) : G := { g with h := { g.h with dest := d } }
def withPos (g : G) (p : Vector Word MAX_N) : G := { g with h := { g.h with pos := p } }

section
variable {g : G}

theorem flat_withDest (d : Vector Word MAX_N) : flat (withDest g d) = { flat g with dest := d } :=
  rfl
theorem flat_withPos (p : Vector Word MAX_N) : flat (withPos g p) = { flat g with pos := p } :=
  rfl

theorem Ok.withDest (h : g.Ok) (d : Vector Word MAX_N) : (withDest g d).Ok :=
  ⟨h.len, h.n, h.nops, h.spl⟩
theorem Ok.withPos (h : g.Ok) (p : Vector Word MAX_N) : (withPos g p).Ok :=
  ⟨h.len, h.n, h.nops, h.spl⟩

theorem Keep.withDest (d : Vector Word MAX_N) : Keep g (withDest g d) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem Keep.withPos (p : Vector Word MAX_N) : Keep g (withPos g p) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end

section
variable {S : Addr} {g : G} {R : MProp 64} {m : Mem 64}

theorem rd_dest_get (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < MAX_N) :
    BitVec.ofInt 64 (m.loadInt (S + x * 8#64 + 56#64) 8).get! = Flat.get g.h.dest x := by
  rw [get_eq _ hx]; exact rd_dest' h hx

theorem store_dest_put (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < MAX_N) (v : Word) :
    (View S (withDest g (Flat.put g.h.dest x v)) ∗ R).get
      (m.storeInt (S + x * 8#64 + 56#64) 8 v.toInt) := by
  rw [put_eq _ hx]; exact store_dest' h hx v

theorem store_pos_put (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < MAX_N) (v : Word) :
    (View S (withPos g (Flat.put g.h.pos x v)) ∗ R).get
      (m.storeInt (S + x * 8#64 + 8248#64) 8 v.toInt) := by
  rw [put_eq _ hx]; exact store_pos' h hx v

end

/-! ## The invariants of the swap of the destinations -/

-- `.LB52`: the slot `t` and the top slot are equal.
def At52 (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) (t : MachineData) :
    Prop :=
  ∃ g1 fr w, Mid S g1 F s ra fr w t ∧ g1.Ok ∧ Keep g g1 ∧ al t = 0#8
    ∧ t.regs.rsi.toBitVec = g1.h.len - 1#64 ∧ s.regs.rsi.toBitVec.toNat < MAX_N
    ∧ rsi s + 1#64 < g1.h.len ∧ DestOk (flat g1)
    ∧ Flat.generate (flat g) (rsi s)
      = (.done, Flat.swapDestinations (flat g1) (rsi s) (g1.h.len - 1#64))

-- `.LB45`: the destinations are swapped, and `positionOf` is written for `t`.
def At45 (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) (t : MachineData) :
    Prop :=
  ∃ g2 fr w, Mid S g2 F s ra fr w t ∧ g2.Ok ∧ Keep g g2 ∧ al t = 0#8
    ∧ t.regs.rsi.toBitVec.toNat < MAX_N
    ∧ (Flat.get g2.h.dest t.regs.rsi.toBitVec = Flat.NONE
      ∨ (Flat.get g2.h.dest t.regs.rsi.toBitVec).toNat < MAX_N)
    ∧ Flat.generate (flat g) (rsi s) = (.done, posAt (flat g2) t.regs.rsi.toBitVec)


/-! ## The block `.LB52` -/

theorem withDest_dest (g : G) (d : Vector Word MAX_N) : (withDest g d).h.dest = d := rfl

-- The facts of `.LB52`: `a` is the slot of `generate`, `b` is the top slot.
theorem lb52_facts {g1 : G} {a b : Word} (hok : g1.Ok) (ha : a.toNat < MAX_N)
    (h1 : a + 1#64 < g1.h.len) (hb : b = g1.h.len - 1#64) (hd : DestOk (flat g1)) :
    b.toNat < MAX_N ∧ a ≠ b
    ∧ (Flat.get (dsw (flat g1) a b).dest a = Flat.NONE
      ∨ (Flat.get (dsw (flat g1) a b).dest a).toNat < MAX_N)
    ∧ (Flat.get (dsw (flat g1) a b).dest b = Flat.NONE
      ∨ (Flat.get (dsw (flat g1) a b).dest b).toNat < MAX_N) := by
  have hl := hok.len
  have hn := hok.n
  have hlt : a.toNat < g1.h.len.toNat := by simp only [MAX_N] at ha hn; bv_omega
  have hbl : b.toNat < g1.h.len.toNat := by subst hb; bv_omega
  have hbN : b.toNat < MAX_N := by omega
  have hab : a ≠ b := by
    subst hb; intro e; subst e; simp only [MAX_N] at ha hn; bv_omega
  have hdo (i : Word) (hi : i.toNat < g1.h.len.toNat) :
      Flat.get g1.h.dest i = Flat.NONE ∨ (Flat.get g1.h.dest i).toNat < MAX_N := by
    have := hd i.toNat hi
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
    exact this.imp id (fun h => Nat.lt_of_lt_of_le h hn)
  refine ⟨hbN, hab, ?_, ?_⟩
  · simp only [dsw, flat]
    rw [get_put_ne _ _ hab, get_put_self _ ha]
    exact hdo b hbl
  · simp only [dsw, flat]
    rw [get_put_self _ hbN]
    exact hdo a hlt

theorem gen52_none {r : Flat.Status × Flat.St} {g1 : G} {a b : Word}
    (hgen : r = (.done, Flat.swapDestinations (flat g1) a b))
    (hz : Flat.get (dsw (flat g1) a b).dest a = Flat.NONE) :
    r = (.done, posAt (flat (withDest g1 (dsw (flat g1) a b).dest)) b) := by
  rw [hgen, swapDestinations_eq, posAt_none hz]; rfl

theorem gen52_some {r : Flat.Status × Flat.St} {g1 : G} {a b : Word}
    (hgen : r = (.done, Flat.swapDestinations (flat g1) a b))
    (hz : Flat.get (dsw (flat g1) a b).dest a ≠ Flat.NONE) :
    r = (.done, posAt (flat (withPos (withDest g1 (dsw (flat g1) a b).dest)
      (Flat.put g1.h.pos (Flat.get (dsw (flat g1) a b).dest a) a))) b) := by
  rw [hgen, swapDestinations_eq, posAt_some hz]; rfl

-- The state at `.LB45`. `X` keeps `rax` and `rsi` of `t`.
theorem at45_of {S : Addr} {g g2 : G} {F : MProp 64} {s : MachineData} {ra : Int64}
    {fr : List Word} {w : Word} {t X : MachineData}
    (hmid : Mid S g2 F s ra fr w X) (hok : g2.Ok) (hK : Keep g g2)
    (hra : X.regs.rax = t.regs.rax) (hal : al t = 0#8)
    (hrs : X.regs.rsi = t.regs.rsi) (hb : t.regs.rsi.toBitVec.toNat < MAX_N)
    (hd : Flat.get g2.h.dest t.regs.rsi.toBitVec = Flat.NONE
      ∨ (Flat.get g2.h.dest t.regs.rsi.toBitVec).toNat < MAX_N)
    (hgen : Flat.generate (flat g) (rsi s) = (.done, posAt (flat g2) t.regs.rsi.toBitVec)) :
    At45 S g F s ra X :=
  ⟨g2, fr, w, hmid, hok, hK, (al_eq hra).trans hal, by rw [hrs]; exact ⟨hb, hd, hgen⟩⟩

end Generate

/-- `Mid.next` with a reducible `rfl` for each equation. A default `rfl` first unifies the two
machine states field by field. When a register holds a loaded value, this unfolds the memory load
and takes a heartbeat timeout. -/
local macro "mid_next% " h:term:max : term =>
  `(Generate.Mid.next $h (by with_reducible rfl) (by with_reducible rfl) (by with_reducible rfl)
    (by with_reducible rfl) (by with_reducible rfl) (by with_reducible rfl)
    (by with_reducible rfl) (by with_reducible rfl))

/-- `Mid.step` with a reducible `rfl` for each register equation, as `mid_next%`. -/
local macro "mid_step% " h:term:max hm:term:max : term =>
  `(Generate.Mid.step $h $hm (by with_reducible rfl) (by with_reducible rfl)
    (by with_reducible rfl) (by with_reducible rfl) (by with_reducible rfl) (by with_reducible rfl)
    (by with_reducible rfl))

open Generate in
theorem generate_unit [Host] [FunDecls]
    (hprod : Sep.Spec Names.produce produceA 8 produceQ)
    (hswap : Sep.Spec Names.swapWith swapWithA 0 swapWithQ) :
    UnitThm generateAsm generateA 11 generateQ := by
  simp only [Names.produce, Names.swapWith] at hprod hswap
  intro S g F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨fr, v, hfr, hm⟩ := hpre.mem
  have hk0 : Kp S g F s ra fr (s.pushRa ra) := Kp.init hm
  refine Program.WP.cfg (fun
      | .entry, t => t = s.pushRa ra
      | .label l, t =>
        if l = Names.generate then t = s.pushRa ra
        else if l = ".LB49" then Kp S g F s ra fr t ∧ generateQ g g s t
        else if l = ".LB42" then ∃ g' fr8 w, Mid S g' F s ra fr8 w t ∧ generateQ g g' s t ∧ g'.Ok
        else if l = ".LB53" then ∃ g1 fr8 w, Mid S g1 F s ra fr8 w t ∧ g1.Ok ∧ Keep g g1
          ∧ swapWithA g1 t ∧ Flat.generate (flat g) (rsi s) = Flat.swapWith (flat g1) (rsi s)
        else if l = ".LB52" then At52 S g F s ra t
        else if l = ".LB45" then At45 S g F s ra t
        else False
      | .exit, _ => False)
    (fun l _ => if l = ".LB42" then 0 else 1) ?_ rfl
  cfg_blocks
  case entry t ht =>
    subst ht
    kvcgen64
    simp only [Names.generate, ↓reduceIte]
  case «_ZN12_GLOBAL__N_18Emission8generateE11StackOffset» t ht =>
    simp only [Names.generate, ↓reduceIte] at ht
    subst ht
    obtain ⟨fr8, w, x, y, rfl, hfr8⟩ := split11 hfr
    have hS : (s.pushRa ra).regs.rdi.toBitVec = S := by simpa [MachineData.pushRa] using hpre.rdi
    have hn : BitVec.ofInt 64
        ((s.pushRa ra).dmem.loadInt ((s.pushRa ra).regs.rdi.toBitVec + 8#64) 8).get! = g.h.n := by
      rw [hS]; exact rd_n hk0.mem
    have hsp : (s.pushRa ra).regs.rsp.toBitVec = rsp s - 8#64 := by simp [MachineData.pushRa]
    kvcgen64 [hprod]
    all_goals try symexec_norm
    vc_by_shape
    | load =>
      first
      | (rw [hS]; exact isSome_n hk0.mem)
      | with_reducible exact push_isSome2 hk0.mem hsp _
      | exact push_isSome1 hk0.mem hsp
    | goto ".LB49" =>
      rename_i hj _
      have hlt : ¬rsi s < (flat g).targetSize := by
        have := not_lt_of_cf hj
        rwa [hn] at this
      cfg_goto
      · exact (hk0.next rfl rfl rfl rfl rfl rfl rfl rfl).stack
      · simp only [Names.generate, String.reduceEq, ↓reduceIte]
        refine ⟨hk0.next rfl rfl rfl rfl rfl rfl rfl rfl, Keep.refl g, ?_, ?_⟩
        · exact (congrArg Prod.snd (gen_fail hlt)).symm
        · show (rax _).setWidth 8 = code (Flat.generate (flat g) (rsi s)).1
          rw [gen_fail hlt]; rfl
      · simp
    | other =>
      rename_i hj _
      have hlt : rsi s < (flat g).targetSize := by
        have := lt_of_cf hj
        rwa [hn] at this
      have hA := hpre.args
      refine Mid.call (Mid.push hk0.mem hfr8 hsp rfl rfl rfl hS rfl rfl rfl rfl) hS hpre.ok
        ⟨BitVec.lt_def.mp hlt, hA.1, by have := hA.2.1; omega⟩ ?_
      intro t g1 fr1 w1 hmid1 hQ1 hok1
      obtain ⟨hK1, hf1, hal1⟩ : produceQ g g1 s t := hQ1
      have hal : al t = code (Flat.produce (flat g) (rsi s)).1 := hal1
      have hbp1 : t.regs.rbp.toBitVec = S := hmid1.bp
      have hbx1 : t.regs.rbx.toBitVec = s.regs.rsi.toBitVec := by rw [hmid1.bx]
      have hTn : (rsi s).toNat < g.h.n.toNat := BitVec.lt_def.mp hlt
      have hTm : (rsi s).toNat < MAX_N := by have := hpre.ok.n; omega
      have hTn1 : (rsi s).toNat < g1.h.n.toNat := by rw [hK1.n]; exact hTn
      have hm1 := hmid1.mem
      have hnx (h : rsi s + 1#64 < g1.h.len) := top_lt hok1 h
      kvcgen64
      all_goals try symexec_norm
      all_goals simp only [hbp1, hbx1, rd_len' hm1, rd_data' hm1, rd_dest' hm1 hTm, add_neg_one] at *
      vc_by_shape
      | load =>
        first
        | with_reducible exact isSome_len' hm1
        | with_reducible exact isSome_data' hm1
        | with_reducible exact isSome_dest' hm1 hTm
        | with_reducible exact isSome_slot' hm1 hTn1
        | with_reducible exact isSome_slot' hm1 (hnx (lt_of_cf (by with_reducible assumption)))
      | closed => simp
      case vc1 =>
        have hne : al t ≠ 0#8 := al_ne (by with_reducible assumption)
        have hpn : (Flat.produce (flat g) s.regs.rsi.toBitVec).1 ≠ .done := fun e =>
          hne (hal.trans ((congrArg code e).trans rfl))
        cfg_goto
        · exact (mid_next% hmid1).stack
        · simp only [Names.generate, String.reduceEq, ↓reduceIte]
          exact ⟨g1, fr1, w1, mid_next% hmid1,
            genQ hK1 (gen_prod hlt hpn) hf1 hal, hok1⟩
        · simp
      case vc3 =>
        have hal0 : al t = 0#8 := al_zero (by with_reducible assumption)
        have hp := code_eq_zero (hal.symm.trans hal0)
        have hnl : ¬s.regs.rsi.toBitVec + 1#64 < g1.h.len := not_lt_of_cf (by with_reducible assumption)
        have hG := gen_done hlt hp hf1 (fun h => hnl h.1)
        cfg_goto
        · exact (mid_next% hmid1).stack
        · simp only [Names.generate, String.reduceEq, ↓reduceIte]
          exact ⟨g1, fr1, w1, mid_next% hmid1, genQ hK1 hG rfl ((al_eq (by with_reducible rfl)).trans hal0), hok1⟩
        · simp
      case vc5 =>
        have hal0 : al t = 0#8 := al_zero (by with_reducible assumption)
        have hp := code_eq_zero (hal.symm.trans hal0)
        have hfin : g1.h.dest[s.regs.rsi.toBitVec.toNat] = s.regs.rsi.toBitVec :=
          eq_of_z (by with_reducible assumption)
        have hG := gen_done hlt hp hf1 (not_cond_of hTm hfin)
        cfg_goto
        · exact (mid_next% hmid1).stack
        · simp only [Names.generate, String.reduceEq, ↓reduceIte]
          exact ⟨g1, fr1, w1, mid_next% hmid1, genQ hK1 hG rfl ((al_eq (by with_reducible rfl)).trans hal0), hok1⟩
        · simp
      case vc10 =>
        have hal0 : al t = 0#8 := al_zero (by with_reducible assumption)
        have hp := code_eq_zero (hal.symm.trans hal0)
        have h1 : s.regs.rsi.toBitVec + 1#64 < g1.h.len := lt_of_cf (by with_reducible assumption)
        have hfin : g1.h.dest[s.regs.rsi.toBitVec.toNat] ≠ s.regs.rsi.toBitVec :=
          ne_of_z (by with_reducible assumption)
        have he := data_eq hm1 hok1 hTn1 (hnx h1) (by with_reducible assumption)
        have hG := gen_eq hlt hp hf1 (cond_of hTm h1 hfin) he
        have hdok := (after_prod hpre.ok hok1 hK1 hA hlt hp hf1).2.2.2
        cfg_goto
        · exact (mid_next% hmid1).stack
        · simp only [Names.generate, String.reduceEq, ↓reduceIte, At52]
          refine ⟨g1, fr1, w1, ?_, hok1, hK1, ?_, ?_, hTm, h1, hdok, ?_⟩
          · exact mid_next% hmid1
          · exact (al_eq (by with_reducible rfl)).trans hal0
          · rfl
          · exact hG
        · simp
      case vc11 =>
        have hal0 : al t = 0#8 := al_zero (by with_reducible assumption)
        have hp := code_eq_zero (hal.symm.trans hal0)
        have h1 : s.regs.rsi.toBitVec + 1#64 < g1.h.len := lt_of_cf (by with_reducible assumption)
        have hfin : g1.h.dest[s.regs.rsi.toBitVec.toNat] ≠ s.regs.rsi.toBitVec :=
          ne_of_z (by with_reducible assumption)
        have he := data_ne hm1 hok1 hTn1 (hnx h1) (by with_reducible assumption)
        have hd : g1.h.len - s.regs.rsi.toBitVec - 1#64 ≤ 16#64 := le_of_be (by with_reducible assumption)
        have hr := (reach_iff (flat g1) s.regs.rsi.toBitVec).mpr hd
        have hG := gen_swap hlt hp hf1 (cond_of hTm h1 hfin) he hr
        have ha := after_prod hpre.ok hok1 hK1 hA hlt hp hf1
        cfg_goto
        · exact (mid_next% hmid1).stack
        · simp only [Names.generate, String.reduceEq, ↓reduceIte]
          exact ⟨g1, fr1, w1, mid_next% hmid1, hok1, hK1,
            ⟨ha.2.2.1, ha.2.2.2⟩, hG⟩
        · simp
      case vc12 =>
        have hal0 : al t = 0#8 := al_zero (by with_reducible assumption)
        have hp := code_eq_zero (hal.symm.trans hal0)
        have h1 : s.regs.rsi.toBitVec + 1#64 < g1.h.len := lt_of_cf (by with_reducible assumption)
        have hfin : g1.h.dest[s.regs.rsi.toBitVec.toNat] ≠ s.regs.rsi.toBitVec :=
          ne_of_z (by with_reducible assumption)
        have he := data_ne hm1 hok1 hTn1 (hnx h1) (by with_reducible assumption)
        have hd : ¬g1.h.len - s.regs.rsi.toBitVec - 1#64 ≤ 16#64 := not_le_of_be (by with_reducible assumption)
        have hr : ¬Flat.isSwapReachable (flat g1) s.regs.rsi.toBitVec = true := fun h =>
          hd ((reach_iff (flat g1) s.regs.rsi.toBitVec).mp h)
        have hG := gen_far hlt hp hf1 (cond_of hTm h1 hfin) he hr
        simp only [Names.generate, String.reduceEq, ↓reduceIte]
        exact ⟨g1, fr1, w1, mid_next% hmid1, genQ hK1 hG rfl ((al_eq (by with_reducible rfl)).trans hal0), hok1⟩
  case «.LB49» t ht =>
    simp only [Names.generate, String.reduceEq, ↓reduceIte] at ht
    obtain ⟨hk, hQ⟩ := ht
    kvcgen64
    vc_by_shape
    | retAddr => simp [hk.retAddr]
    | ret => exact Kp.ret hk hfr hpre.ok fun t' _ hax =>
        ⟨hQ.1, hQ.2.1, by show (rax t').setWidth 8 = _; rw [hax]; exact hQ.2.2⟩
  case «.LB42» t ht =>
    simp only [Names.generate, String.reduceEq, ↓reduceIte] at ht
    obtain ⟨g', fr8, w, hmid, hQ, hok'⟩ := ht
    kvcgen64
    vc_by_shape
    | load => first | exact hmid.isSome_bx | exact hmid.isSome_bp
    | retAddr =>
      refine (congrArg Option.isSome (hmid.pop ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).retAddr).trans rfl
      all_goals rfl
    | ret =>
      refine Kp.ret (hmid.pop ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (by simp [hmid.len]) hok' fun t' _ hax =>
        ⟨hQ.1, hQ.2.1, by show (rax t').setWidth 8 = _; rw [hax]; exact hQ.2.2⟩
      all_goals rfl
  case «.LB53» t ht =>
    simp only [Names.generate, String.reduceEq, ↓reduceIte] at ht
    obtain ⟨g1, fr1, w1, hmid1, hok1, hK1, hA1, hgen⟩ := ht
    have hbp1 : t.regs.rbp.toBitVec = S := hmid1.bp
    kvcgen64 [hswap]
    all_goals try symexec_norm
    refine Mid.call0 (mid_next% hmid1) hbp1 hok1 hA1 ?_
    intro t2 g2 w2 hmid2 hQ2 hok2
    obtain ⟨hK2, hf2, hal2⟩ : swapWithQ g1 g2 s t2 :=
      swapQ_of hQ2 (show t.regs.rbx.toBitVec = s.regs.rsi.toBitVec by rw [hmid1.bx])
    kvcgen64
    vc_by_shape
    | goto ".LB42" =>
      cfg_goto
      · exact hmid2.stack
      · simp only [Names.generate, String.reduceEq, ↓reduceIte]
        exact ⟨g2, fr1, w2, hmid2, genQ (Keep.trans hK1 hK2) hgen hf2 hal2, hok2⟩
      · simp
  case «.LB52» t ht =>
    simp only [Names.generate, String.reduceEq, ↓reduceIte] at ht
    obtain ⟨g1, fr1, w1, hmid1, hok1, hK1, hal0, hrsi, ha, h1, hdok, hgen⟩ := ht
    rw [← hrsi] at hgen
    obtain ⟨hb, hab, hda, hdb⟩ := lb52_facts hok1 ha h1 hrsi hdok
    have hbp1 : t.regs.rbp.toBitVec = S := hmid1.bp
    have hbx1 : t.regs.rbx.toBitVec = s.regs.rsi.toBitVec := by rw [hmid1.bx]
    have hm1 := hmid1.mem
    have h1' := store_dest_put hm1 ha (Flat.get g1.h.dest t.regs.rsi.toBitVec)
    have h2' : (View S (withDest g1 (dsw (flat g1) s.regs.rsi.toBitVec t.regs.rsi.toBitVec).dest)
        ∗ _).get _ := store_dest_put h1' hb (Flat.get g1.h.dest s.regs.rsi.toBitVec)
    kvcgen64
    all_goals try symexec_norm
    all_goals simp only [hbp1, hbx1, rd_dest_get hm1 ha, rd_dest_get hm1 hb] at *
    all_goals try simp only [rd_dest_get h2' ha, withDest_dest] at *
    vc_by_shape
    | load =>
      first
      | with_reducible exact isSome_dest' hm1 ha
      | with_reducible exact isSome_dest' hm1 hb
      | with_reducible exact isSome_dest' h1' hb
      | with_reducible exact isSome_dest' h2' ha
      | with_reducible exact isSome_pos' h2' (hda.resolve_left (ne_none_of_z (by with_reducible assumption)))
    | goto ".LB45" =>
      have hz := none_of_z (by with_reducible assumption)
      cfg_goto
      · exact (mid_step% hmid1 h2').stack
      · simp only [Names.generate, String.reduceEq, ↓reduceIte]
        exact at45_of (t := t) (mid_step% hmid1 h2') (Ok.withDest hok1 _) (Keep.trans hK1 (Keep.withDest _)) (by with_reducible rfl) hal0 (by with_reducible rfl) hb hdb (gen52_none hgen hz)
      · simp
    | closed => simp
    | other =>
      have hz := ne_none_of_z (by with_reducible assumption)
      have h3' : (View S (withPos (withDest g1 (dsw (flat g1) s.regs.rsi.toBitVec t.regs.rsi.toBitVec).dest)
          (Flat.put g1.h.pos (Flat.get (dsw (flat g1) s.regs.rsi.toBitVec t.regs.rsi.toBitVec).dest
            s.regs.rsi.toBitVec) s.regs.rsi.toBitVec)) ∗ _).get _ :=
        store_pos_put h2' (hda.resolve_left hz) s.regs.rsi.toBitVec
      simp only [Names.generate, String.reduceEq, ↓reduceIte]
      exact at45_of (t := t) (mid_step% hmid1 h3') (Ok.withPos (Ok.withDest hok1 _) _) (Keep.trans hK1 (Keep.trans (Keep.withDest _) (Keep.withPos _))) (by with_reducible rfl) hal0 (by with_reducible rfl) hb hdb (gen52_some hgen hz)
  case «.LB45» t ht =>
    simp only [Names.generate, String.reduceEq, ↓reduceIte] at ht
    obtain ⟨g2, fr2, w2, hmid2, hok2, hK2, hal0, hi, hd, hgen⟩ := ht
    have hbp2 : t.regs.rbp.toBitVec = S := hmid2.bp
    have hm2 := hmid2.mem
    kvcgen64
    all_goals try symexec_norm
    all_goals simp only [hbp2, rd_dest_get hm2 hi] at *
    vc_by_shape
    | load =>
      first
      | with_reducible exact isSome_dest' hm2 hi
      | with_reducible exact isSome_pos' hm2 (hd.resolve_left (ne_none_of_z (by with_reducible assumption)))
    | goto ".LB42" =>
      first
      | have hz := none_of_z (by with_reducible assumption)
        cfg_goto
        · exact (mid_next% hmid2).stack
        · simp only [Names.generate, String.reduceEq, ↓reduceIte]
          exact ⟨g2, fr2, w2, mid_next% hmid2,
            genQ hK2 hgen (posAt_none (st := flat g2) hz).symm
              ((al_eq (t := t) (by with_reducible rfl)).trans hal0), hok2⟩
        · simp
      | have hz := ne_none_of_z (by with_reducible assumption)
        have hdn := hd.resolve_left hz
        cfg_goto
        · exact (mid_step% hmid2 (store_pos_put hm2 hdn _)).stack
        · simp only [Names.generate, String.reduceEq, ↓reduceIte]
          exact ⟨_, fr2, w2, mid_step% hmid2 (store_pos_put hm2 hdn _),
            genQ (Keep.trans hK2 (Keep.withPos _)) hgen
              ((flat_withPos _).trans (posAt_some (st := flat g2) hz).symm)
              ((al_eq (t := t) (by with_reducible rfl)).trans hal0), Ok.withPos hok2 _⟩
        · simp

end Bbu.Unit
