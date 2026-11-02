module

public import FlatShuffler.Unit.StackCall
import all FlatShuffler.Unit.StackCall
public import FlatShuffler.Sep.Stores
import all FlatShuffler.Sep.Stores
public import ProofKit.Cfg
import all ProofKit.Cfg
public import ProofKit.Idioms
import all ProofKit.Idioms

@[expose] public section

/-!
# `buildBottomUp`: the stack frame

The prologue pushes `r15`, `r14`, `r13`, `r12`, `rbp`, `rbx` and subtracts 8216 from `rsp`. The
body `rsp` is `rsp s - 8272`. The locals are, from the body `rsp` up:

* `x0` at `(%rsp)` (`rsp s - 8272`);
* `u` at `8(%rsp)` (`rsp s - 8264`): the `urgentToDup` of the C++;
* `x2.A`, 1024 words at `16(%rsp)` (`rsp s - 8256`): the array `permutation`, the argument of
  `permute`;
* `x2.pad` at `rsp s - 64`.

The callees get the free words below `rsp s - 8272`: 1034 words and the return slot `w` at
`rsp s - 8280`.

`Mid` is a body state. It fixes only `rsp` and `r12` (the struct): the loop uses the other
callee-saved registers, and their entry values are in the frame `Fr`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace FlatShuffler.Unit
open FlatShuffler.Sep
namespace Loop

/-! ## Addresses -/

theorem sub_sub_ofNat (a : Addr) (j k : Nat) :
    a - BitVec.ofNat 64 j - BitVec.ofNat 64 k = a - BitVec.ofNat 64 (j + k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-! ## The stack -/

-- The locals above `8(%rsp)`: the array `permutation` and one word.
structure Lc where
  A : Vector Word MAX_N
  pad : Word

-- The words from `sp - 8272` up without the array: the locals `x0`, `u`, `pad`, the six pushed
-- registers and the return address.
def TopR (sp : Addr) (x0 u pad b0 b1 b2 b3 b4 b5 v : Word) (F : MProp 64) : MProp 64 :=
  Wd (sp - 8272#64) x0 ∗ Wd (sp - 8264#64) u ∗ Wd (sp - 64#64) pad ∗ Wd (sp - 56#64) b0
    ∗ Wd (sp - 48#64) b1 ∗ Wd (sp - 40#64) b2 ∗ Wd (sp - 32#64) b3 ∗ Wd (sp - 24#64) b4
    ∗ Wd (sp - 16#64) b5 ∗ Wd (sp - 8#64) v ∗ F

-- The 1033 words from `sp - 8272` up and the return address.
def Top (sp : Addr) (x0 u : Word) (L : Lc) (b0 b1 b2 b3 b4 b5 v : Word) (F : MProp 64) :
    MProp 64 :=
  Arr (sp - 8256#64) L.A.toList ∗ TopR sp x0 u L.pad b0 b1 b2 b3 b4 b5 v F

-- The top word `w` of the free words `lo ++ w :: hi` is the return slot of a callee.
theorem stk_top (sp : Addr) (lo hi : List Word) (w v : Word) (F : MProp 64) :
    Stk sp (lo ++ w :: hi) v ∗ F
      = Stk (sp - 8#64 - BitVec.ofNat 64 (8 * hi.length)) lo w
        ∗ Arr (sp - 8#64 - BitVec.ofNat 64 (8 * hi.length)) hi ∗ Wd (sp - 8#64) v ∗ F := by
  have e1 : sp - 8#64 - BitVec.ofNat 64 (8 * (lo ++ w :: hi).length)
      = sp - 8#64 - BitVec.ofNat 64 (8 * hi.length) - 8#64 - BitVec.ofNat 64 (8 * lo.length) := by
    apply BitVec.eq_of_toNat_eq
    simp only [List.length_append, List.length_cons, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have e2 : sp - 8#64 - BitVec.ofNat 64 (8 * hi.length) - 8#64 - BitVec.ofNat 64 (8 * lo.length)
      + BitVec.ofNat 64 (8 * lo.length) = sp - 8#64 - BitVec.ofNat 64 (8 * hi.length) - 8#64 :=
    BitVec.sub_add_cancel _ _
  have e3 : sp - 8#64 - BitVec.ofNat 64 (8 * hi.length) - 8#64 + 8#64
      = sp - 8#64 - BitVec.ofNat 64 (8 * hi.length) := BitVec.sub_add_cancel _ _
  unfold Stk
  rw [e1, Arr.append, e2]
  simp only [Arr, e3]
  ac_rfl

-- The free words of the entry: `lo` for the callees, the return slot `w`, the locals and the six
-- pushed registers.
theorem stk_frame (sp : Addr) (lo : List Word) (w x0 u : Word) (L : Lc)
    (b0 b1 b2 b3 b4 b5 v : Word) (F : MProp 64) :
    Stk sp (lo ++ w :: x0 :: u :: (L.A.toList ++ [L.pad, b0, b1, b2, b3, b4, b5])) v ∗ F
      = Stk (sp - 8272#64) lo w ∗ Top sp x0 u L b0 b1 b2 b3 b4 b5 v F := by
  have hl : (x0 :: u :: (L.A.toList ++ [L.pad, b0, b1, b2, b3, b4, b5])).length = 1033 := by
    simp only [List.length_cons, List.length_append, Vector.length_toList, List.length_nil]; rfl
  rw [stk_top, hl]
  rw [show sp - 8#64 - BitVec.ofNat 64 (8 * 1033) = sp - 8272#64 by bv_omega]
  simp only [Arr]
  rw [Arr.append, Vector.length_toList]
  simp only [Arr, MProp.sep_emp]
  rw [show sp - 8272#64 + 8#64 = sp - 8264#64 by bv_omega,
    show sp - 8264#64 + 8#64 = sp - 8256#64 by bv_omega,
    show sp - 8256#64 + BitVec.ofNat 64 (8 * MAX_N) = sp - 64#64 by simp [MAX_N]; bv_omega,
    show sp - 64#64 + 8#64 = sp - 56#64 by bv_omega,
    show sp - 56#64 + 8#64 = sp - 48#64 by bv_omega,
    show sp - 48#64 + 8#64 = sp - 40#64 by bv_omega,
    show sp - 40#64 + 8#64 = sp - 32#64 by bv_omega,
    show sp - 32#64 + 8#64 = sp - 24#64 by bv_omega,
    show sp - 24#64 + 8#64 = sp - 16#64 by bv_omega]
  unfold Top TopR
  ac_rfl

-- The free words `lo` below the top `hi` words go to the frame.
theorem stk_split (sp : Addr) (lo hi : List Word) (v : Word) (F : MProp 64) {k : Nat}
    (hk : lo.length + hi.length = k) :
    Stk sp (lo ++ hi) v ∗ F
      = Stk sp hi v ∗ (Arr (sp - 8#64 - BitVec.ofNat 64 (8 * k)) lo ∗ F) := by
  have e : sp - 8#64 - BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 (8 * lo.length)
      = sp - 8#64 - BitVec.ofNat 64 (8 * hi.length) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  unfold Stk
  rw [List.length_append, hk, Arr.append, e]
  ac_rfl

-- The 2068 free words of the entry.
theorem split2068 {fr : List Word} (h : fr.length = 2068) :
    ∃ lo w x0 u, ∃ L : Lc, ∃ a3 a4 a5 a6 a7 a8,
      fr = lo ++ w :: x0 :: u :: (L.A.toList ++ [L.pad, a3, a4, a5, a6, a7, a8])
        ∧ lo.length = 1034 := by
  have hd : (fr.drop 1034).length = 1034 := by simp [h]
  match e : fr.drop 1034, hd with
  | w :: x0 :: u :: r, hd =>
    have hr : r.length = 1031 := by simpa using hd
    have hd' : (r.drop 1024).length = 7 := by simp [hr]
    match e' : r.drop 1024, hd' with
    | [pad, a3, a4, a5, a6, a7, a8], _ =>
      refine ⟨fr.take 1034, w, x0, u, ⟨⟨(r.take 1024).toArray, by simp [hr, MAX_N]⟩, pad⟩,
        a3, a4, a5, a6, a7, a8, ?_, by simp [h]⟩
      have hr' : r = r.take 1024 ++ [pad, a3, a4, a5, a6, a7, a8] := by
        conv => lhs; rw [← List.take_append_drop 1024 r, e']
      conv => lhs; rw [← List.take_append_drop 1034 fr, e]
      show _ = _ ++ w :: x0 :: u :: (r.take 1024 ++ [pad, a3, a4, a5, a6, a7, a8])
      rw [← hr']

/-! ## The body state -/

-- The frame of the callees: the locals, the pushed registers, the return address and `F`.
def Fr (s : MachineData) (ra : Int64) (x0 u : Word) (L : Lc) (F : MProp 64) : MProp 64 :=
  Top (rsp s) x0 u L s.regs.rbx.toBitVec s.regs.rbp.toBitVec s.regs.r12.toBitVec
    s.regs.r13.toBitVec s.regs.r14.toBitVec s.regs.r15.toBitVec ra.toBitVec F

-- `Fr` without the array `permutation`.
def FrR (s : MachineData) (ra : Int64) (x0 u pad : Word) (F : MProp 64) : MProp 64 :=
  TopR (rsp s) x0 u pad s.regs.rbx.toBitVec s.regs.rbp.toBitVec s.regs.r12.toBitVec
    s.regs.r13.toBitVec s.regs.r14.toBitVec s.regs.r15.toBitVec ra.toBitVec F

-- A state between the prologue and the epilogue: 1034 free words `lo`, the return slot `w` of
-- a callee, the local `u` at `8(%rsp)`, the array `x2.A` at `16(%rsp)`, and `r12` is the struct.
structure Mid (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) (x0 : Word)
    (x2 : Lc) (lo : List Word) (w u : Word) (t : MachineData) : Prop where
  len : lo.length = 1034
  mem : (View S g ∗ Stk (rsp s - 8272#64) lo w ∗ Fr s ra x0 u x2 F).get t.dmem
  sp : t.regs.rsp.toBitVec = rsp s - 8272#64
  r12 : t.regs.r12.toBitVec = S

-- The registers that a callee keeps.
structure Saved (c t : MachineData) : Prop where
  bx : t.regs.rbx = c.regs.rbx
  bp : t.regs.rbp = c.regs.rbp
  r12 : t.regs.r12 = c.regs.r12
  r13 : t.regs.r13 = c.regs.r13
  r14 : t.regs.r14 = c.regs.r14
  r15 : t.regs.r15 = c.regs.r15

theorem Saved.of_agree {c t : MachineData} (hag : Sep.mod.Agree c t) : Saved c t :=
  ⟨mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbx, mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbp,
    mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r12, mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r13,
    mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r14, mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r15⟩

-- A store into a word atom, with the atom found by `ecancel`.
theorem wd_store {P P' R : MProp 64} {a : Addr} {v v' : Word} {m : Mem 64} (h : P.get m)
    (e : P = Wd a v ∗ R) (e' : P' = Wd a v' ∗ R) : P'.get (m.storeInt a 8 v'.toInt) :=
  e' ▸ Wd.store (e ▸ h) v'

section
variable {S : Addr} {g : G} {F : MProp 64} {s : MachineData} {ra : Int64} {x0 : Word} {x2 : Lc}
  {lo : List Word} {w u : Word}

-- The prologue, from the entry stack (`r` is `rsp` after the call).
theorem Mid.push {m₀ : Mem 64} {a3 a4 a5 a6 a7 a8 : Word} {c : MachineData}
    (hm : (View S g ∗ Stk (rsp s) (lo ++ w :: x0 :: u :: (x2.A.toList ++ [x2.pad, a3, a4, a5, a6,
      a7, a8])) ra.toBitVec ∗ F).get m₀)
    (hlo : lo.length = 1034) {r : Addr} (hr : r = rsp s - 8#64)
    (hc : c.dmem = (((((m₀.storeInt (r - 8#64) 8 s.regs.r15.toBitVec.toInt).storeInt
        (r - 8#64 - 8#64) 8 s.regs.r14.toBitVec.toInt).storeInt
        (r - 8#64 - 8#64 - 8#64) 8 s.regs.r13.toBitVec.toInt).storeInt
        (r - 8#64 - 8#64 - 8#64 - 8#64) 8 s.regs.r12.toBitVec.toInt).storeInt
        (r - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8 s.regs.rbp.toBitVec.toInt).storeInt
        (r - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8 s.regs.rbx.toBitVec.toInt)
    (hsp : c.regs.rsp.toBitVec = r - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8216#64)
    (h12 : c.regs.r12.toBitVec = S) : Mid S g F s ra x0 x2 lo w u c := by
  subst hr
  simp only [sub_sub_ofNat, Nat.reduceAdd] at hc hsp
  rw [stk_frame] at hm
  refine ⟨hlo, ?_, hsp, h12⟩
  rw [hc]
  have h1 : (View S g ∗ Stk (rsp s - 8272#64) lo w
      ∗ Top (rsp s) x0 u x2 a3 a4 a5 a6 a7 s.regs.r15.toBitVec ra.toBitVec F).get _ :=
    wd_store (a := rsp s - 16#64) hm (by unfold Top TopR; ecancel) (by unfold Top TopR; ecancel)
  have h2 : (View S g ∗ Stk (rsp s - 8272#64) lo w
      ∗ Top (rsp s) x0 u x2 a3 a4 a5 a6 s.regs.r14.toBitVec s.regs.r15.toBitVec ra.toBitVec F).get _ :=
    wd_store (a := rsp s - 24#64) h1 (by unfold Top TopR; ecancel) (by unfold Top TopR; ecancel)
  have h3 : (View S g ∗ Stk (rsp s - 8272#64) lo w
      ∗ Top (rsp s) x0 u x2 a3 a4 a5 s.regs.r13.toBitVec s.regs.r14.toBitVec s.regs.r15.toBitVec
        ra.toBitVec F).get _ :=
    wd_store (a := rsp s - 32#64) h2 (by unfold Top TopR; ecancel) (by unfold Top TopR; ecancel)
  have h4 : (View S g ∗ Stk (rsp s - 8272#64) lo w
      ∗ Top (rsp s) x0 u x2 a3 a4 s.regs.r12.toBitVec s.regs.r13.toBitVec s.regs.r14.toBitVec
        s.regs.r15.toBitVec ra.toBitVec F).get _ :=
    wd_store (a := rsp s - 40#64) h3 (by unfold Top TopR; ecancel) (by unfold Top TopR; ecancel)
  have h5 : (View S g ∗ Stk (rsp s - 8272#64) lo w
      ∗ Top (rsp s) x0 u x2 a3 s.regs.rbp.toBitVec s.regs.r12.toBitVec s.regs.r13.toBitVec
        s.regs.r14.toBitVec s.regs.r15.toBitVec ra.toBitVec F).get _ :=
    wd_store (a := rsp s - 48#64) h4 (by unfold Top TopR; ecancel) (by unfold Top TopR; ecancel)
  exact wd_store (a := rsp s - 56#64) h5 (by unfold Top TopR; ecancel)
    (by unfold Fr Top TopR; ecancel)

-- The six loads of the epilogue.
theorem Mid.isSome_pop {t : MachineData} (h : Mid S g F s ra x0 x2 lo w u t) {k : Nat}
    (hk : k < 6) :
    (t.dmem.loadInt (8216#64 + t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * k)) 8).isSome
      = true := by
  rw [h.sp]
  have hm := h.mem
  match k, hk with
  | 0, _ => rw [show 8216#64 + (rsp s - 8272#64) + BitVec.ofNat 64 (8 * 0) = rsp s - 56#64 by
              bv_omega]
            exact isSome_of_eq _ hm (by unfold Fr Top TopR; ecancel)
  | 1, _ => rw [show 8216#64 + (rsp s - 8272#64) + BitVec.ofNat 64 (8 * 1) = rsp s - 48#64 by
              bv_omega]
            exact isSome_of_eq _ hm (by unfold Fr Top TopR; ecancel)
  | 2, _ => rw [show 8216#64 + (rsp s - 8272#64) + BitVec.ofNat 64 (8 * 2) = rsp s - 40#64 by
              bv_omega]
            exact isSome_of_eq _ hm (by unfold Fr Top TopR; ecancel)
  | 3, _ => rw [show 8216#64 + (rsp s - 8272#64) + BitVec.ofNat 64 (8 * 3) = rsp s - 32#64 by
              bv_omega]
            exact isSome_of_eq _ hm (by unfold Fr Top TopR; ecancel)
  | 4, _ => rw [show 8216#64 + (rsp s - 8272#64) + BitVec.ofNat 64 (8 * 4) = rsp s - 24#64 by
              bv_omega]
            exact isSome_of_eq _ hm (by unfold Fr Top TopR; ecancel)
  | 5, _ => rw [show 8216#64 + (rsp s - 8272#64) + BitVec.ofNat 64 (8 * 5) = rsp s - 16#64 by
              bv_omega]
            exact isSome_of_eq _ hm (by unfold Fr Top TopR; ecancel)

-- The epilogue: the state `P` before the `ret` is a `Kp` state.
theorem Mid.pop {t P : MachineData} (h : Mid S g F s ra x0 x2 lo w u t) (hm : P.dmem = t.dmem)
    (hsp : P.regs.rsp.toBitVec
      = 8216#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64)
    (hbx : P.regs.rbx.toBitVec = rd t.dmem (8216#64 + t.regs.rsp.toBitVec))
    (hbp : P.regs.rbp.toBitVec = rd t.dmem (8216#64 + t.regs.rsp.toBitVec + 8#64))
    (h12 : P.regs.r12.toBitVec = rd t.dmem (8216#64 + t.regs.rsp.toBitVec + 8#64 + 8#64))
    (h13 : P.regs.r13.toBitVec
      = rd t.dmem (8216#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64))
    (h14 : P.regs.r14.toBitVec
      = rd t.dmem (8216#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64))
    (h15 : P.regs.r15.toBitVec
      = rd t.dmem (8216#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64 + 8#64)) :
    Kp S g F s ra (lo ++ w :: x0 :: u :: (x2.A.toList ++ [x2.pad, s.regs.rbx.toBitVec,
      s.regs.rbp.toBitVec, s.regs.r12.toBitVec, s.regs.r13.toBitVec, s.regs.r14.toBitVec,
      s.regs.r15.toBitVec])) P := by
  have hmem := h.mem
  rw [h.sp] at hsp hbx hbp h12 h13 h14 h15
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm, stk_frame]; exact hmem
  · apply UInt64.toBitVec_inj.mp
    rw [hsp]
    show _ = rsp s - 8#64
    bv_omega
  · apply UInt64.toBitVec_inj.mp
    rw [hbx, show 8216#64 + (rsp s - 8272#64) = rsp s - 56#64 by bv_omega]
    exact rd_of_eq hmem (by unfold Fr Top TopR; ecancel)
  · apply UInt64.toBitVec_inj.mp
    rw [hbp, show 8216#64 + (rsp s - 8272#64) + 8#64 = rsp s - 48#64 by bv_omega]
    exact rd_of_eq hmem (by unfold Fr Top TopR; ecancel)
  · apply UInt64.toBitVec_inj.mp
    rw [h12, show 8216#64 + (rsp s - 8272#64) + 8#64 + 8#64 = rsp s - 40#64 by bv_omega]
    exact rd_of_eq hmem (by unfold Fr Top TopR; ecancel)
  · apply UInt64.toBitVec_inj.mp
    rw [h13, show 8216#64 + (rsp s - 8272#64) + 8#64 + 8#64 + 8#64 = rsp s - 32#64 by bv_omega]
    exact rd_of_eq hmem (by unfold Fr Top TopR; ecancel)
  · apply UInt64.toBitVec_inj.mp
    rw [h14, show 8216#64 + (rsp s - 8272#64) + 8#64 + 8#64 + 8#64 + 8#64 = rsp s - 24#64 by
      bv_omega]
    exact rd_of_eq hmem (by unfold Fr Top TopR; ecancel)
  · apply UInt64.toBitVec_inj.mp
    rw [h15, show 8216#64 + (rsp s - 8272#64) + 8#64 + 8#64 + 8#64 + 8#64 + 8#64
      = rsp s - 16#64 by bv_omega]
    exact rd_of_eq hmem (by unfold Fr Top TopR; ecancel)

-- A step that keeps `rsp` and `r12`: the struct is now `g'`.
theorem Mid.step {t P : MachineData} {g' : G} (h : Mid S g F s ra x0 x2 lo w u t)
    (hm : (View S g' ∗ Stk (rsp s - 8272#64) lo w ∗ Fr s ra x0 u x2 F).get P.dmem)
    (hsp : P.regs.rsp = t.regs.rsp) (h12 : P.regs.r12 = t.regs.r12) :
    Mid S g' F s ra x0 x2 lo w u P :=
  ⟨h.len, hm, by rw [hsp]; exact h.sp, by rw [h12]; exact h.r12⟩

-- A step that keeps the memory, `rsp` and `r12`.
theorem Mid.next {t P : MachineData} (h : Mid S g F s ra x0 x2 lo w u t) (hm : P.dmem = t.dmem)
    (hsp : P.regs.rsp = t.regs.rsp) (h12 : P.regs.r12 = t.regs.r12) :
    Mid S g F s ra x0 x2 lo w u P :=
  h.step (hm ▸ h.mem) hsp h12

theorem Mid.stack {t : MachineData} (h : Mid S g F s ra x0 x2 lo w u t) :
    t.StackAtOrBelow (s.pushRa ra) :=
  MachineData.stackAtOrBelow_of_toNat_lt (by
    rw [Reg64s.get64_rsp, Reg64s.get64_rsp, h.sp]
    simp only [MachineData.pushRa, rsp, Reg64s.get64_rsp, Reg64s.set64_rsp]
    bv_omega)

-- The stack goal at a state `P` with the `rsp` of `t`.
theorem Mid.stack_of {t P : MachineData} (h : Mid S g F s ra x0 x2 lo w u t)
    (hsp : P.regs.rsp = t.regs.rsp) : P.StackAtOrBelow (s.pushRa ra) :=
  MachineData.stackAtOrBelow_of_toNat_lt (by
    rw [Reg64s.get64_rsp, Reg64s.get64_rsp, hsp, h.sp]
    simp only [MachineData.pushRa, rsp, Reg64s.get64_rsp, Reg64s.set64_rsp]
    bv_omega)

theorem Mid.isSome_exit {t : MachineData} (h : Mid S g F s ra x0 x2 lo w u t) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec - 8#64) 8).isSome = true := by
  rw [h.sp]
  exact isSome_of_eq w h.mem (by unfold Stk; ecancel)

theorem Mid.mem_exit {t : MachineData} (h : Mid S g F s ra x0 x2 lo w u t) (exitra : Int64) :
    (View S g ∗ Stk (rsp s) (lo ++ exitra.toBitVec :: x0 :: u :: (x2.A.toList ++ [x2.pad,
      s.regs.rbx.toBitVec, s.regs.rbp.toBitVec, s.regs.r12.toBitVec,
      s.regs.r13.toBitVec, s.regs.r14.toBitVec, s.regs.r15.toBitVec])) ra.toBitVec ∗ F).get
      (t.dmem.storeInt (t.regs.rsp.toBitVec - 8#64) 8 exitra.toBitVec.toInt) := by
  rw [stk_frame, h.sp]
  exact wd_store h.mem (by unfold Stk; ecancel) (by unfold Stk; ecancel)

theorem Mid.directExitPost {t v : MachineData} {X : G → MachineData → Prop}
    (h : Mid S g F s ra x0 x2 lo w u t) (hok : g.Ok) (exitra : Int64)
    (hm : v.dmem = t.dmem.storeInt (t.regs.rsp.toBitVec - 8#64) 8 exitra.toBitVec.toInt)
    (hx : X g v) : Sep.Post S F 2068 X s v := by
  refine ⟨g, lo ++ exitra.toBitVec :: x0 :: u :: (x2.A.toList ++ [x2.pad,
      s.regs.rbx.toBitVec, s.regs.rbp.toBitVec, s.regs.r12.toBitVec,
      s.regs.r13.toBitVec, s.regs.r14.toBitVec, s.regs.r15.toBitVec]), ra.toBitVec,
    hx, hok, by simp only [List.length_append, List.length_cons, List.length_nil,
      Vector.length_toList, h.len]; rfl, ?_⟩
  rw [hm]
  exact h.mem_exit exitra

-- `8(%rsp)`: the local `u`.
theorem Mid.u_addr {t : MachineData} (h : Mid S g F s ra x0 x2 lo w u t) :
    t.regs.rsp.toBitVec + 8#64 = rsp s - 8264#64 := by
  rw [h.sp]; bv_omega

theorem Mid.rd_u {t : MachineData} (h : Mid S g F s ra x0 x2 lo w u t) :
    rd t.dmem (t.regs.rsp.toBitVec + 8#64) = u := by
  rw [h.u_addr]; exact rd_of_eq h.mem (by unfold Fr Top TopR; ecancel)

theorem Mid.isSome_u {t : MachineData} (h : Mid S g F s ra x0 x2 lo w u t) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + 8#64) 8).isSome = true := by
  rw [h.u_addr]; exact isSome_of_eq _ h.mem (by unfold Fr Top TopR; ecancel)

-- A store to `8(%rsp)`.
theorem Mid.setU {t P : MachineData} (h : Mid S g F s ra x0 x2 lo w u t) (v : Word)
    (hm : P.dmem = t.dmem.storeInt (t.regs.rsp.toBitVec + 8#64) 8 v.toInt)
    (hsp : P.regs.rsp = t.regs.rsp) (h12 : P.regs.r12 = t.regs.r12) :
    Mid S g F s ra x0 x2 lo w v P := by
  refine ⟨h.len, ?_, by rw [hsp]; exact h.sp, by rw [h12]; exact h.r12⟩
  rw [hm, h.u_addr]
  exact wd_store h.mem (by unfold Fr Top TopR; ecancel) (by unfold Fr Top TopR; ecancel)

/-! ## The array `permutation` at `16(%rsp)` -/

theorem mid_A (V X : MProp 64) (s : MachineData) (ra : Int64) (x0 u : Word) (L : Lc)
    (F : MProp 64) :
    V ∗ X ∗ Fr s ra x0 u L F = Arr (rsp s - 8256#64) L.A.toList ∗ (V ∗ X ∗ FrR s ra x0 u L.pad F) := by
  unfold Fr FrR Top; ac_rfl

theorem Mid.rdA {t : MachineData} (h : Mid S g F s ra x0 x2 lo w u t) {i : Nat} (hi : i < MAX_N)
    {a : Addr} (ha : a = rsp s - 8256#64 + BitVec.ofNat 64 (8 * i)) : rd t.dmem a = x2.A[i] := by
  have hm := h.mem
  rw [mid_A] at hm
  rw [ha]
  exact (Arr.rd hm (by simpa using hi)).trans (by simp)

theorem Mid.isSomeA {t : MachineData} (h : Mid S g F s ra x0 x2 lo w u t) {i : Nat}
    (hi : i < MAX_N) {a : Addr} (ha : a = rsp s - 8256#64 + BitVec.ofNat 64 (8 * i)) :
    (t.dmem.loadInt a 8).isSome = true := by
  have hm := h.mem
  rw [mid_A] at hm
  rw [ha]
  exact Arr.isSome hm (by simpa using hi)

theorem Mid.storeA {t P : MachineData} (h : Mid S g F s ra x0 x2 lo w u t) {i : Nat}
    (hi : i < MAX_N) {a : Addr} (ha : a = rsp s - 8256#64 + BitVec.ofNat 64 (8 * i)) (v : Word)
    (hm : P.dmem = t.dmem.storeInt a 8 v.toInt) (hsp : P.regs.rsp = t.regs.rsp)
    (h12 : P.regs.r12 = t.regs.r12) :
    Mid S g F s ra x0 { x2 with A := x2.A.set i v hi } lo w u P := by
  refine ⟨h.len, ?_, by rw [hsp]; exact h.sp, by rw [h12]; exact h.r12⟩
  have hm0 := h.mem
  rw [mid_A] at hm0
  rw [hm, ha, mid_A]
  have h2 := Arr.store hm0 (by simpa using hi) v
  rw [← Vector.toList_set hi] at h2
  exact h2

/-! ## Calls -/

-- The call rule of a callee with `d` free words, from a `Mid` state. The callee gets the top
-- `d` free words; the other `1034 - d` go to its frame.
theorem Mid.call {d : Nat} (hd : d ≤ 1034) {A : G → MachineData → Prop}
    {Q : G → G → MachineData → MachineData → Prop} {c : MachineData} {K : MachineData → Prop}
    (h : Mid S g F s ra x0 x2 lo w u c) (hdi : rdi c = S) (hok : g.Ok) (hA : A g c)
    (hK : ∀ t g' lo' w', Mid S g' F s ra x0 x2 lo' w' u t → Q g g' c t → g'.Ok → Saved c t → K t) :
    ∃ S' g' F', Sep.Pre S' g' F' A d c
      ∧ ∀ s', Sep.Post S' F' d (fun g'' t => Q g' g'' c t) c s' → Sep.mod.Agree c s' → K s' := by
  have hl := h.len
  have e := stk_split (rsp s - 8272#64) (lo.take (1034 - d)) (lo.drop (1034 - d)) w
    (Fr s ra x0 u x2 F) (k := 1034) (by simp [hl])
  refine ⟨S, g, Arr (rsp s - 8272#64 - 8#64 - BitVec.ofNat 64 (8 * 1034)) (lo.take (1034 - d))
    ∗ Fr s ra x0 u x2 F, ⟨hdi, hok, ⟨lo.drop (1034 - d), w, by simp [hl]; omega, ?_⟩, hA⟩, ?_⟩
  · have hm := h.mem
    rw [← List.take_append_drop (1034 - d) lo, e] at hm
    simpa only [rsp, Reg64s.get64_rsp, h.sp] using hm
  · rintro s' ⟨g', fr', v', hQ, hok', hfl, hm⟩ hag
    have e' := stk_split (rsp s - 8272#64) (lo.take (1034 - d)) fr' v'
      (Fr s ra x0 u x2 F) (k := 1034) (by simp [hl, hfl]; omega)
    refine hK s' g' (lo.take (1034 - d) ++ fr') v' ⟨by simp [hl, hfl]; omega, ?_, ?_, ?_⟩ hQ hok'
      (Saved.of_agree hag)
    · rw [e']; simpa only [rsp, Reg64s.get64_rsp, h.sp] using hm
    · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp]; exact h.sp
    · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r12]; exact h.r12

-- The caller owns the saved registers and locals when a callee exits.
theorem Mid.exitPost {d : Nat} (hd : d ≤ 1034) {c t : MachineData}
    {X : G → MachineData → Prop} (h : Mid S g F s ra x0 x2 lo w u c)
    (hp : Sep.Post S
      (Arr (rsp s - 8272#64 - 8#64 - BitVec.ofNat 64 (8 * 1034)) (lo.take (1034 - d))
        ∗ Fr s ra x0 u x2 F) d X c t) : Sep.Post S F 2068 X s t := by
  obtain ⟨g', fr', w', hx, hok, hlen, hm⟩ := hp
  let lo' := lo.take (1034 - d) ++ fr'
  have hlo' : lo'.length = 1034 := by simp [lo', h.len, hlen]; omega
  refine ⟨g', lo' ++ w' :: x0 :: u :: (x2.A.toList ++ [x2.pad,
      s.regs.rbx.toBitVec, s.regs.rbp.toBitVec, s.regs.r12.toBitVec,
      s.regs.r13.toBitVec, s.regs.r14.toBitVec, s.regs.r15.toBitVec]), ra.toBitVec,
    hx, hok, by simp only [List.length_append, List.length_cons, List.length_nil,
      Vector.length_toList, hlo']; rfl, ?_⟩
  rw [stk_frame]
  change (View S g' ∗ Stk (rsp s - 8272#64) lo' w' ∗ Fr s ra x0 u x2 F).get t.dmem
  have e := stk_split (rsp s - 8272#64) (lo.take (1034 - d)) fr' w'
    (Fr s ra x0 u x2 F) (k := 1034) (by simpa only [lo', List.length_append] using hlo')
  rw [show lo' = lo.take (1034 - d) ++ fr' from rfl, e]
  simpa only [rsp, Reg64s.get64_rsp, h.sp] using hm

-- A callee with an exit contract uses the same frame as a normal callee.
theorem Mid.callExit {d : Nat} (hd : d ≤ 1034) {A : G → MachineData → Prop}
    {Q X : G → G → MachineData → MachineData → Prop} {c : MachineData}
    {K E : MachineData → Prop} (h : Mid S g F s ra x0 x2 lo w u c)
    (hdi : rdi c = S) (hok : g.Ok) (hA : A g c)
    (hK : ∀ t g' lo' w', Mid S g' F s ra x0 x2 lo' w' u t →
      Q g g' c t → g'.Ok → Saved c t → K t)
    (hX : ∀ t, Sep.Post S F 2068 (fun g' t => X g g' c t) s t →
      t.regs.get64 .rdi = 1#64 → E t) :
    ∃ S' g' F', Sep.Pre S' g' F' A d c
      ∧ (∀ t, Sep.Post S' F' d (fun g'' t => Q g' g'' c t) c t → Sep.mod.Agree c t → K t)
      ∧ (∀ t, Sep.Post S' F' d (fun g'' t => X g' g'' c t) c t →
        t.regs.get64 .rdi = 1#64 → E t) := by
  have hl := h.len
  have e := stk_split (rsp s - 8272#64) (lo.take (1034 - d)) (lo.drop (1034 - d)) w
    (Fr s ra x0 u x2 F) (k := 1034) (by simp [hl])
  refine ⟨S, g, Arr (rsp s - 8272#64 - 8#64 - BitVec.ofNat 64 (8 * 1034)) (lo.take (1034 - d))
    ∗ Fr s ra x0 u x2 F, ⟨hdi, hok, ⟨lo.drop (1034 - d), w, by simp [hl]; omega, ?_⟩, hA⟩, ?_, ?_⟩
  · have hm := h.mem
    rw [← List.take_append_drop (1034 - d) lo, e] at hm
    simpa only [rsp, Reg64s.get64_rsp, h.sp] using hm
  · rintro t ⟨g', fr', v', hQ, hok', hfl, hm⟩ hag
    have e' := stk_split (rsp s - 8272#64) (lo.take (1034 - d)) fr' v'
      (Fr s ra x0 u x2 F) (k := 1034) (by simp [hl, hfl]; omega)
    refine hK t g' (lo.take (1034 - d) ++ fr') v' ⟨by simp [hl, hfl]; omega, ?_, ?_, ?_⟩ hQ hok'
      (Saved.of_agree hag)
    · rw [e']; simpa only [rsp, Reg64s.get64_rsp, h.sp] using hm
    · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp]; exact h.sp
    · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r12]; exact h.r12
  · intro t hp harg
    exact hX t (h.exitPost hd hp) harg

-- The call of `permute`: the callee gets all 1034 free words and owns the array at `rsi`. After
-- the call the array has new values.
theorem Mid.callW {A : G → MachineData → Prop} {Q : G → G → MachineData → MachineData → Prop}
    {c : MachineData} {K : MachineData → Prop} (h : Mid S g F s ra x0 x2 lo w u c)
    (hdi : rdi c = S) (hsi : rsi c = rsp s - 8256#64) (hok : g.Ok) (hA : A g c)
    (hK : ∀ t g' (L : Lc) lo' w', L.pad = x2.pad → Mid S g' F s ra x0 L lo' w' u t →
      Q g g' c t → g'.Ok → Saved c t → K t) :
    ∃ S' g' F', Sep.Pre S' g' (permW c ∗ F') A 1034 c
      ∧ ∀ s', Sep.Post S' (permW c ∗ F') 1034 (fun g'' t => Q g' g'' c t) c s'
        → Sep.mod.Agree c s' → K s' := by
  have e : ∀ (X : MProp 64) (g' : G) (lo' : List Word) (w' : Word),
      View S g' ∗ Stk (rsp s - 8272#64) lo' w' ∗ (X ∗ FrR s ra x0 u x2.pad F)
        = X ∗ (View S g' ∗ Stk (rsp s - 8272#64) lo' w' ∗ FrR s ra x0 u x2.pad F) :=
    fun _ _ _ _ => by ac_rfl
  have hsp : rsp c = rsp s - 8272#64 := by
    show c.regs.get64 .rsp = _
    rw [Reg64s.get64_rsp, h.sp]
  refine ⟨S, g, FrR s ra x0 u x2.pad F, ⟨hdi, hok, ⟨lo, w, h.len, ?_⟩, hA⟩, ?_⟩
  · have hm := h.mem
    rw [mid_A] at hm
    rw [hsp, permW, hsi, e]
    exact ExArr.intro (n := MAX_N) (by simp) hm
  · rintro s' ⟨g', fr', v', hQ, hok', hfl, hm⟩ hag
    rw [hsp, permW, hsi, e] at hm
    obtain ⟨vs, hvs, hm⟩ := ExArr.elim hm
    refine hK s' g' ⟨⟨vs.toArray, by simp [hvs]⟩, x2.pad⟩ fr' v' rfl ⟨hfl, ?_, ?_, ?_⟩ hQ hok'
      (Saved.of_agree hag)
    · rw [mid_A]
      exact hm
    · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp]; exact h.sp
    · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r12]; exact h.r12

-- The permutation array can change before the callee exits.
theorem Mid.callWExit {A : G → MachineData → Prop}
    {Q X : G → G → MachineData → MachineData → Prop} {c : MachineData}
    {K E : MachineData → Prop} (h : Mid S g F s ra x0 x2 lo w u c)
    (hdi : rdi c = S) (hsi : rsi c = rsp s - 8256#64) (hok : g.Ok) (hA : A g c)
    (hK : ∀ t g' (L : Lc) lo' w', L.pad = x2.pad → Mid S g' F s ra x0 L lo' w' u t →
      Q g g' c t → g'.Ok → Saved c t → K t)
    (hX : ∀ t, Sep.Post S F 2068 (fun g' t => X g g' c t) s t →
      t.regs.get64 .rdi = 1#64 → E t) :
    ∃ S' g' F', Sep.Pre S' g' (permW c ∗ F') A 1034 c
      ∧ (∀ t, Sep.Post S' (permW c ∗ F') 1034 (fun g'' t => Q g' g'' c t) c t →
        Sep.mod.Agree c t → K t)
      ∧ (∀ t, Sep.Post S' (permW c ∗ F') 1034 (fun g'' t => X g' g'' c t) c t →
        t.regs.get64 .rdi = 1#64 → E t) := by
  have e : ∀ (X : MProp 64) (g' : G) (lo' : List Word) (w' : Word),
      View S g' ∗ Stk (rsp s - 8272#64) lo' w' ∗ (X ∗ FrR s ra x0 u x2.pad F)
        = X ∗ (View S g' ∗ Stk (rsp s - 8272#64) lo' w' ∗ FrR s ra x0 u x2.pad F) :=
    fun _ _ _ _ => by ac_rfl
  have hsp : rsp c = rsp s - 8272#64 := by
    show c.regs.get64 .rsp = _
    rw [Reg64s.get64_rsp, h.sp]
  refine ⟨S, g, FrR s ra x0 u x2.pad F, ⟨hdi, hok, ⟨lo, w, h.len, ?_⟩, hA⟩, ?_, ?_⟩
  · have hm := h.mem
    rw [mid_A] at hm
    rw [hsp, permW, hsi, e]
    exact ExArr.intro (n := MAX_N) (by simp) hm
  · rintro t ⟨g', fr', v', hQ, hok', hfl, hm⟩ hag
    rw [hsp, permW, hsi, e] at hm
    obtain ⟨vs, hvs, hm⟩ := ExArr.elim hm
    refine hK t g' ⟨⟨vs.toArray, by simp [hvs]⟩, x2.pad⟩ fr' v' rfl ⟨hfl, ?_, ?_, ?_⟩ hQ hok'
      (Saved.of_agree hag)
    · rw [mid_A]
      exact hm
    · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp]; exact h.sp
    · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r12]; exact h.r12
  · rintro t ⟨g', fr', v', hx, hok', hfl, hm⟩ harg
    rw [hsp, permW, hsi, e] at hm
    obtain ⟨vs, hvs, hm⟩ := ExArr.elim hm
    let L : Lc := ⟨⟨vs.toArray, by simp [hvs]⟩, x2.pad⟩
    apply hX t ?_ harg
    refine ⟨g', fr' ++ v' :: x0 :: u :: (L.A.toList ++ [L.pad,
        s.regs.rbx.toBitVec, s.regs.rbp.toBitVec, s.regs.r12.toBitVec,
        s.regs.r13.toBitVec, s.regs.r14.toBitVec, s.regs.r15.toBitVec]), ra.toBitVec,
      hx, hok', by simp only [List.length_append, List.length_cons, List.length_nil,
        Vector.length_toList, hfl]; rfl, ?_⟩
    rw [stk_frame]
    change (View S g' ∗ Stk (rsp s - 8272#64) fr' v' ∗ Fr s ra x0 u L F).get t.dmem
    rw [mid_A]
    exact hm

end

end Loop
end FlatShuffler.Unit
