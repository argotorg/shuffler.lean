module

public import FlatShuffler.Unit.ExitDefs
import all FlatShuffler.Unit.ExitDefs
public import FlatShuffler.Sep.Stores
import all FlatShuffler.Sep.Stores
public import ProofKit.Cfg
import all ProofKit.Cfg
public import ProofKit.Idioms
import all ProofKit.Idioms

@[expose] public section

/-!
# `permute`: the stack frame

The prologue pushes `r15`, `r14`, `r13`, `r12`, `rbp`, `rbx` and subtracts 8216 from `rsp`.
The body `rsp` is `base s = rsp s - 8272`. The locals (`Lc`) are, from `base s - 8` up:

* `w`: the return slot of the callee `shallowestCopyPosition` (at `base s - 8`);
* `c0` at `(%rsp)`: an unused word; `c1` at `8(%rsp)`: the stack pointer in `regroup`;
* `D`, 1024 words at `16(%rsp)`: the array `desiredBy`;
* `pad`, one word at `8208(%rsp)`.

These are 1028 words. With the six pushed registers they are the 1034 free words of the entry.
The array `permutation` (`P`) is the argument at `rsi`: the frame atom `Arr (rsi s) L.P.toList`.
`L.P` is a part of `Lc`, but not of `Lc.toList`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace FlatShuffler.Unit
open FlatShuffler.Sep
namespace Permute

/-! ## Addresses -/

theorem sub_sub_ofNat (a : Addr) (j k : Nat) :
    a - BitVec.ofNat 64 j - BitVec.ofNat 64 k = a - BitVec.ofNat 64 (j + k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

-- The body `rsp`.
def base (s : MachineData) : Addr := rsp s - 8272#64

/-! ## The locals -/

structure Lc where
  w : Word
  c0 : Word
  c1 : Word
  D : Vector Word maxStackSize
  P : Vector Word maxStackSize
  pad : Word

-- The words of the locals, from `base - 8` up.
def Lc.toList (L : Lc) : List Word :=
  L.w :: L.c0 :: L.c1 :: (L.D.toList ++ [L.pad])

theorem Lc.length_toList (L : Lc) : L.toList.length = 1028 := by
  simp only [Lc.toList, List.length_cons, List.length_append, List.length_nil]
  rw [Vector.length_toList]
  rfl

-- The locals without the return slot of the callee.
def Bd (b : Addr) (L : Lc) : MProp 64 :=
  Wd b L.c0 ∗ Wd (b + 8#64) L.c1 ∗ Arr (b + 16#64) L.D.toList ∗ Wd (b + 8208#64) L.pad

def Loc (b : Addr) (L : Lc) : MProp 64 := Wd (b - 8#64) L.w ∗ Bd b L

theorem arr_loc (b : Addr) (L : Lc) : Arr (b - 8#64) L.toList = Loc b L := by
  simp only [Lc.toList, Arr, Arr.append, Vector.length_toList, Loc, Bd, MProp.sep_emp]
  rw [show b - 8#64 + 8#64 = b by bv_omega, show b + 8#64 + 8#64 = b + 16#64 by bv_omega,
    show b + 16#64 + BitVec.ofNat 64 (8 * maxStackSize) = b + 8208#64 by simp [maxStackSize]; bv_omega]

/-! ## The pushed registers -/

-- The seven words from `sp - 56` up: the six pushed registers and the return address.
def Top (sp : Addr) (x0 x1 x2 x3 x4 x5 v : Word) (F : MProp 64) : MProp 64 :=
  Wd (sp - 56#64) x0 ∗ Wd (sp - 48#64) x1 ∗ Wd (sp - 40#64) x2 ∗ Wd (sp - 32#64) x3
    ∗ Wd (sp - 24#64) x4 ∗ Wd (sp - 16#64) x5 ∗ Wd (sp - 8#64) v ∗ F

-- The saved registers of the entry state `s`, the return address and `F`.
def Sv (s : MachineData) (ra : Int64) (F : MProp 64) : MProp 64 :=
  Top (rsp s) s.regs.rbx.toBitVec s.regs.rbp.toBitVec s.regs.r12.toBitVec s.regs.r13.toBitVec
    s.regs.r14.toBitVec s.regs.r15.toBitVec ra.toBitVec F
theorem stk_frame (sp : Addr) (L : Lc) (x0 x1 x2 x3 x4 x5 v : Word) (F : MProp 64) :
    Stk sp (L.toList ++ [x0, x1, x2, x3, x4, x5]) v ∗ F
      = Loc (sp - 8272#64) L ∗ Top sp x0 x1 x2 x3 x4 x5 v F := by
  have hl : (L.toList ++ [x0, x1, x2, x3, x4, x5]).length = 1034 := by
    simp [Lc.length_toList]
  unfold Stk Top
  rw [hl, Arr.append, Lc.length_toList,
    show sp - 8#64 - BitVec.ofNat 64 (8 * 1034) = sp - 8272#64 - 8#64 by bv_omega, arr_loc]
  simp only [Arr, MProp.sep_emp]
  rw [show sp - 8272#64 - 8#64 + BitVec.ofNat 64 (8 * 1028) = sp - 56#64 by bv_omega,
    show sp - 56#64 + 8#64 = sp - 48#64 by bv_omega,
    show sp - 48#64 + 8#64 = sp - 40#64 by bv_omega,
    show sp - 40#64 + 8#64 = sp - 32#64 by bv_omega,
    show sp - 32#64 + 8#64 = sp - 24#64 by bv_omega,
    show sp - 24#64 + 8#64 = sp - 16#64 by bv_omega]
  ac_rfl

-- The 1034 free words of the entry: the locals and the six words of the pushes. `P` is the
-- ghost of the array `permutation`.
theorem split1034 {fr : List Word} (h : fr.length = 1034) (P : Vector Word maxStackSize) :
    ∃ L : Lc, L.P = P ∧ ∃ x0 x1 x2 x3 x4 x5, fr = L.toList ++ [x0, x1, x2, x3, x4, x5] := by
  match fr, h with
  | w :: c0 :: c1 :: r, h =>
    have hr : r.length = 1031 := by simpa using h
    have hd : (r.drop 1024).length = 7 := by simp [hr]
    match e : r.drop 1024, hd with
    | [pad, x0, x1, x2, x3, x4, x5], _ =>
      refine ⟨⟨w, c0, c1, ⟨(r.take 1024).toArray, by simp [hr, maxStackSize]⟩, P, pad⟩, rfl,
        x0, x1, x2, x3, x4, x5, ?_⟩
      have hr' : r = r.take 1024 ++ [pad, x0, x1, x2, x3, x4, x5] := by
        conv => lhs; rw [← List.take_append_drop 1024 r, e]
      show _ = (w :: c0 :: c1 :: (r.take 1024 ++ [pad])) ++ [x0, x1, x2, x3, x4, x5]
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and, List.nil_append]
      exact hr'

/-! ## The body state -/

-- The frame of the body: the saved registers, the return address, the array `permutation` at
-- the argument `rsi s` and `F`.
def Fr (s : MachineData) (ra : Int64) (L : Lc) (F : MProp 64) : MProp 64 :=
  Sv s ra (Arr (rsi s) L.P.toList ∗ F)

-- A state between the prologue and the epilogue: the struct `g`, the locals `L`, and `rsp` is
-- `base s`.
structure Fm (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) (L : Lc)
    (t : MachineData) : Prop where
  mem : (View S g ∗ Loc (base s) L ∗ Fr s ra L F).get t.dmem
  sp : t.regs.rsp.toBitVec = base s

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
variable {S : Addr} {g : G} {F : MProp 64} {s : MachineData} {ra : Int64} {L : Lc}

-- The six `pushq` and the `subq` of the prologue, from the entry stack (`r` is `rsp` after the
-- call).
theorem Fm.push {m₀ : Mem 64} {x0 x1 x2 x3 x4 x5 : Word} {c : MachineData}
    (hm : (View S g ∗ Stk (rsp s) (L.toList ++ [x0, x1, x2, x3, x4, x5]) ra.toBitVec
      ∗ (Arr (rsi s) L.P.toList ∗ F)).get m₀)
    {r : Addr} (hr : r = rsp s - 8#64)
    (hc : c.dmem = (((((m₀.storeInt (r - 8#64) 8 s.regs.r15.toBitVec.toInt).storeInt
        (r - 8#64 - 8#64) 8 s.regs.r14.toBitVec.toInt).storeInt
        (r - 8#64 - 8#64 - 8#64) 8 s.regs.r13.toBitVec.toInt).storeInt
        (r - 8#64 - 8#64 - 8#64 - 8#64) 8 s.regs.r12.toBitVec.toInt).storeInt
        (r - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8 s.regs.rbp.toBitVec.toInt).storeInt
        (r - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8 s.regs.rbx.toBitVec.toInt)
    (hsp : c.regs.rsp.toBitVec = r - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8216#64) :
    Fm S g F s ra L c := by
  subst hr
  simp only [sub_sub_ofNat, Nat.reduceAdd] at hc hsp
  rw [stk_frame] at hm
  refine ⟨?_, hsp⟩
  rw [hc]
  have h1 : (View S g ∗ Loc (rsp s - 8272#64) L
      ∗ Top (rsp s) x0 x1 x2 x3 x4 s.regs.r15.toBitVec ra.toBitVec (Arr (rsi s) L.P.toList ∗ F)).get _ :=
    wd_store (a := rsp s - 16#64) hm (by unfold Top; ecancel) (by unfold Top; ecancel)
  have h2 : (View S g ∗ Loc (rsp s - 8272#64) L
      ∗ Top (rsp s) x0 x1 x2 x3 s.regs.r14.toBitVec s.regs.r15.toBitVec ra.toBitVec
        (Arr (rsi s) L.P.toList ∗ F)).get _ :=
    wd_store (a := rsp s - 24#64) h1 (by unfold Top; ecancel) (by unfold Top; ecancel)
  have h3 : (View S g ∗ Loc (rsp s - 8272#64) L
      ∗ Top (rsp s) x0 x1 x2 s.regs.r13.toBitVec s.regs.r14.toBitVec s.regs.r15.toBitVec
        ra.toBitVec (Arr (rsi s) L.P.toList ∗ F)).get _ :=
    wd_store (a := rsp s - 32#64) h2 (by unfold Top; ecancel) (by unfold Top; ecancel)
  have h4 : (View S g ∗ Loc (rsp s - 8272#64) L
      ∗ Top (rsp s) x0 x1 s.regs.r12.toBitVec s.regs.r13.toBitVec s.regs.r14.toBitVec
        s.regs.r15.toBitVec ra.toBitVec (Arr (rsi s) L.P.toList ∗ F)).get _ :=
    wd_store (a := rsp s - 40#64) h3 (by unfold Top; ecancel) (by unfold Top; ecancel)
  have h5 : (View S g ∗ Loc (rsp s - 8272#64) L
      ∗ Top (rsp s) x0 s.regs.rbp.toBitVec s.regs.r12.toBitVec s.regs.r13.toBitVec
        s.regs.r14.toBitVec s.regs.r15.toBitVec ra.toBitVec (Arr (rsi s) L.P.toList ∗ F)).get _ :=
    wd_store (a := rsp s - 48#64) h4 (by unfold Top; ecancel) (by unfold Top; ecancel)
  exact wd_store (a := rsp s - 56#64) h5 (by unfold Top; ecancel)
    (by unfold base Fr Sv Top; ecancel)

-- The six loads of the epilogue.
theorem Fm.isSome_pop {t : MachineData} (h : Fm S g F s ra L t) {k : Nat} (hk : k < 6) :
    (t.dmem.loadInt (8216#64 + t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * k)) 8).isSome
      = true := by
  rw [h.sp]
  have hm := h.mem
  unfold base
  match k, hk with
  | 0, _ => rw [show 8216#64 + (rsp s - 8272#64) + BitVec.ofNat 64 (8 * 0) = rsp s - 56#64 by
              bv_omega]
            exact isSome_of_eq _ hm (by unfold Fr Sv Top; ecancel)
  | 1, _ => rw [show 8216#64 + (rsp s - 8272#64) + BitVec.ofNat 64 (8 * 1) = rsp s - 48#64 by
              bv_omega]
            exact isSome_of_eq _ hm (by unfold Fr Sv Top; ecancel)
  | 2, _ => rw [show 8216#64 + (rsp s - 8272#64) + BitVec.ofNat 64 (8 * 2) = rsp s - 40#64 by
              bv_omega]
            exact isSome_of_eq _ hm (by unfold Fr Sv Top; ecancel)
  | 3, _ => rw [show 8216#64 + (rsp s - 8272#64) + BitVec.ofNat 64 (8 * 3) = rsp s - 32#64 by
              bv_omega]
            exact isSome_of_eq _ hm (by unfold Fr Sv Top; ecancel)
  | 4, _ => rw [show 8216#64 + (rsp s - 8272#64) + BitVec.ofNat 64 (8 * 4) = rsp s - 24#64 by
              bv_omega]
            exact isSome_of_eq _ hm (by unfold Fr Sv Top; ecancel)
  | 5, _ => rw [show 8216#64 + (rsp s - 8272#64) + BitVec.ofNat 64 (8 * 5) = rsp s - 16#64 by
              bv_omega]
            exact isSome_of_eq _ hm (by unfold Fr Sv Top; ecancel)

-- The epilogue: the state `P` before the `ret` is a `Kp` state, with the array `permutation`
-- in the frame.
theorem Fm.pop {t P : MachineData} (h : Fm S g F s ra L t) (hm : P.dmem = t.dmem)
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
    Kp S g (Arr (rsi s) L.P.toList ∗ F) s ra (L.toList ++ [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec,
      s.regs.r12.toBitVec, s.regs.r13.toBitVec, s.regs.r14.toBitVec, s.regs.r15.toBitVec]) P := by
  have hmem := h.mem
  rw [h.sp] at hsp hbx hbp h12 h13 h14 h15
  unfold base at hsp hbx hbp h12 h13 h14 h15 hmem
  unfold Fr at hmem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm, stk_frame]; exact hmem
  · apply UInt64.toBitVec_inj.mp
    rw [hsp]
    show _ = rsp s - 8#64
    bv_omega
  · apply UInt64.toBitVec_inj.mp
    rw [hbx, show 8216#64 + (rsp s - 8272#64) = rsp s - 56#64 by bv_omega]
    exact rd_of_eq hmem (by unfold Sv Top; ecancel)
  · apply UInt64.toBitVec_inj.mp
    rw [hbp, show 8216#64 + (rsp s - 8272#64) + 8#64 = rsp s - 48#64 by bv_omega]
    exact rd_of_eq hmem (by unfold Sv Top; ecancel)
  · apply UInt64.toBitVec_inj.mp
    rw [h12, show 8216#64 + (rsp s - 8272#64) + 8#64 + 8#64 = rsp s - 40#64 by bv_omega]
    exact rd_of_eq hmem (by unfold Sv Top; ecancel)
  · apply UInt64.toBitVec_inj.mp
    rw [h13, show 8216#64 + (rsp s - 8272#64) + 8#64 + 8#64 + 8#64 = rsp s - 32#64 by bv_omega]
    exact rd_of_eq hmem (by unfold Sv Top; ecancel)
  · apply UInt64.toBitVec_inj.mp
    rw [h14, show 8216#64 + (rsp s - 8272#64) + 8#64 + 8#64 + 8#64 + 8#64 = rsp s - 24#64 by
      bv_omega]
    exact rd_of_eq hmem (by unfold Sv Top; ecancel)
  · apply UInt64.toBitVec_inj.mp
    rw [h15, show 8216#64 + (rsp s - 8272#64) + 8#64 + 8#64 + 8#64 + 8#64 + 8#64
      = rsp s - 16#64 by bv_omega]
    exact rd_of_eq hmem (by unfold Sv Top; ecancel)

-- A step that keeps `rsp`: the struct is now `g'` and the locals are `L'`.
theorem Fm.step {t P : MachineData} {g' : G} {L' : Lc} (h : Fm S g F s ra L t)
    (hm : (View S g' ∗ Loc (base s) L' ∗ Fr s ra L' F).get P.dmem)
    (hsp : P.regs.rsp = t.regs.rsp) : Fm S g' F s ra L' P :=
  ⟨hm, by rw [hsp]; exact h.sp⟩

-- A step that keeps the memory and `rsp`.
theorem Fm.next {t P : MachineData} (h : Fm S g F s ra L t) (hm : P.dmem = t.dmem)
    (hsp : P.regs.rsp = t.regs.rsp) : Fm S g F s ra L P :=
  h.step (hm ▸ h.mem) hsp

theorem Fm.stack {t : MachineData} (h : Fm S g F s ra L t) : t.StackAtOrBelow (s.pushRa ra) :=
  MachineData.stackAtOrBelow_of_toNat_lt (by
    rw [Reg64s.get64_rsp, Reg64s.get64_rsp, h.sp]
    simp only [MachineData.pushRa, base, rsp, Reg64s.get64_rsp, Reg64s.set64_rsp]
    bv_omega)

-- An external call writes only its return slot below the body frame.
theorem Fm.pushExit {t : MachineData} (h : Fm S g F s ra L t) (exitRa : Int64) :
    (View S g ∗ Loc (base s) { L with w := exitRa.toBitVec } ∗ Fr s ra L F).get
      (t.pushRa exitRa).dmem := by
  have hm := h.mem
  have he : View S g ∗ Loc (base s) L ∗ Fr s ra L F =
      Wd (base s - 8#64) L.w ∗ (View S g ∗ Bd (base s) L ∗ Fr s ra L F) := by
    unfold Loc; ac_rfl
  have he' : View S g ∗ Loc (base s) { L with w := exitRa.toBitVec } ∗ Fr s ra L F =
      Wd (base s - 8#64) exitRa.toBitVec ∗ (View S g ∗ Bd (base s) L ∗ Fr s ra L F) := by
    unfold Loc Bd; ac_rfl
  rw [he']
  simpa only [MachineData.pushRa, Reg64s.get64_rsp, h.sp] using Wd.store (he ▸ hm) exitRa.toBitVec

-- A body frame gives the memory postcondition at an external boundary.
theorem frame_post {t : MachineData}
    (hm : (View S g ∗ Loc (base s) L ∗ Fr s ra L F).get t.dmem)
    {Q : G → MachineData → Prop} (hok : g.Ok) (hq : Q g t) :
    Sep.Post S (permW s ∗ F) 1034 Q s t := by
  have he : View S g ∗ Loc (base s) L ∗ Fr s ra L F =
      View S g ∗ Stk (rsp s)
        (L.toList ++ [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec, s.regs.r12.toBitVec,
          s.regs.r13.toBitVec, s.regs.r14.toBitVec, s.regs.r15.toBitVec]) ra.toBitVec ∗
        (Arr (rsi s) L.P.toList ∗ F) := by
    rw [stk_frame]; rfl
  rw [he] at hm
  have he' : ∀ X : MProp 64, View S g ∗ Stk (rsp s)
      (L.toList ++ [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec, s.regs.r12.toBitVec,
        s.regs.r13.toBitVec, s.regs.r14.toBitVec, s.regs.r15.toBitVec]) ra.toBitVec ∗ (X ∗ F) =
      X ∗ (View S g ∗ Stk (rsp s)
        (L.toList ++ [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec, s.regs.r12.toBitVec,
          s.regs.r13.toBitVec, s.regs.r14.toBitVec, s.regs.r15.toBitVec]) ra.toBitVec ∗ F) := by
    intro X; ac_rfl
  refine ⟨g, L.toList ++ [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec, s.regs.r12.toBitVec,
    s.regs.r13.toBitVec, s.regs.r14.toBitVec, s.regs.r15.toBitVec],
    ra.toBitVec, hq, hok, by simp [Lc.length_toList], ?_⟩
  rw [he'] at hm ⊢
  exact ExArr.intro (by simp) hm

/-! ## The call of `shallowestCopyPosition` -/

-- The callee gets no free word: its return address goes to the slot `w` below the locals.
theorem frame_call (P : MProp 64) (b : Addr) (L : Lc) (X : MProp 64) :
    P ∗ Loc b L ∗ X = P ∗ Stk b [] L.w ∗ (Bd b L ∗ X) := by
  unfold Stk Loc
  simp only [Arr, MProp.emp_sep]
  ac_rfl

-- The call rule of a callee with no free word, from a `Fm` state.
theorem Fm.call0 {A : G → MachineData → Prop} {Q : G → G → MachineData → MachineData → Prop}
    {c : MachineData} {K : MachineData → Prop} (h : Fm S g F s ra L c) (hdi : rdi c = S)
    (hok : g.Ok) (hA : A g c)
    (hK : ∀ t g' w', Fm S g' F s ra { L with w := w' } t → Q g g' c t → g'.Ok → Saved c t → K t) :
    ∃ S' g' F', Sep.Pre S' g' F' A 0 c
      ∧ ∀ s', Sep.Post S' F' 0 (fun g'' t => Q g' g'' c t) c s' → Sep.mod.Agree c s' → K s' := by
  refine ⟨S, g, Bd (base s) L ∗ Fr s ra L F, ⟨hdi, hok, ⟨[], L.w, rfl, ?_⟩, hA⟩, ?_⟩
  · have hm := h.mem
    rw [frame_call] at hm
    simpa only [rsp, Reg64s.get64_rsp, h.sp] using hm
  · rintro s' ⟨g', fr', v', hQ, hok', hl, hm⟩ hag
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    refine hK s' g' v' ⟨?_, ?_⟩ hQ hok' (Saved.of_agree hag)
    · rw [frame_call, show Bd (base s) { L with w := v' } = Bd (base s) L from rfl,
        show Fr s ra { L with w := v' } F = Fr s ra L F from rfl]
      simpa only [rsp, Reg64s.get64_rsp, h.sp] using hm
    · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp]; exact h.sp

/-! ## The locals and the array `permutation` -/

theorem fm_P (P : MProp 64) (b : Addr) (L : Lc) (s : MachineData) (ra : Int64) (F : MProp 64) :
    P ∗ Loc b L ∗ Fr s ra L F = Arr (rsi s) L.P.toList ∗ (P ∗ Loc b L ∗ Sv s ra F) := by
  unfold Fr Sv Top; ac_rfl

theorem loc_D (P : MProp 64) (b : Addr) (L : Lc) (X : MProp 64) :
    P ∗ Loc b L ∗ X = Arr (b + 16#64) L.D.toList ∗ (P ∗ Wd (b - 8#64) L.w ∗ Wd b L.c0
      ∗ Wd (b + 8#64) L.c1 ∗ Wd (b + 8208#64) L.pad ∗ X) := by
  unfold Loc Bd; ac_rfl

theorem Fm.rdP {t : MachineData} (h : Fm S g F s ra L t) {i : Nat} (hi : i < maxStackSize) {a : Addr}
    (ha : a = rsi s + BitVec.ofNat 64 (8 * i)) : rd t.dmem a = L.P[i] := by
  have hm := h.mem
  rw [fm_P] at hm
  rw [ha]
  exact (Arr.rd hm (by simpa using hi)).trans (by simp)

theorem Fm.isSomeP {t : MachineData} (h : Fm S g F s ra L t) {i : Nat} (hi : i < maxStackSize)
    {a : Addr} (ha : a = rsi s + BitVec.ofNat 64 (8 * i)) :
    (t.dmem.loadInt a 8).isSome = true := by
  have hm := h.mem
  rw [fm_P] at hm
  rw [ha]
  exact Arr.isSome hm (by simpa using hi)

theorem Fm.storeP {t P : MachineData} (h : Fm S g F s ra L t) {i : Nat} (hi : i < maxStackSize)
    {a : Addr} (ha : a = rsi s + BitVec.ofNat 64 (8 * i)) (w : Word)
    (hm : P.dmem = t.dmem.storeInt a 8 w.toInt) (hsp : P.regs.rsp = t.regs.rsp) :
    Fm S g F s ra { L with P := L.P.set i w hi } P := by
  refine h.step ?_ hsp
  have hm0 := h.mem
  rw [fm_P] at hm0
  rw [hm, ha, fm_P]
  have h2 := Arr.store hm0 (by simpa using hi) w
  rw [← Vector.toList_set hi] at h2
  exact h2

theorem Fm.rdD {t : MachineData} (h : Fm S g F s ra L t) {i : Nat} (hi : i < maxStackSize) {a : Addr}
    (ha : a = base s + 16#64 + BitVec.ofNat 64 (8 * i)) : rd t.dmem a = L.D[i] := by
  have hm := h.mem
  rw [loc_D] at hm
  rw [ha]
  exact (Arr.rd hm (by simpa using hi)).trans (by simp)

theorem Fm.isSomeD {t : MachineData} (h : Fm S g F s ra L t) {i : Nat} (hi : i < maxStackSize)
    {a : Addr} (ha : a = base s + 16#64 + BitVec.ofNat 64 (8 * i)) :
    (t.dmem.loadInt a 8).isSome = true := by
  have hm := h.mem
  rw [loc_D] at hm
  rw [ha]
  exact Arr.isSome hm (by simpa using hi)

theorem Fm.storeD {t P : MachineData} (h : Fm S g F s ra L t) {i : Nat} (hi : i < maxStackSize)
    {a : Addr} (ha : a = base s + 16#64 + BitVec.ofNat 64 (8 * i)) (w : Word)
    (hm : P.dmem = t.dmem.storeInt a 8 w.toInt) (hsp : P.regs.rsp = t.regs.rsp) :
    Fm S g F s ra { L with D := L.D.set i w hi } P := by
  refine h.step ?_ hsp
  have hm0 := h.mem
  rw [loc_D] at hm0
  rw [hm, ha, loc_D]
  have h2 := Arr.store hm0 (by simpa using hi) w
  rw [← Vector.toList_set hi] at h2
  exact h2

-- `(%rsp)`: `c0`.
theorem Fm.rdC0 {t : MachineData} (h : Fm S g F s ra L t) {a : Addr} (ha : a = base s) :
    rd t.dmem a = L.c0 := by
  rw [ha]; exact rd_of_eq h.mem (by unfold Loc Bd; ecancel)

theorem Fm.isSomeC0 {t : MachineData} (h : Fm S g F s ra L t) {a : Addr} (ha : a = base s) :
    (t.dmem.loadInt a 8).isSome = true := by
  rw [ha]; exact isSome_of_eq _ h.mem (by unfold Loc Bd; ecancel)

theorem Fm.storeC0 {t P : MachineData} (h : Fm S g F s ra L t) {a : Addr} (ha : a = base s)
    (w : Word) (hm : P.dmem = t.dmem.storeInt a 8 w.toInt) (hsp : P.regs.rsp = t.regs.rsp) :
    Fm S g F s ra { L with c0 := w } P := by
  refine h.step ?_ hsp
  show (View S g ∗ Loc (base s) _ ∗ Fr s ra L F).get _
  rw [hm, ha]
  exact wd_store h.mem (by unfold Loc Bd; ecancel) (by unfold Loc Bd; ecancel)

-- `8(%rsp)`: `c1`.
theorem Fm.rdC1 {t : MachineData} (h : Fm S g F s ra L t) {a : Addr} (ha : a = base s + 8#64) :
    rd t.dmem a = L.c1 := by
  rw [ha]; exact rd_of_eq h.mem (by unfold Loc Bd; ecancel)

theorem Fm.isSomeC1 {t : MachineData} (h : Fm S g F s ra L t) {a : Addr}
    (ha : a = base s + 8#64) : (t.dmem.loadInt a 8).isSome = true := by
  rw [ha]; exact isSome_of_eq _ h.mem (by unfold Loc Bd; ecancel)

theorem Fm.storeC1 {t P : MachineData} (h : Fm S g F s ra L t) {a : Addr}
    (ha : a = base s + 8#64) (w : Word) (hm : P.dmem = t.dmem.storeInt a 8 w.toInt)
    (hsp : P.regs.rsp = t.regs.rsp) : Fm S g F s ra { L with c1 := w } P := by
  refine h.step ?_ hsp
  show (View S g ∗ Loc (base s) _ ∗ Fr s ra L F).get _
  rw [hm, ha]
  exact wd_store h.mem (by unfold Loc Bd; ecancel) (by unfold Loc Bd; ecancel)

end

/-! ## Address forms of the asm -/

-- An index of scale 8.
theorem idx8 (b x : Addr) : b + x * 8#64 = b + BitVec.ofNat 64 (8 * x.toNat) := by
  bv_omega

-- An index of scale 8 and a displacement.
theorem idx8d (b x c : Addr) : b + x * 8#64 + c = b + c + BitVec.ofNat 64 (8 * x.toNat) := by
  bv_omega

-- An index of scale 1 that is 8 times an offset, and a displacement.
theorem idx1d (b y c : Addr) {i : Nat} (hy : y.toNat = 8 * i) :
    b + y + c = b + c + BitVec.ofNat 64 (8 * i) := by
  bv_omega

-- An index of scale 1 that is 8 times an offset.
theorem idx1 (b y : Addr) {i : Nat} (hy : y.toNat = 8 * i) :
    b + y = b + BitVec.ofNat 64 (8 * i) := by
  bv_omega

end Permute
end FlatShuffler.Unit
