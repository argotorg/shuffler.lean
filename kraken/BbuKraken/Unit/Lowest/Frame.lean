module

public import BbuKraken.Unit.Lowest.Defs
import all BbuKraken.Unit.Lowest.Defs
public import BbuKraken.Unit.Loop.Frame
import all BbuKraken.Unit.Loop.Frame

@[expose] public section

/-!
# `permuteAtLowestHeight`: the stack frame

The function pushes no register and subtracts 24584 from `rsp`. The body `rsp` is
`rsp s - 24592`. The locals are, from the body `rsp` up:

* `parked`, 1024 words at `(%rsp)` (`rsp s - 24592`);
* `holes`, 1024 words at `8192(%rsp)` (`rsp s - 16400`);
* `permutation`, 1024 words at `16384(%rsp)` (`rsp s - 8208`), the argument of `permute`;
* `pad` at `rsp s - 16`.

`permute` gets the free words below `rsp s - 24592`: 1034 words and the return slot `w` at
`rsp s - 24600`.

`Mid` is a body state. The function does not write `rbx`, `rbp`, `r12` to `r15`, and
`permute` keeps them, so `Mid` holds their entry values (`Saved`).
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace Bbu.Unit
open Bbu.Sep
namespace Lowest

open Loop (Saved sub_sub_ofNat)

/-! ## The stack -/

-- The local arrays and one word.
structure Lc where
  parked : Vector Word MAX_N
  holes : Vector Word MAX_N
  perm : Vector Word MAX_N
  pad : Word

-- The 3073 words of the locals, from the body `rsp` up.
def Lc.words (L : Lc) : List Word :=
  L.parked.toList ++ L.holes.toList ++ L.perm.toList ++ [L.pad]

-- The content of the arrays as `Flat.Locals`.
def Lc.locals (L : Lc) : Flat.Locals := ⟨L.perm, L.holes, L.parked⟩

-- The locals, the return address and `F`.
def Top (sp : Addr) (L : Lc) (v : Word) (F : MProp 64) : MProp 64 :=
  Arr (sp - 24592#64) L.parked.toList ∗ Arr (sp - 16400#64) L.holes.toList
    ∗ Arr (sp - 8208#64) L.perm.toList ∗ Wd (sp - 16#64) L.pad ∗ Wd (sp - 8#64) v ∗ F

-- The free words of the entry: `lo` for `permute`, its return slot `w`, and the locals.
theorem stk_frame (sp : Addr) (lo : List Word) (w : Word) (L : Lc) (v : Word) (F : MProp 64) :
    Stk sp (lo ++ w :: L.words) v ∗ F = Stk (sp - 24592#64) lo w ∗ Top sp L v F := by
  have hl : L.words.length = 3073 := by
    simp only [Lc.words, List.length_append, Vector.length_toList, List.length_cons,
      List.length_nil]; rfl
  rw [Loop.stk_top, hl]
  rw [show sp - 8#64 - BitVec.ofNat 64 (8 * 3073) = sp - 24592#64 by bv_omega]
  unfold Lc.words
  have hp : L.parked.toList.length = 1024 := Vector.length_toList
  have hh : L.holes.toList.length = 1024 := Vector.length_toList
  have hq : L.perm.toList.length = 1024 := Vector.length_toList
  rw [Arr.append, Arr.append, Arr.append]
  simp only [Arr, MProp.sep_emp]
  rw [show sp - 24592#64 + BitVec.ofNat 64 (8 * L.parked.toList.length) = sp - 16400#64 by
      simp only [hp]; bv_omega,
    show sp - 24592#64 + BitVec.ofNat 64 (8 * (L.parked.toList ++ L.holes.toList).length)
      = sp - 8208#64 by simp only [List.length_append, hp, hh]; bv_omega,
    show sp - 24592#64 + BitVec.ofNat 64
      (8 * (L.parked.toList ++ L.holes.toList ++ L.perm.toList).length) = sp - 16#64 by
      simp only [List.length_append, hp, hh, hq]; bv_omega]
  unfold Top
  ac_rfl

-- 3073 words are the locals of an `Lc`.
theorem lc_of_length {r : List Word} (hr : r.length = 3073) : ∃ L : Lc, r = L.words := by
  have hd : (r.drop 3072).length = 1 := by simp [hr]
  match e : r.drop 3072, hd with
  | [pad], _ =>
    refine ⟨⟨⟨(r.take 1024).toArray, by simp [hr, MAX_N]⟩,
      ⟨((r.drop 1024).take 1024).toArray, by simp [hr, MAX_N]⟩,
      ⟨((r.drop 2048).take 1024).toArray, by simp [hr, MAX_N]⟩, pad⟩, ?_⟩
    have h1 : r = r.take 3072 ++ [pad] := by rw [← e, List.take_append_drop]
    have h2 : r.take 3072
        = r.take 1024 ++ (r.drop 1024).take 1024 ++ (r.drop 2048).take 1024 := by
      have a : r.take 3072 = r.take 2048 ++ (r.drop 2048).take 1024 := by
        rw [show 3072 = 2048 + 1024 from rfl, List.take_add]
      have b : r.take 2048 = r.take 1024 ++ (r.drop 1024).take 1024 := by
        rw [show 2048 = 1024 + 1024 from rfl, List.take_add]
      rw [a, b]
    simp only [Lc.words]
    exact h1.trans (by rw [h2]; rfl)

-- The 4108 free words of the entry.
theorem split4108 {fr : List Word} (h : fr.length = 4108) :
    ∃ lo w, ∃ L : Lc, fr = lo ++ w :: L.words ∧ lo.length = 1034 := by
  have hd : (fr.drop 1034).length = 3074 := by simp [h]
  match e : fr.drop 1034, hd with
  | w :: r, hd =>
    have hr : r.length = 3073 := by simpa using hd
    obtain ⟨L, rfl⟩ := lc_of_length hr
    refine ⟨fr.take 1034, w, L, ?_, by simp [h]⟩
    conv => lhs; rw [← List.take_append_drop 1034 fr, e]

/-! ## The body state -/

-- The frame of `permute`: the locals, the return address and `F`.
def Fr (s : MachineData) (ra : Int64) (L : Lc) (F : MProp 64) : MProp 64 :=
  Top (rsp s) L ra.toBitVec F

-- A state between the prologue and the epilogue: 1034 free words `lo`, the return slot `w` of
-- `permute`, the locals `L`, and the callee-saved registers of the entry.
structure Mid (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) (L : Lc)
    (lo : List Word) (w : Word) (t : MachineData) : Prop where
  len : lo.length = 1034
  mem : (View S g ∗ Stk (rsp s - 24592#64) lo w ∗ Fr s ra L F).get t.dmem
  sp : t.regs.rsp.toBitVec = rsp s - 24592#64
  sv : Saved s t

theorem _root_.Bbu.Unit.Loop.Saved.trans {a b c : MachineData} (h1 : Saved a b) (h2 : Saved b c) : Saved a c :=
  ⟨h2.bx.trans h1.bx, h2.bp.trans h1.bp, h2.r12.trans h1.r12, h2.r13.trans h1.r13,
    h2.r14.trans h1.r14, h2.r15.trans h1.r15⟩

section
variable {S : Addr} {g : G} {F : MProp 64} {s : MachineData} {ra : Int64} {L : Lc}
  {lo : List Word} {w : Word}

-- The prologue: the state `P` after `subq $24584, %rsp` in the state `c` after the call.
theorem Mid.init {fr : List Word} {c P : MachineData} (hk : Kp S g F s ra fr c)
    (hfr : fr = lo ++ w :: L.words) (hlo : lo.length = 1034) (hm : P.dmem = c.dmem)
    (hsp : P.regs.rsp.toBitVec = rsp s - 24592#64)
    (hsv : Saved c P := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) : Mid S g F s ra L lo w P := by
  have hm' := hk.mem
  rw [hfr, stk_frame] at hm'
  exact ⟨hlo, hm ▸ hm', hsp, Saved.trans ⟨hk.bx, hk.bp, hk.r12, hk.r13, hk.r14, hk.r15⟩ hsv⟩

-- A step that keeps `rsp` and the callee-saved registers: the struct is now `g'` and the
-- locals are `L'`.
theorem Mid.step {t P : MachineData} {g' : G} {L' : Lc} (h : Mid S g F s ra L lo w t)
    (hm : (View S g' ∗ Stk (rsp s - 24592#64) lo w ∗ Fr s ra L' F).get P.dmem)
    (hsp : P.regs.rsp = t.regs.rsp)
    (hsv : Saved t P := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) :
    Mid S g' F s ra L' lo w P :=
  ⟨h.len, hm, by rw [hsp]; exact h.sp, h.sv.trans hsv⟩

-- A step that keeps the memory, `rsp` and the callee-saved registers.
theorem Mid.next {t P : MachineData} (h : Mid S g F s ra L lo w t) (hm : P.dmem = t.dmem)
    (hsp : P.regs.rsp = t.regs.rsp)
    (hsv : Saved t P := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) :
    Mid S g F s ra L lo w P :=
  h.step (hm ▸ h.mem) hsp hsv

theorem Mid.stack {t : MachineData} (h : Mid S g F s ra L lo w t) :
    t.StackAtOrBelow (s.pushRa ra) :=
  MachineData.stackAtOrBelow_of_toNat_lt (by
    rw [Reg64s.get64_rsp, Reg64s.get64_rsp, h.sp]
    simp only [MachineData.pushRa, rsp, Reg64s.get64_rsp, Reg64s.set64_rsp]
    bv_omega)

-- The epilogue: the state `P` after `addq $24584, %rsp` is a `Kp` state.
theorem Mid.pop {t P : MachineData} (h : Mid S g F s ra L lo w t) (hm : P.dmem = t.dmem)
    (hsp : P.regs.rsp.toBitVec = 24584#64 + t.regs.rsp.toBitVec)
    (hsv : Saved t P := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) :
    Kp S g F s ra (lo ++ w :: L.words) P := by
  have hs := h.sv.trans hsv
  refine ⟨?_, ?_, hs.bx, hs.bp, hs.r12, hs.r13, hs.r14, hs.r15⟩
  · rw [hm, stk_frame]; exact h.mem
  · apply UInt64.toBitVec_inj.mp
    rw [hsp, h.sp]
    show _ = rsp s - 8#64
    bv_omega

theorem words_length (lo : List Word) (w : Word) (L : Lc) (hlo : lo.length = 1034) :
    (lo ++ w :: L.words).length = lowestD := by
  simp only [Lc.words, List.length_append, Vector.length_toList, List.length_cons,
    List.length_nil, hlo]; rfl

theorem Mid.pushExit {t : MachineData} (h : Mid S g F s ra L lo w t) (exitRa : Int64) :
    (View S g ∗ Stk (rsp s - 24592#64) lo exitRa.toBitVec ∗ Fr s ra L F).get
      (t.pushRa exitRa).dmem := by
  have he : View S g ∗ Stk (rsp s - 24592#64) lo w ∗ Fr s ra L F =
      Wd (rsp s - 24592#64 - 8#64) w ∗
        (View S g ∗ Arr (rsp s - 24592#64 - 8#64 - BitVec.ofNat 64 (8 * lo.length)) lo ∗
          Fr s ra L F) := by
    unfold Stk; ac_rfl
  have he' : View S g ∗ Stk (rsp s - 24592#64) lo exitRa.toBitVec ∗ Fr s ra L F =
      Wd (rsp s - 24592#64 - 8#64) exitRa.toBitVec ∗
        (View S g ∗ Arr (rsp s - 24592#64 - 8#64 - BitVec.ofNat 64 (8 * lo.length)) lo ∗
          Fr s ra L F) := by
    unfold Stk; ac_rfl
  rw [he']
  simpa only [MachineData.pushRa, Reg64s.get64_rsp, h.sp] using Wd.store (he ▸ h.mem) exitRa.toBitVec

theorem frame_post {t : MachineData}
    (hm : (View S g ∗ Stk (rsp s - 24592#64) lo w ∗ Fr s ra L F).get t.dmem)
    (hlo : lo.length = 1034) {Q : G → MachineData → Prop} (hok : g.Ok) (hq : Q g t) :
    Sep.Post S F lowestD Q s t := by
  refine ⟨g, lo ++ w :: L.words, ra.toBitVec, hq, hok, words_length lo w L hlo, ?_⟩
  rw [stk_frame]
  exact hm

/-! ## The local arrays -/

theorem arr_rd {P R : MProp 64} {m : Mem 64} {a : Addr} (l : List Word) (h : P.get m)
    (e : P = Arr a l ∗ R) {i : Nat} (hi : i < l.length) :
    rd m (a + BitVec.ofNat 64 (8 * i)) = l[i] := Arr.rd (e ▸ h) hi

theorem arr_isSome {P R : MProp 64} {m : Mem 64} {a : Addr} (l : List Word) (h : P.get m)
    (e : P = Arr a l ∗ R) {i : Nat} (hi : i < l.length) :
    (m.loadInt (a + BitVec.ofNat 64 (8 * i)) 8).isSome = true := Arr.isSome (e ▸ h) hi

theorem arr_store {P P' R : MProp 64} {m : Mem 64} {a : Addr} (l : List Word) (h : P.get m)
    (e : P = Arr a l ∗ R) {i : Nat} (hi : i < l.length) (v : Word) (e' : P' = Arr a (l.set i v) ∗ R) :
    P'.get (m.storeInt (a + BitVec.ofNat 64 (8 * i)) 8 v.toInt) := e' ▸ Arr.store (e ▸ h) hi v

-- The base addresses of the arrays.
abbrev aParked (s : MachineData) : Addr := rsp s - 24592#64
abbrev aHoles (s : MachineData) : Addr := rsp s - 16400#64
abbrev aPerm (s : MachineData) : Addr := rsp s - 8208#64

theorem Mid.rdParked {t : MachineData} (h : Mid S g F s ra L lo w t) {i : Nat} (hi : i < MAX_N)
    {a : Addr} (ha : a = aParked s + BitVec.ofNat 64 (8 * i)) : rd t.dmem a = L.parked[i] := by
  rw [ha]
  exact (arr_rd L.parked.toList h.mem (by unfold Fr Top; ecancel) (by simpa using hi)).trans
    (by simp)

theorem Mid.isSomeParked {t : MachineData} (h : Mid S g F s ra L lo w t) {i : Nat}
    (hi : i < MAX_N) {a : Addr} (ha : a = aParked s + BitVec.ofNat 64 (8 * i)) :
    (t.dmem.loadInt a 8).isSome = true := by
  rw [ha]; exact arr_isSome L.parked.toList h.mem (by unfold Fr Top; ecancel) (by simpa using hi)

theorem Mid.storeParked {t P : MachineData} (h : Mid S g F s ra L lo w t) {i : Nat}
    (hi : i < MAX_N) {a : Addr} (ha : a = aParked s + BitVec.ofNat 64 (8 * i)) (v : Word)
    (hm : P.dmem = t.dmem.storeInt a 8 v.toInt) (hsp : P.regs.rsp = t.regs.rsp)
    (hsv : Saved t P := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) :
    Mid S g F s ra { L with parked := L.parked.set i v hi } lo w P := by
  refine h.step ?_ hsp hsv
  rw [hm, ha]
  exact arr_store L.parked.toList h.mem (by unfold Fr Top; ecancel) (by simpa using hi) v
    (by rw [← Vector.toList_set hi]; unfold Fr Top; ecancel)

theorem Mid.rdHoles {t : MachineData} (h : Mid S g F s ra L lo w t) {i : Nat} (hi : i < MAX_N)
    {a : Addr} (ha : a = aHoles s + BitVec.ofNat 64 (8 * i)) : rd t.dmem a = L.holes[i] := by
  rw [ha]
  exact (arr_rd L.holes.toList h.mem (by unfold Fr Top; ecancel) (by simpa using hi)).trans
    (by simp)

theorem Mid.isSomeHoles {t : MachineData} (h : Mid S g F s ra L lo w t) {i : Nat}
    (hi : i < MAX_N) {a : Addr} (ha : a = aHoles s + BitVec.ofNat 64 (8 * i)) :
    (t.dmem.loadInt a 8).isSome = true := by
  rw [ha]; exact arr_isSome L.holes.toList h.mem (by unfold Fr Top; ecancel) (by simpa using hi)

theorem Mid.storeHoles {t P : MachineData} (h : Mid S g F s ra L lo w t) {i : Nat}
    (hi : i < MAX_N) {a : Addr} (ha : a = aHoles s + BitVec.ofNat 64 (8 * i)) (v : Word)
    (hm : P.dmem = t.dmem.storeInt a 8 v.toInt) (hsp : P.regs.rsp = t.regs.rsp)
    (hsv : Saved t P := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) :
    Mid S g F s ra { L with holes := L.holes.set i v hi } lo w P := by
  refine h.step ?_ hsp hsv
  rw [hm, ha]
  exact arr_store L.holes.toList h.mem (by unfold Fr Top; ecancel) (by simpa using hi) v
    (by rw [← Vector.toList_set hi]; unfold Fr Top; ecancel)

theorem Mid.rdPerm {t : MachineData} (h : Mid S g F s ra L lo w t) {i : Nat} (hi : i < MAX_N)
    {a : Addr} (ha : a = aPerm s + BitVec.ofNat 64 (8 * i)) : rd t.dmem a = L.perm[i] := by
  rw [ha]
  exact (arr_rd L.perm.toList h.mem (by unfold Fr Top; ecancel) (by simpa using hi)).trans
    (by simp)

theorem Mid.isSomePerm {t : MachineData} (h : Mid S g F s ra L lo w t) {i : Nat}
    (hi : i < MAX_N) {a : Addr} (ha : a = aPerm s + BitVec.ofNat 64 (8 * i)) :
    (t.dmem.loadInt a 8).isSome = true := by
  rw [ha]; exact arr_isSome L.perm.toList h.mem (by unfold Fr Top; ecancel) (by simpa using hi)

theorem Mid.storePerm {t P : MachineData} (h : Mid S g F s ra L lo w t) {i : Nat}
    (hi : i < MAX_N) {a : Addr} (ha : a = aPerm s + BitVec.ofNat 64 (8 * i)) (v : Word)
    (hm : P.dmem = t.dmem.storeInt a 8 v.toInt) (hsp : P.regs.rsp = t.regs.rsp)
    (hsv : Saved t P := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) :
    Mid S g F s ra { L with perm := L.perm.set i v hi } lo w P := by
  refine h.step ?_ hsp hsv
  rw [hm, ha]
  exact arr_store L.perm.toList h.mem (by unfold Fr Top; ecancel) (by simpa using hi) v
    (by rw [← Vector.toList_set hi]; unfold Fr Top; ecancel)

/-! ## The planned mapping in the frame -/

section
variable {PM : Addr} {planned : Vector Word MAX_N} {F0 : MProp 64}

theorem Mid.rdPM {t : MachineData} (h : Mid S g (Planned S PM planned ∗ F0) s ra L lo w t) :
    rd t.dmem (Fld.plannedMapping S) = PM :=
  rd_of_eq (F := Stk (rsp s - 24592#64) lo w ∗ Fr s ra L (Planned S PM planned ∗ F0)) h.mem
    (by unfold Fr Top Planned; ecancel)

theorem Mid.isSomePM {t : MachineData} (h : Mid S g (Planned S PM planned ∗ F0) s ra L lo w t) :
    (t.dmem.loadInt (Fld.plannedMapping S) 8).isSome = true :=
  isSome_of_eq (F := Stk (rsp s - 24592#64) lo w ∗ Fr s ra L (Planned S PM planned ∗ F0)) PM
    h.mem (by unfold Fr Top Planned; ecancel)

theorem Mid.rdPlanned {t : MachineData} (h : Mid S g (Planned S PM planned ∗ F0) s ra L lo w t)
    {i : Nat} (hi : i < MAX_N) {a : Addr} (ha : a = PM + 8192#64 + BitVec.ofNat 64 (8 * i)) :
    rd t.dmem a = planned[i] := by
  rw [ha]
  exact (arr_rd planned.toList h.mem (by unfold Fr Top Planned; ecancel) (by simpa using hi)).trans
    (by simp)

theorem Mid.isSomePlanned {t : MachineData}
    (h : Mid S g (Planned S PM planned ∗ F0) s ra L lo w t) {i : Nat} (hi : i < MAX_N) {a : Addr}
    (ha : a = PM + 8192#64 + BitVec.ofNat 64 (8 * i)) : (t.dmem.loadInt a 8).isSome = true := by
  rw [ha]
  exact arr_isSome planned.toList h.mem (by unfold Fr Top Planned; ecancel) (by simpa using hi)

end

/-! ## The call of `permute` -/

-- `Fr` without the array `permutation`.
def FrR (s : MachineData) (ra : Int64) (L : Lc) (F : MProp 64) : MProp 64 :=
  Arr (rsp s - 24592#64) L.parked.toList ∗ Arr (rsp s - 16400#64) L.holes.toList
    ∗ Wd (rsp s - 16#64) L.pad ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F

theorem mid_perm (V X : MProp 64) (s : MachineData) (ra : Int64) (L : Lc) (F : MProp 64) :
    V ∗ X ∗ Fr s ra L F = Arr (rsp s - 8208#64) L.perm.toList ∗ (V ∗ X ∗ FrR s ra L F) := by
  unfold Fr FrR Top; ac_rfl

-- The call of `permute`: it gets all 1034 free words and owns the array `permutation` at `rsi`.
-- After the call the array has new values.
theorem Mid.callW {A : G → MachineData → Prop} {Q : G → G → MachineData → MachineData → Prop}
    {c : MachineData} {K : MachineData → Prop} (h : Mid S g F s ra L lo w c)
    (hdi : rdi c = S) (hsi : rsi c = rsp s - 8208#64) (hok : g.Ok) (hA : A g c)
    (hK : ∀ t g' (L' : Lc) lo' w', Mid S g' F s ra L' lo' w' t → Q g g' c t → g'.Ok → K t) :
    ∃ S' g' F', Sep.Pre S' g' (permW c ∗ F') A 1034 c
      ∧ ∀ s', Sep.Post S' (permW c ∗ F') 1034 (fun g'' t => Q g' g'' c t) c s'
        → Sep.mod.Agree c s' → K s' := by
  have e : ∀ (X : MProp 64) (g' : G) (lo' : List Word) (w' : Word),
      View S g' ∗ Stk (rsp s - 24592#64) lo' w' ∗ (X ∗ FrR s ra L F)
        = X ∗ (View S g' ∗ Stk (rsp s - 24592#64) lo' w' ∗ FrR s ra L F) :=
    fun _ _ _ _ => by ac_rfl
  have hsp : rsp c = rsp s - 24592#64 := by
    show c.regs.get64 .rsp = _
    rw [Reg64s.get64_rsp, h.sp]
  refine ⟨S, g, FrR s ra L F, ⟨hdi, hok, ⟨lo, w, h.len, ?_⟩, hA⟩, ?_⟩
  · have hm := h.mem
    rw [mid_perm] at hm
    rw [hsp, permW, hsi, e]
    exact ExArr.intro (n := MAX_N) (by simp) hm
  · rintro s' ⟨g', fr', v', hQ, hok', hfl, hm⟩ hag
    rw [hsp, permW, hsi, e] at hm
    obtain ⟨vs, hvs, hm⟩ := ExArr.elim hm
    refine hK s' g' { L with perm := ⟨vs.toArray, by simp [hvs]⟩ } fr' v'
      ⟨hfl, ?_, ?_, h.sv.trans (Saved.of_agree hag)⟩ hQ hok'
    · rw [mid_perm]
      exact hm
    · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp]; exact h.sp

theorem Mid.callWWithExit {A : G → MachineData → Prop}
    {Q X : G → G → MachineData → MachineData → Prop}
    {c : MachineData} {K E : MachineData → Prop} (h : Mid S g F s ra L lo w c)
    (hdi : rdi c = S) (hsi : rsi c = rsp s - 8208#64) (hok : g.Ok) (hA : A g c)
    (hK : ∀ t g' (L' : Lc) lo' w', Mid S g' F s ra L' lo' w' t → Q g g' c t → g'.Ok → K t)
    (hE : ∀ t g' (L' : Lc) lo' w',
      (View S g' ∗ Stk (rsp s - 24592#64) lo' w' ∗ Fr s ra L' F).get t.dmem →
      lo'.length = 1034 → X g g' c t → g'.Ok → t.regs.get64 .rdi = 1#64 → E t) :
    ∃ S' g' F', Sep.Pre S' g' (permW c ∗ F') A 1034 c
      ∧ (∀ t, Sep.Post S' (permW c ∗ F') 1034 (fun g'' t => Q g' g'' c t) c t →
        Sep.mod.Agree c t → K t)
      ∧ (∀ t, Sep.Post S' (permW c ∗ F') 1034 (fun g'' t => X g' g'' c t) c t →
        t.regs.get64 .rdi = 1#64 → E t) := by
  have e : ∀ (X : MProp 64) (g' : G) (lo' : List Word) (w' : Word),
      View S g' ∗ Stk (rsp s - 24592#64) lo' w' ∗ (X ∗ FrR s ra L F) =
        X ∗ (View S g' ∗ Stk (rsp s - 24592#64) lo' w' ∗ FrR s ra L F) := by
    intros; ac_rfl
  have hsp : rsp c = rsp s - 24592#64 := by
    show c.regs.get64 .rsp = _
    rw [Reg64s.get64_rsp, h.sp]
  refine ⟨S, g, FrR s ra L F, ⟨hdi, hok, ⟨lo, w, h.len, ?_⟩, hA⟩, ?_, ?_⟩
  · have hm := h.mem
    rw [mid_perm] at hm
    rw [hsp, permW, hsi, e]
    exact ExArr.intro (n := MAX_N) (by simp) hm
  · rintro t ⟨g', lo', w', hQ, hok', hl, hm⟩ hag
    rw [hsp, permW, hsi, e] at hm
    obtain ⟨vs, hvs, hm⟩ := ExArr.elim hm
    refine hK t g' { L with perm := ⟨vs.toArray, by simp [hvs]⟩ } lo' w'
      ⟨hl, ?_, ?_, h.sv.trans (Saved.of_agree hag)⟩ hQ hok'
    · rw [mid_perm]; exact hm
    · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp]; exact h.sp
  · rintro t ⟨g', lo', w', hX, hok', hl, hm⟩ harg
    rw [hsp, permW, hsi, e] at hm
    obtain ⟨vs, hvs, hm⟩ := ExArr.elim hm
    refine hE t g' { L with perm := ⟨vs.toArray, by simp [hvs]⟩ } lo' w'
      ?_ hl hX hok' harg
    rw [mid_perm]; exact hm

end

end Lowest
end Bbu.Unit
