module

public import BbuKraken.Unit.Plan.PlannerRunBuilderCall
import all BbuKraken.Unit.Plan.PlannerRunBuilderCall
public import Init.Data.Fin.Lemmas
import all Init.Data.Fin.Lemmas

@[expose] public section

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

def BuilderLocals.ofList (locals : List Word) (hl : locals.length = 4121) : BuilderLocals where
  head := ⟨(locals.take 4).toArray, by simp [hl]⟩
  stratPad := (locals[9]'(by omega)).extractLsb' 8 56
  sawPad := (locals[11]'(by omega)).extractLsb' 8 56
  tail := ⟨(locals.drop 2060).toArray, by simp [hl]⟩

private theorem pack_low (w : Word) : w.extractLsb' 8 56 ++ w.setWidth 8 = w := by
  bv_decide

theorem BuilderLocals.ofList_toList (locals : List Word) (hl : locals.length = 4121)
    (b : BG)
    (hsrc : locals[4]? = some b.src) (hm : locals[5]? = some b.m)
    (htgt : locals[6]? = some b.tgt) (hn : locals[7]? = some b.n)
    (hdrp : locals[8]? = some b.drp)
    (hstrat : (locals[9]'(by omega)).setWidth 8 = b.strat)
    (hmp : locals[10]? = some b.mp)
    (hsaw : (locals[11]'(by omega)).setWidth 8 = b.saw)
    (hmap : b.M = localMapping locals hl) :
    (BuilderLocals.ofList locals hl).toList b = locals := by
  have field_eq (i : Nat) (hi : i < locals.length) (v : Word)
      (h : locals[i]? = some v) : locals[i] = v := by
    rw [List.getElem?_eq_getElem hi] at h
    exact Option.some.inj h
  have hsrc' := field_eq 4 (by omega) b.src hsrc
  have hm' := field_eq 5 (by omega) b.m hm
  have htgt' := field_eq 6 (by omega) b.tgt htgt
  have hn' := field_eq 7 (by omega) b.n hn
  have hdrp' := field_eq 8 (by omega) b.drp hdrp
  have hmp' := field_eq 10 (by omega) b.mp hmp
  have hfields : locals.take 12 = locals.take 4 ++
      [b.src, b.m, b.tgt, b.n, b.drp,
        (locals[9]'(by omega)).extractLsb' 8 56 ++ b.strat,
        b.mp, (locals[11]'(by omega)).extractLsb' 8 56 ++ b.saw] := by
    rw [← hstrat, ← hsaw, pack_low, pack_low]
    apply List.ext_getElem?
    intro i
    by_cases hi : i < 4
    · simp [hl, hi, show i < 12 by omega]
    · by_cases hi12 : i < 12
      · have he : i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 := by omega
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp [hl,
          hsrc', hm', htgt', hn', hdrp', hmp']
      · simp [hl, hi12]
  rw [BuilderLocals.toList, BuilderLocals.ofList]
  simp only [Vector.toList_mk]
  rw [hmap]
  simp only [localMapping]
  rw [← hfields]
  exact (local_partition locals).symm

theorem localMapping_set_head (locals : List Word) (hl : locals.length = 4121)
    (i : Nat) (hi : i < 12) (w : Word) :
    localMapping (locals.set i w) (by simpa using hl) = localMapping locals hl := by
  simp only [localMapping, List.drop_set_of_lt hi,
    List.drop_set_of_lt (by omega : i < 1036)]

inductive BuilderWrite where
  | word (i : Fin 4121) (v : Word)
  | byte (i : Fin 4121) (v : BitVec 8)

def BuilderWrite.locals (locals : List Word) : BuilderWrite → List Word
  | .word i v => locals.set i.val v
  | .byte i v => locals.set i.val ((locals[i.val]?.getD 0#64).extractLsb' 8 56 ++ v)

def BuilderWrite.mem (m : Mem 64) (sp : Addr) : BuilderWrite → Mem 64
  | .word i v => m.storeInt (sp + BitVec.ofNat 64 (8 * i.val)) 8 v.toInt
  | .byte i v => m.storeInt (sp + BitVec.ofNat 64 (8 * i.val)) 1 v.toInt

def builderStores (g : PlannerRunG) (sp : Addr) (strat : BitVec 8) : List BuilderWrite :=
  [.word ⟨4, by decide⟩ g.p.src, .word ⟨5, by decide⟩ g.p.m,
    .word ⟨6, by decide⟩ g.p.tgt, .word ⟨7, by decide⟩ g.p.n,
    .word ⟨8, by decide⟩ g.p.drp, .byte ⟨9, by decide⟩ strat,
    .word ⟨10, by decide⟩ (sp + 96#64), .byte ⟨11, by decide⟩ 0#8]

def builderSetLocals (locals : List Word) (ws : List BuilderWrite) : List Word :=
  ws.foldl BuilderWrite.locals locals

def builderStoreMem (m : Mem 64) (sp : Addr) (ws : List BuilderWrite) : Mem 64 :=
  ws.foldl (fun m w => w.mem m sp) m

theorem Bd.builderStores {P : Addr} {g : PlannerRunG} {F : MProp 64}
    {s t : MachineData} {ra : Int64} {lo locals : List Word}
    (h : Bd P g F s ra lo locals t) (ws : List BuilderWrite) :
    Bd P g F s ra lo (builderSetLocals locals ws)
      {t with dmem := builderStoreMem t.dmem t.regs.rsp.toBitVec ws} := by
  induction ws generalizing locals t with
  | nil => exact h.next rfl rfl
  | cons w ws ih =>
    have h1 : Bd P g F s ra lo (w.locals locals)
        {t with dmem := w.mem t.dmem t.regs.rsp.toBitVec} := by
      cases w with
      | word i v => exact h.storeLocal i.isLt v rfl rfl
      | byte i v =>
        have hi : i.val < locals.length := by rw [h.localLength]; exact i.isLt
        have hs := h.storeLocalLowByte i.isLt v.toInt
          (u := {t with dmem := (BuilderWrite.byte i v).mem t.dmem t.regs.rsp.toBitVec}) rfl rfl
        simpa only [BuilderWrite.locals, List.getElem?_eq_getElem hi,
          Option.getD_some, BitVec.ofInt_toInt] using hs
    exact ih h1

theorem Bd.localByteSome {P : Addr} {g : PlannerRunG} {F : MProp 64}
    {s t : MachineData} {ra : Int64} {lo locals : List Word}
    (h : Bd P g F s ra lo locals t) (i : Nat) (hi : i < 4121) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i)) 1).isSome = true := by
  obtain ⟨R, e⟩ := h.localFocus
  have hi' : i < locals.length := by rw [h.localLength]; exact hi
  obtain ⟨Q, he, _⟩ := ResolveU.Arr_focus_set t.regs.rsp.toBitVec locals hi'
  have hm := e locals h.localLength ▸ h.kb.mem
  rw [he, MProp.sep_assoc] at hm
  simpa only [BitVec.add_zero] using Wd.isSome_byte hm (j := 0) (by decide)

theorem InitLI.builderSome {P : Addr} {g : PlannerRunG} {F : MProp 64}
    {s t : MachineData} {ra : Int64} {lo locals : List Word}
    (h : InitLI P g F s ra lo locals t) (j : Nat) (hj : j < 8) :
    let m := builderStoreMem t.dmem t.regs.rsp.toBitVec
      ((builderStores g t.regs.rsp.toBitVec (s.regs.rsi.toBitVec.setWidth 8)).take j)
    (m.loadInt (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * (4 + j)))
      (if j = 5 ∨ j = 7 then 1 else 8)).isSome = true := by
  have hb := h.toBd.builderStores
    ((builderStores g t.regs.rsp.toBitVec (s.regs.rsi.toBitVec.setWidth 8)).take j)
  dsimp only
  split
  · exact hb.localByteSome (4 + j) (by omega)
  · exact hb.localSome (i := 4 + j) (by omega)

private theorem pack_byte (w : Word) (v : BitVec 8) :
    (w.extractLsb' 8 56 ++ v).setWidth 8 = v := by bv_decide

theorem builderSetLocals_layout (g : PlannerRunG) (sp : Addr) (strat : BitVec 8)
    (locals : List Word) (hl : locals.length = 4121) :
    let out := builderSetLocals locals (builderStores g sp strat)
    ∃ (l : BuilderLocals), out = l.toList
      (builderGhost g (sp + 96#64) strat 0#8 (localMapping locals hl)) := by
  let out := builderSetLocals locals (builderStores g sp strat)
  have hout : out.length = 4121 := by
    simp [out, builderSetLocals, builderStores, BuilderWrite.locals, hl]
  refine ⟨BuilderLocals.ofList out hout, Eq.symm ?_⟩
  apply BuilderLocals.ofList_toList
  · dsimp only [out, builderSetLocals, builderStores, BuilderWrite.locals, List.foldl_cons,
      List.foldl_nil, builderGhost]
    simp [hl]
  · dsimp only [out, builderSetLocals, builderStores, BuilderWrite.locals, List.foldl_cons,
      List.foldl_nil, builderGhost]
    simp [hl]
  · dsimp only [out, builderSetLocals, builderStores, BuilderWrite.locals, List.foldl_cons,
      List.foldl_nil, builderGhost]
    simp [hl]
  · dsimp only [out, builderSetLocals, builderStores, BuilderWrite.locals, List.foldl_cons,
      List.foldl_nil, builderGhost]
    simp [hl]
  · dsimp only [out, builderSetLocals, builderStores, BuilderWrite.locals, List.foldl_cons,
      List.foldl_nil, builderGhost]
    simp [hl]
  · dsimp only [out, builderSetLocals, builderStores, BuilderWrite.locals, List.foldl_cons,
      List.foldl_nil, builderGhost]
    simp [hl, pack_byte]
  · dsimp only [out, builderSetLocals, builderStores, BuilderWrite.locals, List.foldl_cons,
      List.foldl_nil, builderGhost]
    simp [hl]
  · dsimp only [out, builderSetLocals, builderStores, BuilderWrite.locals, List.foldl_cons,
      List.foldl_nil, builderGhost]
    simp [hl, pack_byte]
  · dsimp only [builderGhost]
    symm
    simp only [out, builderSetLocals, builderStores, List.foldl_cons, List.foldl_nil,
      BuilderWrite.locals]
    repeat rw [localMapping_set_head _ _ _ (by decide)]
    all_goals simp only [List.length_set, hl]

end Bbu.Unit.PlannerRunU
