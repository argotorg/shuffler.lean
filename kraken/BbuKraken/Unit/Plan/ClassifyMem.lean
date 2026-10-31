import BbuKraken.Unit.Plan.ClassifyModel
import BbuKraken.Unit.Plan.Emission

namespace Bbu.Unit
open Bbu.Sep

structure CG where
  h : HG
  spills : BitVec 32 → BitVec 8

def CG.Ok (c : CG) : Prop := c.h.Ok

def CView (P : Addr) (c : CG) : MProp 64 :=
  HView P c.h ∗ Spl c.h.p.spl c.spills (splIds c.h.p.sw)

def classifyA (c : CG) (s : MachineData) : Prop :=
  hasOtherA c.h s ∧ (Flat.get c.h.M.dest (rcx s)).toNat < c.h.p.n.toNat

def classifyQ (c c' : CG) (s t : MachineData) : Prop :=
  c' = c ∧ al t = Flat.classify c.h.p.fl c.spills c.h.M c.h.dv (rcx s)

namespace ClassifyU

theorem B32.rd {a : Addr} {v : BitVec 32} {F : MProp 64} {m : Mem 64}
    (h : (B32 a v ∗ F).get m) : BitVec.ofInt 32 (m.loadInt a 4).get! = v := by
  unfold B32 at h
  simp only [Mem.loadInt_eq_of_AtM h (Int.toBytes_length _ _) (by decide), Option.get!_some,
    BitVec.ofInt_ofBytes_toBytes 32 4 rfl]

def inp (c : CG) (s : MachineData) : Inputs :=
  inputs c.h.p.fl c.spills c.h.M c.h.dv (rcx s)

def sw (c : CG) (s : MachineData) : Word := c.h.p.sw[(rcx s).toNat]!

theorem slot_eq (c : CG) (s : MachineData) (hok : c.Ok) (ha : classifyA c s) :
    StackSlot.ofWord (sw c s) = (inp c s).slot := by
  have hi : (rcx s).toNat < c.h.p.sw.length := hok.sw ▸ ha.1.2.2
  simp only [inp, inputs, PG.fl, sw]
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
    get_vecL (by simpa using hi) (by simpa [hok.sw] using hok.m),
    List.getElem_map]

section
variable {P : Addr} {c : CG} {F : MProp 64} {m : Mem 64}

theorem CView.hv (h : (CView P c ∗ F).get m) :
    (HView P c.h ∗ (Spl c.h.p.spl c.spills (splIds c.h.p.sw) ∗ F)).get m := by
  simpa only [CView, MProp.sep_assoc] using h

theorem CView.pv (h : (CView P c ∗ F).get m) : ∃ R, (PView P c.h.p ∗ R).get m :=
  HView.pv (CView.hv h)

theorem CView.map (h : (CView P c ∗ F).get m) : ∃ R, (MapM c.h.mp c.h.M ∗ R).get m := by
  rw [CView, MProp.sep_assoc, HView.split] at h
  exact ⟨_, h⟩

theorem PView.wd_sw {p : PG} (h : (PView P p ∗ F).get m) (hok : p.Ok)
    {i : Word} (hi : i.toNat < p.m.toNat) :
    ∃ R, (Wd (slotAt p.src i.toNat) p.sw[i.toNat]! ∗ R).get m := by
  obtain ⟨R, h⟩ := PView.arr_src h
  have hi' : i.toNat < p.sw.length := hok.sw ▸ hi
  obtain ⟨Q, e⟩ := Arr.focus p.src p.sw hi'
  rw [e, MProp.sep_assoc] at h
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
  exact ⟨_, h⟩

theorem CView.spl {s : MachineData} (h : (CView P c ∗ F).get m) (hok : c.Ok)
    (ha : classifyA c s) (hv : Flat.isVariable (inp c s).slot = true) :
    ∃ R, (B8 (c.h.p.spl + BitVec.ofNat 64 (inp c s).slot.payload.toNat)
      (inp c s).spilled ∗ R).get m := by
  have hs := slot_eq c s hok ha
  have hi : (rcx s).toNat < c.h.p.sw.length := hok.sw ▸ ha.1.2.2
  have hv' : spillId (StackSlot.ofWord (sw c s)) = some (inp c s).slot.payload.toNat := by
    rw [hs]
    simp only [Flat.isVariable, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
      beq_eq_false_iff_ne, isLiteralValue] at hv
    simp [spillId, hv.1, hv.2]
  have hm : (inp c s).slot.payload.toNat ∈ splIds c.h.p.sw := by
    apply List.mem_eraseDups.mpr
    apply List.mem_filterMap.mpr
    exact ⟨sw c s, by
      simp only [sw, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact List.getElem_mem hi, hv'⟩
  obtain ⟨R, e⟩ : ∃ R, CView P c ∗ F =
      Spl c.h.p.spl c.spills (splIds c.h.p.sw) ∗ R := ⟨_, by unfold CView; ecancel⟩
  rw [e, Spl.erase _ _ hm, MProp.sep_assoc] at h
  refine ⟨Spl c.h.p.spl c.spills ((splIds c.h.p.sw).erase (inp c s).slot.payload.toNat) ∗ R, ?_⟩
  simpa only [inp, inputs, BitVec.ofNat_toNat, BitVec.setWidth_eq] using h

theorem PView.spills {p : PG} (h : (PView P p ∗ F).get m) :
    ∃ R, (Wd (P + 32#64) p.spl ∗ R).get m :=
  ⟨_, (by unfold PView; ecancel : PView P p ∗ F = Wd (P + 32#64) p.spl ∗ _) ▸ h⟩

theorem PView.allowed {p : PG} (h : (PView P p ∗ F).get m) :
    ∃ R, (B8 (P + 40#64) p.allowed ∗ R).get m :=
  ⟨_, (by unfold PView; ecancel : PView P p ∗ F = B8 (P + 40#64) p.allowed ∗ _) ▸ h⟩
end

-- The local word holds the opcode in byte 3 and the payload in bytes 4 to 7.
theorem Wd.split34 (a : Addr) (v : Word) :
    Wd a v = B32 (a + 4#64) (v.extractLsb' 32 32) ∗
      B8 (a + 3#64) (v.extractLsb' 24 8) ∗ (Int.toBytes 3 v.toInt).AtM a := by
  unfold Wd B32 B8
  rw [show Int.toBytes 8 v.toInt = Int.toBytes (3 + (1 + 4)) v.toInt from rfl,
    toBytes_add, toBytes_add, AtM_append _ _ _ (by simp [Int.toBytes_length]),
    AtM_append _ _ _ (by simp [Int.toBytes_length])]
  simp only [Int.toBytes_length, ← BitVec.toInt_sshiftRight]
  rw [toBytes_sext 1, toBytes_sext 4]
  have e1 : (v.sshiftRight 24).signExtend 8 = v.extractLsb' 24 8 := by bv_decide
  have e2 : ((v.sshiftRight 24).sshiftRight 8).signExtend 32 = v.extractLsb' 32 32 := by bv_decide
  rw [e1, e2, show a + 3#64 + 1#64 = a + 4#64 by bv_omega]
  rw [MProp.sep_comm _ ((Int.toBytes 1 _).AtM _ ∗ _), MProp.sep_assoc, sep_lc]

theorem Wd.store34 {a : Addr} {v : Word} {F : MProp 64} {m : Mem 64}
    (h : (Wd a v ∗ F).get m) (x : BitVec 32) (o : BitVec 8) :
    (Wd a (x ++ o ++ v.extractLsb' 0 24) ∗ F).get
      ((m.storeInt (a + 4#64) 4 x.toInt).storeInt (a + 3#64) 1 o.toInt) := by
  rw [Wd.split34] at h ⊢
  simp only [MProp.sep_assoc] at h ⊢
  have h1 := B32.store h x.toInt
  rw [sep_lc] at h1
  have h2 := B8.store h1 o.toInt
  simp only [BitVec.ofInt_toInt] at h2
  have e0 : Int.toBytes 3 (x ++ o ++ v.extractLsb' 0 24).toInt = Int.toBytes 3 v.toInt := by
    rw [toBytes_sext 3, toBytes_sext 3 v]
    congr 1
    bv_decide
  have e1 : (x ++ o ++ v.extractLsb' 0 24).extractLsb' 32 32 = x := by bv_decide
  have e2 : (x ++ o ++ v.extractLsb' 0 24).extractLsb' 24 8 = o := by bv_decide
  rw [e0, e1, e2, sep_lc]
  exact h2

end ClassifyU
end Bbu.Unit
