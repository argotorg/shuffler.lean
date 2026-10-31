import BbuKraken.Unit.Plan.PlannerRunMem
import BbuKraken.Unit.Plan.IsDemanded

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

theorem target_slot {g : PlannerRunG} (hok : g.Ok) {i : Word} (hi : i < g.p.n) :
    StackSlot.ofWord g.p.tw[i.toNat]! = Flat.get g.p.fl.target i := by
  have hi' : i.toNat < g.p.tw.length := hok.planner.tw ▸ BitVec.lt_def.mp hi
  simp only [PG.fl]
  rw [get_vecL (by simpa using hi') (by simpa [hok.planner.tw] using hok.planner.n),
    List.getElem_map]
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]

theorem target_word {P : Addr} {g : PlannerRunG} {F : MProp 64} {m : Mem 64}
    (h : (PlannerRunView P g ∗ F).get m) (hok : g.Ok) {i : Word} (hi : i < g.p.n) :
    ∃ R, (Wd (slotAt g.p.tgt i.toNat) g.p.tw[i.toNat]! ∗ R).get m := by
  obtain ⟨R, hm⟩ := pv h
  obtain ⟨Q, hm⟩ := PView.arr_tgt hm
  have hi' : i.toNat < g.p.tw.length := hok.planner.tw ▸ BitVec.lt_def.mp hi
  obtain ⟨L, e⟩ := Arr.focus g.p.tgt g.p.tw hi'
  rw [e, MProp.sep_assoc] at hm
  exact ⟨_, by simpa only [slotAt, List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem hi', Option.getD_some] using hm⟩

theorem target_opcode {P : Addr} {g : PlannerRunG} {F : MProp 64} {m : Mem 64}
    (h : (PlannerRunView P g ∗ F).get m) (hok : g.Ok) {i : Word} (hi : i < g.p.n) :
    ∃ R, (B8 (slotAt g.p.tgt i.toNat + 5#64)
      (Flat.get g.p.fl.target i).valueOpcode ∗ R).get m := by
  obtain ⟨R, hm⟩ := target_word h hok hi
  obtain ⟨Q, e⟩ := Wd.focus_byte (slotAt g.p.tgt i.toNat) g.p.tw[i.toNat]!
    (j := 5) (by decide)
  rw [e, MProp.sep_assoc] at hm
  have hv : (Flat.get g.p.fl.target i).valueOpcode =
      g.p.tw[i.toNat]!.extractLsb' 40 8 := by
    rw [← target_slot hok hi]
    rfl
  exact ⟨_, hv ▸ hm⟩

theorem target_payload {P : Addr} {g : PlannerRunG} {F : MProp 64} {m : Mem 64}
    (h : (PlannerRunView P g ∗ F).get m) (hok : g.Ok) {i : Word} (hi : i < g.p.n) :
    ∃ R, (B32 (slotAt g.p.tgt i.toNat) (Flat.get g.p.fl.target i).payload ∗ R).get m := by
  obtain ⟨R, hm⟩ := target_word h hok hi
  rw [Wd.split, MProp.sep_assoc] at hm
  have hv : (Flat.get g.p.fl.target i).payload =
      g.p.tw[i.toNat]!.extractLsb' 0 32 := by
    rw [← target_slot hok hi]
    rfl
  exact ⟨_, hv ▸ hm⟩

theorem target_id_lt {g : PlannerRunG} (hok : g.Ok) {i : Word} (hi : i < g.p.n)
    (hv : Flat.isVariable (Flat.get g.p.fl.target i) = true) :
    (Flat.get g.p.fl.target i).payload.toNat < g.spillCount := by
  have hi' : i.toNat < g.p.tw.length := hok.planner.tw ▸ BitVec.lt_def.mp hi
  have hid : spillId (StackSlot.ofWord g.p.tw[i.toNat]!) =
      some (Flat.get g.p.fl.target i).payload.toNat := by
    rw [target_slot hok hi]
    simp only [Flat.isVariable, Bool.and_eq_true, Bool.not_eq_true',
      beq_iff_eq, beq_eq_false_iff_ne, isLiteralValue] at hv
    simp [spillId, hv.1, hv.2]
  apply hok.targetIds
  apply List.mem_eraseDups.mpr
  apply List.mem_filterMap.mpr
  refine ⟨_, ?_, hid⟩
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
  exact List.getElem_mem hi'

theorem target_spill {P : Addr} {g : PlannerRunG} {F : MProp 64} {m : Mem 64}
    (h : (PlannerRunView P g ∗ F).get m) (hok : g.Ok) {i : Word} (hi : i < g.p.n)
    (hv : Flat.isVariable (Flat.get g.p.fl.target i) = true) :
    ∃ R, (B8 (g.p.spl + BitVec.ofNat 64 (Flat.get g.p.fl.target i).payload.toNat)
      (g.spills (Flat.get g.p.fl.target i).payload) ∗ R).get m := by
  obtain ⟨R, e⟩ : ∃ R, PlannerRunView P g ∗ F =
      Spl g.p.spl g.spills (List.range g.spillCount) ∗ R :=
    ⟨_, by unfold PlannerRunView; ecancel⟩
  obtain ⟨Q, eq⟩ := Spl.focus g.p.spl g.spills
    (List.mem_range.mpr (target_id_lt hok hi hv))
  rw [e, eq, MProp.sep_assoc] at h
  exact ⟨_, by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h⟩

theorem spill_pointer {P : Addr} {g : PlannerRunG} {F : MProp 64} {m : Mem 64}
    (h : (PlannerRunView P g ∗ F).get m) : rd m (P + 32#64) = g.p.spl :=
  rd_of_eq h (by unfold PlannerRunView PView; ecancel)

theorem spill_pointer_some {P : Addr} {g : PlannerRunG} {F : MProp 64} {m : Mem 64}
    (h : (PlannerRunView P g ∗ F).get m) : (m.loadInt (P + 32#64) 8).isSome = true :=
  isSome_of_eq g.p.spl h (by unfold PlannerRunView PView; ecancel)

end Bbu.Unit.PlannerRunU
