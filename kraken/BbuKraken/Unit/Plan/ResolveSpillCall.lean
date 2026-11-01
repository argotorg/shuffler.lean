module

public import BbuKraken.Unit.Plan.ResolveCall
import all BbuKraken.Unit.Plan.ResolveCall
public import BbuKraken.Unit.Plan.ResolveWorkModel
import all BbuKraken.Unit.Plan.ResolveWorkModel

@[expose] public section

namespace Bbu.Unit.ResolveU
open Bbu.Sep

section
variable {P : Addr} {r : RG} {F : MProp 64} {s t : MachineData} {ra : Int64}
  {lo : List Word} {L : Lc} {K : MachineData → Prop}

theorem Bd.callAdd (hb : Bd P r F s ra lo L.toList t) (hok : r.Ok)
    (hdi : rdi t = P + 32#64) {off : Word}
    (ho : off.toNat < r.p.m.toNat)
    (hsi : StackSlot.ofWord (rsi t) = Flat.get r.p.fl.source off)
    (hK : ∀ (u : MachineData) (lo' : List Word),
      Bd P { r with spills := (Flat.spillAdd r.spills (Flat.get r.p.fl.source off)).2 }
        F s ra lo' L.toList u →
      al u = Bbu.Unit.code (Flat.spillAdd r.spills (Flat.get r.p.fl.source off)).1 →
      Sep.mod.Agree t u → K u) :
    ∃ S a CF, VPre AddView AddG.Ok S a CF addA 0 t ∧
      ∀ u, VPost AddView AddG.Ok S CF 0 (fun a' u => addQ a a' t u) t u →
        Sep.mod.Agree t u → K u := by
  obtain ⟨xs, w, he, hxs⟩ := split17 lo hb.free
  obtain ⟨rest, hr⟩ := add_split P r
  let a : AddG := ⟨r.p.spl, r.spillCount, r.spills⟩
  have hconv : ∀ f : BitVec 32 → BitVec 8,
      RView P { r with spills := f } ∗ F =
        AddView (P + 32#64) { a with spills := f } ∗ (rest ∗ F) := by
    intro f
    rw [hr]
    simp only [AddView, a, MProp.sep_assoc]
  have hkb : Kb (AddView (P + 32#64) a ∗ (rest ∗ F)) s ra
      (xs ++ [] ++ w :: (L.toList ++ saved s)) 9320#64 t := by
    have hm := hb.kb.mem
    change (Stk (rsp s) (lo ++ (L.toList ++ saved s)) ra.toBitVec ∗ (RView P r ∗ F)).get t.dmem at hm
    rw [he, List.append_assoc, List.singleton_append] at hm
    change (Stk (rsp s) (xs ++ w :: (L.toList ++ saved s)) ra.toBitVec ∗
      (RView P { r with spills := r.spills } ∗ F)).get t.dmem at hm
    rw [hconv] at hm
    exact ⟨by simpa only [List.append_nil, a] using hm, hb.kb.sp⟩
  refine hkb.vcall_above hb.hi_len rfl hdi hok.spillCount ?_ ?_
  · intro hv
    change (StackSlot.ofWord (rsi t)).payload.toNat < r.spillCount
    rw [hsi] at hv ⊢
    exact source_id_lt hok ho hv
  · intro u a' free v hbu hfree hq hagood hag
    obtain rfl : free = [] := List.eq_nil_of_length_eq_zero hfree
    obtain ⟨hal, ha'⟩ := hq
    subst a'
    rw [hsi] at hal hbu
    apply hK u (xs ++ [v])
    · refine ⟨⟨?_, hbu.sp⟩, by simp [hxs], L.length⟩
      have hm := hbu.mem
      rw [← hconv] at hm
      simpa only [fr, List.append_assoc, List.nil_append, List.singleton_append] using hm
    · exact hal
    · exact hag

end

section
variable {P : Addr} {r : RG} {F : MProp 64} {s t u : MachineData} {ra : Int64}
  {lo lo' : List Word} {L : Lc} {w : Work}

theorem Core.afterAdd (h : Core P r F s ra w lo L t)
    (sp : BitVec 32 → BitVec 8)
    (hb : Bd P ({ w with spills := sp }.ghost r) F s ra lo' L.toList u)
    (hag : Sep.mod.Agree t u) :
    Core P r F s ra { w with spills := sp } lo' L u := by
  have hsp := mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp
  have h12 := mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r12
  have h14 := mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r14
  have h13 := mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r13
  refine ⟨hb, h.candidates, h.droppedNow, h.count, h.pass, h.excess,
    ⟨h.ok.count, h.ok.pass, h.ok.bounded, h.ok.live⟩,
    h12 ▸ h.r12, h14 ▸ h.r14, ?_⟩
  rw [h13, hsp]
  exact h.r13

end

section
variable {P : Addr} {r : RG} {F : MProp 64} {s t c : MachineData} {ra : Int64}
  {lo : List Word} {L : Lc} {w : Work} {K : MachineData → Prop} {off : Word}

theorem Core.callAdd (h : Core P r F s ra w lo L t) (hok : r.Ok)
    (hmem : c.dmem = t.dmem) (hsp : c.regs.rsp = t.regs.rsp)
    (h12 : c.regs.r12 = t.regs.r12) (h14 : c.regs.r14 = t.regs.r14)
    (h13 : c.regs.r13 = t.regs.r13) (h15 : c.regs.r15 = t.regs.r15)
    (hdi : rdi c = P + 32#64) (ho : off.toNat < r.p.m.toNat)
    (hsi : StackSlot.ofWord (rsi c) = Flat.get r.p.fl.source off)
    (hK : ∀ u lo',
      Core P r F s ra { w with spills :=
        (Flat.spillAdd w.spills (Flat.get r.p.fl.source off)).2 } lo' L u →
      al u = Bbu.Unit.code (Flat.spillAdd w.spills (Flat.get r.p.fl.source off)).1 →
      u.regs.r15.toBitVec = t.regs.r15.toBitVec → K u) :
    ∃ S a CF, VPre AddView AddG.Ok S a CF addA 0 c ∧
      ∀ u, VPost AddView AddG.Ok S CF 0 (fun a' u => addQ a a' c u) c u →
        Sep.mod.Agree c u → K u := by
  have hc := h.next hmem hsp h12 h14 h13
  refine hc.bd.callAdd (update_ok hok _ _) hdi ho hsi ?_
  intro u lo' hb hal hag
  apply hK u lo' (hc.afterAdd _ hb hag) hal
  rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r15, h15]

end
end Bbu.Unit.ResolveU
