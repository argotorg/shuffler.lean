module

public import FlatShuffler.Unit.Plan.ResolveCall
import all FlatShuffler.Unit.Plan.ResolveCall
public import FlatShuffler.Unit.Plan.ResolveWorkModel
import all FlatShuffler.Unit.Plan.ResolveWorkModel

@[expose] public section

namespace FlatShuffler.Unit.ResolveU
open FlatShuffler.Sep

section
variable {P : Addr} {r : RG} {F : MProp 64} {s t : MachineData} {ra : Int64}
  {lo : List Word} {L : Lc} {K E : MachineData → Prop}

-- An add uses two of the words that are reserved for classify.
theorem split17_add (lo : List Word) (hl : lo.length = 17) :
    ∃ xs a b w, lo = xs ++ [a, b, w] ∧ xs.length = 14 := by
  have hd : (lo.drop 14).length = 3 := by simp [hl]
  match he : lo.drop 14, hd with
  | [a, b, w], _ =>
    exact ⟨lo.take 14, a, b, w, by rw [← he, List.take_append_drop], by simp [hl]⟩

theorem Bd.callAdd (hb : Bd P r F s ra lo L.toList t) (hok : r.Ok)
    (hdi : rdi t = P + 32#64) {off : Word}
    (ho : off.toNat < r.p.sourceSize.toNat)
    (hsi : StackSlot.ofWord (rsi t) = Flat.get r.p.fl.source off)
    (hK : ∀ (u : MachineData) (lo' : List Word),
      Bd P { r with spills := (Flat.spillAdd r.spills (Flat.get r.p.fl.source off)).2 }
        F s ra lo' L.toList u →
      al u = FlatShuffler.Unit.code (Flat.spillAdd r.spills (Flat.get r.p.fl.source off)).1 →
      Sep.mod.Agree t u → K u)
    (hX : ∀ (u : MachineData) (lo' : List Word), lo'.length = 17 →
      (Stk (rsp s) (fr s lo' L.toList) ra.toBitVec ∗ RView P r ∗ F).get u.dmem →
      Flat.spillAdd r.spills (Flat.get r.p.fl.source off) = (.assertionFailed, r.spills) →
      u.regs.get64 .rdi = 1#64 → E u) :
    ∃ S a CF, VPre AddView AddG.Ok S a CF addA 2 t ∧
      (∀ u, VPost AddView AddG.Ok S CF 2 (fun a' u => addQ a a' t u) t u →
        Sep.mod.Agree t u → K u) ∧
      (∀ u, VPost AddView AddG.Ok S CF 2 (fun a' u => addX a a' t u) t u →
        u.regs.get64 .rdi = 1#64 → E u) := by
  obtain ⟨xs, a0, b0, w, he, hxs⟩ := split17_add lo hb.free
  obtain ⟨rest, hr⟩ := add_split P r
  let a : AddG := ⟨r.p.spl, r.spillCount, r.spills⟩
  have hconv : ∀ f : BitVec 32 → BitVec 8,
      RView P { r with spills := f } ∗ F =
        AddView (P + 32#64) { a with spills := f } ∗ (rest ∗ F) := by
    intro f
    rw [hr]
    simp only [AddView, a, MProp.sep_assoc]
  have hkb : Kb (AddView (P + 32#64) a ∗ (rest ∗ F)) s ra
      (xs ++ [a0, b0] ++ w :: (L.toList ++ saved s)) 9320#64 t := by
    have hm := hb.kb.mem
    change (Stk (rsp s) (lo ++ (L.toList ++ saved s)) ra.toBitVec ∗
      (RView P { r with spills := r.spills } ∗ F)).get t.dmem at hm
    rw [hconv, he] at hm
    exact ⟨by simpa only [a, List.append_assoc, List.cons_append, List.nil_append] using hm,
      hb.kb.sp⟩
  refine hkb.vcallWithExit_above hb.hi_len rfl hdi hok.spillCount ?_ ?_ ?_
  · intro hv
    change (StackSlot.ofWord (rsi t)).payload.toNat < r.spillCount
    rw [hsi] at hv ⊢
    exact source_id_lt hok ho hv
  · intro u a' free v hbu hfree hq hagood hag
    obtain ⟨hal, ha'⟩ := hq
    subst a'
    rw [hsi] at hal hbu
    apply hK u (xs ++ free ++ [v])
    · refine ⟨⟨?_, hbu.sp⟩, by simp [hxs, hfree], L.length⟩
      have hm := hbu.mem
      rw [← hconv] at hm
      simpa only [fr, List.append_assoc, List.singleton_append] using hm
    · exact hal
    · exact hag
  · intro u a' free v hm hfree hq hagood harg
    obtain ⟨ha', hf⟩ := hq
    subst a'
    rw [hsi] at hf
    apply hX u (xs ++ free ++ [v]) (by simp [hxs, hfree]) ?_ hf harg
    change (Stk (rsp s) (xs ++ free ++ v :: (L.toList ++ saved s)) ra.toBitVec ∗
      (AddView (P + 32#64) { a with spills := r.spills } ∗ (rest ∗ F))).get u.dmem at hm
    rw [← hconv] at hm
    simpa only [fr, List.append_assoc, List.singleton_append, MProp.sep_assoc] using hm

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
  {lo : List Word} {L : Lc} {w : Work} {K E : MachineData → Prop} {off : Word}

theorem Core.callAdd (h : Core P r F s ra w lo L t) (hok : r.Ok)
    (hmem : c.dmem = t.dmem) (hsp : c.regs.rsp = t.regs.rsp)
    (h12 : c.regs.r12 = t.regs.r12) (h14 : c.regs.r14 = t.regs.r14)
    (h13 : c.regs.r13 = t.regs.r13) (h15 : c.regs.r15 = t.regs.r15)
    (hdi : rdi c = P + 32#64) (ho : off.toNat < r.p.sourceSize.toNat)
    (hsi : StackSlot.ofWord (rsi c) = Flat.get r.p.fl.source off)
    (hK : ∀ u lo',
      Core P r F s ra { w with spills :=
        (Flat.spillAdd w.spills (Flat.get r.p.fl.source off)).2 } lo' L u →
      al u = FlatShuffler.Unit.code (Flat.spillAdd w.spills (Flat.get r.p.fl.source off)).1 →
      u.regs.r15.toBitVec = t.regs.r15.toBitVec → K u)
    (hX : ∀ u lo', lo'.length = 17 →
      (Stk (rsp s) (fr s lo' L.toList) ra.toBitVec ∗ RView P (w.ghost r) ∗ F).get u.dmem →
      Flat.spillAdd w.spills (Flat.get r.p.fl.source off) = (.assertionFailed, w.spills) →
      u.regs.get64 .rdi = 1#64 → E u) :
    ∃ S a CF, VPre AddView AddG.Ok S a CF addA 2 c ∧
      (∀ u, VPost AddView AddG.Ok S CF 2 (fun a' u => addQ a a' c u) c u →
        Sep.mod.Agree c u → K u) ∧
      (∀ u, VPost AddView AddG.Ok S CF 2 (fun a' u => addX a a' c u) c u →
        u.regs.get64 .rdi = 1#64 → E u) := by
  have hc := h.next hmem hsp h12 h14 h13
  refine hc.bd.callAdd (update_ok hok _ _) hdi ho hsi ?_ hX
  intro u lo' hb hal hag
  apply hK u lo' (hc.afterAdd _ hb hag) hal
  rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r15, h15]

end
end FlatShuffler.Unit.ResolveU
