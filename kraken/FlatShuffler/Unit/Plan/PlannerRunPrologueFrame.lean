module

public import FlatShuffler.Unit.Plan.PlannerRunStore
import all FlatShuffler.Unit.Plan.PlannerRunStore

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep

def pushWords (s : MachineData) : List Word :=
  [s.regs.r15.toBitVec, s.regs.r14.toBitVec, s.regs.r13.toBitVec,
    s.regs.r12.toBitVec, s.regs.rbp.toBitVec, s.regs.rbx.toBitVec]

private theorem split_locals (xs : List Word) (hl : xs.length = 8240) :
    xs.take (xs.length - 6) = xs.take 4113 ++ (xs.drop 4113).take 4121 := by
  have ht : (xs.take 4113).length = 4113 := by simp [hl]
  calc
    xs.take (xs.length - 6) = (xs.take 4113 ++ xs.drop 4113).take 8234 := by
      rw [List.take_append_drop, hl]
    _ = xs.take 4113 ++ (xs.drop 4113).take 4121 := by
      rw [List.take_append, ht]
      simp only [List.take_take, Nat.reduceSub]
      rw [show min 8234 4113 = 4113 by decide]

theorem prologue_raw {P : Addr} {g : PlannerCallMemory} {F : MProp 64}
    {s t : MachineData} {ra : Int64} {xs : List Word}
    (h : Kg (plannerCallOwnedMemory P g ∗ F) s ra xs (s.pushRa ra)) (hl : xs.length = plannerRunD)
    (hm : t.dmem = pushes (s.pushRa ra).dmem (s.pushRa ra).regs.rsp.toBitVec (pushWords s))
    (hsp : t.regs.rsp.toBitVec = rsp s - 8#64 - 33016#64) :
    ∃ lo locals, Bd P g F s ra lo locals t := by
  let lo := xs.take 4113
  let loc := (xs.drop 4113).take 4121
  have hlo : lo.length = 4113 := by simp [lo, hl, plannerRunD]
  have hloc : loc.length = 4121 := by simp [loc, hl, plannerRunD]
  obtain ⟨_, hv⟩ := h.pushes (xs := pushWords s) (by simp [pushWords, hl, plannerRunD])
  have he : xs.take (xs.length - (pushWords s).length) ++ (pushWords s).reverse =
      fr s lo loc := by
    simp only [pushWords, List.length_cons, List.length_nil]
    rw [split_locals xs (by simpa only [plannerRunD] using hl)]
    simp only [fr, List.append_assoc]
    rfl
  rw [he] at hv
  exact ⟨lo, loc, ⟨⟨hm ▸ hv, hsp⟩, hlo, hloc⟩⟩

theorem prologue_frame {P : Addr} {g : PlannerCallMemory} {F : MProp 64}
    {s t : MachineData} {ra : Int64} {xs : List Word}
    (h : Kg (plannerCallOwnedMemory P g ∗ F) s ra xs (s.pushRa ra)) (hl : xs.length = plannerRunD)
    (hm : t.dmem = ((pushes (s.pushRa ra).dmem (s.pushRa ra).regs.rsp.toBitVec
      (pushWords s)).storeInt (t.regs.rsp.toBitVec + 16#64) 8 g.sourcesPtr.toInt).storeInt
        (P + 56#64) 1 0)
    (hsp : t.regs.rsp.toBitVec = rsp s - 8#64 - 33016#64) :
    ∃ lo locals, Bd P (withSaw g 0#8) F s ra lo locals t ∧
      locals[2]? = some g.sourcesPtr := by
  let lo := xs.take 4113
  let loc := (xs.drop 4113).take 4121
  have hlo : lo.length = 4113 := by simp [lo, hl, plannerRunD]
  have hloc : loc.length = 4121 := by simp [loc, hl, plannerRunD]
  let mem0 := pushes (s.pushRa ra).dmem (s.pushRa ra).regs.rsp.toBitVec (pushWords s)
  let u : MachineData := { t with dmem := mem0 }
  let v : MachineData := { t with dmem := (mem0.storeInt
    (t.regs.rsp.toBitVec + 16#64) 8 g.sourcesPtr.toInt) }
  obtain ⟨_, hv⟩ := h.pushes (xs := pushWords s) (by simp [pushWords, hl, plannerRunD])
  have he : xs.take (xs.length - (pushWords s).length) ++ (pushWords s).reverse =
      fr s lo loc := by
    simp only [pushWords, List.length_cons, List.length_nil]
    rw [split_locals xs (by simpa only [plannerRunD] using hl)]
    simp only [fr, List.append_assoc]
    rfl
  rw [he] at hv
  have hb : Bd P g F s ra lo loc u := ⟨⟨hv, hsp⟩, hlo, hloc⟩
  have hs : Bd P g F s ra lo (loc.set 2 g.sourcesPtr) v :=
    hb.storeLocal (i := 2) (by decide) g.sourcesPtr rfl rfl
  refine ⟨lo, loc.set 2 g.sourcesPtr, hs.storeSaw 0 hm rfl, ?_⟩
  exact List.getElem?_set_self (by rw [hloc]; decide)

end FlatShuffler.Unit.PlannerRunU
