module

public import BbuKraken.Unit.Plan.ResolveLocalRead
import all BbuKraken.Unit.Plan.ResolveLocalRead

@[expose] public section

namespace Bbu.Unit.ResolveU
open Bbu.Sep

def pushWords (s : MachineData) : List Word :=
  [s.regs.r15.toBitVec, s.regs.r14.toBitVec, s.regs.r13.toBitVec,
    s.regs.r12.toBitVec, s.regs.rbp.toBitVec, s.regs.rbx.toBitVec]

def InitPayload (s : MachineData) (_ : List Word) (loc : List Word) : Prop :=
  ∃ L : Lc, loc = L.toList ∧ L.excess = rcx s

theorem initPayload_store (s : MachineData) (lo loc : List Word) (o : Word) (w : Word)
    (ho : o.toNat < MAX_N) (h : InitPayload s lo loc) :
    InitPayload s lo (loc.set (1030 + o.toNat / 8) w) := by
  obtain ⟨L, rfl, hL⟩ := h
  have hi : o.toNat / 8 < 128 := by change o.toNat < 1024 at ho; omega
  refine ⟨{ L with droppedWords := L.droppedWords.set (o.toNat / 8) w }, ?_, hL⟩
  exact L.set_droppedWord _ hi w

private theorem split_locals (xs : List Word) (hl : xs.length = 1182) :
    xs.take (xs.length - 6) = xs.take 17 ++ (xs.drop 17).take 1159 := by
  calc
    xs.take (xs.length - 6) = (xs.take 17 ++ xs.drop 17).take 1176 := by
      rw [List.take_append_drop, hl]
    _ = xs.take 17 ++ (xs.drop 17).take 1159 := by
      rw [List.take_append, show (xs.take 17).length = 17 by simp [hl]]
      simp only [List.take_take, Nat.reduceSub]
      rw [show min 1176 17 = 17 by decide]

theorem prologue_stack {P : Addr} {r : RG} {F : MProp 64}
    {s t : MachineData} {ra : Int64} {xs : List Word}
    (h : Kg (RView P r ∗ F) s ra xs (s.pushRa ra)) (hl : xs.length = resolveD)
    (hm : t.dmem = pushes (s.pushRa ra).dmem (s.pushRa ra).regs.rsp.toBitVec (pushWords s))
    (hsp : t.regs.rsp.toBitVec = rsp s - 8#64 - 9320#64) :
    ∃ lo, ∃ L : Lc, Bd P r F s ra lo L.toList t := by
  let lo := xs.take 17
  let loc := (xs.drop 17).take 1159
  have hlo : lo.length = 17 := by simp [lo, hl, resolveD]
  have hloc : loc.length = 1159 := by simp [loc, hl, resolveD]
  obtain ⟨L, hL⟩ := Lc.exists_of_length loc hloc
  obtain ⟨_, hv⟩ := h.pushes (xs := pushWords s) (by simp [pushWords, hl, resolveD])
  have he : xs.take (xs.length - (pushWords s).length) ++ (pushWords s).reverse =
      fr s lo loc := by
    simp only [pushWords, List.length_cons, List.length_nil]
    rw [split_locals xs (by simpa only [resolveD] using hl)]
    simp only [fr, List.append_assoc]
    rfl
  rw [he, hL] at hv
  exact ⟨lo, L, ⟨⟨hm ▸ hv, hsp⟩, hlo, L.length⟩⟩

theorem prologue_frame {P : Addr} {r : RG} {F : MProp 64}
    {s t : MachineData} {ra : Int64} {xs : List Word}
    (h : Kg (RView P r ∗ F) s ra xs (s.pushRa ra)) (hl : xs.length = resolveD)
    (hm : t.dmem = (pushes (s.pushRa ra).dmem (s.pushRa ra).regs.rsp.toBitVec
      (pushWords s)).storeInt (t.regs.rsp.toBitVec + 24#64) 8 (rcx s).toInt)
    (hsp : t.regs.rsp.toBitVec = rsp s - 8#64 - 9320#64) :
    ∃ lo, ∃ L : Lc, Bd P r F s ra lo L.toList t ∧ L.excess = rcx s := by
  let lo := xs.take 17
  let loc := (xs.drop 17).take 1159
  have hlo : lo.length = 17 := by simp [lo, hl, resolveD]
  have hloc : loc.length = 1159 := by simp [loc, hl, resolveD]
  obtain ⟨L, hL⟩ := Lc.exists_of_length loc hloc
  let mem0 := pushes (s.pushRa ra).dmem (s.pushRa ra).regs.rsp.toBitVec (pushWords s)
  let u : MachineData := { t with dmem := mem0 }
  obtain ⟨_, hv⟩ := h.pushes (xs := pushWords s) (by simp [pushWords, hl, resolveD])
  have he : xs.take (xs.length - (pushWords s).length) ++ (pushWords s).reverse =
      fr s lo loc := by
    simp only [pushWords, List.length_cons, List.length_nil]
    rw [split_locals xs (by simpa only [resolveD] using hl)]
    simp only [fr, List.append_assoc]
    rfl
  rw [he, hL] at hv
  have hb : Bd P r F s ra lo L.toList u := ⟨⟨hv, hsp⟩, hlo, L.length⟩
  have hs := hb.storeLocal (u := t) (i := 3) (by simp) (rcx s) hm rfl
  rw [L.set_excess] at hs
  exact ⟨lo, { L with excess := rcx s }, hs, rfl⟩

end Bbu.Unit.ResolveU
