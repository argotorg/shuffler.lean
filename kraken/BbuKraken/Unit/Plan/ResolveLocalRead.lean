import BbuKraken.Unit.Plan.ResolveLocals
import BbuKraken.Unit.Plan.ResolveZero

namespace Bbu.Unit.ResolveU
open Bbu.Sep

theorem Lc.exists_of_length (xs : List Word) (hl : xs.length = 1159) :
    ∃ L : Lc, xs = L.toList := by
  match xs, hl with
  | x0 :: pending :: cls :: excess :: pass :: count :: xs, hl =>
    have hx : xs.length = 1153 := by simpa using hl
    let cand : Vector Word MAX_N := ⟨(xs.take 1024).toArray, by simp [hx, MAX_N]⟩
    let dn : Vector Word 128 := ⟨((xs.drop 1024).take 128).toArray, by simp [hx]⟩
    have hd : (xs.drop 1152).length = 1 := by simp [hx]
    match he : xs.drop 1152, hd with
    | [pad], _ =>
      refine ⟨⟨x0, pending, cls, excess, pass, count, cand, dn, pad⟩, ?_⟩
      simp only [Lc.toList, List.append_assoc, List.cons_append, List.nil_append]
      congr 6
      change xs = xs.take 1024 ++ ((xs.drop 1024).take 128 ++ [pad])
      rw [← he, show xs.drop 1152 = (xs.drop 1024).drop 128 by rw [List.drop_drop],
        List.take_append_drop, List.take_append_drop]

theorem Lc.dropped_frame (sp : Addr) (L : Lc) (sv : List Word) :
    Arr sp (L.toList ++ sv) =
      Arr sp ([L.x0, L.pending, L.classWord, L.excess, L.pass, L.count] ++
        L.candidates.toList) ∗ Bs (sp + 8240#64) L.droppedNow.toList ∗
        Arr (sp + 9264#64) (L.padding :: sv) := by
  have hp : ([L.x0, L.pending, L.classWord, L.excess, L.pass, L.count] ++
      L.candidates.toList).length = 1030 := by
    simp only [List.length_append, Vector.length_toList, List.length_cons, List.length_nil]
    rfl
  have he : L.toList ++ sv =
      ([L.x0, L.pending, L.classWord, L.excess, L.pass, L.count] ++ L.candidates.toList) ++
        (L.droppedWords.toList ++ (L.padding :: sv)) := by
    simp only [Lc.toList, List.append_assoc, List.singleton_append]
  rw [he, Arr.append sp
    ([L.x0, L.pending, L.classWord, L.excess, L.pass, L.count] ++ L.candidates.toList), hp]
  simp only [Nat.reduceMul]
  rw [Arr.append (sp + 8240#64) L.droppedWords.toList]
  simp only [Vector.length_toList, Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd]
  rw [Arr_Bs (sp + 8240#64) L.droppedWords.toList]
  rfl

section
variable {P : Addr} {r : RG} {F : MProp 64} {s t : MachineData} {ra : Int64}
  {lo : List Word} {L : Lc}

theorem Bd.typedWord (h : Bd P r F s ra lo L.toList t) (i : Nat) (hi : i < 1159) :
    ∃ R, (Wd (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i))
      (L.toList.get ⟨i, by simpa using hi⟩) ∗ R).get t.dmem :=
  h.localWord i (by simpa using hi)

theorem Bd.droppedRead (h : Bd P r F s ra lo L.toList t) {o : Word}
    (ho : o.toNat < MAX_N) :
    Flat.get L.droppedNow o = rdb t.dmem (t.regs.rsp.toBitVec + 8240#64 + o) := by
  obtain ⟨R, hm⟩ := h.kb.arr_hi (lo := lo) (hi := L.toList ++ saved s) h.hi_len
  rw [Lc.dropped_frame] at hm
  have e : (Arr t.regs.rsp.toBitVec
      ([L.x0, L.pending, L.classWord, L.excess, L.pass, L.count] ++ L.candidates.toList) ∗
      Bs (t.regs.rsp.toBitVec + 8240#64) L.droppedNow.toList ∗
      Arr (t.regs.rsp.toBitVec + 9264#64) (L.padding :: saved s)) ∗ R =
      Bs (t.regs.rsp.toBitVec + 8240#64) L.droppedNow.toList ∗
        (Arr t.regs.rsp.toBitVec
          ([L.x0, L.pending, L.classWord, L.excess, L.pass, L.count] ++ L.candidates.toList) ∗
          Arr (t.regs.rsp.toBitVec + 9264#64) (L.padding :: saved s) ∗ R) := by ecancel
  rw [e] at hm
  obtain ⟨Q, he, _⟩ := SpillSetProof.Bs.focus
    (t.regs.rsp.toBitVec + 8240#64) L.droppedNow.toList (i := o.toNat)
    (by rw [Vector.length_toList]; exact ho) 0#8
  rw [he, MProp.sep_assoc, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hm
  simpa only [Flat.get, dif_pos ho, Vector.getElem_toList] using (B8.rdb hm).symm

theorem Bd.droppedZero (h : Bd P r F s ra lo L.toList t)
    (hz : ZeroPrefix r.p.m t) (hm : r.p.m.toNat ≤ MAX_N) :
    ∀ o : Word, o < r.p.m → Flat.get L.droppedNow o = 0#8 := by
  intro o ho
  exact (h.droppedRead (Nat.lt_of_lt_of_le (BitVec.lt_def.mp ho) hm)).trans (hz o ho)

end
end Bbu.Unit.ResolveU
