module

public import FlatShuffler.Unit.Plan.ResolveDropDefs
import all FlatShuffler.Unit.Plan.ResolveDropDefs
public import FlatShuffler.Unit.Plan.ResolveClassByte
import all FlatShuffler.Unit.Plan.ResolveClassByte

@[expose] public section

namespace FlatShuffler.Unit.ResolveU
open FlatShuffler.Sep

section
variable {P : Addr} {r : RG} {F : MProp 64} {s t u : MachineData} {ra : Int64}
  {lo : List Word} {L : Lc} {best : Word}

theorem Bd.dropLocal (h : Bd P r F s ra lo L.toList t)
    (ho : best.toNat < maxStackSize)
    (hmem : u.dmem = t.dmem.storeInt (t.regs.rsp.toBitVec + 8240#64 + best) 1 1)
    (hsp : u.regs.rsp = t.regs.rsp) :
    ∃ v : Word,
      Bd P r F s ra lo { L with droppedWords := (L.droppedWords.set (best.toNat / 8) v
        (by have hh : best.toNat < 1024 := ho; omega)) }.toList u ∧
      ({ L with droppedWords := (L.droppedWords.set (best.toNat / 8) v
        (by have hh : best.toNat < 1024 := ho; omega)) } : Lc).droppedNow =
        Flat.put L.droppedNow best 1 := by
  obtain ⟨v, hv⟩ := h.storeDroppedNow ho 1 hmem hsp
  have hi : best.toNat / 8 < 128 := by have hh : best.toNat < 1024 := ho; omega
  rw [Lc.set_droppedWord _ _ hi] at hv
  refine ⟨v, hv, ?_⟩
  apply Vector.ext
  intro j hj
  have hjo : (BitVec.ofNat 64 j).toNat = j := by
    have hh : j < 1024 := hj
    simp only [BitVec.toNat_ofNat]
    omega
  have hj' : (BitVec.ofNat 64 j).toNat < maxStackSize := by rw [hjo]; exact hj
  have hu := hv.droppedRead hj'
  have ht := h.droppedRead hj'
  rw [hmem, hsp] at hu
  have hg : Flat.get
      ({ L with droppedWords := L.droppedWords.set (best.toNat / 8) v hi } : Lc).droppedNow
      (BitVec.ofNat 64 j) = Flat.get (Flat.put L.droppedNow best 1) (BitVec.ofNat 64 j) := by
    rw [Flat.get_put _ _ _ ho]
    by_cases he : BitVec.ofNat 64 j = best
    · rw [ite_eq_left he, hu, he, rdb_storeByte]
      rfl
    · rw [ite_eq_right he, hu, ht]
      apply rdb_storeByte_ne
      intro ha
      apply he
      bv_omega
  simpa only [Flat.get, hjo, dite_eq_left hj] using hg

end
end FlatShuffler.Unit.ResolveU
