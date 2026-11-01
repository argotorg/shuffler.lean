module

public import BbuKraken.Unit.Plan.ResolveInitDefs
import all BbuKraken.Unit.Plan.ResolveInitDefs

@[expose] public section

namespace Bbu.Unit.ResolveU
open Bbu.Sep

theorem put_eq_set (v : Vector Word MAX_N) (i w : Word) (hi : i.toNat < MAX_N) :
    Flat.put v i w = v.set i.toNat w := by
  apply Vector.ext
  intro j hj
  simp only [Flat.put, Vector.getElem_setIfInBounds, Vector.getElem_set]

theorem candidate_append {P : Addr} {r : RG} {F : MProp 64} {s t u : MachineData}
    {ra : Int64} {lo : List Word} {L : Lc} {u0 : Flat.ResolveU} {count off : Word}
    (hc : CandidateState P r F s ra lo L u0 count t) (hn : count.toNat < MAX_N)
    (ho : off < r.p.m) (hl : Flat.get r.M.dest off ≠ Flat.NONE)
    (hm : u.dmem = t.dmem.storeInt
      (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * (6 + count.toNat))) 8 off.toInt)
    (hsp : u.regs.rsp = t.regs.rsp)
    (h12 : u.regs.r12 = t.regs.r12) (h14 : u.regs.r14 = t.regs.r14)
    (h8 : r8 u = r8 t) (h9 : r9 u = r9 t) :
    CandidateState P r F s ra lo
      { L with candidates := L.candidates.set count.toNat off } u0 (count + 1#64) u := by
  have hb := hc.bd.storeLocal (u := u) (i := 6 + count.toNat)
    (by rw [Lc.length]; change count.toNat < 1024 at hn; omega) off hm hsp
  rw [L.set_candidate _ hn off] at hb
  have hcount : (count + 1#64).toNat ≤ MAX_N := by
    change (count + 1).toNat ≤ MAX_N
    rw [small_succ count hn]
    omega
  refine ⟨hb, hc.excess, h12 ▸ hc.r12, h14 ▸ hc.r14,
    h8 ▸ hc.r8, h9 ▸ hc.r9, hcount, ?_, ?_, hc.zero, hc.droppedNow⟩
  · change CandidatesBound r.p.m (L.candidates.set count.toNat off) (count + 1)
    rw [← put_eq_set _ count off hn]
    exact candidatesBound_extend hc.bounded hn ho
  · change CandidatesLive r.M (L.candidates.set count.toNat off) (count + 1)
    rw [← put_eq_set _ count off hn]
    exact candidatesLive_extend hc.live hn hl

end Bbu.Unit.ResolveU
