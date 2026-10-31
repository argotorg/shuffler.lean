import BbuKraken.Unit.Plan.ResolveByteFrame

namespace Bbu.Unit.ResolveU
open Bbu.Sep

theorem store_dropped {P : Addr} {r : RG} {F : MProp 64} {m : Mem 64} {o : Word}
    (hm : (RView P r ∗ F).get m) (ho : o.toNat < r.p.m.toNat)
    (hoN : o.toNat < MAX_N) (z : Int) :
    (RView P { r with dropped := Flat.put r.dropped o (BitVec.ofInt 8 z) } ∗ F).get
      (m.storeInt (r.p.drp + o) 1 z) := by
  let rest := PView P r.p ∗ MapM r.mp r.M ∗ MapM r.currentPtr r.current ∗
    Spl r.p.spl r.spills (List.range r.spillCount) ∗ F
  have he : ∀ d : Vector (BitVec 8) MAX_N,
      RView P { r with dropped := d } ∗ F =
        Bs r.p.drp (d.toList.take r.p.m.toNat) ∗ rest := by
    intro d
    unfold RView rest
    ecancel
  have hm' : (Bs r.p.drp (r.dropped.toList.take r.p.m.toNat) ∗ rest).get m :=
    he r.dropped ▸ hm
  have hs := SpillSetProof.Bs.store hm'
    (by simpa only [List.length_take, Vector.length_toList] using
      Nat.lt_min.mpr (And.intro ho hoN)) z
  rw [he]
  simpa only [Flat.put, Vector.toList_setIfInBounds, List.take_set] using hs

section
variable {P : Addr} {r : RG} {F : MProp 64} {s t u : MachineData} {ra : Int64}
    {lo loc : List Word}

theorem Bd.storeDropped (hb : Bd P r F s ra lo loc t) {o : Word}
    (ho : o.toNat < r.p.m.toNat) (hoN : o.toNat < MAX_N) (z : Int)
    (hm : u.dmem = t.dmem.storeInt (r.p.drp + o) 1 z)
    (hsp : u.regs.rsp = t.regs.rsp) :
    Bd P { r with dropped := Flat.put r.dropped o (BitVec.ofInt 8 z) } F s ra lo loc u := by
  have hm' : (RView P r ∗ (Stk (rsp s) (fr s lo loc) ra.toBitVec ∗ F)).get t.dmem :=
    (sep_lc _ _ _) ▸ hb.kb.mem
  have hs := store_dropped hm' ho hoN z
  refine ⟨⟨?_, hsp ▸ hb.kb.sp⟩, hb.free, hb.locals⟩
  rw [hm]
  exact (sep_lc _ _ _).symm ▸ hs

theorem Bd.storeDroppedNow (hb : Bd P r F s ra lo loc t) {o : Word}
    (ho : o.toNat < MAX_N) (z : Int)
    (hm : u.dmem = t.dmem.storeInt (t.regs.rsp.toBitVec + 8240#64 + o) 1 z)
    (hsp : u.regs.rsp = t.regs.rsp) :
    ∃ w : Word, Bd P r F s ra lo (loc.set (1030 + o.toNat / 8) w) u := by
  change o.toNat < 1024 at ho
  let i := 1030 + o.toNat / 8
  have hi : i < loc.length := by rw [hb.locals]; change 1030 + o.toNat / 8 < 1159; omega
  have he : t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 (o.toNat % 8) =
      t.regs.rsp.toBitVec + 8240#64 + o := by
    have hn : 8 * i + o.toNat % 8 = 8240 + o.toNat := by dsimp [i]; omega
    have hc : BitVec.ofNat 64 o.toNat = o := by simp
    simpa only [BitVec.ofNat_add, hc, BitVec.add_assoc] using
      congrArg (fun n => t.regs.rsp.toBitVec + BitVec.ofNat 64 n) hn
  exact hb.storeLocalByte hi (j := BitVec.ofNat 64 (o.toNat % 8))
    (by simp; omega) z (by rw [he]; exact hm) hsp

end
end Bbu.Unit.ResolveU
