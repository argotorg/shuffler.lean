module

public import BbuKraken.Unit.Plan.ResolveBytes
import all BbuKraken.Unit.Plan.ResolveBytes

@[expose] public section

namespace Bbu.Unit.ResolveU
open Bbu.Sep

theorem local_partition (loc : List Word) :
    loc = loc.take 1030 ++ (loc.drop 1030).take 128 ++ loc.drop 1158 := by
  have hd : (loc.drop 1030).drop 128 = loc.drop 1158 := by rw [List.drop_drop]
  rw [← hd, List.append_assoc, List.take_append_drop, List.take_append_drop]

theorem local_bytes (sp : Addr) (loc : List Word) (hl : loc.length = 1159)
    (sv : List Word) :
    ∃ dv : Vector (BitVec 8) MAX_N,
      Arr sp (loc ++ sv) =
        Arr sp (loc.take 1030) ∗ Bs (sp + 8240#64) dv.toList ∗
          Arr (sp + 9264#64) (loc.drop 1158 ++ sv) := by
  have hfront : (loc.take 1030).length = 1030 := by simp [hl]
  have hbytes : ((loc.drop 1030).take 128).length = 128 := by simp [hl]
  let dv : Vector (BitVec 8) MAX_N :=
    ⟨(wordsBytes ((loc.drop 1030).take 128)).toArray, by
      simp [wordsBytes_length, hbytes, MAX_N]⟩
  refine ⟨dv, ?_⟩
  conv => lhs; rw [local_partition loc]
  rw [List.append_assoc, List.append_assoc, Arr.append, hfront]
  rw [Arr.append, hbytes]
  simp only [Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd]
  rw [Arr_Bs (sp + 8240#64) ((loc.drop 1030).take 128)]
  rfl

-- The frame does not depend on the free words or on the callee return word.
theorem classify_frame (P : Addr) (r : RG) (hok : r.Ok) (s : MachineData)
    (ra : Int64) (loc : List Word) (hl : loc.length = 1159) (F : MProp 64) :
    let sp := rsp s - 8#64 - 9320#64
    ∃ (dv : Vector (BitVec 8) MAX_N) (CF : MProp 64),
      ∀ (lo : List Word) (w : Word),
        Stk (rsp s) (lo ++ w :: (loc ++ saved s)) ra.toBitVec ∗ (RView P r ∗ F) =
          Stk sp lo w ∗ (CView P (classifyGhost r (sp + 8240#64) dv) ∗ CF) := by
  dsimp
  let sp := rsp s - 8#64 - 9320#64
  obtain ⟨dv, he⟩ := local_bytes sp loc hl (saved s)
  obtain ⟨rest, hr⟩ := classify_split P r hok (sp + 8240#64) dv
  refine ⟨dv,
    Arr sp (loc.take 1030) ∗ Arr (sp + 9264#64) (loc.drop 1158 ++ saved s) ∗
      Wd (rsp s - 8#64) ra.toBitVec ∗ MapM r.currentPtr r.current ∗
      Bs r.p.drp (r.dropped.toList.take r.p.m.toNat) ∗ Spl r.p.spl r.spills rest ∗ F,
    fun lo w => ?_⟩
  have hhi : BitVec.ofNat 64 (8 * (loc ++ saved s).length) = 9320#64 := by
    simp [hl, saved]
  rw [Stk.callee, hhi]
  change Stk sp lo w ∗ (RView P r ∗
    (Arr sp (loc ++ saved s) ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F)) = _
  rw [he]
  have hr' : RView P r ∗ Bs (sp + 8240#64) dv.toList =
      CView P (classifyGhost r (sp + 8240#64) dv) ∗
        (MapM r.currentPtr r.current ∗ Bs r.p.drp (r.dropped.toList.take r.p.m.toNat) ∗
          Spl r.p.spl r.spills rest) := hr r.spills
  calc
    _ = Stk sp lo w ∗ ((RView P r ∗ Bs (sp + 8240#64) dv.toList) ∗
        (Arr sp (loc.take 1030) ∗ Arr (sp + 9264#64) (loc.drop 1158 ++ saved s) ∗
          Wd (rsp s - 8#64) ra.toBitVec ∗ F)) := by ecancel
    _ = _ := by rw [hr']; simp only [sp, rsp, Reg64s.get64_rsp]; ecancel

theorem split17 (lo : List Word) (hl : lo.length = 17) :
    ∃ xs w, lo = xs ++ [w] ∧ xs.length = 16 := by
  have hd : (lo.drop 16).length = 1 := by simp [hl]
  match he : lo.drop 16, hd with
  | [w], _ =>
    exact ⟨lo.take 16, w, by rw [← he, List.take_append_drop], by simp [hl]⟩

section
variable {P : Addr} {r : RG} {F : MProp 64} {s t : MachineData} {ra : Int64}
  {lo loc : List Word} {K : MachineData → Prop}

theorem Bd.callClassify (hb : Bd P r F s ra lo loc t) (hok : r.Ok)
    (hdi : rdi t = P) (hsi : rsi t = r.mp)
    (hdx : rdx t = t.regs.rsp.toBitVec + 8240#64)
    (hoff : (rcx t).toNat < r.p.m.toNat)
    (hret : Flat.get r.M.dest (rcx t) ≠ Flat.NONE)
    (hK : ∀ (dv : Vector (BitVec 8) MAX_N) (u : MachineData) (lo' : List Word),
      (∀ o : Word, o.toNat < MAX_N →
        Flat.get dv o = rdb t.dmem (t.regs.rsp.toBitVec + 8240#64 + o)) →
      Bd P r F s ra lo' loc u →
      al u = Flat.classify r.p.fl r.spills r.M dv (rcx t) →
      Sep.mod.Agree t u → K u) :
    ∃ S c CF, VPre CView CG.Ok S c CF classifyA 16 t ∧
      ∀ u, VPost CView CG.Ok S CF 16 (fun c' u => classifyQ c c' t u) t u →
        Sep.mod.Agree t u → K u := by
  obtain ⟨xs, w, he, hxs⟩ := split17 lo hb.free
  obtain ⟨dv, CF, hf⟩ := classify_frame P r hok s ra loc hb.locals F
  have hsp : rsp t = rsp s - 8#64 - 9320#64 := hb.kb.sp
  have hm := hb.kb.mem
  change (Stk (rsp s) (lo ++ (loc ++ saved s)) ra.toBitVec ∗ (RView P r ∗ F)).get t.dmem at hm
  rw [he, List.append_assoc, List.singleton_append, hf xs w, ← hsp] at hm
  have hcv : (CView P (classifyGhost r (t.regs.rsp.toBitVec + 8240#64) dv) ∗
      (Stk (rsp t) xs w ∗ CF)).get t.dmem := (sep_lc _ _ _) ▸ hm
  have hdv : ∀ o : Word, o.toNat < MAX_N →
      Flat.get dv o = rdb t.dmem (t.regs.rsp.toBitVec + 8240#64 + o) := by
    intro o ho
    exact (HView.rdb_dn (ClassifyU.CView.hv hcv) ho).symm
  refine ⟨P, classifyGhost r (t.regs.rsp.toBitVec + 8240#64) dv, CF,
    ⟨hdi, classifyGhost_ok hok _ dv, classify_args hok hsi hdx hoff hret,
      xs, w, hxs, hm⟩, ?_⟩
  intro u hpost hag
  obtain ⟨c', ⟨hc, hal⟩, _, xs', w', hxs', hm'⟩ := hpost
  subst c'
  have hspu : u.regs.rsp.toBitVec = t.regs.rsp.toBitVec := by
    rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp]
  apply hK dv u (xs' ++ [w']) hdv
  · refine ⟨⟨?_, hspu.trans hb.kb.sp⟩, by simp [hxs'], hb.locals⟩
    change (Stk (rsp s) ((xs' ++ [w']) ++ (loc ++ saved s)) ra.toBitVec ∗
      (RView P r ∗ F)).get u.dmem
    rw [List.append_assoc, List.singleton_append, hf xs' w', ← hsp]
    exact hm'
  · exact hal
  · exact hag

end

end Bbu.Unit.ResolveU
