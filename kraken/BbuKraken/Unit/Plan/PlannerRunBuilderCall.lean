module

public import BbuKraken.Unit.Plan.PlannerRunBuilderView
import all BbuKraken.Unit.Plan.PlannerRunBuilderView
public import BbuKraken.Unit.Plan.ExitCall
import all BbuKraken.Unit.Plan.ExitCall

@[expose] public section

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

theorem builder_call_frame (P : Addr) (g : PlannerRunG) (hok : g.Ok)
    (s : MachineData) (ra : Int64) (l : BuilderLocals) (strat : BitVec 8) (F : MProp 64) :
    let sp := rsp s - 8#64 - 33016#64
    ∃ CF, ∀ (lo : List Word) (w : Word) (M : Flat.Mapping) (saw : BitVec 8),
      let b := builderGhost g (sp + 96#64) strat saw M
      Stk (rsp s) (lo ++ w :: (l.toList b ++ saved s)) ra.toBitVec ∗
          (PlannerRunView P g ∗ F) =
        Stk sp lo w ∗ (BView (sp + 32#64) b ∗ CF) := by
  dsimp
  let sp := rsp s - 8#64 - 33016#64
  let b := builderGhost g (sp + 96#64) strat 0#8
    ⟨Vector.replicate MAX_N 0#64, Vector.replicate MAX_N 0#64⟩
  obtain ⟨BF, hf⟩ := builder_local_frame sp l b rfl (saved s)
  obtain ⟨PF, hp⟩ := builder_view_frame P (sp + 32#64) g hok (sp + 96#64) strat
  refine ⟨BF ∗ PF ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F, ?_⟩
  intro lo w M saw
  have hs : (saved s).length = 6 := rfl
  rw [Stk.callee]
  simp only [List.length_append, l.length, hs, Nat.reduceAdd, Nat.reduceMul]
  change Stk sp lo w ∗ (PlannerRunView P g ∗
    (Arr sp (l.toList (builderGhost g (sp + 96#64) strat saw M) ++ saved s) ∗
      Wd (rsp s - 8#64) ra.toBitVec ∗ F)) = _
  rw [show Arr sp (l.toList (builderGhost g (sp + 96#64) strat saw M) ++ saved s) =
    BuilderMembers (sp + 32#64) (builderGhost g (sp + 96#64) strat saw M) ∗
      MapM (sp + 96#64) M ∗ BF from hf M saw]
  calc
    _ = Stk sp lo w ∗ ((PlannerRunView P g ∗ MapM (sp + 96#64) M ∗
        BuilderMembers (sp + 32#64) (builderGhost g (sp + 96#64) strat saw M)) ∗
          (BF ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F)) := by ac_rfl
    _ = _ := by
      rw [hp M saw]
      simp only [sp, rsp, BitVec.add_comm]
      ac_rfl

theorem splitBuilderStack (lo : List Word) (hl : lo.length = 4113)
    (k : Nat) (hk : k ≤ 4112) :
    ∃ unused xs w, lo = unused ++ xs ++ [w] ∧
      unused.length = 4112 - k ∧ xs.length = k := by
  have hd : (lo.drop 4112).length = 1 := by simp [hl]
  match he : lo.drop 4112, hd with
  | [w], _ =>
    refine ⟨(lo.take 4112).take (4112 - k), (lo.take 4112).drop (4112 - k), w, ?_, ?_, ?_⟩
    · rw [List.take_append_drop, ← he, List.take_append_drop]
    · simp only [List.length_take, hl, Nat.min_eq_left (by omega : 4112 ≤ 4113),
        Nat.min_eq_left (by omega : 4112 - k ≤ 4112)]
    · simp only [List.length_drop, List.length_take, hl,
        Nat.min_eq_left (by omega : 4112 ≤ 4113)]
      omega

section
variable {P : Addr} {g : PlannerRunG} {F : MProp 64} {s t : MachineData} {ra : Int64}
    {lo : List Word} {l : BuilderLocals} {strat saw : BitVec 8} {M : Flat.Mapping}
    {A : BG → MachineData → Prop} {Q X : BG → BG → MachineData → MachineData → Prop}
    {K E : MachineData → Prop} {k : Nat}

theorem Bd.callBuilder
    (hb : Bd P g F s ra lo
      (l.toList (builderGhost g (t.regs.rsp.toBitVec + 96#64) strat saw M)) t)
    (hok : g.Ok) (hk : k ≤ 4112)
    (hdi : rdi t = t.regs.rsp.toBitVec + 32#64)
    (hA : A (builderGhost g (t.regs.rsp.toBitVec + 96#64) strat saw M) t)
    (hshape : ∀ b' u,
      Q (builderGhost g (t.regs.rsp.toBitVec + 96#64) strat saw M) b' t u →
      b' = builderGhost g (t.regs.rsp.toBitVec + 96#64) strat b'.saw b'.M)
    (hxshape : ∀ b' u,
      X (builderGhost g (t.regs.rsp.toBitVec + 96#64) strat saw M) b' t u →
      b' = builderGhost g (t.regs.rsp.toBitVec + 96#64) strat b'.saw b'.M)
    (hK : ∀ (M' : Flat.Mapping) (saw' : BitVec 8) (u : MachineData) (lo' : List Word),
      Bd P g F s ra lo'
        (l.toList (builderGhost g (t.regs.rsp.toBitVec + 96#64) strat saw' M')) u →
      Q (builderGhost g (t.regs.rsp.toBitVec + 96#64) strat saw M)
        (builderGhost g (t.regs.rsp.toBitVec + 96#64) strat saw' M') t u →
      Sep.mod.Agree t u → K u)
    (hE : ∀ (M' : Flat.Mapping) (saw' : BitVec 8) (u : MachineData) (lo' : List Word),
      (Stk (rsp s) (fr s lo'
        (l.toList (builderGhost g (t.regs.rsp.toBitVec + 96#64) strat saw' M')))
          ra.toBitVec ∗ (PlannerRunView P g ∗ F)).get u.dmem →
      lo'.length = 4113 →
      X (builderGhost g (t.regs.rsp.toBitVec + 96#64) strat saw M)
        (builderGhost g (t.regs.rsp.toBitVec + 96#64) strat saw' M') t u →
      u.regs.get64 .rdi = 1#64 → E u) :
    ∃ B b CF, VPre BView BG.Ok B b CF A k t ∧
      (∀ u, VPost BView BG.Ok B CF k (fun b' u => Q b b' t u) t u →
        Sep.mod.Agree t u → K u) ∧
      (∀ u, VPost BView BG.Ok B CF k (fun b' u => X b b' t u) t u →
        u.regs.get64 .rdi = 1#64 → E u) := by
  obtain ⟨unused, xs, w, he, hunused, hxs⟩ := splitBuilderStack lo hb.low k hk
  obtain ⟨CF, hf⟩ := builder_call_frame P g hok s ra l strat F
  have hsp : rsp t = rsp s - 8#64 - 33016#64 := hb.kb.sp
  change t.regs.rsp.toBitVec = rsp s - 8#64 - 33016#64 at hsp
  have hm := hb.kb.mem
  change (Stk (rsp s) (lo ++ (l.toList
    (builderGhost g (t.regs.rsp.toBitVec + 96#64) strat saw M) ++ saved s))
      ra.toBitVec ∗ (PlannerRunView P g ∗ F)).get t.dmem at hm
  rw [he, List.append_assoc, List.singleton_append, hsp, hf (unused ++ xs) w M saw,
    ← hsp, Stk.split, hxs] at hm
  refine ⟨t.regs.rsp.toBitVec + 32#64,
    builderGhost g (t.regs.rsp.toBitVec + 96#64) strat saw M,
    Arr (rsp t - 8#64 - BitVec.ofNat 64 (8 * (unused.length + k))) unused ∗ CF,
    ⟨hdi, builderGhost_ok g hok _ strat saw M, hA, xs, w, hxs, ?_⟩, ?_, ?_⟩
  · rw [sep_lc (Arr _ unused) (BView _ _)] at hm
    exact hm
  · intro u hpost hag
    obtain ⟨b', hQ, _, xs', w', hxs', hm'⟩ := hpost
    have heq := hshape b' u hQ
    rw [heq] at hQ hm'
    apply hK b'.M b'.saw u (unused ++ xs' ++ [w'])
    · refine ⟨⟨?_, ?_⟩, ?_, l.length _⟩
      · change (Stk (rsp s) ((unused ++ xs' ++ [w']) ++
          (l.toList (builderGhost g (t.regs.rsp.toBitVec + 96#64) strat b'.saw b'.M) ++ saved s))
            ra.toBitVec ∗ (PlannerRunView P g ∗ F)).get u.dmem
        rw [List.append_assoc, List.singleton_append, hsp,
          hf (unused ++ xs') w' b'.M b'.saw, ← hsp, Stk.split, hxs']
        rw [sep_lc (BView _ _) (Arr _ unused)] at hm'
        exact hm'
      · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp]
        exact hb.kb.sp
      · simp only [List.length_append, List.length_singleton, hunused, hxs']
        omega
    · exact hQ
    · exact hag
  · intro u hpost harg
    obtain ⟨b', hX, _, xs', w', hxs', hm'⟩ := hpost
    have heq := hxshape b' u hX
    rw [heq] at hX hm'
    apply hE b'.M b'.saw u (unused ++ xs' ++ [w']) ?_ ?_ hX harg
    · change (Stk (rsp s) ((unused ++ xs' ++ [w']) ++
          (l.toList (builderGhost g (t.regs.rsp.toBitVec + 96#64) strat b'.saw b'.M) ++ saved s))
            ra.toBitVec ∗ (PlannerRunView P g ∗ F)).get u.dmem
      rw [List.append_assoc, List.singleton_append, hsp,
        hf (unused ++ xs') w' b'.M b'.saw, ← hsp, Stk.split, hxs']
      rw [sep_lc (BView _ _) (Arr _ unused)] at hm'
      exact hm'
    · simp only [List.length_append, List.length_singleton, hunused, hxs']
      omega

end

end Bbu.Unit.PlannerRunU
