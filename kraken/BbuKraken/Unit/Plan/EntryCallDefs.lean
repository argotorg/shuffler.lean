module

public import BbuKraken.Unit.Plan.EntryClearDefs
import all BbuKraken.Unit.Plan.EntryClearDefs
public import BbuKraken.Unit.Plan.PlannerRunBuilderMem
import all BbuKraken.Unit.Plan.PlannerRunBuilderMem
public import BbuKraken.Unit.Plan.EntryIdsModel
import all BbuKraken.Unit.Plan.EntryIdsModel

@[expose] public section

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

def withRun (g : EG) (r : PlannerRunG) : EG :=
  {g with r := {g.r with
    p := {g.r.p with saw := r.p.saw}
    spills := r.spills
    dropped := r.dropped
    data := r.data
    ops := r.ops
    traceLength := r.traceLength
    sources := r.sources
    count := r.count}}

def strategyState (g : EG) (s : MachineData) : MachineData :=
  {s with regs := s.regs.set64 .rsi (g.strategy.setWidth 64)}

def RunQ (g g' : EG) (s t : MachineData) : Prop :=
  plannerRunQ g.r g'.r (strategyState g s) t ∧ Keep g g'

structure CallLocals where
  unused : Word
  allowedPad : BitVec 56
  sawPad : BitVec 56

def CallLocals.toList (l : CallLocals) (r : PlannerRunG) : List Word :=
  [l.unused, r.count, r.p.src, r.p.m, r.p.tgt, r.p.n, r.p.spl,
    l.allowedPad ++ r.p.allowed, r.p.drp, l.sawPad ++ r.p.saw]

theorem CallLocals.length (l : CallLocals) (r : PlannerRunG) : (l.toList r).length = 10 := rfl

def Members (P : Addr) (r : PlannerRunG) : MProp 64 :=
  Wd P r.p.src ∗ Wd (P + 8#64) r.p.m ∗ Wd (P + 16#64) r.p.tgt ∗
  Wd (P + 24#64) r.p.n ∗ Wd (P + 32#64) r.p.spl ∗ B8 (P + 40#64) r.p.allowed ∗
  Wd (P + 48#64) r.p.drp ∗ B8 (P + 56#64) r.p.saw

theorem call_local_frame (sp : Addr) (l : CallLocals) (sv : Word) :
    ∃ LF, ∀ r : PlannerRunG, Arr sp (l.toList r ++ [sv]) =
      Members (sp + 16#64) r ∗ Wd (sp + 8#64) r.count ∗ LF := by
  obtain ⟨AF, ha⟩ := PlannerRunU.word_lowByte (sp + 56#64) l.allowedPad
  obtain ⟨SF, hs⟩ := PlannerRunU.word_lowByte (sp + 72#64) l.sawPad
  refine ⟨Wd sp l.unused ∗ AF ∗ SF ∗ Wd (sp + 80#64) sv, fun r => ?_⟩
  simp only [CallLocals.toList, List.cons_append, List.nil_append, Arr, MProp.sep_emp,
    BitVec.add_assoc, BitVec.reduceAdd]
  rw [ha, hs]
  simp only [Members, BitVec.add_assoc, BitVec.reduceAdd]
  ecancel

theorem call_frame (g : EG) (s : MachineData) (ra : Int64) (l : CallLocals) (F : MProp 64)
    (hcount : g.r.countPtr = rsp s - 88#64) :
    let sp := rsp s - 8#64 - 88#64
    ∃ CF, ∀ (lo : List Word) (w : Word) (r : PlannerRunG),
      Stk (rsp s) (lo ++ w :: (l.toList (withRun g r).r ++ [s.regs.rbx.toBitVec]))
          ra.toBitVec ∗ (View (rsp s) (withRun g r) ∗ F) =
        Stk sp lo w ∗ (PlannerRunView (sp + 16#64) (withRun g r).r ∗ CF) := by
  dsimp
  let sp := rsp s - 8#64 - 88#64
  obtain ⟨LF, hl⟩ := call_local_frame sp l s.regs.rbx.toBitVec
  refine ⟨LF ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ Args (rsp s) g ∗ B8 g.sawPtr g.saw ∗ F, ?_⟩
  intro lo w r
  rw [Stk.callee]
  simp only [List.length_append, CallLocals.length, List.length_singleton,
    Nat.reduceAdd, Nat.reduceMul]
  change Stk sp lo w ∗ (View (rsp s) (withRun g r) ∗
    (Arr sp (l.toList (withRun g r).r ++ [s.regs.rbx.toBitVec]) ∗
      Wd (rsp s - 8#64) ra.toBitVec ∗ F)) = _
  rw [hl]
  have hc : sp + 8#64 = g.r.countPtr := by dsimp only [sp]; rw [hcount]; simp only [rsp, Reg64s.get64_rsp]; bv_omega
  simp only [PlannerRunView, PView, View, Buffers, Args, Members, withRun, hc,
    BitVec.add_assoc, BitVec.reduceAdd]
  dsimp only [sp, rsp, Reg64s.get64_rsp]
  ac_rfl

theorem checked_run_ok (g : EG) (hok : g.Ok) (hs : Sizes g)
    (hsrc : idsFrom g.r.p.sw g.idCount 0 = true)
    (htgt : idsFrom g.r.p.tw g.idCount 0 = true) : g.r.Ok := by
  refine ⟨⟨sizes_m hs, sizes_n hs, hok.sw, hok.tw⟩, ?_, ?_, ?_, hok.ops, hok.traceLength⟩
  · rw [hok.ids]
    exact Nat.min_le_right _ _
  · rw [hok.ids]
    apply EntryU.checked_spill_ids g.idCount g.r.p.sw
    simpa only [idsFrom, List.drop_zero, List.all_map, Function.comp_def] using hsrc
  · rw [hok.ids]
    apply EntryU.checked_spill_ids g.idCount g.r.p.tw
    simpa only [idsFrom, List.drop_zero, List.all_map, Function.comp_def] using htgt

theorem withRun_keep (g : EG) (r : PlannerRunG) : Keep g (withRun g r) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem run_shape (g : EG) (saw : BitVec 8) (r : PlannerRunG) (s t : MachineData)
    (hq : plannerRunQ (PlannerRunU.withSaw g.r saw) r s t) : r = (withRun g r).r := by
  obtain ⟨us, ha, hstate, hp, hd, ho, hsrc, hc, hi, hcount⟩ := hq
  cases r
  simp only [withRun, PlannerRunU.withSaw] at hp hd ho hsrc hc hi ⊢
  congr 1 <;> first | rfl | exact hp | exact hd | exact ho | exact hsrc | exact hc | exact hi

end Bbu.Unit.EntryValidU
