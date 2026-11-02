module

public import FlatShuffler.Unit.Plan.PlannerRunBuilderMem
import all FlatShuffler.Unit.Plan.PlannerRunBuilderMem

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep

structure BuilderLocals where
  head : Vector Word 4
  stratPad : BitVec 56
  sawPad : BitVec 56
  tail : Vector Word 2061

def BuilderLocals.toList (l : BuilderLocals) (b : BG) : List Word :=
  l.head.toList ++ [b.src, b.m, b.tgt, b.n, b.drp, l.stratPad ++ b.strat,
    b.mp, l.sawPad ++ b.saw] ++ b.M.dest.toList ++ b.M.pos.toList ++ l.tail.toList

theorem BuilderLocals.length (l : BuilderLocals) (b : BG) : (l.toList b).length = 4121 := by
  have hd : b.M.dest.toList.length = MAX_N := Vector.length_toList
  have hp : b.M.pos.toList.length = MAX_N := Vector.length_toList
  simp only [BuilderLocals.toList, List.length_append, List.length_cons, List.length_nil,
    Vector.length_toList, hd, hp]
  rfl

theorem BuilderLocals.destSlice (l : BuilderLocals) (b : BG) :
    ((l.toList b).drop 12).take 1024 = b.M.dest.toList := by
  have hd : b.M.dest.toList.length = 1024 := Vector.length_toList
  simp [BuilderLocals.toList, List.drop_append, List.take_append, hd]

theorem BuilderLocals.posSlice (l : BuilderLocals) (b : BG) :
    ((l.toList b).drop 1036).take 1024 = b.M.pos.toList := by
  have hd : b.M.dest.toList.length = 1024 := Vector.length_toList
  have hp : b.M.pos.toList.length = 1024 := Vector.length_toList
  simp [BuilderLocals.toList, List.drop_append, List.take_append, hd, hp]

theorem BuilderLocals.mapping (l : BuilderLocals) (b : BG) :
    localMapping (l.toList b) (l.length b) = b.M := by
  cases hb : b.M with
  | mk dest pos =>
    have hd := l.destSlice b
    have hp := l.posSlice b
    simp only [hb] at hd hp
    simp only [localMapping, hd, hp, Vector.toArray_toList]

def BuilderMembers (B : Addr) (b : BG) : MProp 64 :=
  Wd B b.src ∗ Wd (B + 8#64) b.m ∗ Wd (B + 16#64) b.tgt ∗ Wd (B + 24#64) b.n
    ∗ Wd (B + 32#64) b.drp ∗ B8 (B + 40#64) b.strat ∗ Wd (B + 48#64) b.mp
    ∗ B8 (B + 56#64) b.saw

theorem builder_local_frame (sp : Addr) (l : BuilderLocals) (b : BG)
    (hmp : b.mp = sp + 96#64) (sv : List Word) :
    ∃ BF, ∀ (M : Flat.Mapping) (saw : BitVec 8),
      Arr sp (l.toList { b with M := M, saw := saw } ++ sv) =
        BuilderMembers (sp + 32#64) { b with M := M, saw := saw } ∗
          MapM b.mp M ∗ BF := by
  obtain ⟨Rstrat, hs⟩ := word_lowByte (sp + 72#64) l.stratPad
  obtain ⟨Rsaw, hw⟩ := word_lowByte (sp + 88#64) l.sawPad
  refine ⟨Arr sp l.head.toList ∗ Rstrat ∗ Rsaw ∗
    Arr (sp + 16480#64) (l.tail.toList ++ sv), ?_⟩
  intro M saw
  simp only [BuilderLocals.toList, List.append_assoc, Arr.append, Vector.length_toList,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
    BitVec.add_assoc, BitVec.reduceAdd, Arr, MProp.sep_emp]
  rw [hs, hw]
  simp only [BuilderMembers, MapM, hmp, BitVec.add_assoc, BitVec.reduceAdd, MAX_N]
  simp only [Nat.reduceMul, BitVec.reduceAdd]
  ecancel

end FlatShuffler.Unit.PlannerRunU
