module

public import FlatShuffler.Unit.Plan.PlannerRunBuilderFrame
import all FlatShuffler.Unit.Plan.PlannerRunBuilderFrame
public import FlatShuffler.Unit.Run.Frame
import all FlatShuffler.Unit.Run.Frame

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep
set_option maxRecDepth 4096

def emissionWords (h : Hdr) : List Word :=
  [h.tgt, h.n, h.spl, h.data, h.len, h.ops, h.nops] ++
    h.dest.toList ++ h.pos.toList ++ [h.pend, h.blkOff, h.blkExc]

theorem emissionWords_length (h : Hdr) : (emissionWords h).length = 2058 := by
  simp only [emissionWords, List.length_append, List.length_cons, List.length_nil,
    Vector.length_toList]
  rfl

theorem emissionWords_mem (S : Addr) (h : Hdr) :
    Arr S (emissionWords h) = Em S h := by
  have hd : h.dest.toList.length = 1024 := Vector.length_toList
  have hp : h.pos.toList.length = 1024 := Vector.length_toList
  simp only [emissionWords, Arr.append, List.length_cons, List.length_nil,
    List.length_append, hd, hp, Nat.reduceAdd, Nat.reduceMul,
    BitVec.add_assoc, BitVec.reduceAdd, Arr, MProp.sep_emp]
  simp only [Em, Fld.target, Fld.targetSize, Fld.spills, Fld.stack_data,
    Fld.stack_size, Fld.stack_trace, Fld.stack_traceSize, Fld.pendingGenerations,
    Fld.blocked_offset, Fld.blocked_excess]
  simp only [MProp.sep_assoc]

structure EmissionLocals where
  head : Vector Word 12
  planned : Flat.Mapping
  tail : Vector Word 2

def EmissionLocals.toList (l : EmissionLocals) (h : Hdr) (PM : Addr) : List Word :=
  l.head.toList ++ l.planned.dest.toList ++ l.planned.pos.toList ++
    emissionWords h ++ [PM] ++ l.tail.toList

theorem EmissionLocals.length (l : EmissionLocals) (h : Hdr) (PM : Addr) :
    (l.toList h PM).length = 4121 := by
  simp only [EmissionLocals.toList, List.length_append, List.length_singleton,
    Vector.length_toList, emissionWords_length]
  rfl

theorem emission_local_frame (sp : Addr) (l : EmissionLocals) (h : Hdr)
    (sv : List Word) :
    Arr sp (l.toList h (sp + 96#64) ++ sv) =
      Em (sp + 16480#64) h ∗
        Planned (sp + 16480#64) (sp + 96#64) l.planned.pos ∗
        (Arr sp l.head.toList ∗ Arr (sp + 96#64) l.planned.dest.toList ∗
          Arr (sp + 32952#64) (l.tail.toList ++ sv)) := by
  have hd : l.planned.dest.toList.length = 1024 := Vector.length_toList
  have hp : l.planned.pos.toList.length = 1024 := Vector.length_toList
  simp only [EmissionLocals.toList, List.append_assoc, Arr.append,
    hd, hp, Vector.length_toList, emissionWords_length, List.length_singleton,
    Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd]
  rw [emissionWords_mem]
  simp only [Arr, MProp.sep_emp, Planned, Fld.plannedMapping,
    BitVec.add_assoc, BitVec.reduceAdd]
  simp only [MProp.sep_assoc]
  conv =>
    lhs
    rw [sep_lc (Arr (sp + 8288#64) l.planned.pos.toList) (Em (sp + 16480#64) h),
      sep_lc (Arr (sp + 96#64) l.planned.dest.toList) (Em (sp + 16480#64) h),
      sep_lc (Arr sp l.head.toList) (Em (sp + 16480#64) h),
      sep_lc (Arr (sp + 8288#64) l.planned.pos.toList) (Wd (sp + 32944#64) (sp + 96#64)),
      sep_lc (Arr (sp + 96#64) l.planned.dest.toList) (Wd (sp + 32944#64) (sp + 96#64)),
      sep_lc (Arr sp l.head.toList) (Wd (sp + 32944#64) (sp + 96#64)),
      sep_lc (Arr (sp + 96#64) l.planned.dest.toList) (Arr (sp + 8288#64) l.planned.pos.toList),
      sep_lc (Arr sp l.head.toList) (Arr (sp + 8288#64) l.planned.pos.toList)]

def localEmissionHdr (locals : List Word) (hl : locals.length = 4121) : Hdr where
  tgt := locals[2060]'(by omega)
  n := locals[2061]'(by omega)
  spl := locals[2062]'(by omega)
  data := locals[2063]'(by omega)
  len := locals[2064]'(by omega)
  ops := locals[2065]'(by omega)
  nops := locals[2066]'(by omega)
  dest := ⟨((locals.drop 2067).take 1024).toArray, by simp [hl, maxStackSize]⟩
  pos := ⟨((locals.drop 3091).take 1024).toArray, by simp [hl, maxStackSize]⟩
  pend := locals[4115]'(by omega)
  blkOff := locals[4116]'(by omega)
  blkExc := locals[4117]'(by omega)

def EmissionLocals.ofList (locals : List Word) (hl : locals.length = 4121) :
    EmissionLocals where
  head := ⟨(locals.take 12).toArray, by simp [hl]⟩
  planned := localMapping locals hl
  tail := ⟨(locals.drop 4119).toArray, by simp [hl]⟩

private theorem take_words (locals : List Word) {base n : Nat}
    (hl : base + n ≤ locals.length) :
    (locals.drop base).take n = (List.range n).map (fun i => locals[base + i]!) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_map, List.length_range]
    omega
  · intro i hi hi'
    have hb : base + i < locals.length := by
      simp only [List.length_take, List.length_drop] at hi
      omega
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map,
      List.getElem_range, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem hb, Option.getD_some]

theorem emission_local_partition (locals : List Word) (hl : locals.length = 4121) :
    (EmissionLocals.ofList locals hl).toList (localEmissionHdr locals hl)
      (locals[4118]'(by omega)) = locals := by
  have hheader : (locals.drop 2060).take 7 =
      [locals[2060]'(by omega), locals[2061]'(by omega), locals[2062]'(by omega),
        locals[2063]'(by omega), locals[2064]'(by omega), locals[2065]'(by omega),
        locals[2066]'(by omega)] := by
    rw [take_words locals (base := 2060) (n := 7) (by omega)]
    simp [List.range_succ, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem (show 2060 < locals.length by omega),
      List.getElem?_eq_getElem (show 2061 < locals.length by omega),
      List.getElem?_eq_getElem (show 2062 < locals.length by omega),
      List.getElem?_eq_getElem (show 2063 < locals.length by omega),
      List.getElem?_eq_getElem (show 2064 < locals.length by omega),
      List.getElem?_eq_getElem (show 2065 < locals.length by omega),
      List.getElem?_eq_getElem (show 2066 < locals.length by omega)]
  have htail : (locals.drop 4115).take 4 =
      [locals[4115]'(by omega), locals[4116]'(by omega),
        locals[4117]'(by omega), locals[4118]'(by omega)] := by
    rw [take_words locals (base := 4115) (n := 4) (by omega)]
    simp [List.range_succ, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem (show 4115 < locals.length by omega),
      List.getElem?_eq_getElem (show 4116 < locals.length by omega),
      List.getElem?_eq_getElem (show 4117 < locals.length by omega),
      List.getElem?_eq_getElem (show 4118 < locals.length by omega)]
  change locals.take 12 ++ (locals.drop 12).take 1024 ++
    (locals.drop 1036).take 1024 ++
    ([locals[2060]'(by omega), locals[2061]'(by omega), locals[2062]'(by omega),
      locals[2063]'(by omega), locals[2064]'(by omega), locals[2065]'(by omega),
      locals[2066]'(by omega)] ++
    (locals.drop 2067).take 1024 ++ (locals.drop 3091).take 1024 ++
    [locals[4115]'(by omega), locals[4116]'(by omega),
      locals[4117]'(by omega)]) ++ [locals[4118]'(by omega)] ++ locals.drop 4119 = locals
  simp only [List.append_assoc]
  rw [← List.append_assoc
    [locals[4115]'(by omega), locals[4116]'(by omega), locals[4117]'(by omega)]
    [locals[4118]'(by omega)] (locals.drop 4119)]
  change (locals.drop 4115).take 4 =
    [locals[4115]'(by omega), locals[4116]'(by omega), locals[4117]'(by omega)] ++
      [locals[4118]'(by omega)] at htail
  rw [← hheader, ← htail]
  have split (b n : Nat) :
      (locals.drop b).take n ++ locals.drop (b + n) = locals.drop b := by
    rw [← List.drop_drop, List.take_append_drop]
  rw [split 4115 4, split 3091 1024, split 2067 1024, split 2060 7,
    split 1036 1024, split 12 1024, List.take_append_drop]

end FlatShuffler.Unit.PlannerRunU
