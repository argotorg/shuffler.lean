import BbuKraken.PlanReject

namespace Bbu.Unit.EntryRejectIds.Test
open EntryValidU

-- Variable zero with a nonzero opcode. Its ID is invalid when idCount = 0.
private def invalid : Word := 1099511627776#64

private def sourcePrefix : G where
  m := 10
  n := 0
  src := 4096
  tgt := 0
  idCount := 0
  allowed := 0
  strategy := 0
  sw := [invalid]
  tw := []

example : sourcePrefix.Ok := by
  constructor
  · unfold EntryU.BadArgs
    decide +kernel
  all_goals decide +kernel

-- The source prefix rejects before any target or output-buffer access.
example [Host] [FunDecls] (F : MProp 64) :
    Sep.Body planAsm (Pre sourcePrefix F) (Post sourcePrefix F) :=
  Bbu.plan_rejects_invalid_ids sourcePrefix F

private def targetPrefix : G :=
  {sourcePrefix with m := 1, n := 10, sw := [0], tw := [invalid]}

example : targetPrefix.Ok := by
  constructor
  · unfold EntryU.BadArgs
    decide +kernel
  all_goals decide +kernel

-- An empty source is also permitted on a target rejection path.
example : ({targetPrefix with m := 0, sw := []} : G).Ok := by
  constructor
  · unfold EntryU.BadArgs
    decide +kernel
  all_goals decide +kernel

-- Valid prefixes cannot justify a rejection.
example : ¬ ({sourcePrefix with sw := [0]} : G).Ok := by
  intro h
  have hn : ¬ (idsFrom [0] 0 0 = false ∨
      (([0] : List Word).length = 10 ∧ idsFrom [] 0 0 = false)) := by decide +kernel
  exact hn h.bad

-- A target rejection needs the complete source scan.
example : ¬ ({targetPrefix with m := 2} : G).Ok := by
  intro h
  have hn : ¬ (idsFrom [0] 0 0 = false ∨
      (([0] : List Word).length = 2 ∧ idsFrom [invalid] 0 0 = false)) := by decide +kernel
  exact hn h.bad

-- An owned prefix cannot exceed the public size.
example : ¬ ({sourcePrefix with m := 0} : G).Ok := by
  intro h
  have hn : ¬ (([invalid] : List Word).length ≤ 0) := by decide +kernel
  exact hn h.sw

end Bbu.Unit.EntryRejectIds.Test
