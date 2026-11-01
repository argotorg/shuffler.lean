module

public import BbuKraken.Unit.Run.Load
import all BbuKraken.Unit.Run.Load

@[expose] public section

namespace Bbu.Unit.RunU.Test

example (m : Mem 64) (a b : BitVec 64) :
    (m.loadInt a 8).isSome = true → (m.loadInt b 1).isSome = true →
      (m.loadInt b 1).isSome = true := by
  intro h8 h1
  run_loads [h8, h1]

example (m n : Mem 64) (a : BitVec 64)
    (_hm : (m.loadInt a 8).isSome = true) (hn : (n.loadInt a 8).isSome = true) :
    (n.loadInt a 8).isSome = true := by
  run_loads [_hm, hn]

example (m : Mem 64) (a b : BitVec 64)
    (_h8 : (m.loadInt a 8).isSome = true) (h1 : (m.loadInt b 1).isSome = true) :
    (m.loadInt b 1).isSome = true := by
  fail_if_success (run_loads [_h8]; done)
  exact h1

private abbrev sameMemory (m : Mem 64) := m
private abbrev sameAddress (a : BitVec 64) := a

example (m : Mem 64) (a : BitVec 64)
    (h : ((sameMemory m).loadInt (sameAddress a) (4 + 4)).isSome = true) :
    (m.loadInt a 8).isSome = true := by
  run_loads [h]

example (m : Mem 64) (a : BitVec 64)
    (_h : ((sameMemory m).loadInt (sameAddress a) 1).isSome = true)
    (h8 : (m.loadInt a 8).isSome = true) :
    (m.loadInt a 8).isSome = true := by
  fail_if_success (run_loads [_h]; done)
  exact h8

end Bbu.Unit.RunU.Test
