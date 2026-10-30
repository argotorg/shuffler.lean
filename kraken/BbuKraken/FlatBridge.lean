import BbuKraken.FlatRel

/-!
The bridge from the flat model to the list model: for each input that the guard of
`build_bottom_up` accepts and whose destinations are distinct and below `n`, the result of
`build_bottom_up` is the result of `Bbu.buildBottomUp` on the list inputs (`Rel`).
`FlatModelTest.lean` and `FlatRelTest.lean` check this by evaluation.

The uninitialized members `u` and the slots of `data` from `m` on do not change the result.
-/

namespace Bbu.Flat

theorem build_bottom_up_rel {m n : Word} {data target : Vector StackSlot MAX_N}
    {dest : Vector Word MAX_N} {spilled : BitVec 32 → BitVec 8} (u : Uninit) (hm : m ≤ n)
    (hn : n.toNat ≤ MAX_N) (hd : Dests n.toNat (listDests m.toNat dest)) :
    Rel (build_bottom_up m n data target dest spilled u)
      (Bbu.buildBottomUp (listEnv n.toNat target spilled) (listSource m.toNat data)
        (listDests m.toNat dest)) := by
  sorry

end Bbu.Flat
