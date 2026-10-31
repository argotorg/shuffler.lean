import BbuKraken.FlatList.Loop
import BbuKraken.FlatList.Ctor
import BbuKraken.FlatList.Permute

/-!
The bridge from the flat model to the list model: for each input that the guard of
`build_bottom_up` accepts and whose destinations are distinct and below `n`, the result of
`build_bottom_up` is the result of `Bbu.buildBottomUp` on the list inputs (`Rel`).
`FlatModelTest.lean` and `FlatRelTest.lean` check this by evaluation.

The uninitialized members `u` and the slots of `data` from `m` on do not change the result.

The proof: the state of the constructor holds the initial state of the list model
(`FlatList/Ctor.lean`), each iteration of the loop keeps the relation (`FlatList/Step.lean`,
`FlatList/Loop.lean`), and the final permutation keeps it (`PermR`, `FlatList/Permute.lean`).
-/

namespace Bbu.Flat

theorem build_bottom_up_rel_of_perm {m n : Word} {data target : Vector StackSlot MAX_N}
    {dest : Vector Word MAX_N} {spilled : BitVec 32 → BitVec 8} (u : Uninit) (hm : m ≤ n)
    (hn : n.toNat ≤ MAX_N) (hd : Dests n.toNat (listDests m.toNat dest))
    (hfin : PermR (listEnv n.toNat target spilled)) :
    Rel (build_bottom_up m n data target dest spilled u)
      (Bbu.buildBottomUp (listEnv n.toNat target spilled) (listSource m.toNat data)
        (listDests m.toNat dest)) := by
  have hmn : m.toNat ≤ n.toNat := hm
  have hM : m.toNat ≤ MAX_N := by omega
  have hen := listEnv_n target spilled hn
  have hg : ¬(m > n ∨ n > BitVec.ofNat 64 MAX_N) := by
    rw [MAX_N_eq] at hn ⊢
    intro h
    rcases h with h | h <;> bv_omega
  have hl : (listSource m.toNat data).length = (listDests m.toNat dest).length := by
    rw [listSource_length data hM, listDests_length dest hM]
  have hd' : Dests (listEnv n.toNat target spilled).n (listDests m.toNat dest) := by
    rw [hen]; exact hd
  have hi := Inv_init hl (by rw [hen, listDests_length dest hM]; exact hmn) (by rw [hen]; exact hn) hd'
  have hs := sim_ctor (data := data) (target := target) (spilled := spilled) u hm hn hd
  have h := sim_loop hfin _ _ 0 hs hi.toS (Nat.zero_le _)
  unfold build_bottom_up
  rw [ite_eq_right hg]
  exact rel_outOf h

theorem build_bottom_up_rel {m n : Word} {data target : Vector StackSlot MAX_N}
    {dest : Vector Word MAX_N} {spilled : BitVec 32 → BitVec 8} (u : Uninit) (hm : m ≤ n)
    (hn : n.toNat ≤ MAX_N) (hd : Dests n.toNat (listDests m.toNat dest)) :
    Rel (build_bottom_up m n data target dest spilled u)
      (Bbu.buildBottomUp (listEnv n.toNat target spilled) (listSource m.toNat data)
        (listDests m.toNat dest)) :=
  build_bottom_up_rel_of_perm u hm hn hd (permR _)

end Bbu.Flat
