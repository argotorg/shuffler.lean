import Shuffler.Placement.Defs
import Mathlib.Data.List.Perm.Basic

namespace Shuffler.Placement

private theorem swap_after_fixed {α : Type*} (fixed : List α) (a b : α) (rest : List α) :
    (fixed ++ a :: b :: rest).swap fixed.length (fixed.length + 1) =
      fixed ++ b :: a :: rest := by
  induction fixed with
  | nil => simp [List.swap_cons_zero_left]
  | cons value fixed ih => simpa [Nat.add_assoc] using congrArg (value :: ·) ih

private theorem swap_conjugate {α : Type*} (xs : List α) (top a b : Nat)
    (ht : top < xs.length) (ha : a < xs.length) (hb : b < xs.length)
    (hta : top ≠ a) (htb : top ≠ b) (hab : a ≠ b) :
    ((xs.swap top a).swap top b).swap top a = xs.swap a b := by
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    by_cases hka : k = a
    · subst k
      simp [ht, hb, Ne.symm hta, Ne.symm htb, Ne.symm hab]
    by_cases hkb : k = b
    · subst k
      simp [ht, ha, Ne.symm htb, Ne.symm hab]
    by_cases hkt : k = top
    · subst k
      simp [ht, ha, hta, htb, hab, Ne.symm hta]
    · simp [hka, hkb, hkt]

-- An absolute source position can be exchanged with the top when reachable.
theorem canPlace_swap_top (spills : SpillSet) (source : Stack) (pos : Nat)
    (hpos : pos < source.length)
    (hdepth : source.length - 1 - pos ≤ MAX_SWAP_DEPTH) :
    CanPlace spills source (source.swap (source.length - 1) pos) 0 := by
  by_cases he : pos = source.length - 1
  · simpa [he] using CanPlace.refl spills source
  · have hlt : source.length - 1 - pos < source.length := by omega
    have hlo : 1 ≤ source.length - 1 - pos := by omega
    have hp : source.length - 1 - (source.length - 1 - pos) = pos := by omega
    have htrace : CanPlace spills source
        (source.swap (source.length - 1) (source.length - 1 - (source.length - 1 - pos))) 0 :=
      ⟨.Swap _ hlt hlo hdepth (.Lit source), trivial, rfl⟩
    simpa only [hp] using htrace

-- A swap between two reachable positions is at most three top swaps.
theorem canPlace_swap (spills : SpillSet) (source : Stack) (a b : Nat)
    (ha : a < source.length) (hb : b < source.length)
    (hda : source.length - 1 - a ≤ MAX_SWAP_DEPTH)
    (hdb : source.length - 1 - b ≤ MAX_SWAP_DEPTH) :
    CanPlace spills source (source.swap a b) 0 := by
  by_cases hab : a = b
  · simpa [hab] using CanPlace.refl spills source
  by_cases hat : a = source.length - 1
  · subst a
    exact canPlace_swap_top spills source b hb hdb
  by_cases hbt : b = source.length - 1
  · subst b
    simpa only [List.swap_comm] using canPlace_swap_top spills source a ha hda
  let top := source.length - 1
  have first := canPlace_swap_top spills source a ha hda
  have second : CanPlace spills (source.swap top a) ((source.swap top a).swap top b) 0 := by
    simpa only [List.length_swap] using canPlace_swap_top spills (source.swap top a) b
      (by simpa only [List.length_swap] using hb) (by simpa only [List.length_swap] using hdb)
  have third : CanPlace spills ((source.swap top a).swap top b)
      (((source.swap top a).swap top b).swap top a) 0 := by
    simpa only [List.length_swap] using
      canPlace_swap_top spills ((source.swap top a).swap top b) a
        (by simpa only [List.length_swap] using ha) (by simpa only [List.length_swap] using hda)
  have he : ((source.swap top a).swap top b).swap top a = source.swap a b :=
    swap_conjugate source top a b (by dsimp [top]; omega) ha hb (Ne.symm hat) (Ne.symm hbt) hab
  simpa only [he, Multiset.add_zero] using (first.trans second).trans third

-- A list permutation of at most seventeen suffix slots can use only swaps.
theorem canPlace_perm_append (spills : SpillSet) {left right : Stack} (hperm : left.Perm right) :
    ∀ fixed : Stack, left.length ≤ MAX_SWAP_DEPTH + 1 →
      CanPlace spills (fixed ++ left) (fixed ++ right) 0 := by
  induction hperm with
  | nil =>
    intro fixed _
    exact CanPlace.refl spills _
  | @cons value left right hperm ih =>
    intro fixed hlen
    have hsmall : left.length ≤ MAX_SWAP_DEPTH + 1 := by simpa using Nat.le_of_succ_le hlen
    simpa only [List.append_assoc, List.singleton_append] using ih (fixed ++ [value]) hsmall
  | swap a b rest =>
    intro fixed hlen
    have hswap := canPlace_swap spills (fixed ++ b :: a :: rest)
      fixed.length (fixed.length + 1) (by simp) (by simp)
      (by simp only [List.length_append, List.length_cons] at *; omega)
      (by simp only [List.length_append, List.length_cons] at *; omega)
    simpa only [swap_after_fixed] using hswap
  | @trans left middle right hleft hright ihleft ihright =>
    intro fixed hlen
    have hmid : middle.length ≤ MAX_SWAP_DEPTH + 1 := by simpa only [hleft.length_eq] using hlen
    simpa only [Multiset.add_zero] using (ihleft fixed hlen).trans (ihright fixed hmid)

-- Equal values may be assigned to positions freely. The shared fixed prefix
-- stays in place, while every remaining source position is within SWAP reach.
theorem canPlace_perm_of_take_eq (spills : SpillSet) (source target : Stack) (count : Nat)
    (hperm : source.Perm target) (hfixed : source.take count = target.take count)
    (hbound : source.length - count ≤ MAX_SWAP_DEPTH + 1) :
    CanPlace spills source target 0 := by
  have htail : (source.drop count).Perm (target.drop count) :=
    hperm.drop (by rw [hfixed])
  have htrace := canPlace_perm_append spills htail (source.take count)
    (by simpa only [List.length_drop] using hbound)
  have htarget : source.take count ++ target.drop count = target := by
    rw [hfixed, List.take_append_drop]
  simpa only [List.take_append_drop, htarget] using htrace

end Shuffler.Placement
