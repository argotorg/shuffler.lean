module

public import FlatShuffler.Unit.Plan.ResolveCall
import all FlatShuffler.Unit.Plan.ResolveCall

@[expose] public section

namespace FlatShuffler.Unit.ResolveU
open FlatShuffler.Sep

structure Lc where
  x0 : Word
  pending : Word
  classWord : Word
  excess : Word
  pass : Word
  count : Word
  candidates : Vector Word MAX_N
  droppedWords : Vector Word 128
  padding : Word

def Lc.toList (L : Lc) : List Word :=
  [L.x0, L.pending, L.classWord, L.excess, L.pass, L.count] ++
    L.candidates.toList ++ L.droppedWords.toList ++ [L.padding]

@[simp] theorem Lc.length (L : Lc) : L.toList.length = 1159 := by
  have hc : L.candidates.toList.length = MAX_N := Vector.length_toList
  have hd : L.droppedWords.toList.length = 128 := Vector.length_toList
  simp only [Lc.toList, List.length_append, List.length_cons, List.length_nil,
    hc, hd]
  rfl

def Lc.bestClass (L : Lc) : BitVec 8 := L.classWord.extractLsb' 56 8

def Lc.droppedNow (L : Lc) : Vector (BitVec 8) MAX_N :=
  ⟨(wordsBytes L.droppedWords.toList).toArray, by
    simp [wordsBytes_length, MAX_N]⟩

@[simp] theorem Lc.droppedNow_toList (L : Lc) :
    L.droppedNow.toList = wordsBytes L.droppedWords.toList := rfl

theorem Lc.set_pending (L : Lc) (w : Word) :
    L.toList.set 1 w = { L with pending := w }.toList := rfl

theorem Lc.set_classWord (L : Lc) (w : Word) :
    L.toList.set 2 w = { L with classWord := w }.toList := rfl

theorem Lc.set_excess (L : Lc) (w : Word) :
    L.toList.set 3 w = { L with excess := w }.toList := rfl

theorem Lc.set_pass (L : Lc) (w : Word) :
    L.toList.set 4 w = { L with pass := w }.toList := rfl

theorem Lc.set_count (L : Lc) (w : Word) :
    L.toList.set 5 w = { L with count := w }.toList := rfl

theorem Lc.set_candidate (L : Lc) (i : Nat) (hi : i < MAX_N) (w : Word) :
    L.toList.set (6 + i) w =
      { L with candidates := L.candidates.set i w }.toList := by
  simp only [Lc.toList, List.append_assoc]
  rw [List.set_append_right _ _ (by simp), List.length_cons, List.length_cons,
    List.length_cons, List.length_cons, List.length_cons, List.length_cons,
    List.length_nil, Nat.add_sub_cancel_left,
    List.set_append_left _ _ (by simpa using hi)]
  rfl

theorem Lc.set_droppedWord (L : Lc) (i : Nat) (hi : i < 128) (w : Word) :
    L.toList.set (1030 + i) w =
      { L with droppedWords := L.droppedWords.set i w }.toList := by
  simp only [Lc.toList, List.append_assoc]
  rw [List.set_append_right _ _ (by simp; omega), List.length_cons, List.length_cons,
    List.length_cons, List.length_cons, List.length_cons, List.length_cons,
    List.length_nil]
  have hn : 1030 + i - 6 = MAX_N + i := by simp [MAX_N]; omega
  rw [hn, List.set_append_right _ _ (by simp), Vector.length_toList,
    Nat.add_sub_cancel_left, List.set_append_left _ _ (by simpa using hi)]
  rfl

end FlatShuffler.Unit.ResolveU
