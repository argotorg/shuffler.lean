module

public import BbuKraken.FlatModel
import all BbuKraken.FlatModel

@[expose] public section

/-!
# The loops of `Flat.ctor`

The constructor of `Emission` has three loops. Each loop writes one or two members, and the asm
runs each loop one offset at a time. Here each loop is a fold over the first `k` offsets on the
members that it writes (`clearPos`, `bindDest`, `bindPos`, `countNone`), with the step lemmas for
`k + 1`. `ctor_folds` gives `ctor` with these folds.
-/

namespace Bbu.Flat

-- The first `k` offsets.
def offs (k : Nat) : List Word := (List.range k).map (BitVec.ofNat 64)

theorem offs_zero : offs 0 = [] := rfl

theorem offs_succ (k : Nat) : offs (k + 1) = offs k ++ [BitVec.ofNat 64 k] := by
  simp only [offs, List.range_succ, List.map_append, List.map_cons, List.map_nil]

-- The first loop: `m_positionOf[d] = NONE` for the first `k` offsets.
def clearPos (k : Nat) (p : Vector Word MAX_N) : Vector Word MAX_N :=
  (offs k).foldl (fun p d => put p d NONE) p

-- The second loop: `bind(p, dests[p])` for the first `k` offsets.
def bindDest (dests : Vector Word MAX_N) (k : Nat) (d : Vector Word MAX_N) : Vector Word MAX_N :=
  (offs k).foldl (fun d p => put d p (get dests p)) d

def bindPos (dests : Vector Word MAX_N) (k : Nat) (q : Vector Word MAX_N) : Vector Word MAX_N :=
  (offs k).foldl (fun q p => put q (get dests p) p) q

-- The third loop: the count of the first `k` offsets with no position.
def countNone (pos : Vector Word MAX_N) (k : Nat) (e : Word) : Word :=
  (offs k).foldl (fun e d => if get pos d = NONE then e + 1 else e) e

section
variable (dests p d q pos : Vector Word MAX_N) (e : Word)

@[simp] theorem clearPos_zero : clearPos 0 p = p := rfl
@[simp] theorem bindDest_zero : bindDest dests 0 d = d := rfl
@[simp] theorem bindPos_zero : bindPos dests 0 q = q := rfl
@[simp] theorem countNone_zero : countNone pos 0 e = e := rfl

theorem clearPos_succ (k : Nat) :
    clearPos (k + 1) p = put (clearPos k p) (BitVec.ofNat 64 k) NONE := by
  simp only [clearPos, offs_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem bindDest_succ (k : Nat) :
    bindDest dests (k + 1) d
      = put (bindDest dests k d) (BitVec.ofNat 64 k) (get dests (BitVec.ofNat 64 k)) := by
  simp only [bindDest, offs_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem bindPos_succ (k : Nat) :
    bindPos dests (k + 1) q
      = put (bindPos dests k q) (get dests (BitVec.ofNat 64 k)) (BitVec.ofNat 64 k) := by
  simp only [bindPos, offs_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem countNone_succ (k : Nat) :
    countNone pos (k + 1) e
      = if get pos (BitVec.ofNat 64 k) = NONE then countNone pos k e + 1 else countNone pos k e := by
  simp only [countNone, offs_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

end

/-! ## The folds on the state -/

private theorem foldl_clearPos (l : List Word) (st : St) :
    l.foldl (fun st d => { st with pos := put st.pos d NONE }) st
      = { st with pos := l.foldl (fun p d => put p d NONE) st.pos } := by
  induction l generalizing st with
  | nil => rfl
  | cons x l ih => exact ih _

private theorem foldl_bind (dests : Vector Word MAX_N) (l : List Word) (st : St) :
    l.foldl (fun st p => bind st p (get dests p)) st
      = { st with dest := l.foldl (fun d p => put d p (get dests p)) st.dest,
                  pos := l.foldl (fun q p => put q (get dests p) p) st.pos } := by
  induction l generalizing st with
  | nil => rfl
  | cons x l ih => exact ih _

private theorem foldl_count (l : List Word) (st : St) :
    l.foldl (fun st d => if get st.pos d = NONE then { st with pend := st.pend + 1 } else st) st
      = { st with pend := l.foldl (fun e d => if get st.pos d = NONE then e + 1 else e) st.pend } := by
  induction l generalizing st with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    split
    · exact ih _
    · exact ih _

-- `ctor` with the three folds.
theorem ctor_folds (data : Vector StackSlot MAX_N) (m : Word) (target : Vector StackSlot MAX_N)
    (n : Word) (dests : Vector Word MAX_N) (spills : BitVec 32 → BitVec 8) (u : Uninit) :
    ctor data m target n dests spills u =
      { target, targetSize := n, spills, data, size := m, trace := [],
        dest := bindDest dests m.toNat u.dest,
        pos := bindPos dests m.toNat (clearPos n.toNat u.pos),
        pend := countNone (bindPos dests m.toNat (clearPos n.toNat u.pos)) n.toNat 0,
        blockedOffset := u.blockedOffset, blockedExcess := u.blockedExcess } := by
  simp only [ctor, foldl_clearPos, foldl_bind, foldl_count]
  rfl

/-! ## `get` and `put` below `MAX_N` -/

theorem get_of_lt {α : Type} [Inhabited α] (v : Vector α MAX_N) {i : Word} (hi : i.toNat < MAX_N) :
    get v i = v[i.toNat] := by
  simp only [get, hi, ↓reduceDIte]

theorem put_of_lt {α : Type} (v : Vector α MAX_N) {i : Word} (hi : i.toNat < MAX_N) (x : α) :
    put v i x = v.set i.toNat x hi := by
  ext j hj; simp [put, Vector.getElem_set, Vector.getElem_setIfInBounds]

end Bbu.Flat
