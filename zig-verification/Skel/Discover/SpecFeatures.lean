import Skel.Discover.Features

/-! The spec items of a machine loop site (task INV-D4c): features and atoms from the inputs of the problem, the L3
function, the L3 input, the L2⁺ relation (`heapOf`) and the classes of the state registers. They are the same rules for
each site; no rule names a function, a label or a fixture. `withSpec` adds them to the pool of D4 (`machinePoolOf`).

The context (`SpecCtx`) holds the names of the slot of the loop row: the list `xs` of the L3 input, the heap of the input,
the counters and the accumulators of the state (as paths below the state `st`), the chain ghosts (a pointer register and
the offset of its next word), and the result kind. Let `L` be `xs.length` and, for a counter `i`, `n_i` its value
`st.i.toNat`.

The rules:
- prefix and suffix of the L3 function: for a value result, the features `run (xs.take n_i)` and `run (xs.drop n_i)`
  (`Feature.runTake`, `runDrop`), with the input form of the statement. The part of the input that the loop has read and
  the part that is left.
- the list: the feature `L`, and for each counter the feature `L - n_i` (the length of `xs.drop n_i`).
- register and feature: for each counter, the atoms `n_i ≤ L` and `n_i = L`.
- heap object: for a heap result of a list input, for each counter, the atoms `st.mem = heapOf <params> frame (r.take n_i
  ++ xs.drop n_i)` and `st.mem = heapOf <params> frame (xs.take n_i ++ r.drop n_i)`, with `r` the L3 result of `xs`. The
  object holds the result below the counter and the input above it, or the other way round.
- ghost length: for each chain ghost from the pointer `q` at the offset `off`, the feature `(chain heap off q).length`, the
  atom `ends heap off q = true` (its defining equation: the walk reaches `0`, so the chain is defined and each step drops
  its head), and for each accumulator `c` the atom `st.c + UInt64.ofNat (chain heap off q).length = UInt64.ofNat L`
  (`Atom.wordSum`: the sum is in the word type of the register, which wraps).

Each item has the frequency of the number of rules that give it. `withSpec` adds the frequencies of an item that the pool
has, sorts each list by falling frequency (the base items first for one frequency), and keeps at most `maxPool` items:
at most `maxFeatures` features, then atoms up to `maxPool` (the limits of `Skel/Discover/Features.lean`). The order does not depend on the names: a context and a pool
with other names give the same pool with the other names (`SpecCtx.rename`). -/

namespace Skel.Discover

/-- The result of the function, as the spec items read it: a value, a heap (the memory field of the state and the
parameters of `heapOf`), or another kind. -/
inductive SpecResult where
  | value
  | heap (mem : List String) (params : List String)
  | other
  deriving DecidableEq, Repr

/-- The inputs of the problem that the spec items read (see the top of the file). -/
structure SpecCtx where
  l3 : L3In
  xs : List String
  heap : List String
  counters : List (List String)
  accumulators : List (List String)
  ghosts : List (List String × Nat)
  result : SpecResult
  deriving DecidableEq, Repr

/-- The value of a word register as a `Nat`. -/
def wordNat (r : List String) : Feature := .field (r ++ ["toNat"])

/-- The spec features and atoms of the context, in the order of the rules, each once for each rule that gives it. -/
def specItems (c : SpecCtx) : List Feature × List Atom :=
  let len : Feature := .len c.xs
  let idx := c.counters.map wordNat
  let runs : List Feature := match c.result with
    | .value => idx.flatMap fun n => [.runTake c.l3 c.xs n, .runDrop c.l3 c.xs n]
    | _ => []
  let chains := c.ghosts.map fun (q, off) => (q, off, Feature.chainLen c.heap off q)
  let feats := runs ++ [len] ++ idx.map (Feature.sub len ·) ++ chains.map (·.2.2)
  let heapAtoms : List Atom := match c.result, c.l3.form with
    | .heap mem ps, .list => idx.flatMap fun n => [.heapIs mem ps c.l3.run c.xs n true, .heapIs mem ps c.l3.run c.xs n false]
    | _, _ => []
  let atoms := idx.flatMap (fun n => [Atom.le n len, Atom.eq n len]) ++ heapAtoms ++
    chains.flatMap fun (q, off, g) => Atom.ends c.heap off q :: c.accumulators.map fun r => Atom.wordSum r g len
  (feats, atoms)

/-- `xs` with the frequency of `x` raised by `k`, or `x` at the end with the frequency `k`. -/
private def addFreq {α : Type} [BEq α] (xs : List (α × Nat)) (x : α) (k : Nat) : List (α × Nat) :=
  if xs.any (·.1 == x) then xs.map fun (a, j) => if a == x then (a, j + k) else (a, j) else xs ++ [(x, k)]

/-- The items of `ys` added to `xs`, each occurrence with the frequency one, then sorted by falling frequency. -/
private def merge {α : Type} [BEq α] (xs : List (α × Nat)) (ys : List α) : List (α × Nat) :=
  byFrequency (ys.foldl (fun acc y => addFreq acc y 1) xs)

/-- The pool `p` with the spec items of `c` (see the top of the file). -/
def withSpec (c : SpecCtx) (p : Pool) : Pool :=
  let (fs, as) := specItems c
  let features := (merge p.features fs).take maxFeatures
  { features, atoms := (merge p.atoms as).take (maxPool - features.length) }

/-! ## Renaming -/

/-- The L3 input with each name renamed by `r`. The function name is one name. -/
def L3In.rename (r : String → String) (l : L3In) : L3In :=
  { run := r l.run,
    form := match l.form with
      | .list => .list
      | .record ty f ss => .record (r ty) (r f) (ss.map r)
      | .flat ns l => .flat (ns.map r) (r l) }

/-- The context with each name renamed by `r`. -/
def SpecCtx.rename (r : String → String) (c : SpecCtx) : SpecCtx :=
  { l3 := c.l3.rename r, xs := c.xs.map r, heap := c.heap.map r, counters := c.counters.map (·.map r),
    accumulators := c.accumulators.map (·.map r), ghosts := c.ghosts.map fun (q, k) => (q.map r, k),
    result := match c.result with
      | .heap mem ps => .heap (mem.map r) (ps.map r)
      | k => k }

end Skel.Discover
