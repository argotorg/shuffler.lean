/-! A pure splitmix64 generator. The state is a value; each draw returns the next state.
A draw has no hidden input, so a seed fixes every result. -/

namespace Coordinator.Dst

structure Rng where
  state : UInt64
  deriving DecidableEq, Repr

namespace Rng

/-- Constant added to the state at each draw. -/
def gamma : UInt64 := 0x9E3779B97F4A7C15

/-- The splitmix64 output function. -/
def mix (z : UInt64) : UInt64 :=
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

def ofSeed (seed : Nat) : Rng := ⟨seed.toUInt64⟩

/-- One 64-bit draw and the next state. -/
def next (r : Rng) : UInt64 × Rng :=
  let state := r.state + gamma
  (mix state, ⟨state⟩)

/-- Two independent generators: the advanced state, and one seeded from a draw. -/
def split (r : Rng) : Rng × Rng :=
  let (draw, r) := r.next
  (r, ⟨draw⟩)

/-- The generator of stream `i`. Stream `i` does not depend on the draws of other streams. -/
def stream (r : Rng) (i : Nat) : Rng :=
  ⟨(Rng.mk (r.state + gamma * i.toUInt64)).next.1⟩

/-- A number below `bound`, for a bound up to 2^64. A zero bound gives zero. -/
def nat (r : Rng) (bound : Nat) : Nat × Rng :=
  let (draw, r) := r.next
  (if bound = 0 then 0 else draw.toNat % bound, r)

/-- A number from `lo` to `hi`, both included. -/
def natIn (r : Rng) (lo hi : Nat) : Nat × Rng :=
  let (n, r) := r.nat (hi + 1 - lo)
  (lo + n, r)

def bool (r : Rng) : Bool × Rng :=
  let (n, r) := r.nat 2
  (n == 1, r)

/-- A member of a list that has at least one element. -/
def pick {α : Type} (r : Rng) (first : α) (rest : List α) : α × Rng :=
  let (n, r) := r.nat (rest.length + 1)
  ((first :: rest).getD n first, r)

/-- A member chosen by weight. If all weights are zero, the result is the first member. -/
def weighted {α : Type} (r : Rng) (first : Nat × α) (rest : List (Nat × α)) : α × Rng :=
  let choices := first :: rest
  let (n, r) := r.nat (choices.foldl (fun sum (w, _) => sum + w) 0)
  let rec go : Nat → List (Nat × α) → α
    | _, [] => first.2
    | n, (w, x) :: more => if n < w then x else go (n - w) more
  (go n choices, r)

end Rng

end Coordinator.Dst
