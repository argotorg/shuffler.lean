import Lift.Sem.HeapFast
import Coordinator.Dst.Rng

/-! The timing of `Heap.load`, `Heap.store` and `Heap.loadB` on objects of N W64 cells (suite `heaptime`):
`lake exe skel-test --only heaptime`. Cell `j` holds `val j` at the address `addrOf j`. The objects of a heap
are contiguous, so the address of each cell is the same in every case; only the grouping into objects differs.
The checks are on the results only: each load gives the value of its cell, each store gives `.ok` in each object,
and each byte load at offset 4 of a cell gives the byte of the cell. A check that does not hold prints one `FAIL`
line. The timings print one line per case and do not fail the suite. -/

namespace HeapTimeTests

open Lift.Sem Coordinator.Dst

/-- The calls of each case: loads, stores, and byte loads of the fallback path of `Heap.loadB`. -/
def loads : Nat := 1000
def stores : Nat := 100
def byteLoads : Nat := 100

/-- The address of cell 0. -/
def base : BitVec 64 := 0x100000

/-- The address of cell `j`. -/
def addrOf (j : Nat) : BitVec 64 := base + BitVec.ofNat 64 (8 * j)

/-- The value of cell `j`. Its byte 4 is `j mod 256` for `j < 2^32`. -/
def val (j : Nat) : BitVec 64 := BitVec.ofNat 64 (j * 0x100000001)

/-- The heap of `n` cells in objects of `per` cells: object `k` holds the cells `per * k` to `per * k + per - 1`. -/
def heapOf (n per : Nat) : Heap :=
  (List.range (n / per)).map fun k =>
    Obj.words (addrOf (per * k)) true .W64 ((List.range per).map fun i => val (per * k + i))

/-- `count` cell indices below `n`, drawn from the generator `g`. -/
def drawIdx (n : Nat) : Nat → Rng → List Nat
  | 0, _ => []
  | k + 1, g =>
    let (i, g') := g.nat n
    i :: drawIdx n k g'

/-- The number of the indices `j` whose load gives `val j`. -/
def loadHits (h : Heap) (js : List Nat) : Nat :=
  js.foldl (fun n j => match h.load (addrOf j) .W64 with
    | .ok v => if v == val j then n + 1 else n
    | _ => n) 0

/-- The sum, over the indices `j`, of the number of objects of the heap after a store at `j`: a store that
gives `.ok` gives a heap with the objects of `h`. -/
def storeHits (h : Heap) (js : List Nat) : Nat :=
  js.foldl (fun n j => match h.store (addrOf j) .W64 (val (j + 1)) with
    | .ok h' => n + h'.length
    | _ => n) 0

/-- The number of the indices `j` whose byte load at offset 4 gives the byte `j mod 256` of cell `j`. -/
def byteHits (h : Heap) (js : List Nat) : Nat :=
  js.foldl (fun n j => match h.loadB (addrOf j + 4) .W8 with
    | .ok v => if v == BitVec.ofNat 8 (j % 256) then n + 1 else n
    | _ => n) 0

/-- Runs `f`, which gives a count that must be `expected`. Returns whether the count is `expected` and the time of
the run in nanoseconds. A count that differs prints a `FAIL` line. The count is read before the second clock read,
so the run is inside the time. -/
@[noinline] def timed (name : String) (expected : Nat) (f : Unit → Nat) : IO (Bool × Nat) := do
  let t0 ← IO.monoNanosNow
  let n := f ()
  if n != expected then IO.println s!"FAIL  heaptime: {name}: {n} of {expected} held"
  let t1 ← IO.monoNanosNow
  return (n == expected, t1 - t0)

/-- The time per call in microseconds, with three decimals. -/
def perCallUs (ns calls : Nat) : String :=
  let x := ns / calls
  let frac := toString (x % 1000)
  s!"{x / 1000}.{"".pushn '0' (3 - frac.length)}{frac}"

/-- Times one case: `n` cells in objects of `per` cells. Gives the number of failed checks and the lines. -/
def runCase (n per : Nat) (seed : Rng) : IO (Nat × List String) := do
  let h := heapOf n per
  let objs := n / per
  let loadJs := drawIdx n loads (seed.stream 1)
  let storeJs := drawIdx n stores (seed.stream 2)
  let (lOk, lNs) ← timed s!"load N={n} objs={objs}" loads fun _ => loadHits h loadJs
  let (sOk, sNs) ← timed s!"store N={n} objs={objs}" (stores * objs) fun _ => storeHits h storeJs
  let line := s!"heaptime: N={n} objs={objs} load_us={perCallUs lNs loads} store_us={perCallUs sNs stores}"
  if per != n then return ((if lOk && sOk then 0 else 1), [line])
  let byteJs := drawIdx n byteLoads (seed.stream 3)
  let (bOk, bNs) ← timed s!"loadB N={n}" byteLoads fun _ => byteHits h byteJs
  let byteLine := s!"heaptime: N={n} objs={objs} loadB_w8_us={perCallUs bNs byteLoads}"
  return ((if lOk && sOk && bOk then 0 else 1), [line, byteLine])

/-- Gives the number of failed checks. The suite runs when `only` is none or `heaptime`. The default run has the
cases of up to 512 cells (about 1 s). `--only heaptime` adds the cases of 2048 to 51200 cells (about 85 s). -/
def run (seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "heaptime" then return 0
  let t0 ← IO.monoMsNow
  let ns := if only.isSome then [64, 512, 2048, 4096, 8192, 51200] else [64, 512]
  let g := Rng.ofSeed seed
  let mut failed := 0
  for n in ns do
    for per in (if n == 64 then [64] else [n, 64]) do
      let (f, lines) ← runCase n per g
      failed := failed + f
      for l in lines do IO.println l
  IO.println s!"heaptime: suite {(← IO.monoMsNow) - t0} ms"
  return failed

end HeapTimeTests
