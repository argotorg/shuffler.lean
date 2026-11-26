import Skel.Discover.SpecFeatures
import Skel.Test.DiscoverSite

/-! The tests of `Skel/Discover/Features.lean` (suite `discoverfeatures`): `lake exe skel-test --only discoverfeatures`.
Each check is a value that must hold. A check that does not hold prints one `FAIL` line; the suite gives the number of
failed checks.

`poolOfFn` runs on each test site when this module is built (`pool%`), and the suite reads the pool as a value. The
sites are the functions of the suite `discoversite` and the functions below. `markLoop2` is `markLoop` with each field
and the structure renamed, and `swapLoop2` is `swapLoop` with each field and the structure renamed. -/

namespace DiscoverFeaturesTests

open Lean Skel.Gen Skel.Discover

/-! ## The test functions -/

/-- The state of the mark loop. `spare` is a field that the step never reads or writes. -/
structure MSt where
  v : Vector Nat 8
  i : Nat
  lim : Nat
  spare : Nat

/-- A loop that writes `0` at each nonzero element of `v` below `lim`. `lim` is read and not written. -/
def markLoop : Nat → MSt → Option Nat
  | 0, _ => none
  | n + 1, s =>
    if h : s.i < 8 then
      if s.i < s.lim then
        if s.v[s.i] = 0 then markLoop n { s with i := s.i + 1 }
        else markLoop n { s with v := s.v.set s.i 0 h, i := s.i + 1 }
      else some s.i
    else none

/-- `MSt` with each name changed. -/
structure MSt2 where
  tab : Vector Nat 8
  pos : Nat
  cap : Nat
  unused : Nat

/-- `markLoop` on `MSt2`. -/
def markLoop2 : Nat → MSt2 → Option Nat
  | 0, _ => none
  | n + 1, s =>
    if h : s.pos < 8 then
      if s.pos < s.cap then
        if s.tab[s.pos] = 0 then markLoop2 n { s with pos := s.pos + 1 }
        else markLoop2 n { s with tab := s.tab.set s.pos 0 h, pos := s.pos + 1 }
      else some s.pos
    else none

/-- The state of the inverse loop: two tables, and a count. -/
structure ISt where
  fwd : Vector Nat 8
  back : Vector Nat 8
  i : Nat

/-- A loop that writes `back[fwd[i]] := i`, so that `back` becomes the inverse of `fwd` on the values below 8. -/
def invLoop : Nat → ISt → Option ISt
  | 0, _ => none
  | n + 1, s =>
    if h : s.i < 8 then
      if hj : s.fwd[s.i] < 8 then invLoop n { s with back := s.back.set s.fwd[s.i] s.i hj, i := s.i + 1 }
      else none
    else some s

/-- A loop on a `UInt64` count and a parameter bound, with a guard `>` and a field written and never read. -/
structure WSt where
  pend : UInt64
  done : Nat
  last : Nat

def wordLoop (top : Nat) : Nat → WSt → Option Nat
  | 0, _ => none
  | n + 1, s =>
    if s.pend.toNat > top then none
    else if s.pend = 0 then some s.done
    else wordLoop top n { s with pend := s.pend - 1, done := s.done + 1, last := 7 }

/-! ### The sites of INV-D4b: moves, permutations, list elements, converted elements -/

/-- The state of the swap pass. -/
structure SSt where
  a : Vector Nat 8
  i : Nat
  m : Nat

/-- A selection-sort pass: it swaps `a[i]` and `a[m]` when `a[m]` is smaller. The step only permutes `a`. -/
def swapLoop : Nat → SSt → Option (Vector Nat 8)
  | 0, _ => none
  | n + 1, s =>
    if h : s.i < 8 then
      if hm : s.m < 8 then
        if s.a[s.m] < s.a[s.i] then swapLoop n { s with a := s.a.swap s.i s.m, i := s.i + 1 }
        else swapLoop n { s with i := s.i + 1 }
      else none
    else some s.a

/-- `SSt` with each name changed. -/
structure SSt2 where
  arr : Vector Nat 8
  pos : Nat
  low : Nat

/-- `swapLoop` on `SSt2`. -/
def swapLoop2 : Nat → SSt2 → Option (Vector Nat 8)
  | 0, _ => none
  | n + 1, s =>
    if h : s.pos < 8 then
      if hm : s.low < 8 then
        if s.arr[s.low] < s.arr[s.pos] then swapLoop2 n { s with arr := s.arr.swap s.pos s.low, pos := s.pos + 1 }
        else swapLoop2 n { s with pos := s.pos + 1 }
      else none
    else some s.arr

/-- The state of the cycle walk. -/
structure CSt where
  p : Vector Nat 8
  i : Nat

/-- A cycle sort: it exchanges `p[i]` and `p[p[i]]` by two writes, until `p[i] = i`. The step only permutes `p`. -/
def cycleLoop : Nat → CSt → Option (Vector Nat 8)
  | 0, _ => none
  | n + 1, s =>
    if h : s.i < 8 then
      if hj : s.p[s.i] < 8 then
        if s.p[s.i] = s.i then cycleLoop n { s with i := s.i + 1 }
        else cycleLoop n { s with p := (s.p.set s.i s.p[s.p[s.i]] h).set s.p[s.i] s.p[s.i] hj }
      else none
    else some s.p

/-- The state of the position loop, on arrays. -/
structure PSt where
  perm : Array Nat
  pos : Array Nat
  k : Nat

/-- A loop that writes `pos[perm[k]] := k`. -/
def posLoop : Nat → PSt → Option (Array Nat)
  | 0, _ => none
  | n + 1, s =>
    if s.k < s.perm.size then posLoop n { s with pos := s.pos.set! s.perm[s.k]! s.k, k := s.k + 1 }
    else some s.pos

/-- The state of the list loop. -/
structure LSt where
  xs : List UInt8
  hits : Nat

/-- A loop over a list with tests of the head, one of them under `toNat`. -/
def listLoop : Nat → LSt → Option Nat
  | 0, _ => none
  | n + 1, s =>
    match s.xs with
    | [] => some s.hits
    | x :: rest =>
      if x.toNat > 200 then none
      else if x = 0 then listLoop n { s with xs := rest, hits := s.hits + 1 }
      else listLoop n { s with xs := rest }

/-- The state of the seen loop. -/
structure NSt where
  xs : List Nat
  seen : Vector Bool 8

/-- A loop that marks each element of a list as an index into `seen`. -/
def seenLoop : Nat → NSt → Option (Vector Bool 8)
  | 0, _ => none
  | n + 1, s =>
    match s.xs with
    | [] => some s.seen
    | x :: rest => if h : x < 8 then seenLoop n { s with xs := rest, seen := s.seen.set x true h } else none

/-- The state of the fill loop. -/
structure FSt where
  b : Vector UInt8 8
  i : Nat

/-- A loop that writes new values (`b[i] + 1`) where a converted element is zero: not a permutation. -/
def fillLoop : Nat → FSt → Option (Vector UInt8 8)
  | 0, _ => none
  | n + 1, s =>
    if h : s.i < 8 then
      if s.b[s.i].toNat = 0 then fillLoop n { s with b := s.b.set s.i (s.b[s.i] + 1) h, i := s.i + 1 }
      else fillLoop n { s with i := s.i + 1 }
    else some s.b

/-- The state of the copy loop. -/
structure KSt where
  a : Vector Nat 8
  i : Nat
  j : Nat

/-- A loop that copies `a[j]` to `a[i]`: a move with no exchange, so not a permutation. -/
def copyLoop : Nat → KSt → Option (Vector Nat 8)
  | 0, _ => none
  | n + 1, s =>
    if h : s.i < 8 then
      if hj : s.j < 8 then copyLoop n { s with a := s.a.set s.i s.a[s.j] h, i := s.i + 1 }
      else none
    else some s.a

/-- Two writes of elements of `a` whose read indexes (`j`, `j`) are not the written indexes (`i`, `j`): `a[j]` is
copied to `a[i]`, so not a permutation. -/
def dupLoop : Nat → KSt → Option (Vector Nat 8)
  | 0, _ => none
  | n + 1, s =>
    if h : s.i < 8 then
      if hj : s.j < 8 then dupLoop n { s with a := (s.a.set s.i s.a[s.j] h).set s.j s.a[s.j] hj, i := s.i + 1 }
      else none
    else some s.a

/-- A loop that swaps in one branch and writes `0` in the other: not a permutation. -/
def mixLoop : Nat → SSt → Option (Vector Nat 8)
  | 0, _ => none
  | n + 1, s =>
    if h : s.i < 8 then
      if hm : s.m < 8 then
        if s.a[s.m] < s.a[s.i] then mixLoop n { s with a := s.a.swap s.i s.m, i := s.i + 1 }
        else mixLoop n { s with a := s.a.set s.i 0 h, i := s.i + 1 }
      else none
    else some s.a

/-! ## The pools, computed when this module is built -/

deriving instance ToExpr for Pred1
deriving instance ToExpr for L3Form
deriving instance ToExpr for L3In
deriving instance ToExpr for Feature
deriving instance ToExpr for ITerm
deriving instance ToExpr for BTerm
deriving instance ToExpr for Atom
deriving instance ToExpr for Pool

open Elab Term in
/-- `pool% f`: the pool of the site of `f`, read when the term is elaborated. A function with no site is an error. -/
elab "pool% " f:ident : term => do
  match ← poolOfFn f.getId with
  | .ok p => pure (toExpr p)
  | .error e => throwError "poolOfFn {f.getId}: {repr e}"

def countDownPool : Pool := pool% DiscoverSiteTests.countDown
def vecLoopPool : Pool := pool% DiscoverSiteTests.vecLoop
def branchLoopPool : Pool := pool% DiscoverSiteTests.branchLoop
def sumTwoPool : Pool := pool% DiscoverSiteTests.sumTwo
def markLoopPool : Pool := pool% DiscoverFeaturesTests.markLoop
def markLoop2Pool : Pool := pool% DiscoverFeaturesTests.markLoop2
def invLoopPool : Pool := pool% DiscoverFeaturesTests.invLoop
def wordLoopPool : Pool := pool% DiscoverFeaturesTests.wordLoop
def swapLoopPool : Pool := pool% DiscoverFeaturesTests.swapLoop
def swapLoop2Pool : Pool := pool% DiscoverFeaturesTests.swapLoop2
def cycleLoopPool : Pool := pool% DiscoverFeaturesTests.cycleLoop
def posLoopPool : Pool := pool% DiscoverFeaturesTests.posLoop
def listLoopPool : Pool := pool% DiscoverFeaturesTests.listLoop
def seenLoopPool : Pool := pool% DiscoverFeaturesTests.seenLoop
def fillLoopPool : Pool := pool% DiscoverFeaturesTests.fillLoop
def copyLoopPool : Pool := pool% DiscoverFeaturesTests.copyLoop
def mixLoopPool : Pool := pool% DiscoverFeaturesTests.mixLoop
def dupLoopPool : Pool := pool% DiscoverFeaturesTests.dupLoop

def pools : List (String × Pool) :=
  [("countDown", countDownPool), ("vecLoop", vecLoopPool), ("branchLoop", branchLoopPool), ("sumTwo", sumTwoPool),
    ("markLoop", markLoopPool), ("markLoop2", markLoop2Pool), ("invLoop", invLoopPool), ("wordLoop", wordLoopPool),
    ("swapLoop", swapLoopPool), ("swapLoop2", swapLoop2Pool), ("cycleLoop", cycleLoopPool), ("posLoop", posLoopPool),
    ("listLoop", listLoopPool), ("seenLoop", seenLoopPool), ("fillLoop", fillLoopPool), ("copyLoop", copyLoopPool),
    ("mixLoop", mixLoopPool), ("dupLoop", dupLoopPool)]

/-! ## Renaming -/

def renPred (r : String → String) : Pred1 → Pred1
  | .eqAt w => .eqAt (w.map r)
  | p => p

def renFeature (r : String → String) : Feature → Feature
  | .field p => .field (p.map r)
  | .len p => .len (p.map r)
  | .count v p => .count (v.map r) (renPred r p)
  | .sub a b => .sub (renFeature r a) (renFeature r b)
  | .add a b => .add (renFeature r a) (renFeature r b)
  | .scale k a => .scale k (renFeature r a)
  | .const n => .const n
  | .chainLen h off p => .chainLen (h.map r) off (p.map r)
  | .runTake l xs n => .runTake (l.rename r) (xs.map r) (renFeature r n)
  | .runDrop l xs n => .runDrop (l.rename r) (xs.map r) (renFeature r n)
  | .free t => .free t

def renAtom (r : String → String) : Atom → Atom
  | .le a b => .le (renFeature r a) (renFeature r b)
  | .lt a b => .lt (renFeature r a) (renFeature r b)
  | .eq a b => .eq (renFeature r a) (renFeature r b)
  | .forallBelow n v p => .forallBelow (renFeature r n) (v.map r) (renPred r p)
  | .inverse n v w => .inverse (renFeature r n) (v.map r) (w.map r)
  | .injOn n v => .injOn (renFeature r n) (v.map r)
  | .permSlice n v ref => .permSlice (renFeature r n) (v.map r) (pathText ((ref.splitOn ".").map r))
  | .frameEq p => .frameEq (p.map r)
  | .smt t => .smt t
  | .ends h off p => .ends (h.map r) off (p.map r)
  | .wordSum x g f => .wordSum (x.map r) (renFeature r g) (renFeature r f)
  | .heapIs mem ps run xs n first => .heapIs (mem.map r) (ps.map r) (r run) (xs.map r) (renFeature r n) first
  | .free t => .free t

def renPool (r : String → String) (p : Pool) : Pool :=
  { features := p.features.map fun (f, k) => (renFeature r f, k), atoms := p.atoms.map fun (a, k) => (renAtom r a, k) }

/-- The names of `MSt` to the names of `MSt2`. -/
def toMSt2 (s : String) : String :=
  match s with
  | "v" => "tab" | "i" => "pos" | "lim" => "cap" | "spare" => "unused" | _ => s

/-- The names of `SSt` to the names of `SSt2`. -/
def toSSt2 (s : String) : String :=
  match s with
  | "a" => "arr" | "i" => "pos" | "m" => "low" | _ => s

/-! ## The checks -/

def F (p : List String) : Feature := .field p
def st (f : String) : List String := ["st", f]

def hasF (p : Pool) (f : Feature) : Bool := p.features.any (·.1 == f)
def hasA (p : Pool) (a : Atom) : Bool := p.atoms.any (·.1 == a)

/-- The texts of the items of a pool. -/
def texts (p : Pool) : List String := p.features.map (·.1.text) ++ p.atoms.map (·.1.text)

/-- `t` contains `s`. -/
def has (t s : String) : Bool := (t.splitOn s).length > 1

/-- The frequencies do not rise along a list. -/
def falling {α : Type} : List (α × Nat) → Bool
  | a :: b :: rest => a.2 ≥ b.2 && falling (b :: rest)
  | _ => true

def checks : List (String × Bool) :=
  [ -- the guard differences
    ("vecLoop: the guard st.i < 8 gives the difference 8 - st.i", hasF vecLoopPool (.sub (.const 8) (F (st "i")))),
    ("vecLoop: the guard st.i < 8 gives the atom st.i ≤ 8", hasA vecLoopPool (.le (F (st "i")) (.const 8))),
    ("countDown: the guard st.k = 0 gives the feature st.k", hasF countDownPool (F (st "k"))),
    ("markLoop: the guard st.i < st.lim gives the difference st.lim - st.i",
      hasF markLoopPool (.sub (F (st "lim")) (F (st "i")))),
    ("wordLoop: the guard st.pend.toNat > top gives the difference st.pend.toNat - top",
      hasF wordLoopPool (.sub (F ["st", "pend", "toNat"]) (F ["top"]))),
    -- the fields and the lengths
    ("countDown: the written field st.acc is a feature", hasF countDownPool (F (st "acc"))),
    ("vecLoop: the parameter lim is a feature", hasF vecLoopPool (F ["lim"])),
    ("branchLoop: the length of the list st.fst is a feature", hasF branchLoopPool (.len (st "fst"))),
    ("branchLoop: the Fin field st.snd is a feature by its value", hasF branchLoopPool (F ["st", "snd", "val"])),
    ("sumTwo: the length of st.snd and the field st.fst are features",
      hasF sumTwoPool (.len (st "snd")) && hasF sumTwoPool (F (st "fst"))),
    ("vecLoop: the size of the vector st.v is a feature", hasF vecLoopPool (F ["st", "v", "size"])),
    ("wordLoop: the written field st.last, never read, is a feature", hasF wordLoopPool (F (st "last"))),
    -- the vector tests and writes
    ("markLoop: the test st.v[st.i] = 0 gives the count of the zeros",
      hasF markLoopPool (.count (st "v") .eqZero)),
    ("markLoop: the write of 0 at st.i gives ∀ i < st.i, st.v[i] = 0",
      hasA markLoopPool (.forallBelow (F (st "i")) (st "v") .eqZero)),
    ("markLoop: the test st.v[st.i] = 0 gives ∀ i < st.i, st.v[i] ≠ 0",
      hasA markLoopPool (.forallBelow (F (st "i")) (st "v") .neZero)),
    ("invLoop: the write back[fwd[i]] := i gives the inverse below st.i",
      hasA invLoopPool (.inverse (F (st "i")) (st "fwd") (st "back"))),
    ("invLoop: the write back[fwd[i]] := i gives the inverse below the size of fwd",
      hasA invLoopPool (.inverse (F ["st", "fwd", "size"]) (st "fwd") (st "back"))),
    -- the frame
    ("markLoop: the field lim, read and not written, gives frameEq", hasA markLoopPool (.frameEq (st "lim"))),
    ("invLoop: the table fwd, read and not written, gives frameEq", hasA invLoopPool (.frameEq (st "fwd"))),
    ("markLoop: the written fields v and i give no frameEq",
      !hasA markLoopPool (.frameEq (st "v")) && !hasA markLoopPool (.frameEq (st "i"))),
    ("countDown: no frameEq (each field is written)", countDownPool.atoms.all fun (a, _) => !(a matches .frameEq _)),
    ("vecLoop: the parameter lim gives no frameEq", !hasA vecLoopPool (.frameEq ["lim"])),
    -- negative: a field that the step never reads or writes
    ("markLoop: the field spare, never read or written, is in no feature and no atom",
      (texts markLoopPool).all (!has · "spare")),
    ("markLoop: the field spare gives no frameEq", !hasA markLoopPool (.frameEq (st "spare"))),
    ("markLoop2: the field unused is in no feature and no atom", (texts markLoop2Pool).all (!has · "unused")),
    -- renaming
    ("markLoop2 = markLoop with the names changed", renPool toMSt2 markLoopPool == markLoop2Pool),
    ("the renaming check fails for a wrong name map",
      renPool (fun s => if s == "lim" then "pos" else toMSt2 s) markLoopPool != markLoop2Pool),
    -- the frequencies
    ("the frequencies fall along each list of each pool",
      pools.all fun (_, p) => falling p.features && falling p.atoms),
    ("vecLoop: st.i is the first feature (the most frequent)", (vecLoopPool.features.head?.map (·.1)) == some (F (st "i"))),
    ("each item of each pool has a frequency of at least 1",
      pools.all fun (_, p) => p.features.all (·.2 ≥ 1) && p.atoms.all (·.2 ≥ 1)),
    ("no item occurs twice in a pool",
      pools.all fun (_, p) => (p.features.map (·.1)).eraseDups.length == p.features.length &&
        (p.atoms.map (·.1)).eraseDups.length == p.atoms.length),
    -- INV-D4b: permutations and moves
    ("swapLoop: the swap of a[i] and a[m] gives permSlice of a against the entry",
      hasA swapLoopPool (.permSlice (F ["st", "a", "size"]) (st "a") "st₀.a")),
    ("swapLoop: the swap of a[i] and a[m] gives injOn of a", hasA swapLoopPool (.injOn (F ["st", "a", "size"]) (st "a"))),
    ("cycleLoop: the exchange by two writes gives permSlice of p",
      hasA cycleLoopPool (.permSlice (F ["st", "p", "size"]) (st "p") "st₀.p")),
    ("cycleLoop: the exchange by two writes gives injOn of p", hasA cycleLoopPool (.injOn (F ["st", "p", "size"]) (st "p"))),
    ("copyLoop: the write a[i] := a[j] gives injOn of a", hasA copyLoopPool (.injOn (F ["st", "a", "size"]) (st "a"))),
    -- INV-D4b: an element used as an index
    ("posLoop: the write pos[perm[k]] := k gives the inverse below st.k",
      hasA posLoopPool (.inverse (F (st "k")) (st "perm") (st "pos"))),
    ("posLoop: the elements of perm as indexes give injOn of perm",
      hasA posLoopPool (.injOn (F ["st", "perm", "size"]) (st "perm"))),
    ("seenLoop: the head of xs as an index into seen gives injOn of xs",
      hasA seenLoopPool (.injOn (.len (st "xs")) (st "xs"))),
    -- INV-D4b: list elements and converted elements
    ("listLoop: the test x = 0 of the head of xs gives ∀ i < xs.length, xs[i] = 0 and ≠ 0",
      hasA listLoopPool (.forallBelow (.len (st "xs")) (st "xs") .eqZero) &&
        hasA listLoopPool (.forallBelow (.len (st "xs")) (st "xs") .neZero)),
    ("listLoop: the test x.toNat > 200 of the head of xs gives ∀ i < xs.length, xs[i] ≤ 200",
      hasA listLoopPool (.forallBelow (.len (st "xs")) (st "xs") (.le 200))),
    ("listLoop: a list gives no count (its text needs a size)",
      listLoopPool.features.all fun (f, _) => !(f matches .count ..)),
    ("fillLoop: the test b[i].toNat = 0 gives the count of the zeros of b", hasF fillLoopPool (.count (st "b") .eqZero)),
    ("fillLoop: the test b[i].toNat = 0 gives ∀ i < st.i, b[i] = 0 and ≠ 0",
      hasA fillLoopPool (.forallBelow (F (st "i")) (st "b") .eqZero) &&
        hasA fillLoopPool (.forallBelow (F (st "i")) (st "b") .neZero)),
    -- INV-D4b: negative
    ("fillLoop: the write of a new value gives no permSlice and no injOn",
      fillLoopPool.atoms.all fun (a, _) => !(a matches .permSlice .. || a matches .injOn ..)),
    ("copyLoop: a move with no exchange gives no permSlice",
      copyLoopPool.atoms.all fun (a, _) => !(a matches .permSlice ..)),
    ("mixLoop: a swap in one branch and a write of 0 in the other gives no permSlice",
      mixLoopPool.atoms.all fun (a, _) => !(a matches .permSlice ..)),
    ("dupLoop: two moves whose read indexes are not the written indexes give no permSlice",
      dupLoopPool.atoms.all fun (a, _) => !(a matches .permSlice ..)),
    ("dupLoop: the two moves give injOn of a with the frequency 2",
      dupLoopPool.atoms.contains (.injOn (F ["st", "a", "size"]) (st "a"), 2)),
    ("posLoop: the write of k into pos gives no permSlice", posLoopPool.atoms.all fun (a, _) => !(a matches .permSlice ..)),
    ("markLoop: no permSlice and no injOn",
      markLoopPool.atoms.all fun (a, _) => !(a matches .permSlice .. || a matches .injOn ..)),
    -- INV-D4b: renaming
    ("swapLoop2 = swapLoop with the names changed", renPool toSSt2 swapLoopPool == swapLoop2Pool),
    ("the renaming check of swapLoop fails for a wrong name map",
      renPool (fun s => if s == "m" then "pos" else toSSt2 s) swapLoopPool != swapLoop2Pool),
    -- the size
    ("each pool has fewer than 60 items", pools.all fun (_, p) => p.size < 60),
    ("each pool is not empty", pools.all fun (_, p) => p.size > 0) ]

/-- One line per pool: its name and its size. -/
def sizes : String := ", ".intercalate (pools.map fun (n, p) => s!"{n} {p.size}")

/-- Gives the number of failed checks. The suite runs when `only` is none or `discoverfeatures`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoverfeatures" then return 0
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoverfeatures: {name}"
  IO.println s!"discoverfeatures: pool sizes: {sizes}"
  return failed

end DiscoverFeaturesTests
