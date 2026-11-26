import Skel.Discover.SpecFeatures
import Skel.Toy.UpperDiscover
import Skel.Test.DiscoverLang
import Skel.Test.DiscoverClose
import Skel.Test.DiscoverFeatures
import Skel.Test.DiscoverLadder

/-! The tests of `Skel/Discover/SpecFeatures.lean` (suite `discoverspec`, task INV-D4c): `lake exe skel-test --only
discoverspec`. Each check is a value that must hold; a check that does not hold prints one `FAIL` line.

- the rules on fixed contexts, by kind: each result kind gives its items, and no other;
- the renaming property: a context and a pool with renamed names give the renamed pool (random contexts and pools);
- the production pools (`Machine.pool`, a Lean process on the model text) of `toyFind`, `toyWalk` and `toyFill` hold the spec
  items, by kind, and have fewer than 60 items;
- the trace of `toyFill` (D3, with the lets of the slot) evaluates the spec items on concrete states;
- a mutant of `toyFill` that stores `i + 1` at the index `i` (its loop does not follow the spec) gives no closed quad. -/

namespace DiscoverSpecTests

open Skel Skel.Discover DiscoverLangTests

/-! ## The kinds -/

def isRunVal : Feature → Bool
  | .runTake .. | .runDrop .. => true
  | _ => false

def isChainLen : Feature → Bool
  | .chainLen .. => true
  | _ => false

def isEnds : Atom → Bool
  | .ends .. => true
  | _ => false

def isWordSum : Atom → Bool
  | .wordSum .. => true
  | _ => false

def isHeapIs : Atom → Bool
  | .heapIs .. => true
  | _ => false

/-- A register = feature equality: the value of a register of the state is the length of the L3 list. -/
def isRegEq (xs : List String) : Atom → Bool
  | .eq (.field (_ :: _ :: ["toNat"])) (.len l) => l == xs
  | _ => false

/-! ## The fixed contexts -/

def l3List : L3In := { run := "M.run", form := .list }

def ctxValue : SpecCtx :=
  { l3 := { run := "M.run", form := .record "M.In" "xs" ["key"] }, xs := ["xs"], heap := ["a", "heap"],
    counters := [["st", "rcx"], ["st", "rax"]], accumulators := [], ghosts := [], result := .value }

def ctxChain : SpecCtx :=
  { l3 := l3List, xs := ["xs"], heap := ["a", "heap"], counters := [], accumulators := [["st", "rax"]],
    ghosts := [(["st", "rdi"], 8)], result := .value }

def ctxHeap : SpecCtx :=
  { l3 := l3List, xs := ["xs"], heap := ["a", "heap"], counters := [["st", "rax"]], accumulators := [], ghosts := [],
    result := .heap ["st", "mem"] ["p"] }

def fixedChecks : List (String × Bool) :=
  let (fv, av) := specItems ctxValue
  let (fc, ac) := specItems ctxChain
  let (fh, ah) := specItems ctxHeap
  [ ("value: prefix and suffix of the L3 function for each counter", (fv.filter isRunVal).length == 4),
    ("value: a register = feature equality for each counter", (av.filter (isRegEq ["xs"])).length == 2),
    ("value: no heap, ghost or word-sum item", !av.any isHeapIs && !av.any isEnds && !av.any isWordSum && !fv.any isChainLen),
    ("value: the text of the suffix of a record input",
      (Feature.runDrop ctxValue.l3 ["xs"] (wordNat ["st", "rcx"])).text ==
        "((M.run ({ xs := xs.drop st.rcx.toNat, key := key } : M.In)).getD 0).toNat"),
    ("chain: the ghost length, its defining equation, the word sum of the accumulator",
      fc.any isChainLen && ac.any isEnds && ac.any isWordSum),
    ("chain: the text of the word sum",
      (ac.find? isWordSum).map Atom.text ==
        some "st.rax + UInt64.ofNat (Lift.Sem.Heap.chain a.heap 8 st.rdi.toBitVec).length = UInt64.ofNat xs.length"),
    ("chain: no counter, so no register = feature equality", !ac.any (isRegEq ["xs"])),
    ("heap: two heap atoms for the counter, no L3 value feature", (ah.filter isHeapIs).length == 2 && !fh.any isRunVal),
    ("heap: the text of the heap atom",
      (ah.find? isHeapIs).map Atom.text ==
        some "st.mem = heapOf p frame (((M.run xs).getD []).take st.rax.toNat ++ xs.drop st.rax.toNat)"),
    ("heap: a record input gives no heap atom",
      !(specItems { ctxHeap with l3 := ctxValue.l3 }).2.any isHeapIs),
    ("the pool keeps fewer than 60 items",
      (withSpec ctxValue { features := (List.range 50).map fun i => (.const i, 1),
                           atoms := (List.range 50).map fun i => (.le (.const i) (.const 0), 1) }).size < 60),
    ("an item of the pool and of a rule has the sum of the frequencies",
      ((withSpec ctxHeap { features := [(.len ["xs"], 2)], atoms := [] }).features.find? (·.1 == .len ["xs"])).map (·.2) ==
        some 3) ]

/-! ## The renaming property -/

/-- The renaming of the property: each generated name gets a prefix, other names (`st`, `toNat`) stay. -/
def ren (s : String) : String := if names.contains s && s != "st" && s != "toNat" then "q_" ++ s else s

def renPool := DiscoverFeaturesTests.renPool
def genPaths : Nat → G (List (List String))
  | 0 => pure []
  | n + 1 => do
    let p ← genPath
    let ps ← genPaths n
    pure (p :: ps)

def genForm : G L3Form := do
  match ← draw 3 with
  | 0 => pure .list
  | 1 => do pure (.record (← genName) (← genName) (← genNames (← draw 3)))
  | _ => do pure (.flat (← genNames (← draw 3)) (← genName))

def genCtx : G SpecCtx := do
  let l3 : L3In := { run := ← genName, form := ← genForm }
  let xs ← genPath
  let heap ← genPath
  let counters ← genPaths (← draw 3)
  let accumulators ← genPaths (← draw 3)
  let ghosts ← (← genPaths (← draw 2)).mapM fun q => do pure (q, 8 * (← draw 3))
  let result ← match ← draw 3 with
    | 0 => pure SpecResult.value
    | 1 => do pure (SpecResult.heap (← genPath) (← genNames (← draw 3)))
    | _ => pure SpecResult.other
  pure { l3, xs, heap, counters, accumulators, ghosts, result }

def genPool : G Pool := do
  let fs ← (List.range (← draw 6)).mapM fun _ => do pure (← genFeature 2, 1 + (← draw 3))
  let ats ← (List.range (← draw 6)).mapM fun _ => do pure (← genAtom, 1 + (← draw 3))
  pure { features := fs, atoms := ats }

def propertyChecks (seed cases : Nat) : List (String × Bool) :=
  let bad := (List.range cases).filter fun k =>
    let ds := ParseTests.draws (seed + k * 7919) 600
    let ((c, p), _) := (do pure (← genCtx, ← genPool) : G (SpecCtx × Pool)).run ds
    withSpec (c.rename ren) (renPool ren p) != renPool ren (withSpec c p)
  [ (s!"renaming: a renamed context and pool give the renamed pool ({cases} cases; first bad {bad.head?})", bad.isEmpty) ]

/-! ## The production pools -/

def cfg : Skel.Config := { gate := .strict, limitMs := 180000, seed := 1, samples := 200, useTemplates := false, discover := true }

/-- The pool of the loop row of `fn` from the production path, or the error. -/
def poolOf (fn : String) : IO (Except String Pool) := do
  let dir ← DiscoverCloseTests.newDir s!"spec-pool-{fn}"
  match Skel.Toy.UpperDiscover.machineOf cfg fn dir with
  | .error e => pure (.error e)
  | .ok m => m.pool

def poolChecks : IO (List (String × Bool)) := do
  let find ← poolOf "toyFind"
  let walk ← poolOf "toyWalk"
  let fill ← poolOf "toyFill"
  let on (r : Except String Pool) (f : Pool → Bool) : Bool := match r with
    | .ok p => f p
    | .error _ => false
  let err (r : Except String Pool) : String := match r with
    | .ok _ => ""
    | .error e => (e.take 200).toString
  pure
    [ (s!"toyFind: a prefix or suffix value of the L3 function {err find}", on find fun p => p.features.any (isRunVal ·.1)),
      ("toyFind: a register = feature equality with the L3 list", on find fun p => p.atoms.any (isRegEq ["xs"] ·.1)),
      (s!"toyWalk: a ghost chain length {err walk}", on walk fun p => p.features.any (isChainLen ·.1)),
      ("toyWalk: the defining equation of the ghost", on walk fun p => p.atoms.any (isEnds ·.1)),
      ("toyWalk: the word sum of the accumulator and the ghost", on walk fun p => p.atoms.any (isWordSum ·.1)),
      (s!"toyFill: a heap-object atom {err fill}", on fill fun p => p.atoms.any (isHeapIs ·.1)),
      ("toyFill: no L3 value feature (a heap result)", on fill fun p => !p.features.any (isRunVal ·.1)),
      ("the three pools have fewer than 60 items", [find, walk, fill].all fun r => on r (·.size < 60)) ]

/-! ## The trace and the mutant -/

/-- The trace of `toyFill` evaluates the heap atoms: the atom with the result below the counter is true at each visit, and the
atom with the input below the counter is false at a visit. -/
def traceChecks : IO (List (String × Bool)) := do
  let dir ← DiscoverCloseTests.newDir "spec-trace-fill"
  match Skel.Toy.UpperDiscover.machineOf cfg "toyFill" dir with
  | .error e => pure [(s!"trace: the machine: {e}", false)]
  | .ok m =>
    match ← m.pool with
    | .error e => pure [(s!"trace: the pool: {e}", false)]
    | .ok p =>
      match ← (m.env p).trace Store.empty with
      | .error e => pure [(s!"trace: the trace ran: {(e.take 300).toString}", false)]
      | .ok inj =>
        let atoms := p.atoms.map (·.1)
        let at? (first : Bool) : Option Nat := atoms.findIdx? fun
          | .heapIs _ _ _ _ _ f => f == first
          | _ => false
        let t := inj.all
        let truths (i : Nat) : List Bool := t.filterMap (·.atoms[i]?)
        pure
          [ ("trace: the trace has visits", !t.isEmpty),
            ("trace: the result below the counter holds at each visit",
              (at? true).any fun i => (truths i).length == t.length && (truths i).all id),
            ("trace: the input below the counter is false at a visit", (at? false).any fun i => (truths i).any (!·)) ]

/-- `toyFill` with the store of `i + 1` at the index `i`. -/
def fillMutant (s : String) : String := s.replace ".W64 x.rax.toBitVec with" ".W64 (x.rax + 1).toBitVec with"

def mutantChecks : IO (List (String × Bool)) := do
  let dir ← DiscoverCloseTests.newDir "spec-mutant-fill"
  let changed := match Skel.Toy.UpperDiscover.machineOf cfg "toyFill" dir fillMutant with
    | .ok m => (m.gen.modelText.splitOn "(x.rax + 1).toBitVec with").length > 1
    | .error _ => false
  match ← Skel.Toy.UpperDiscover.discover cfg "toyFill" dir (limit := 2) (mutate := fillMutant) with
  | .error e => pure [(s!"mutant: the discovery ran: {e}", false)]
  | .ok (r, t) =>
    pure
      [ ("mutant: the model text has the changed store", changed),
        ("mutant: no closed quad", r.ledger.status == "open" && t.isNone && (match r.outcome with | .open _ => true | _ => false)) ]

/-! ## The pass of the empty invariant (`Ladder.evaluate`) -/

open DiscoverLadderTests in
/-- With the fake effects of the ladder suite: when the refuter passes the empty invariant and the atoms, the quad keeps the
atoms of the traces, and a closer that needs an atom closes it. When the refuter passes the empty invariant and refutes each
atom, the quad has the empty invariant. -/
def passChecks : IO (List (String × Bool)) := do
  let sizes ← IO.mkRef []
  let log ← IO.mkRef []
  let r ← Ladder.run (fakeEnv (fakeTrace sizes) (fun _ => pure (.pass 1)) (closeBy (fun q => !q.inv.isEmpty) log) (limit := 1))
  let log2 ← IO.mkRef []
  let r2 ← Ladder.run (fakeEnv (fakeTrace sizes) (fun q => pure (if q.inv.isEmpty then .pass 1 else .cti (cexAt 3)))
    (closeBy (fun _ => true) log2) (limit := 1))
  pure
    [ ("pass: the quad keeps the atom of the traces and closes",
        r.ledger.status == "closed" && r.ledger.quad.map (·.inv) == some ["st.k ≤ 12"]),
      ("pass: an atom that the refuter refutes is dropped, the quad has the empty invariant",
        r2.ledger.status == "closed" && r2.ledger.quad.map (·.inv) == some [] &&
          (r2.ledger.rounds.head?.bind (·.candidates.head?.map (·.dropped))) == some ["st.k ≤ 12"]) ]

/-- The number of failed checks. The suite runs when `only` is none or `discoverspec`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoverspec" then return 0
  let io := (← passChecks) ++ (← poolChecks) ++ (← traceChecks) ++ (← mutantChecks)
  let mut failed := 0
  for (name, ok) in fixedChecks ++ propertyChecks seed cases ++ io do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoverspec: {name}"
  return failed

end DiscoverSpecTests
