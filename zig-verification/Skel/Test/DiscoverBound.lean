import Skel.Discover.Upper
import Skel.Discover.Targets
import Skel.Test.DiscoverBlind

/-! The tests of the bound atoms of a loop head (`Skel/Discover/Result.lean`, section "The bound atoms", suite `discoverbound`,
task DISC-BOUND): `lake exe skel-test --only discoverbound`. A check that does not hold prints one `FAIL` line.

- The parts: the parse of the probe, the contract constant of a shape, the atoms of each source on the plan of `toyFind` (an
  index from `0` that goes up) and on two changes of its blocks: the index goes down, and the index starts at an input register.
  A bound of `2 ^ 64` or more gives no atom; `0 ≤ r` is no atom. Property: on each list of bounds of a grid, each atom has a
  register that can hold a bounded input on its bounded side, and a bound below `2 ^ 64`.
- The probe (`#contract_bounds`, a Lean run): the contracts of `toyFind` and `toySum`, and a contract of the test with three
  conjuncts, one with no literal bound.
- Negative: the false contract bound `rcx ≤ 2` of `toyFind` is in the invariant of a quad, and the Houdini loop of the ladder
  (`Ladder.evaluate`, with the production refuter) passes no quad that has it; it drops only the atoms that a counterexample
  blames (HARNESS-LOOP D1).
- Negative: the mutant of `toyFind` whose index goes down (`x.rcx - 1`) is never closed.
- A sum that counts down (`toySumDown`, below): the result `x.rax + run (xs.take x.rcx)` (source `spec-prefix`) fits each
  admitted run, and the invariant has the entry bound `rcx ≤ st.input.rsi` and passes the refuter.
- The slot of one input with no list form (`shallowestCopyPosition`): the loop row binds `inp`, the name of the result term. -/

namespace DiscoverBoundTests

open Skel Skel.Gen Skel.Discover Skel.Discover.Upper
open System (FilePath)

def cfg : Skel.Config :=
  { gate := .strict, limitMs := 180000, seed := 1, samples := 200, useTemplates := false, discover := true }

def le (r : Reg64) (k : Nat) : Atom := .le (Result.regNat r) (.const k)

/-- The blocks with each write `r + 1` of the register `r` turned to `r - 1` (`r + (2^64 - 1)`). -/
def downBlocks (r : Reg64) (bs : List Block) : List Block :=
  bs.map fun b => { b with regs := b.regs.map fun (s, v) =>
    if s == r && Result.litStep r v == some 1 then (s, Val.add (.reg r) (.lit 0xFFFFFFFFFFFFFFFF)) else (s, v) }

/-- The head with the register `r` at the value of the input register `i`. -/
def fromInput (h : Head) (r i : Reg64) : Head :=
  { h with state := h.state.map fun (s, v) => if s == r then (s, .input i) else (s, v) }

def partChecks : List (String × Bool) :=
  let find := Skel.Discover.Targets.toyUnit "toyFind"
  let at_ (k : UpperPlan → List Block → Head → Bool) : Bool := match find with
    | .ok u => match u.plan.heads with
      | [h] => k u.plan u.blocks h
      | _ => false
    | .error _ => false
  let shape := find.toOption.map (·.shape)
  let grid : List (List Result.BoundSrc) :=
    [0, 1, 2, 1024, 2 ^ 61, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 70].flatMap fun k => [true, false].map fun s =>
      [{ source := "contract", bound := k, strict := s }, { source := "size", bound := k + 1 }]
  [ ("parse: the bounds of a probe", Result.parseBounds
      "x\n{\"source\":\"contract\",\"bound\":1024,\"strict\":false}\n{\"source\":\"words\",\"bound\":8,\"strict\":true}\n{\"bound\":3}\n" ==
        [{ source := "contract", bound := 1024 }, { source := "words", bound := 8, strict := true }]),
    ("contract: the constant C of the spec module of toyFind",
      (shape.bind Result.contractConst) == some "Lift.Toys.FindSpec.C"),
    ("contract: True has no constant",
      (shape.bind fun sh => (Src.parse "True").bind fun c => Result.contractConst { sh with contract := c }) == none),
    ("bounded: rcx (a step) and rax (an input, not written) of toyFind",
      at_ fun pl bs h => Result.boundedRegs pl bs h == [.rax, .rcx]),
    ("contract: the bound 2 gives rax ≤ 2 and rcx ≤ 2; the up index from 0 gives no entry atom",
      at_ fun pl bs h => Result.boundAtoms pl bs h [{ source := "contract", bound := 2 }] == [le .rax 2, le .rcx 2]),
    ("contract: a strict bound gives <",
      at_ fun pl bs h => Result.boundAtoms pl bs h [{ source := "contract", bound := 9, strict := true }] ==
        [.lt (Result.regNat .rax) (.const 9), .lt (Result.regNat .rcx) (.const 9)]),
    ("contract: the bound 2 ^ 64 of toyFind gives no atom",
      at_ fun pl bs h => Result.boundAtoms pl bs h [{ source := "contract", bound := 2 ^ 64, strict := true }] == []),
    ("size: the size 8 of an object bounds the index and the input",
      at_ fun pl bs h => Result.boundAtoms pl bs h [{ source := "size", bound := 8 }] == [le .rax 8, le .rcx 8]),
    ("entry: an index that goes down from the input rsi is at most st.input.rsi",
      at_ fun pl bs h =>
        let bs' := downBlocks .rcx bs
        let h' := fromInput h .rcx .rsi
        Result.stepOf? bs' h' .rcx == some (-1) &&
          Result.boundAtoms pl bs' h' [] == [.le (Result.regNat .rcx) (.field ["st", "input", "rsi", "toNat"])]),
    ("entry: an index that goes up from the input rsi is at least st.input.rsi",
      at_ fun pl bs h => Result.boundAtoms pl bs (fromInput h .rcx .rsi) [] ==
        [.le (.field ["st", "input", "rsi", "toNat"]) (Result.regNat .rcx)]),
    ("entry: an index that goes down from the literal 0 is at most 0",
      at_ fun pl bs h => Result.boundAtoms pl (downBlocks .rcx bs) h [] == [le .rcx 0]),
    ("property: each atom of a grid of bounds has a bounded register and a bound below 2 ^ 64",
      at_ fun pl bs h => grid.all fun srcs =>
        let regs := Result.boundedRegs pl bs h
        (Result.boundAtoms pl bs h srcs).all fun
          | .le (.field ["st", r, "toNat"]) (.const k) | .lt (.field ["st", r, "toNat"]) (.const k) =>
            k < 2 ^ 64 && regs.any (regLower · == r)
          | _ => false) ]

/-! ## The probe -/

def probeChecks : IO (List (String × Bool)) := do
  let dir ← DiscoverBlindTests.newDir "bound-probe"
  let run (name text : String) : IO (List Result.BoundSrc) := do
    IO.FS.writeFile (dir / s!"{name}.lean") text
    pure (Result.parseBounds (← NxLift.Proc.runLean #[(dir / s!"{name}.lean").toString] 120000).output)
  let find ← run "find" (Result.boundProbeText ["Lift.Toys.FindSpec"] "Lift.Toys.FindSpec.C")
  let sum ← run "sum" (Result.boundProbeText ["Lift.Spike.SumSpec"] "Lift.Spike.SumSpec.C")
  let own ← run "own" ("import Skel.Lean.BoundProbe\n" ++
    "structure CIn where\n  a : Nat\n  b : Nat\n  v : Vector Nat 5\n" ++
    "def Cx (x : CIn) : Prop := x.a ≤ x.b ∧ x.a < 10 ∧ 3 ≥ x.b\n#contract_bounds Cx\n")
  pure
    [ (s!"probe: toyFind: the contract length < 2 ^ 64; a list gives no size {repr find}",
        find == [{ source := "contract", bound := 2 ^ 64, strict := true }]),
      (s!"probe: toySum: no bound (the contract True, a list input) {repr sum}", sum == []),
      (s!"probe: the conjuncts with a literal bound, no bound for x.a ≤ x.b, the size 5 of the vector {repr own}",
        own == [{ source := "contract", bound := 10, strict := true }, { source := "contract", bound := 3 },
                { source := "size", bound := 5 }]) ]

/-! ## The ladder on toyFind -/

/-- The mutant of `toyFind`: the index goes down. -/
def downMutant (s : String) : String := s.replace "rcx := x.rcx + 1" "rcx := x.rcx - 1"

def ladderChecks : IO (List (String × Bool)) := do
  match Skel.Discover.Targets.toyUnit "toyFind" with
  | .error e => pure [(s!"toyFind: the unit: {e}", false)]
  | .ok u =>
    match sitesOf u, u.plan.heads with
    | [s], [h] =>
      let dir ← DiscoverBlindTests.newDir "bound-houdini"
      let result := (Result.suffix u.plan u.shape u.blocks h).head?.map (·.text)
      let bad := le .rcx 2
      let atoms := Result.boundAtoms u.plan u.blocks h [{ source := "contract", bound := 2 }]
      let houdini ← match machineFor cfg u s dir (result? := result) with
        | .error e => pure [(s!"houdini: the machine: {e.text}", false)]
        | .ok m =>
          let q : Quad := { inv := atoms ++ [.le (Result.regNat .rcx) (Result.regNat .rax)],
                            measure := .one (.sub (Result.regNat .rax) (Result.regNat .rcx)), bound := none, result := m.result }
          let e ← Ladder.evaluate (m.env { features := [], atoms := [] }) q
          -- the loop drops only the culprits (HARNESS-LOOP D1): a quad that keeps the false bound is refuted, not passed
          pure [ (s!"houdini: no quad that passes has the false bound rcx ≤ 2 {repr (e.quad.inv.map Atom.text, e.dropped.map Atom.text)}",
                   atoms.contains bad && !(Ladder.passes e.verdict && e.quad.inv.contains bad) && !e.dropped.isEmpty &&
                     e.dropped.all q.inv.contains) ]
      let dirM ← DiscoverBlindTests.newDir "bound-mutant"
      let changed := match machineFor cfg u s dirM downMutant with
        | .ok m => (m.gen.modelText.splitOn "rcx := x.rcx - 1").length > 1
        | .error _ => false
      let rm ← discoverSite cfg u s dirM (limit := 2) (mutate := downMutant)
      pure (houdini ++
        [ ("mutant: the model text has the index that goes down", changed),
          (s!"mutant: the index that goes down is never closed {repr rm}", rm.status != "closed" && rm.rowTriple.isNone) ])
    | _, _ => pure [("toyFind: one site and one head", false)]

/-! ## A sum that counts down

`toySumDown`: the sum of `toySum` (`Lift.Spike.SumSpec`: the sum of the words of `xs`) with an index that counts down. The
blocks have the offsets and the return block of `toySum`; the entry, the head and the body are new: `rcx` starts at the length
`rsi`, the head exits at `rcx = 0`, and the body adds the word at `rcx - 1` to `rax` and decreases `rcx` by one. The upper chain
is `generateUpper` of these blocks (`Targets.unitFrom`). No compiled function has these blocks: the loop row reads `blocksP`
only, so the discovery and `loop_close` see a loop that counts down. -/

def m1 : Val := .lit 0xFFFFFFFFFFFFFFFF

/-- The derived parts of `toySumDown`. -/
def downParts : List (Nat × Except GenError Part) :=
  let old := (Skel.Gen.Derived.spike.lookup "toySum").getD []
  let new : List (Nat × Except GenError Part) :=
    [ (0, .ok ⟨0, [], [(.rax, .lit 0), (.rcx, .reg .rsi)], .exit (.goto 4), []⟩),
      (4, .ok ⟨4, [], [], .branch (.eq (.reg .rcx) (.lit 0)) (.goto 18) (.goto 9), []⟩),
      (9, .ok ⟨9, [.load 0 (.add (.reg .rdi) (.mul (.add (.reg .rcx) m1) (.lit 8))) .W64],
        [(.rax, .add (.load 0) (.reg .rax)), (.rcx, .add (.reg .rcx) m1)], .exit (.goto 4), []⟩) ]
  old.map fun (o, p) => (o, (new.lookup o).getD p)

/-- The unit of `toySumDown`: the shape, the hint, the sampler and the header of `toySum`. -/
def downUnit : Except String FnUnit := do
  let some sh := Skel.Toy.Held.shapeOf "toySum" | throw "toySum: no shape"
  let some h := Skel.Toy.Held.hintOf "toySum" | throw "toySum: no hint"
  let t := Skel.Toy.Held.sumTarget
  Skel.Discover.Targets.unitFrom t Lift.Spike.Code.code (.derived [("toySum", downParts)]) "Lift.Spike.Code.code" "toySum"
    "toySumDown" sh h (Skel.Toy.Held.samplerModel t sh) (Skel.Toy.Held.upperHeader "toySum")

def downChecks : IO (List (String × Bool)) := do
  match downUnit with
  | .error e => pure [(s!"down: the unit: {e}", false)]
  | .ok u =>
    match sitesOf u, u.plan.heads with
    | [s], [h] =>
      let parts :=
        [ ("down: rcx goes down by one from the input rsi",
            Result.stepOf? u.blocks h .rcx == some (-1) && Result.downAt u.plan u.blocks h == [.rcx] &&
              Result.entryFeature? h .rcx == some (.field ["st", "input", "rsi", "toNat"])),
          ("down: the entry bound rcx ≤ st.input.rsi",
            (Result.boundAtoms u.plan u.blocks h []).contains (.le (Result.regNat .rcx) (.field ["st", "input", "rsi", "toNat"]))),
          ("down: a spec-prefix result of the rest xs.take rcx",
            (Result.prefixCands u.plan u.shape u.blocks h).any fun c => (c.text.splitOn "xs.take x.rcx.toNat").length > 1) ]
      let r ← discoverSite cfg u s (← DiscoverBlindTests.newDir "bound-down")
      let ledger ← match r.ledger with
        | some f => IO.FS.readFile f
        | none => pure ""
      let passed := (ledger.splitOn "\"verdict\": \"pass (").length > 1
      pure (parts ++
        [ (s!"down: the result is the spec-prefix term, which fits each admitted run {repr r.results}",
            r.resultSource == some "spec-prefix" &&
              r.results.any fun l => l.startsWith s!"spec-prefix {screenRuns}/{screenRuns}," && (l.splitOn "x.rax + ").length > 1),
          (s!"down: the invariant has the entry bound and passes the refuter {repr r.inv}",
            r.inv.contains "st.rcx.toNat ≤ st.input.rsi.toNat" && passed) ])
    | _, _ => pure [("down: one site and one head", false)]

/-- The slots of the loop row: one input with no list form is `inp`; a record keeps its slots. -/
def slotChecks : IO (List (String × Bool)) := do
  let us ← Skel.Discover.Targets.unitsOf (← DiscoverBlindTests.newDir "bound-slots") 180000 ["shallowestCopyPosition"]
  let find := Skel.Discover.Targets.toyUnit "toyFind"
  pure
    [ ("slots: one input with no list form is the slot inp", match us with
        | [(_, .ok u)] => loopSlots u.plan u.shape == ["generalize hinp : x = inp"]
        | _ => false),
      ("slots: toyFind keeps the slots of its record", match find with
        | .ok u => (loopSlots u.plan u.shape).all fun l => l.startsWith "generalize h" && !l.endsWith "= inp"
        | .error _ => false) ]

/-- The number of failed checks. The suite runs when `only` is none or `discoverbound`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoverbound" then return 0
  let io := (← probeChecks) ++ (← slotChecks) ++ (← ladderChecks) ++ (← downChecks)
  let mut failed := 0
  for (name, ok) in partChecks ++ io do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoverbound: {name}"
  return failed

end DiscoverBoundTests
