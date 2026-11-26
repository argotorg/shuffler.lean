import Skel.Gen.Derive.Blocks
import Skel.Gen.Derived.Pilot
import Skel.Gen.Derived.PilotFast
import Skel.Gen.Derived.Level2z
import Skel.Gen.Derived.Toys
import Skel.Gen.Derived.Spike
import Skel.Gen.Generate
import Skel.Gen.Sym
import Skel.Toy.Held
import Skel.Toy.Job
import Lift.Level2.L1

/-! The tests of `Skel/Gen/Derive/Blocks.lean` and of the switch of `generate` to the derived blocks (task N11 of
`docs/research/symexec-pilot-20261118.md`, section 5). The module is checked by `lake build Skel.Test.DeriveBlocks`:
each `#eval` throws when a check fails. No `set_option` changes a limit.

* **Cross-check.** Where the table (`symBlock`) gives a block, the derived part agrees with it (`Part.differs`: equal up
  to the normal form of N7 and N10): the 25 pilot blocks, the 48 level 2 blocks, and the table blocks of the toys.
* **The pilot.** The derived parts of the 49 pilot blocks, and the result of `generate` for each of the 8 functions. The
  five functions with an access below 64 bits (`SpillSet.add`, `Emission.pop`, `MappingBuilder.map`, `closestCopy`,
  `mapInPlace`) generate, with a statement of an access of 8 or 16 bits (N13).
* **The toys.** With the derived source, `generate` gives the rows of the table source for the toys with no call.
* **Errors.** A block whose derived term is not finished (a site equation removed) is `GenError.derive`. The flag input
  of `l2Flags` LBB0_1 (D43) is kept by the exit of its entry block (L2-FLAGS), so `generate` of `l2Flags` gives a model. A function that the parts do not
  have is `GenError.derive`. -/

open Lean Meta Elab Term Skel.Gen Skel.Gen.Derive

namespace Skel.Test.DeriveBlocks

#derive_blocks level2 Lift.Level2.L1.step Lift.Level2.Code.code ["l2Flags", "l2Bits", "l2Arith", "l2Narrow", "l2Field",
  "l2PtrStore", "l2IdxPush", "l2IdxPop", "l2TwoLoops", "l2Nest", "l2Exit3", "l2Frame", "l2Args8", "l2StackCaller",
  "l2Wrap", "l2CallLoop", "l2Alias"]

def check (ok : Bool) (msg : String) : TermElabM Unit := unless ok do throwError "check failed: {msg}"

/-- The table block of each raw block of `fn` (each block alone, not only up to the first error). -/
def tableOf (code : Executable) (fn : String) : List (Nat × Except GenError Block) :=
  match (do split (← sites code fn) (← labels code fn)) with
  | .error _ => []
  | .ok raws =>
    let index := raws.map fun b => (b.name, b.offset)
    raws.map fun b => (b.offset, symBlock index b)

/-- The cross-check of the parts `d` with the table of `code`: the number of table blocks, and the blocks that have no
part or that differ. -/
def crossCheck (code : Executable) (d : Derived) : Nat × List String := Id.run do
  let mut n := 0
  let mut bad : List String := []
  for (fn, parts) in d do
    for (off, r) in tableOf code fn do
      let .ok t := r | continue
      n := n + 1
      match parts.lookup off with
      | some (.ok p) => if let some why := p.differs t then bad := bad ++ [s!"{fn} {t.name.s}: {why}"]
      | some (.error e) => bad := bad ++ [s!"{fn} {t.name.s}: no part: {repr e}"]
      | none => bad := bad ++ [s!"{fn} {t.name.s}: no part"]
  (n, bad)

/-- The errors of the parts `d`. -/
def partErrors (d : Derived) : List (String × Nat × GenError) :=
  d.flatMap fun (fn, ps) => ps.filterMap fun (o, r) => match r with | .error e => some (fn, o, e) | .ok _ => none

/-- The number of parts. -/
def partCount (d : Derived) : Nat := (d.map (·.2.length)).foldl (· + ·) 0

end Skel.Test.DeriveBlocks

open Skel.Test.DeriveBlocks

/-! ## The cross-check: 25 pilot, 48 level 2, and the toy blocks of the table -/

#eval show TermElabM Unit from do
  let (np, bp) := crossCheck Lift.Level3.Code.code Skel.Gen.Derived.pilot
  let (n2, b2) := crossCheck Lift.Level2.Code.code level2
  let (nt, bt) := crossCheck Lift.Toys.Code.code Skel.Gen.Derived.toys
  let (ns, bs) := crossCheck Lift.Spike.Code.code Skel.Gen.Derived.spike
  logInfo m!"cross-check: pilot {np} table blocks, {bp.length} differ {bp}; level 2 {n2}, {b2.length} differ {b2}; toys {nt}, {bt.length} differ {bt}; spike {ns}, {bs.length} differ {bs}"
  check (np == 25) s!"25 pilot table blocks, got {np}"
  check (n2 == 48) s!"48 level 2 table blocks, got {n2}"
  check (bp ++ b2 ++ bt ++ bs).isEmpty "each table block agrees with its derived part"

/-! ## The parts of the pilot and of level 2 -/

#eval show TermElabM Unit from do
  let pe := partErrors Skel.Gen.Derived.pilot
  let le := partErrors level2
  logInfo m!"pilot: {partCount Skel.Gen.Derived.pilot} parts, errors {pe.map fun (f, o, e) => s!"{f} {o}: {repr e}"}"
  logInfo m!"level 2: {partCount level2} parts, errors {le.map fun (f, o, e) => s!"{f} {o}: {repr e}"}"
  check (partCount Skel.Gen.Derived.pilot == 49) "49 pilot parts"
  check pe.isEmpty "each pilot block has a part"
  check (partCount level2 == 79) "79 level 2 parts"
  -- the flag input of `l2Flags` LBB0_1 is kept by the exit of the entry block (L2-FLAGS), so no block has an error
  check le.isEmpty s!"level 2 errors {le.map fun (f, o, _) => (f, o)}"

/-! ## `generate` on the pilot -/

def pilotTarget (pc : String) : Target :=
  { step := "Lift.Level3.L1.step", lo := "Lift.Level3.workspaceAlignmentPC", hi := "Lift.Level3.pilotEndPC",
    entryPC := pc, imports := [], callees := [] }

#eval show TermElabM Unit from do
  let mut lines : List String := []
  for (fn, _) in Skel.Gen.Derived.pilot do
    let r := generate (pilotTarget "pc") Hints.none .storeChain Lift.Level3.Code.code (.derived Skel.Gen.Derived.pilot) fn
    lines := lines ++ [match r with
      | .ok g => s!"{fn}: ok, rows {g.obligations.map (·.id.name)}"
      | .error e => s!"{fn}: {repr e}"]
  logInfo m!"pilot generate:\n{"\n".intercalate lines}"

/-- The callee `map` of `mapInPlace`, with no stack room and no memory. -/
def mapCallee : Callee :=
  ⟨".Lshuffler.MappingBuilder.map", "map", [.rdi, .rsi, .rdx], "Lift.Level3.mappingMapPC", 0, false, 0, none⟩

-- The five pilot functions with an access below 64 bits (N13) generate, and a block statement of each has a narrow access.
#eval show TermElabM Unit from do
  let fns := [".Lshuffler.SpillSet.add", ".Lshuffler.Emission.pop", ".Lshuffler.MappingBuilder.map",
    ".Lshuffler.MappingBuilder.closestCopy", ".Lshuffler.MappingBuilder.mapInPlace"]
  for fn in fns do
    let t := { pilotTarget "pc" with callees := if fn == ".Lshuffler.MappingBuilder.mapInPlace" then [mapCallee] else [] }
    match generate t Hints.none .storeChain Lift.Level3.Code.code (.derived Skel.Gen.Derived.pilot) fn with
    | .error e => throwError "{fn}: generate gives {repr e}"
    | .ok g =>
      let narrow := g.obligations.any fun o =>
        ((o.statement.splitOn ".W8 ").length > 1 || (o.statement.splitOn ".W16 ").length > 1)
      check narrow s!"{fn}: a block statement has an access of 8 or 16 bits"

/-! ## The toys: the derived source and the table give the same rows -/

def toyTarget : Target :=
  { step := "L1.step", lo := "lo", hi := "hi", entryPC := "pc", imports := [], callees := [] }

#eval show TermElabM Unit from do
  let ids (code : Executable) (src : BlockSource) (fn : String) : Option (List String) :=
    (generate toyTarget Hints.none .storeChain code src fn).toOption.map (·.obligations.map (·.id.name))
  let toys := ["toyAt", "toyClamp", "toyFind", "toyFill", "toyWalk", "toyHalf"]
  for fn in toys do
    let d := ids Lift.Toys.Code.code (.derived Skel.Gen.Derived.toys) fn
    check (d.isSome && d == ids Lift.Toys.Code.code .table fn) s!"{fn}: the derived rows are the table rows: {d}"
  -- `toyCount` and `toyInc`: the table and the derived source give no rows, or other rows
  logInfo m!"toyCount, toyInc: derived {["toyCount", "toyInc"].map (ids Lift.Toys.Code.code (.derived Skel.Gen.Derived.toys))}, table {["toyCount", "toyInc"].map (ids Lift.Toys.Code.code .table)}"
  for fn in ["toySum"] do
    let d := ids Lift.Spike.Code.code (.derived Skel.Gen.Derived.spike) fn
    check (d.isSome && d == ids Lift.Spike.Code.code .table fn) s!"{fn}: the derived rows are the table rows: {d}"

/-! ## Errors -/

-- A block whose derived term is not finished: the site equation of its last instruction is removed.
#eval show TermElabM Unit from do
  let code := Lift.Level3.Code.code
  let .ok (raws, base) := rawsOf code ".Lshuffler.Emission.pop" | throwError "pop"
  let eqs ← siteEqs ``Lift.Level3.L1.step `Skel.Test.DeriveBlocks.miss (raws.flatMap fun b => b.sites.map (base + ·.offset))
  let some b := raws.head? | throwError "no block"
  let some last := b.sites.getLast? | throwError "no site"
  let ctx ← blockContext ((eqs.filterMap (·.toOption)).filter (·.addr != base + last.offset))
  let parts ← partsWith ``Lift.Level3.L1.step ctx code base raws
  match parts.lookup b.offset with
  | some (.error (.derive o what)) =>
    check (o == b.offset) "the error names the block"
    check ((what.splitOn "not finished").length > 1) s!"the cause: {what}"
  | _ => throwError "a block with a missing site equation must give GenError.derive"
  -- the other blocks keep their parts
  check ((parts.filter fun (o, r) => o != b.offset && r.toBool).length == raws.length - 1) "the other blocks have parts"
  -- `generate` stops at the first block with no part
  let d : Derived := [(".Lshuffler.Emission.pop", parts)]
  match generate (pilotTarget "pc") Hints.none .storeChain code (.derived d) ".Lshuffler.Emission.pop" with
  | .error (.derive o _) => check (o == b.offset) "generate gives the error of the block"
  | _ => throwError "generate must give GenError.derive"

-- The flag input of `l2Flags` LBB0_1 is kept by the entry block (L2-FLAGS): `generate` gives a model.
#eval show TermElabM Unit from do
  match generate (pilotTarget "pc") Hints.none .storeChain Lift.Level2.Code.code (.derived level2) "l2Flags" with
  | .error e => throwError "l2Flags: {repr e}"
  | .ok _ => pure ()

-- A function that the parts do not have.
#eval show TermElabM Unit from do
  match generate (pilotTarget "pc") Hints.none .storeChain Lift.Toys.Code.code (.derived []) "toySum" with
  | .error (.derive 0 _) => pure ()
  | _ => throwError "a function with no parts must give GenError.derive"

/-! ## The call toys: the return address is stored at `rsp` after the call (N14) -/

/-- The first part with a call whose last store is not at the value of `rsp` after the call, in `d`: the proof of a call
takes the address of the return-address store as the value of `rsp` (`Sites.Stack.retAddr_writeRam`), so the two terms are
the same text, not only the same normal form (`rsp - 8 - 8`, not `rsp - 16`). -/
def callAddressMismatch (d : Derived) : List String :=
  d.flatMap fun (fn, ps) => ps.filterMap fun (o, r) =>
    match r with
    | .ok ⟨_, accs, regs, .exit (.call ..), _⟩ =>
      match accs.getLast?, regs.lookup .rsp with
      | some (.store _ a .W64 _), some v => if a.show == v.show then none else some s!"{fn} {o}: store at {a.show}, rsp {v.show}"
      | _, _ => some s!"{fn} {o}: no last store or no rsp"
    | _ => none

#eval show TermElabM Unit from do
  let calls (d : Derived) : Nat := (d.flatMap fun (_, ps) => ps.filterMap fun (_, r) =>
    match r with | .ok ⟨_, _, _, .exit (.call ..), _⟩ => some () | _ => none).length
  check (calls Skel.Gen.Derived.toys == 6 && calls Skel.Gen.Derived.spike == 3 && calls level2 == 5)
    s!"the calls of the toys, the spike and level 2: {calls Skel.Gen.Derived.toys}, {calls Skel.Gen.Derived.spike}, {calls level2}"
  for (name, d) in [("toys", Skel.Gen.Derived.toys), ("spike", Skel.Gen.Derived.spike), ("level2", level2),
      ("pilot", Skel.Gen.Derived.pilot)] do
    check (callAddressMismatch d).isEmpty s!"{name}: {callAddressMismatch d}"

-- `toyJob`, `toyOuter` and `toyTwo`: the derived source gives the rows of the table.
#eval show TermElabM Unit from do
  let cases : List (String × Target × Executable × Derived) :=
    [("toyJob", Skel.Toy.Job.jobTarget, Lift.Spike.Code.code, Skel.Gen.Derived.spike),
     ("toyOuter", Skel.Toy.Held.targetOf "toyOuter", Lift.Toys.Code.code, Skel.Gen.Derived.toys),
     ("toyTwo", Skel.Toy.Held.targetOf "toyTwo", Lift.Toys.Code.code, Skel.Gen.Derived.toys)]
  for (fn, t, code, d) in cases do
    let ids (src : BlockSource) : Option (List String) :=
      (generate t Hints.none .storeChain code src fn).toOption.map (·.obligations.map (·.id.name))
    check ((ids (.derived d)).isSome && ids (.derived d) == ids .table) s!"{fn}: the derived rows are the table rows: {ids (.derived d)}"

/-! ## The sign form of a sum (N14) -/

/-- The part of a one-path block term at the offset 0 of a function at 0x100000, with no live flag. -/
def partOfTerm (stx : TermElabM Syntax) : TermElabM Part := do
  let e ← Term.elabTerm (← stx) none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let some id := Ident.parse "b" | throwError "identifier"
  match ← walkTerm (← blockContext []) e with
  | .error err => throwError "walk: {repr err}"
  | .ok w =>
    match partOf Lift.Toys.Code.code 0x100000 ⟨id, 0, [], none⟩ w [] false with
    | .ok p => pure p
    | .error err => throwError "part: {repr err}"

/-- The text of the value of `r` in the part. -/
def regText (p : Part) (r : Reg64) : String := ((p.regs.lookup r).map (·.show)).getD "-"

-- A sum with a register that is not `rsp` and a literal of 2^63: `movabsq $2^63, %rax; addq %rdi, %rax`.
#eval show TermElabM Unit from do
  let p ← partOfTerm `(fun d : MachineData =>
    Effects.done ⟨{ d with regs := { d.regs with rax := d.regs.rdi + 9223372036854775808 } }, 1048592⟩)
  check (regText p .rax == "(Reg64.rdi + 9223372036854775808)") s!"rax := rdi + 2^63: {regText p .rax}"
  let p ← partOfTerm `(fun d : MachineData =>
    Effects.done ⟨{ d with regs := { d.regs with rax := 9223372036854775808 + d.regs.rdi } }, 1048592⟩)
  check (regText p .rax == "(Reg64.rdi + 9223372036854775808)") s!"rax := 2^63 + rdi: {regText p .rax}"
  -- a literal of 2^64 - 8 on a register that is not `rsp` stays a sum
  let p ← partOfTerm `(fun d : MachineData =>
    Effects.done ⟨{ d with regs := { d.regs with rax := d.regs.rdi + 18446744073709551608 } }, 1048592⟩)
  check (regText p .rax == "(Reg64.rdi + 18446744073709551608)") s!"rax := rdi + (2^64 - 8): {regText p .rax}"
  -- `rsp` and a literal of 2^64 - 8: a difference
  let p ← partOfTerm `(fun d : MachineData =>
    Effects.done ⟨{ d with regs := { d.regs with rax := d.regs.rsp + 18446744073709551608 } }, 1048592⟩)
  check (regText p .rax == "(Reg64.rsp - 8)") s!"rax := rsp + (2^64 - 8): {regText p .rax}"

/-! ## The heartbeat budget (N16)

Each unit of the derivation has the whole `maxHeartbeats` budget: a site, the simp set of a function, a block (its term
and its walk), and the definition. The sum of the units of a function or of a command can pass the budget. The limits
below are lower than the default (`withTheReader`, and `set_option … in` on one command): the pilot function
`closestCopy` has 64 sites and 15 blocks, its sites need about 10,000 and its largest block about 1,800 (units of 1000
heartbeats, measured in `scratch/n16/Measure.lean`). -/

/-- The pilot function of the budget tests. -/
def lowFn : String := ".Lshuffler.MappingBuilder.closestCopy"

/-- The parts of `lowFn` in the pilot, at the default limit. -/
def lowRef : List (Nat × Except GenError Part) := (Skel.Gen.Derived.pilot.lookup lowFn).getD []

-- A budget of 4000 for each unit, below the sum of the sites (10,000) and above each block: the parts are the parts at the
-- default limit.
#eval show TermElabM Unit from do
  let low ← withTheReader Core.Context (fun c => { c with maxHeartbeats := 4000 * 1000 }) <| withCurrHeartbeats <|
    deriveFn ``Lift.Level3.L1.step `Skel.Test.DeriveBlocks.low4000 Lift.Level3.Code.code lowFn
  check (lowRef.length == 15) s!"15 parts of {lowFn} in the pilot, got {lowRef.length}"
  check (toExpr low == toExpr lowRef) "the parts at a budget of 4000 are the parts at the default limit"

-- A budget of 1500 for each block, below the largest block: each block is its part at the default limit, or the error
-- `derive` that names the block and the limit. At least one block passes the limit; the command does not fail.
#eval show TermElabM Unit from do
  let code := Lift.Level3.Code.code
  let .ok (raws, base) := rawsOf code lowFn | throwError "{lowFn}"
  let eqs ← siteEqs ``Lift.Level3.L1.step `Skel.Test.DeriveBlocks.low1500 (raws.flatMap fun b => b.sites.map (base + ·.offset))
  let ctx ← blockContext (eqs.filterMap (·.toOption))
  let parts ← withTheReader Core.Context (fun c => { c with maxHeartbeats := 1500 * 1000 }) <| withCurrHeartbeats <|
    partsWith ``Lift.Level3.L1.step ctx code base raws
  check (parts.length == raws.length) "one result for each block"
  let mut limits := 0
  for (b, (o, r)) in raws.zip parts do
    check (o == b.offset) "the parts are in the order of the blocks"
    match r with
    | .error (.derive o' what) =>
      check (o' == b.offset) "the error names the offset of the block"
      check ((what.splitOn s!"the block {b.name.s} passes a limit: Skel.Gen.Derive.Limit.maxHeartbeats 1500").length > 1)
        s!"the error names the block and the limit: {what}"
      limits := limits + 1
    | r => check (toExpr r == toExpr ((lowRef.lookup o).getD (.error (.noFunction "")))) s!"block {b.name.s}: the part at the default limit"
  check (limits ≥ 1) "a block passes the budget of 1500"

-- One command at a budget of 4000: its sites, simp sets, blocks and definition each have the budget.
set_option maxHeartbeats 4000 in
#derive_blocks lowCommand Lift.Level3.L1.step Lift.Level3.Code.code [".Lshuffler.MappingBuilder.closestCopy",
  ".Lshuffler.MappingBuilder.mapInPlace"]

#eval show TermElabM Unit from do
  let ref := Skel.Gen.Derived.pilot.filter fun (fn, _) =>
    fn == ".Lshuffler.MappingBuilder.closestCopy" || fn == ".Lshuffler.MappingBuilder.mapInPlace"
  check (ref.length == 2) "the pilot has the two functions"
  check (toExpr lowCommand == toExpr ref) "the command at a budget of 4000 gives the parts of the pilot"

/-! ## The pilot and level2z are unchanged (N16)

The hash of the text of the derived term (`toExpr`) of the pilot, the ReleaseFast pilot and level2z, and the number of
their parts, as the derivation before N16 gave them (`scratch/n16/Golden.lean`). The level2z value is the one that
L2-READ set (669a63e: Bits and Arith derive); the measure on harness-scale without N16 and with N16 gives the same
fingerprints and the same hash of each block.

L2-FLAGS: `Part` has the field `flags`, so the text of each part changes and the three hashes change. The hash of
`(offset, accesses, regs, term)` of each block of the pilot, the ReleaseFast pilot and level2z is the same with and
without L2-FLAGS, except the block `l2zFlags` 8, which had no part (a flag input) and has one (measure:
per-block hashes on harness-scale and on the merge). Only `l2zFlags` keeps flags (`Skel/Test/DeriveFlags.lean`). -/

/-- The number of parts and the hash of the text of `d`. -/
def fingerprint (d : Derived) : Nat × UInt64 :=
  ((d.map fun (p : String × List (Nat × Except GenError Part)) => p.2.length).foldl (· + ·) 0, hash (toString (toExpr d)))

#eval show TermElabM Unit from do
  check (fingerprint Skel.Gen.Derived.pilot == (49, 17702797297410654454)) s!"pilot {fingerprint Skel.Gen.Derived.pilot}"
  check (fingerprint Skel.Gen.Derived.pilotFast == (62, 9258467812170229215))
    s!"pilotFast {fingerprint Skel.Gen.Derived.pilotFast}"
  check (fingerprint Skel.Gen.Derived.level2z == (73, 8701515623618686122))
    s!"level2z {fingerprint Skel.Gen.Derived.level2z}"

/-! ## No raised limit in a derived module (N16)

The derived modules of `Skel/Gen/Derived/` run at the default limits: no file sets `maxHeartbeats` or `maxRecDepth`. The
modules of the full shuffler are among them. -/

#eval show IO Unit from do
  let files ← System.FilePath.readDir "Skel/Gen/Derived"
  let names := files.toList.map (·.fileName)
  unless names.contains "Shuffler.lean" do throw (IO.userError "Skel/Gen/Derived/Shuffler.lean is missing")
  for f in files do
    if f.fileName.endsWith ".lean" then
      let s ← IO.FS.readFile f.path
      for opt in ["maxHeartbeats", "maxRecDepth"] do
        if (s.splitOn opt).length > 1 then throw (IO.userError s!"{f.path} has {opt}")
