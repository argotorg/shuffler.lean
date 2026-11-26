import Skel.Gen.Derive.Site
import Skel.Gen.Asm
import Lift.Level3.L1
import Lift.Level2.L1

/-! The tests of `Skel/Gen/Derive/Site.lean` (task N1 of `docs/research/symexec-pilot-20261118.md`, section 5). The
module is checked by `lake build Skel.Test.DeriveSite`: each `#eval` throws when a check fails. No `set_option` changes a
limit, so every site runs at the default `maxRecDepth` and `maxHeartbeats`.

Pilot: the 171 sites of the 8 functions of `Lift.Level3.Code.code` all succeed. Level 2: the 347 sites of the 17 functions
of `Lift.Level2.Code.code`; the sites that fail at the default limit are errors that name the site and the limit. -/

open Lean Meta Elab Term Skel.Gen Skel.Gen.Derive

namespace DeriveSiteTests

/-- The function labels of the pilot and their entry addresses (`Lift/Level3/L1.lean`). -/
def pilotFns : List (String × Nat) :=
  [ ("solidity_shuffler_workspaceAlignment", 0x100000), (".Lshuffler.SpillSet.add", 0x100004),
    (".Lshuffler.Emission.shallowestCopyPosition", 0x100034), (".Lshuffler.Emission.pop", 0x10005a),
    (".Lshuffler.Planner.isRetained", 0x1000b4), (".Lshuffler.MappingBuilder.map", 0x1000bd),
    (".Lshuffler.MappingBuilder.closestCopy", 0x1000f0), (".Lshuffler.MappingBuilder.mapInPlace", 0x1001bb) ]

/-- The function labels of level 2 and their entry addresses (`Lift/Level2/L1.lean`). -/
def level2Fns : List (String × Nat) :=
  [ ("l2Flags", 0x100000), ("l2Bits", 0x10008b), ("l2Arith", 0x1000ed), ("l2Narrow", 0x100129),
    ("l2Field", 0x100166), ("l2PtrStore", 0x10019e), ("l2IdxPush", 0x1001c2), ("l2IdxPop", 0x100201),
    ("l2TwoLoops", 0x10022a), ("l2Nest", 0x100251), ("l2Exit3", 0x100278), ("l2Frame", 0x10029b),
    ("l2Args8", 0x100308), ("l2StackCaller", 0x100331), ("l2Wrap", 0x100358), ("l2CallLoop", 0x100368),
    ("l2Alias", 0x1003cf) ]

/-- The decoded instruction addresses of the functions. -/
def siteAddrs (code : _root_.Executable) (fns : List (String × Nat)) : List Nat :=
  fns.flatMap fun (label, base) =>
    match sites code label with
    | .ok ss => ss.map fun s => base + s.offset
    | .error _ => []

def pilotAddrs : List Nat := siteAddrs Lift.Level3.Code.code pilotFns
def level2Addrs : List Nat := siteAddrs Lift.Level2.Code.code level2Fns

def pilotStep : Name := ``Lift.Level3.L1.step
def level2Step : Name := ``Lift.Level2.L1.step

def check (ok : Bool) (msg : String) : TermElabM Unit := unless ok do throwError "check failed: {msg}"

/-- The successes of a result list. -/
def oks (rs : List (Except SiteError SiteEq)) : List SiteEq := rs.filterMap fun | .ok e => some e | .error _ => none

/-- The errors of a result list. -/
def errs (rs : List (Except SiteError SiteEq)) : List SiteError :=
  rs.filterMap fun | .ok _ => none | .error e => some e

/-- The constants that must not stay in a body: the step, the dispatch and the decoder. -/
def residual (step : Name) (c : Name) : Bool :=
  c == step || c == ``Lift.P1.dispatch || (c.toString.splitOn "decode").length > 1

/-- A literal `OfNat.ofNat T v inst` whose `v` is closed and not a raw numeral: `normLits` did not normalise it. (A value
that depends on the state, as `Bool.toNat d.status.cf`, is not closed.) -/
def isLitGap (x : Expr) : Bool :=
  x.isAppOfArity ``OfNat.ofNat 3 && !(x.getArg! 1).isRawNatLit && !(x.getArg! 1).hasLooseBVars &&
    !(x.getArg! 1).hasFVar

/-- The number of literal gaps in a term. -/
partial def litGaps (e : Expr) : Nat :=
  (if isLitGap e then 1 else 0) + match e with
  | .app f a => litGaps f + litGaps a
  | .lam _ t b _ | .forallE _ t b _ => litGaps t + litGaps b
  | .letE _ t v b _ => litGaps t + litGaps v + litGaps b
  | .mdata _ b | .proj _ _ b => litGaps b
  | _ => 0

/-- The addresses of the sites whose body has a literal gap. -/
def gapSites (es : List SiteEq) : List Nat := (es.filter fun e => litGaps e.body > 0).map (·.addr)

/-- The theorem of a site equation: in the environment (the kernel accepted it), of the form `∀ d, step ⟨d, addr⟩ = body`,
and with the axioms of Lean only. -/
def checkSite (step : Name) (e : SiteEq) : TermElabM Unit := do
  let some ci := (← getEnv).find? e.name | throwError "{e.name} is not in the environment"
  check ci.isTheorem s!"{e.name} is a theorem"
  forallTelescope ci.type fun xs ty => do
    let some (_, lhs, rhs) := ty.eq? | throwError "{e.name}: not an equation"
    check (xs.size == 1) s!"{e.name}: one bound variable"
    check (lhs.isAppOf step) s!"{e.name}: left side is the step"
    check (rhs == e.body.beta xs) s!"{e.name}: the right side is the body"
  check (!(e.body.getUsedConstants.any (residual step))) s!"{e.name}: body is free of step, dispatch, decode"
  let axs ← collectAxioms e.name
  check (axs.all fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) s!"{e.name}: axioms {axs}"

/-- The addresses of the errors. -/
def errAddr : SiteError → Nat
  | .notASite a | .limit a _ | .failed a _ => a

end DeriveSiteTests

open DeriveSiteTests

/-! ## The pilot -/

#eval show TermElabM Unit from do
  check (pilotAddrs.length == 171) s!"171 pilot instructions, got {pilotAddrs.length}"
  let t0 ← IO.monoMsNow
  let rs ← siteEqs pilotStep `Skel.Test.DeriveSite.l3 pilotAddrs
  let t1 ← IO.monoMsNow
  logInfo m!"pilot: {(oks rs).length} of {pilotAddrs.length} sites, {t1 - t0} ms"
  check (rs.length == 171) "one result for each address"
  check ((errs rs).isEmpty) s!"no pilot site fails: {(errs rs).take 3 |>.map errAddr}"
  check ((oks rs).map (·.addr) == pilotAddrs) "the results keep the order of the addresses"
  for e in oks rs do checkSite pilotStep e
  -- `normLits` leaves no literal gap in a pilot body (without it, 44 of the 171 bodies have one).
  check (gapSites (oks rs) == []) s!"pilot literal gaps: {gapSites (oks rs)}"

/-! ## Errors -/

-- An address inside an instruction, and an address outside the code, are not sites.
#eval show TermElabM Unit from do
  check (!pilotAddrs.contains 0x100001) "0x100001 is no site"
  for a in [0x100001, 0xdeadbeef] do
    match ← siteEq pilotStep `Skel.Test.DeriveSite.bad a with
    | .error (.notASite b) => check (a == b) "the error names the address"
    | _ => throwError "address {a} must give notASite"

-- A name that is not a step is an error value, not an exception.
#eval show TermElabM Unit from do
  match ← siteEq `Skel.Test.DeriveSite.noSuchStep `Skel.Test.DeriveSite.nostep 0x100000 with
  | .error (.failed 0x100000 _) => pure ()
  | _ => throwError "a missing step must give failed"

-- The same name twice: the second site equation is an error and the first stays.
#eval show TermElabM Unit from do
  let r1 ← siteEq pilotStep `Skel.Test.DeriveSite.dup 0x100000
  let r2 ← siteEq pilotStep `Skel.Test.DeriveSite.dup 0x100000
  match r1, r2 with
  | .ok e, .error (.failed 0x100000 _) => checkSite pilotStep e
  | _, _ => throwError "the second equation with one name must give failed"

/-! ## Level 2 -/

#eval show TermElabM Unit from do
  check (level2Addrs.length == 347) s!"347 level 2 instructions, got {level2Addrs.length}"
  let t0 ← IO.monoMsNow
  let rs ← siteEqs level2Step `Skel.Test.DeriveSite.l2 level2Addrs
  let t1 ← IO.monoMsNow
  logInfo m!"level 2: {(oks rs).length} successes, {(errs rs).length} failures, {t1 - t0} ms"
  check (rs.length == 347) "one result for each address"
  -- At the default limits all 347 sites pass. (`#lift_exact` and the E1 and E2 scratch files use `maxRecDepth` 20000
  -- because they take the `whnf` of the dispatch, which walks the table up to the entry.)
  check ((oks rs).length == 347) s!"level 2 successes: {(oks rs).length}"
  check ((errs rs).isEmpty) s!"level 2 failures: {(errs rs).map errAddr}"
  check ((oks rs).map (·.addr) == level2Addrs) "the results keep the order of the addresses"
  for e in oks rs do checkSite level2Step e
  -- `normLits` leaves a literal gap in 2 bodies (`0x1003d3`, `0x1003db`; without it, 125 of the 347 bodies have one).
  check (gapSites (oks rs) == [0x1003d3, 0x1003db]) s!"level 2 literal gaps: {gapSites (oks rs)}"

/-! ## A limit is an error value that names the site and the limit

The limit is lowered in the context of the call. -/

#eval show TermElabM Unit from do
  let addr := 0x1001bb
  check (pilotAddrs.contains addr) "0x1001bb is a pilot site"
  let low : Core.Context → Core.Context := fun c => { c with maxRecDepth := 5 }
  match ← withTheReader Core.Context low (siteEq pilotStep `Skel.Test.DeriveSite.lowDepth addr) with
  | .error (.limit a (.maxRecDepth 5)) => check (a == addr) "the error names the site"
  | _ => throwError "maxRecDepth 5 must give a limit error"
  -- The failed site has no theorem, and the same site passes at the default limit.
  check ((← getEnv).find? (siteName `Skel.Test.DeriveSite.lowDepth addr)).isNone "no theorem for a failed site"
  match ← siteEq pilotStep `Skel.Test.DeriveSite.lowDepth addr with
  | .ok _ => pure ()
  | _ => throwError "the site must pass at the default limit"

#eval show TermElabM Unit from do
  let addr := 0x1001bb
  let low : Core.Context → Core.Context := fun c => { c with maxHeartbeats := 1000 }
  match ← withTheReader Core.Context low (siteEq pilotStep `Skel.Test.DeriveSite.lowBeats addr) with
  | .error (.limit a (.maxHeartbeats 1)) => check (a == addr) "the error names the site"
  | _ => throwError "maxHeartbeats 1 must give a limit error"
