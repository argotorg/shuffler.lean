import Lift.Shuffler.Internal.Proposed.PlannerRunStatement
import Skel.IntQ.Refute

/-! Regression tests of the installed PlannerRun proposal and the production L1 runner. -/

namespace IntQPlannerTests

open Lift.P2.Total Lift.Trusted Lift.Shuffler.Zig
open Lift.Shuffler.Internal.Proposed.PlannerRunStatement
open FlatShuffler (Word StackSlot maxStackSize)
open FlatShuffler.Flat (RunU)
open Skel.IntQ.Refute (Case)

private def vec {α : Type} (fallback : α) (xs : List α) : Vector α maxStackSize :=
  Vector.ofFn fun i => xs.getD i.val fallback

private def slot (id : Nat) : StackSlot := ⟨BitVec.ofNat 32 id, 0, 1⟩

private def planner (src tgt : List StackSlot) (allowed : Bool := true) (reach : Word := 16) : Planner :=
  { source := vec default src, sourcePad := Vector.replicate maxStackSize 0xA1A2
    sourceSize := BitVec.ofNat 64 src.length
    target := vec default tgt, targetPad := Vector.replicate maxStackSize 0xB1B2
    targetSize := BitVec.ofNat 64 tgt.length, allowed, reach }

private def initial : PSt :=
  { spills := fun _ => 0, dropped := Vector.replicate maxStackSize 0, saw := true
    data := Vector.replicate maxStackSize (slot 99), pad := Vector.replicate maxStackSize 0x5A5A
    trace := [], sources := Vector.replicate maxStackSize 0xDEAD }

private def scratch : Nat → RunU := fun k =>
  let ws := Vector.ofFn fun i : Fin maxStackSize => BitVec.ofNat 64 (0x12345 + k + 17 * i.val)
  { mapping := ⟨ws, ws⟩, u := ⟨ws, ws, 0xFAFA, 0xFBFB⟩, l := ⟨ws, ws, ws⟩
    r := ⟨Vector.replicate maxStackSize 0xAC, ws⟩ }

private def env : Lift.Shuffler.Internal.Proposed.Layout.Env :=
  { self := 0x10000, target := 0x20000, spills := 0x30000, data := 0x40000
    trace := 0x50000, mapping := 0x80000, pad := 0 }

private def emissionInit := Vector.replicate 15 (0xBEBEBEBEBEBEBEBE : Word)
private def builderInit := Vector.replicate 8 (0xCECECECECECECECE : Word)
private def scratchInit := Vector.replicate 9344 (0xAEAEAEAEAEAEAEAE : Word)
private def opsInit := Vector.replicate 10240
  ((0xA1 : BitVec 8), (0xB2 : BitVec 8), (0xC3D4 : BitVec 16), (0xE5E5E5E5E5E5E5E5 : Word))

private def pre (pl : Planner) : Bool :=
  decide (C pl false initial scratch 0x1000000 0x1100000 0x1200000 0x1300000
    0x1400000 0x1500000 0x1600000 emissionInit builderInit scratchInit opsInit 0xFACE)

private def sample (pl : Planner) : Case :=
  let fields := args pl false initial scratch 0x1000000 0x1100000 0x1200000 0x1300000
    0x1400000 0x1500000 0x1600000 emissionInit builderInit scratchInit opsInit 0xFACE env
  let abi := stackArgs pl false initial scratch 0x1000000 0x1100000 0x1200000 0x1300000
    0x1400000 0x1500000 0x1600000 emissionInit builderInit scratchInit opsInit 0xFACE env
  let os := objects pl false initial scratch 0x1000000 0x1100000 0x1200000 0x1300000
    0x1400000 0x1500000 0x1600000 emissionInit builderInit scratchInit opsInit 0xFACE env
  Skel.IntQ.Refute.withExpected fn
    { pre := pre pl, args := fields.take 6, stack := some abi, objs := os,
      expect := none, junk := 0xF1F2F3F4F5F6F7F8 }
    (fun _ =>
      let y := plannerRun pl false initial scratch
      some (result pl false initial scratch 0x1000000 0x1100000 0x1200000 0x1300000
        0x1400000 0x1500000 0x1600000 emissionInit builderInit scratchInit opsInit 0xFACE y,
        written pl false initial scratch 0x1000000 0x1100000 0x1200000 0x1300000
        0x1400000 0x1500000 0x1600000 emissionInit builderInit scratchInit opsInit 0xFACE env y))

private def issue (c : Case) : Option String :=
  if !c.pre then some "outside the installed contract"
  else (Skel.IntQ.Refute.admissionIssue fn c).orElse fun _ =>
    Skel.IntQ.Refute.checkCase fn 200000 c

private def checks : List (String × Bool) :=
  let empty := planner [] []
  let done := planner [] [⟨5, 0, 0⟩]
  let blocked := planner [slot 1, slot 2, slot 3, slot 4]
    [slot 4, slot 2, slot 3, slot 1] false 2
  let assertion := planner [slot 1] [slot 2]
  let c := sample done
  let fields := args empty false initial scratch 0x1000000 0x1100000 0x1200000 0x1300000
    0x1400000 0x1500000 0x1600000 emissionInit builderInit scratchInit opsInit 0xFACE env
  let mutant := { c with expect := c.expect.map fun (_, ws) => (⟨.W16, 2⟩, ws) }
  [("normal caller is in the installed domain", pre empty),
   ("capacity boundary is admitted", pre { empty with sourceSize := 1024, targetSize := 1024 }),
   ("capacity overflow is outside the domain", !pre { empty with sourceSize := 1025 }),
   ("reach below the caller bound is outside the domain", !pre { empty with reach := 1 }),
   ("eight arguments use the caller addresses", fields.length == 8 &&
     fields[0]?.any (·.v.toNat == env.self.toNat) &&
     fields[6]?.any (·.v.toNat == 0x1500000) && fields[7]?.any (·.v.toNat == 0x1600000)),
   ("Done with target padding passes the production machine check", (issue c).isNone),
   ("Blocked passes the production machine check", (plannerRun blocked false initial scratch).1 == .blocked &&
     (issue (sample blocked)).isNone),
   ("AssertionFailed preserves caller outputs in the production machine check",
     (plannerRun assertion false initial scratch).1 == .assertionExit && (issue (sample assertion)).isNone),
   ("a result mutation is detected after admission", mutant.pre &&
     (Skel.IntQ.Refute.admissionIssue fn mutant).isNone &&
     (Skel.IntQ.Refute.checkCase fn 200000 mutant).isSome)]

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "intq-planner" then return 0
  let failures := checks.filter (!·.2)
  for (name, _) in failures do IO.println s!"FAIL  intq-planner: {name}"
  return failures.length

end IntQPlannerTests
