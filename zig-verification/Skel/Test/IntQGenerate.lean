import Lift.Shuffler.Internal.Proposed.GenerateStatement
import Skel.IntQ.Refute

/-! Regression tests of the installed Generate proposal and its production machine runner. -/

namespace IntQGenerateTests

open Lift.P2.Total Lift.Trusted Lift.Shuffler.Zig
open Lift.Shuffler.Internal.Proposed
open Lift.Shuffler.Internal.Proposed.GenerateStatement
open FlatShuffler (Word StackSlot maxStackSize)
open FlatShuffler.Flat (NONE)
open Skel.IntQ.Refute (Case)

private def literal : StackSlot := ⟨0x12345678, 0, 0⟩

private def entry : St :=
  { target := Vector.replicate maxStackSize literal,
    targetPad := Vector.replicate maxStackSize 0xA55A, targetSize := 1,
    spills := fun _ => 0, maxSwapDepth := 16, maxDupDepth := 15,
    data := Vector.replicate maxStackSize default,
    pad := Vector.replicate maxStackSize 0xBEEF, size := 0, trace := [],
    dest := Vector.replicate maxStackSize NONE, pos := Vector.replicate maxStackSize NONE,
    pend := 1, blockedOffset := NONE-1, blockedExcess := NONE }

private def env : Layout.Env :=
  { self := 0x1100000, target := 0x2300000, spills := 0x3500000,
    data := 0x4700000, trace := 0x5900000, mapping := 0x6B00000, pad := 0 }

private def raw : Vector (BitVec 8 × BitVec 8 × BitVec 16 × BitVec 64) 10240 :=
  Vector.ofFn fun i => (0xE0, 0xF0, BitVec.ofNat 16 (0xBF00+23*i.val),
    BitVec.ofNat 64 (0xF1F2F3F4F5F60000+47*i.val))

private def sample (st : St) (t : Word := 0) (e : Layout.Env := env) : Case :=
  let c : Case :=
    { pre := decide (C st t raw), args := args st t raw e,
      objs := objects st t raw e, expect := none, junk := 0xAABBCCDDEEFF0123 }
  Skel.IntQ.Refute.withExpected fn c fun _ =>
    let y := generate st t
    some (result st t raw y, written st t raw e y)

private def issue (c : Case) : Option String :=
  if !c.pre then some "outside the installed contract"
  else (Skel.IntQ.Refute.admissionIssue fn c).orElse fun _ =>
    Skel.IntQ.Refute.checkCase fn 100000 c

private def checks : List (String × Bool) :=
  let c := sample entry
  let invalid := sample entry 1
  let mutant := { c with expect := c.expect.map fun (_, os) => (⟨.W16, 2⟩, os) }
  [("nonzero pending caller passes the production machine check", (issue c).isNone),
   ("pending 17 and stored blocked fields pass the production machine check",
     (issue (sample { entry with pend := 17 })).isNone),
   ("the production body completes the pending target",
     (runChecks entry).1 == .done && match body entry 0 with
       | .cont st offset => st.pend == 0 && offset == 0
       | .ret _ => false),
   ("a literal target passes with no spill byte mapped",
     (issue c).isNone &&
       ((Skel.IntQ.Refute.startOf fn c).data.dmem.get? (env.spills+0x12345678)).isNone),
   ("one target word next to the writable data buffer is admitted",
     (issue (sample entry 0 { env with data := env.target+8 })).isNone),
   ("an invalid target offset passes the modelled assertion path",
     (generate entry 1).1 == .assertionExit && (issue invalid).isNone),
   ("a return mutation is detected after admission",
     mutant.pre && (Skel.IntQ.Refute.admissionIssue fn mutant).isNone &&
       (Skel.IntQ.Refute.checkCase fn 100000 mutant).isSome)]

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "intq-generate" then return 0
  let failures := checks.filter (!·.2)
  for (name, _) in failures do IO.println s!"FAIL  intq-generate: {name}"
  return failures.length

end IntQGenerateTests
