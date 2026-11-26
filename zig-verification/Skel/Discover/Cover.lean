import Skel.Types
import Skel.Gen.Types

/-! The edges of a loop for the coverage of the refuter (task REFUTE-COV). The refute file of a loop site runs
`Skel.Refute.refuteLoopG` (`Skel/Lean/Refute.lean`). For the discovery the call is replaced by `refuteLoopCov` with the edges of
the pass of the loop head, so that a candidate that no run refutes, and that is not checked on each branch, is `unknown` and not
`pass`.

* `passEdges`: the edges of the pass of a head from the blocks of the function: each jump and each return of the blocks that the
  head reaches without entering the head again, and the jumps back to the head. A call is the edge to its continuation, as
  `Skel.Refute.inline` runs it (DISC-CALL). A trap is no edge (a trap is a failure of the step).
* `coverText`: the refute text with the call replaced, or none when the text has not exactly one call.
* `isUncovered`: whether a verdict is the `unknown` of an edge with no visit. -/

namespace Skel.Discover.Cover

open Skel Skel.Gen

/-- An edge: its text, the label that it leaves, and the label that it goes to (`none`: a return). -/
abbrev EdgeSpec : Type := String × String × Option String

/-- The offsets that an exit goes to: a jump gives its target, a call its continuation, a return `none`; a trap gives nothing. -/
private def targets : Exit → List (Option Nat)
  | .goto t => [some t]
  | .call _ k => [some k]
  | .ret => [none]
  | .trap => []

/-- The exits of a block. -/
private def exitsOf (b : Block) : List (Option Nat) :=
  match b.term with
  | .exit e => targets e
  | .branch _ y n => targets y ++ targets n

/-- The offsets of the pass: those that the queue reaches without entering `head` again, in order of discovery. -/
private def grow (bs : List Block) (head : Nat) : Nat → List Nat → List Nat → List Nat
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, o :: rest, seen =>
    if seen.contains o then grow bs head fuel rest seen
    else
      let next := match bs.find? (·.offset == o) with
        | some b => (exitsOf b).filterMap id |>.filter (· != head)
        | none => []
      grow bs head fuel (rest ++ next) (seen ++ [o])

/-- The edges of the pass from the block named `head`, with no repeat; none when no block has the name. -/
def passEdges (bs : List Block) (head : String) : List EdgeSpec :=
  match bs.find? (·.name.s == head) with
  | none => []
  | some h =>
    let offs := grow bs h.offset (2 * bs.length + 2) [h.offset] []
    (offs.flatMap fun o =>
      match bs.find? (·.offset == o) with
      | none => []
      | some b =>
        (exitsOf b).filterMap fun
          | none => some (s!"{b.name.s}->ret", b.name.s, none)
          | some t => (bs.find? (·.offset == t)).map fun tb => (s!"{b.name.s}->{tb.name.s}", b.name.s, some tb.name.s)).eraseDups

/-- The Lean list of the edges, for `refuteLoopCov`: the labels are the constructors of `Lbl` of the refute file. -/
def universeText (es : List EdgeSpec) : String :=
  "[" ++ ", ".intercalate (es.map fun (t, a, b) =>
    s!"({t.quote}, (Lbl.{a}, {match b with | some l => s!"some Lbl.{l}" | none => "none"}))") ++ "]"

/-- The call that the refute text of a loop has. -/
def hook : String := "Skel.Refute.refuteLoopG "

/-- The guide of the guided search of a refute text (HARNESS-LOOP3), when the text declares its parts (`refuteMutant` of the
sampler, `refuteOps` of the blocks). -/
def guideText (text : String) : Option String :=
  if ["def refuteMutant ", "def refuteOps "].all fun d => (text.splitOn d).length == 2 then
    some "⟨refuteMutant, refuteOps, refuteRender⟩"
  else none

/-- The refute text with `refuteLoopG` replaced by `refuteLoopCov` and the edges (`refuteLoopCovG` and the guide when the text
has one), or none when the text has not exactly one call. -/
def coverText (es : List EdgeSpec) (text : String) : Option String :=
  if (text.splitOn hook).length == 2 then
    some (text.replace hook (match guideText text with
      | some g => s!"Skel.Refute.refuteLoopCovG {universeText es} {g} "
      | none => s!"Skel.Refute.refuteLoopCov {universeText es} "))
  else none

/-- The start of the reason of the verdict of an edge with no visit. -/
def uncoveredTag : String := "edge not covered"

/-- Whether the verdict is the `unknown` of an edge with no visit. -/
def isUncovered : Verdict → Bool
  | .unknown why => why.startsWith uncoveredTag
  | _ => false

end Skel.Discover.Cover
