import Skel.Gen.UpperPlan
import Skel.Gen.Shape
import Skel.Gen.UpperRel
import Skel.Gen.Template
import Skel.Gen.Regions

/-! The proof text of `refines_l3` for a function with one loop (task G3-21b; `docs/one-way-lift-g3-plan-20261118.md`, 1.2
and 4.6). The text has the shape of the hand proof of `toySum` (`Lift/Spike/Sum.lean`, `refines_l3`):

    by
      intro <params> frame
      intro x a y hs hy
      exact ⟨_, .goto rfl (… (.goto rfl (loop.<head> <params> frame x a y hs hy))), <out>⟩

With none or several inputs (`InputForm`) the inputs are binders of the row, after the frame, and the model input is `_`:
`intro <params> frame <inputs>`, `intro _ a y hs hy` and `loop.<head> <params> frame <inputs> a y hs hy`.

The loop row (4.6) gives `blocksP.Returns noCall .<head> <head state> (<result>)` from `SimArr` and `run x = some y`, so the
proof needs no triple: the triple is in the proof of the loop row, which is a dep. The blocks before the head are the walk of
4.6 from `entry` along `goto` exits (no access, no branch); each one is one `.goto rfl`, since the step of a straight block
reduces to its jump. The head state of the loop row is the state that the walk gives (`headState`), so the last `rfl`
closes up to definitions. The blocks after the head are in the loop row: its result is the result of the return.

A narrow value and a `both` result (L3-U7) have the existential loop row: the row gives a result `r` of the blocks with the relation of
the results, so the proof takes the row apart and gives the relation as it is:

    by
      intro <params> frame
      intro x a y hs hy
      obtain ⟨res, hres, hrel⟩ := loop.<head> <params> frame x a y hs hy
      exact ⟨res, .goto rfl (… (.goto rfl hres)), hrel⟩

`<out>` is the relation of the results (G3-09, G3-17): `rfl` for a value (`(UInt64.ofBitVec y).toBitVec = y`); for a heap,
the input heap is `heapOf <params> frame x` (`SimArr` has `a.heap = objsP <params> x ++ frame`, which is `heapOf` by its
definition) and the result is `heapOf <params> frame y` (`rfl`). The loop row is named `loop.<head>`, the name of its
answer in the check files. -/

namespace Skel.Gen

/-- The number of blocks from the offset `o` to the head `h` along `goto` exits; at most `fuel` blocks. A block with an access
or with an exit that is no `goto` before the head is an error, as in `walkFrom` (a push and its pop are no such access). -/
def blocksToHead (bs : List Block) (h : Block) : Nat → Nat → Except GenError Nat
  | 0, _ => .error (.shape h.offset s!"no straight path from the entry to {h.name.s}")
  | fuel + 1, o =>
    if o == h.offset then .ok 0
    else match blockAt bs o with
      | none => .error (.shape h.offset s!"no block at offset {o} on the way to {h.name.s}")
      | some b =>
        if (straightRegs b).isNone then .error (.shape h.offset s!"{b.name.s} has an access on the way to {h.name.s}")
        else match b.term with
          | .exit (.goto t) => (blocksToHead bs h fuel t).map (· + 1)
          | _ => .error (.shape h.offset s!"{b.name.s} has a branch, call or return on the way to {h.name.s}")

/-- The qualified names of the text `t`: each run of identifier characters with a dot that starts with a letter. -/
def qualifiedNames (t : String) : List String :=
  let isId (c : Char) := c.isAlphanum || c == '.' || c == '_' || c == '\''
  let words := (t.toList.splitBy fun a b => isId a == isId b).map String.ofList
  words.filter fun w => w.contains '.' && (w.toList.headD ' ').isAlpha && !w.endsWith "."

/-- The names of the spec that the closer of `refines_l3` unfolds after `loopUnfolds` (UP-RET): the head of `post`, and the
qualified names of the result term (`StmtShape.result`, as `Lift.Level2z.AliasSpec.run` of `(…AliasSpec.run ws w v).1`) whose
namespace has the parent of the namespace of `post` (`Lift.Level2z` for `Lift.Level2z.AliasStatement.post`): the spec module and
the statement module are side by side, as `StmtShape.runConst` has them. A goal `ret_k` has the statement's `post` of the `run`
of the spec; with both folded, the closer cannot compare them with the result of the code. -/
def specUnfolds (sh : StmtShape) : List String :=
  let post := (sh.post.s.splitOn " ").headD ""
  let postHead := if (qualifiedNames post) == [post] then [post] else []
  let parent := moduleOf (moduleOf post)
  let inFamily (n : String) := !parent.isEmpty && (parent ++ ".").isPrefixOf n && n != post
  let fromResult := ((sh.result.map (qualifiedNames ·.s)).getD []).filter inFamily
  (postHead ++ fromResult).eraseDups

/-- The unfold names of the closer of `refines_l3`: `loopUnfolds`, `initP` (the paths start at the state `initP a`, whose fields
the facts of the paths name), and `specUnfolds`, each once. -/
def refinesL3Unfolds (p : UpperPlan) (sh : StmtShape) : List String :=
  (loopUnfolds p sh ++ ["initP"] ++ specUnfolds sh).eraseDups

/-- The proof text of `refines_l3` for a plan with no loop head (UP-STRAIGHT): each path of the L2⁺ blocks from `entry` reaches
a return, or a step that is `stuck` or `noFuel`, in a bounded number of blocks, so the proof needs no invariant and no loop row.
`lift_straight` walks the paths (one goal for each return and each fault), and `loop_close` closes each goal with the names of
`refinesL3Unfolds` (the L3 function, `objsP`, `heapOf`, the objects of the statement, `initP`, and the spec names of
`specUnfolds`):

    by
      intro <params> frame <inputs>
      intro x a y hs hy
      split_hyps
      lift_straight! [<unfolds>]
-/
def straightL3Proof (p : UpperPlan) (sh : StmtShape) : String :=
  let fm := sh.form
  let frameArgs := " ".intercalate (p.params.map (·.name.s) ++ ["frame"])
  let unfolds := refinesL3Unfolds p sh
  let names := if unfolds.isEmpty then "" else s!" [{", ".intercalate unfolds}]"
  "\n".intercalate [ "by", s!"  intro {" ".intercalate (frameArgs :: fm.modelArgs)}",
    s!"  intro {fm.pat} {freshName sh p "a"} {freshName sh p "y"} hs hy", "  split_hyps", s!"  lift_straight!{names}" ]

/-- The entry block reads the heap: an access whose address is no stack word. Its step in the L2⁺ text is a `match` on the
load, which `.goto rfl` does not reduce (PIL-HEAP2). -/
def entryReadsHeap (bs : List Block) : Bool :=
  (blockAt bs 0).any fun b => b.accesses.any fun | .load _ a _ | .store _ a _ _ => !a.usesRsp

/-- The proof text of `refines_l3` for a head `h` whose path from the entry reads the heap (PIL-HEAP2). `lift_straight exits
[.<head>]` walks the paths from `entry` to the head; the walk splits each entry load. At the head (the goal `exit_1`, the
load `ok`) the loop row gives the return: its loaded values are `_` and their hypotheses come from the facts of the path
(`‹_›`). Each goal `nofault_k` (a load that is `stuck` or `noFuel`) is closed by `heap_fault` from `SimArr` (the heap is the
objects of the statement and the frame, and the address is a cell of an object), else by `loop_close`:

    by
      intro <params> frame <inputs>
      intro x a y hs hy
      lift_straight exits [.<head>]
      case exit_1 => exact Lift.Sem.Visits.exit (loop.<head> <params> frame x a y _ hs ‹_› hy) <out>
      all_goals (split_hyps; first | heap_fault [<unfolds>] | loop_close [<unfolds>])

A narrow value and a `both` result take the existential loop row apart before `Visits.exit`, as `refinesL3Proof` does. -/
def entryL3Proof (p : UpperPlan) (sh : StmtShape) (h : Head) (exists_ : Bool) (out : String) : String :=
  let fm := sh.form
  let frameArgs := " ".intercalate (p.params.map (·.name.s) ++ ["frame"])
  let a := freshName sh p "a"
  let y := freshName sh p "y"
  let loads := h.state.filter fun | (_, .load ..) => true | _ => false
  let blanks := loads.map fun _ => "_"
  let facts := loads.map fun _ => "‹_›"
  let loop := s!"loop.{h.name.s} {" ".intercalate ([frameArgs] ++ fm.names ++ [a, y] ++ blanks ++ ["hs"] ++ facts ++ ["hy"])}"
  let names := ", ".intercalate (refinesL3Unfolds p sh)
  let atHead := if exists_ then
      [ "  case exit_1 =>", s!"    obtain ⟨res, hres, hrel⟩ := {loop}", "    exact Lift.Sem.Visits.exit hres hrel" ]
    else [ s!"  case exit_1 => exact Lift.Sem.Visits.exit ({loop}) {out}" ]
  "\n".intercalate ([ "by", s!"  intro {" ".intercalate (frameArgs :: fm.modelArgs)}",
    s!"  intro {fm.pat} {a} {y} hs hy", s!"  lift_straight exits [.{h.name.s}]" ] ++ atHead ++
    [ s!"  all_goals (split_hyps; first | heap_fault [{names}] | loop_close [{names}])" ])

/-- The proof text of `refines_l3` (see the top of the file) for the summary `s`, the plan `p` and the shape `sh`. A plan with
no loop head has the text of `straightL3Proof`; a plan with one head with a row (`rowHeads`: a head with a carried value has
no row) has the text below, or the text of `entryL3Proof` when the entry block reads the heap; a plan with two heads with a
row is an error. -/
def refinesL3Proof (s : Summary) (p : UpperPlan) (sh : StmtShape) : Except GenError String := do
  if usesRegions p then return regionsL3Proof p sh
  let h ← match rowHeads p with
    | [h] => pure h
    | [] =>
      if p.heads.isEmpty then return straightL3Proof p sh
      else throw (.unsupported 0 s!"refines_l3: the plan has {p.heads.length} loop heads and none with a row")
    | hs => throw (.unsupported 0 s!"refines_l3 has a generated proof for one loop head with a row, the plan has {hs.length}")
  let some hb := s.blocks.find? (·.name == h.name)
    | throw (.shape 0 s!"no block {h.name.s}")
  let exists_ := !(termResult p sh)
  let out := if p.kind == .heap then "⟨by split_hyps; assumption, rfl⟩" else if exists_ then "hrel" else "rfl"
  if entryReadsHeap s.blocks then return entryL3Proof p sh h exists_ out
  let n ← blocksToHead s.blocks hb (s.blocks.length + 1) 0
  let fm := sh.form
  let frameArgs := " ".intercalate (p.params.map (·.name.s) ++ ["frame"])
  let a := freshName sh p "a"
  let y := freshName sh p "y"
  let loop := s!"loop.{h.name.s} {" ".intercalate (frameArgs :: fm.names)} {a} {y} hs hy"
  let start := if exists_ then "hres" else loop
  let path := (List.range n).foldl (fun t _ => s!".goto rfl ({t})") start
  let intro := s!"  intro {fm.pat} {a} {y} hs hy\n" ++
    (if exists_ then s!"  obtain ⟨res, hres, hrel⟩ := {loop}\n" else "")
  pure ("by\n" ++ s!"  intro {" ".intercalate (frameArgs :: fm.modelArgs)}\n" ++ intro ++
    s!"  exact ⟨{if exists_ then "res" else "_"}, {path}, {out}⟩")

end Skel.Gen
