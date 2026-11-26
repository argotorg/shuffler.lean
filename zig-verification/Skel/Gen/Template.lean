import Skel.Gen.UpperPlan
import Skel.Gen.UpperRel
import Skel.Gen.Sampler
import Skel.Types

/-! The template triples of a loop head, generated from the upper plan (task G3-21a; `docs/one-way-lift-g3-plan-20261118.md`,
sections 4.6, 4.7 and 5.2; the triple form of `docs/research/class-r-coordinator-deepseek-20261118.md`, section 3).

`loopTemplates` gives a short list of candidates (invariant, measure, result) for the one loop head of a plan. The rules read
the head state (4.6), the classes of the state registers (5.2), the chain ghosts (4.7), the result kind and the L3 `run` of the
statement shape. They name no function, no label and no fixture. The refuter decides which candidate is kept.

The terms use the names of the slot (4.7), which the refute file binds (`Sampler.slotLets`) and the loop proof binds
(`loopSlots`): the state `x`, the input `a`, the list `xs` of the L3 input, its scalar fields by their names, the binders and
`frame` of an array, and `rest_<reg>` for a chain ghost.

The roles of a state register `r` (from its class and its head value):
* index: a counter that is `0` at the head. A counter is a scaled index or a branch operand (5.2); one that starts at `0`
  counts the steps of the scan of `xs`.
* bound: a counter that is the input register `s` at the head. It is compared with the index, and the head takes it from an
  input, so the loop keeps it.
* accumulator: an accumulator (5.2) that is `0` at the head: the part of the result that the loop has made so far.
A pointer has no role of its own: its ghost `rest_<reg>` (4.7) gives the chain that is left. A ghost is a function of the
state (D35): its text is `Lift.Sem.Heap.chain a.heap off x.<reg>.toBitVec`, the pointers of the walk from the register over
the words at `off` (the offset of the load of the ghost).

The rules (each conjunct of the invariant, each measure, each result):
* `x.i.toNat ≤ xs.length` for an index `i`: the scan stops at the end of `xs`, so the index is at most its length.
* `x.r = a.s` for a bound `r` from the input `s`: the head value of 4.6, which no step changes. A bound whose head value is a
  term (`HeadVal.term`, such as the minimum of two loads of the entry block, `headTerm`) gives `x.r = <term over a>`.
* `x.c + UInt64.ofNat rest_r.length = UInt64.ofNat xs.length` for an accumulator `c` and a ghost `rest_r`: the accumulator
  is `0` when the whole chain is left, and the chain is the list of the L3 input at the head, so each step moves one node
  from the chain to `c`. The sum is in `UInt64`: the 64-bit counter wraps, and the length of the list has no bound.
* `Lift.Sem.Heap.ends a.heap off x.r.toBitVec = true` for a ghost of `r`: the walk from the pointer reaches `0`, so a step
  of the loop loads the next pointer and the chain loses its head.
* A ghost of `r` whose nodes the loop reads (`valueLoads`: a load from `r + voff` in the cycle, `voff` not the offset of the
  ghost) has the values ghost `Lift.Sem.Heap.chainVals a.heap off voff x.r.toBitVec`, the value words of the nodes that are left.
  For such a ghost the rules above change: the count identity gives way to
  `x.c + UInt64.ofBitVec ((run vals).getD 0) = UInt64.ofBitVec ((run xs).getD 0)` for an accumulator `c` (the result of the whole
  input is the part made so far and the result of the nodes that are left), the walk has the values
  (`Lift.Sem.Heap.endsV a.heap off voff x.r.toBitVec = true` as well), and the part of a result is `vals`. A loop that reads
  no value of its nodes keeps the count identity and `rest_r` as the part: the result of `run` on the addresses is the
  count, which is the one case where the addresses stand for the values.
* `x.mem = heapOf <params> frame (((run xs).getD []).take x.i.toNat ++ xs.drop x.i.toNat)` for a heap result of a list
  input and an index `i`: the loop writes the result in the order of the index, so the cells below the index hold the
  result and the others the input.
* measure `xs.length - x.i.toNat` for an index `i`, and `rest_r.length` for a ghost: the part of the scan that is left.
* value result `x.c + UInt64.ofBitVec ((run rest).getD 0)` for an index or accumulator `c` and each part `rest` of the input
  that is left (`xs.drop x.i.toNat` for an index `i`, `rest_r` for a ghost; with the scalar fields for a structure input):
  the result of the whole input is the part made so far and the result of the part that is left.
* heap result `heapOf <params> frame ((run xs).getD [])` for a list input: the heap at the return does not depend on the
  state (D35: it is a function of the input).
A plan with no index and no ghost has no measure, and a head with no role for its registers has no result: the list is
empty, not a guess. A plan with two heads gives the empty list too.

A result narrower than 64 bits (L3-U7) is the whole register at the return, and `run` fixes its low bits only: the refuter
compares the low bits (`RefuteSpec.proj`). The result term is a word, `ValueTy.word` of the L3 value (`UInt64.ofNat v.toNat`
for a `BitVec`), the accumulator rule keeps its form, and a constant candidate is added, the word of the value of the whole
input: a scan that ends with an error code returns the same value from each state. A conjunct that has the sum of a word and
the value of the rest as a `UInt64` takes the low bits of the sum (a narrow value wraps at its own width).

A result that is a value and a heap (`both`, L3-U7) is the pair of the two parts: the value part as above, the heap part as the
heap rule, from the second component of `run` (`((run xs).getD (0, [])).2`; the pair form of `run`), for an array of a list
input with an index and a state that has the memory, and a statement with one input (`heapOf` has the one input). -/

namespace Skel.Gen

/-- The text of a state field `x.<reg>`. -/
private def field (r : Reg64) : String := s!"x.{regLower r}"

/-- The text of the chain ghost `g` (4.7, D35): the pointers of the walk from the state register over the heap of `a`. -/
private def chainText (g : Ghost) : String := s!"(Lift.Sem.Heap.chain a.heap {g.off} {field g.reg}.toBitVec)"

/-- The conjunct of the chain ghost `g`: the walk from the state register reaches `0`. -/
private def endsText (g : Ghost) : String := s!"Lift.Sem.Heap.ends a.heap {g.off} {field g.reg}.toBitVec = true"

/-- The text of the values ghost of `g` with the value offset `voff`: the value words of the nodes of the chain that is left. -/
private def valsText (g : Ghost) (voff : Nat) : String :=
  s!"(Lift.Sem.Heap.chainVals a.heap {g.off} {voff} {field g.reg}.toBitVec)"

/-- The conjunct of the values ghost: the walk reaches `0`, and each load of a value word is `ok`. -/
private def endsValsText (g : Ghost) (voff : Nat) : String :=
  s!"Lift.Sem.Heap.endsV a.heap {g.off} {voff} {field g.reg}.toBitVec = true"

/-- The value offsets of the chain ghosts of the plan `pl` for the blocks `bs`: for a ghost `g`, the offset `c` of a load from
`g.reg + c` in a block of the cycle of the head, `c` not the offset of the ghost. The loop reads the value word of each node
there. The first offset of a ghost is its value offset. A plan with no single head has none. -/
def valueLoads (bs : List Block) (pl : UpperPlan) : List (Reg64 × Nat) :=
  match pl.heads with
  | [h] =>
    match bs.find? (·.name.s == h.name.s) with
    | some hb =>
      let cyc := cycleOf bs hb.offset
      let loads := (bs.filter fun b => cyc.contains b.offset).flatMap fun b =>
        b.accesses.filterMap fun | .load _ a _ => some a | .store .. => none
      pl.ghosts.filterMap fun g =>
        ((loads.filterMap (chainOffset g.reg)).find? (· != g.off)).map (g.reg, ·)
    | none => []
  | _ => []

/-- The registers of the state whose class is `c` and whose head value satisfies `p`, in the order of the state. -/
private def withRole (pl : UpperPlan) (h : Head) (c : FieldClass) (p : HeadVal → Bool) : List Reg64 :=
  pl.state.filterMap fun (r, c') =>
    if c' == c && (h.state.find? (·.1 == r)).any (p ·.2) then some r else none

private def isZero : HeadVal → Bool
  | .lit n => n == 0
  | .input _ | .load .. | .term _ | .carried => false

/-- The bounds: each counter with the text of its head value over `a`, when the value is an input register or a term (a term
of the inputs and of the loads of the entry block, `headTerm`: the minimum of two sizes, MAP-HEAD). -/
private def bounds (pl : UpperPlan) (h : Head) : List (Reg64 × String) :=
  pl.state.filterMap fun (r, c) =>
    if c != .counter then none else
    match h.state.find? (·.1 == r) with
    | some (_, .input s) => some (r, s!"a.{regLower s}")
    | some (_, .term t) => some (r, s!"({t.replace "x.input." "a."})")
    | _ => none

/-- The L3 input, as the arguments of `run`, of a part `rest` of the list: the list itself, or the structure with `rest` as its
list field and the scalar fields by their names, or, for several inputs, each input by name with `rest` for the list. -/
private def inputOf (shape : InShape) (rest : String) : String :=
  match shape with
  | .list .. => s!"({rest})"
  | .record _ inTy l ss =>
    "({ " ++ ", ".intercalate ((s!"{l} := {rest}") :: ss.map fun s => s!"{s} := {s}") ++ s!" } : {inTy})"
  | .flat inputs l =>
    " ".intercalate (inputs.map fun (n, _) => if n == l then s!"({n} := {rest})" else s!"({n} := {n})")

/-- Bind the original input to a part of its list before reading copied statement terms. -/
def InShape.withInput (shape : InShape) (rest body : String) : String :=
  match shape with
  | .list inp inTy => s!"(let {inp} : {inTy} := ({rest}); {body})"
  | .record inp .. => s!"(let {inp} := {inputOf shape rest}; {body})"
  | .flat _ l => s!"(let {l} : List (BitVec 64) := ({rest}); {body})"

/-- The stored run expression with a part of the input list. Old shapes use their input arguments. -/
def runAtInput (sh : StmtShape) (shape : InShape) (rest : String) : String :=
  if sh.runCall.isSome then shape.withInput rest sh.runApplication
  else s!"{runName sh} {inputOf shape rest}"

/-- The register word of a run result, with its projection in the input scope. -/
def runWordAtInput (sh : StmtShape) (shape : InShape) (val : ValueTy) (rest : String) (both : Bool := false) : String :=
  if sh.resultFn.isSome then
    let y := freshAmong sh.names "yRun"
    shape.withInput rest s!"(({sh.runApplication}).map (fun {y} => {resultWord val sh.resultFn y})).getD 0"
  else
    let call := runAtInput sh shape rest
    val.word (if both then s!"(({call}).getD ({val.dflt}, [])).1" else s!"({call}).getD {val.dflt}")

/-- The parameters, the first arguments of `heapOf` before the frame. -/
private def heapArgs (pl : UpperPlan) : String := " ".intercalate (pl.params.map (·.name.s))

/-- The candidates of the head `h` (see the rules at the top of the file), with the L3 input of the shape `shape`, and the value
offsets `vals` of the ghosts (`valueLoads`). -/
private def templatesAt (pl : UpperPlan) (sh : StmtShape) (shape : InShape) (h : Head) (vals : List (Reg64 × Nat)) :
    List Triple :=
  let run := runName sh
  let idx := withRole pl h .counter isZero
  let accs := withRole pl h .accumulator isZero
  let voffOf (g : Ghost) : Option Nat := (vals.find? (·.1 == g.reg)).map (·.2)
  -- the part of the input that a ghost leaves: the values of the nodes that are left, or the chain itself
  let restOf (g : Ghost) : String := match voffOf g with
    | some v => valsText g v
    | none => chainText g
  let rests := pl.ghosts.map restOf
  let isBoth := pl.kind == .both
  let dflt := pl.val.dflt
  let wordOf (rest : String) : String := runWordAtInput sh shape pl.val rest isBoth
  -- the new contents of the array that `run` gives on the whole input
  let whole := if sh.runCall.isSome then runAtInput sh shape "xs" else s!"{run} xs"
  let contents : String := if isBoth then s!"(({whole}).getD ({dflt}, [])).2" else s!"(({whole}).getD [])"
  let heapList := sh.resultFn.isNone && (pl.kind == .heap || (isBoth && sh.form matches .one _)) && pl.mem &&
    (match shape with | .list .. => true | _ => false)
  let conjuncts :=
    idx.map (fun i => s!"{field i}.toNat ≤ xs.length") ++
    (bounds pl h).map (fun (r, v) => s!"{field r} = {v}") ++
    accs.flatMap (fun c => pl.ghosts.map fun g => match voffOf g with
      | some v =>
        if pl.val.isWord then
          s!"{field c} + {wordOf (valsText g v)} = {wordOf "xs"}"
        else
          s!"({field c} + {wordOf (valsText g v)}) &&& {pl.val.mask} = {wordOf "xs"}"
      | none => s!"{field c} + UInt64.ofNat {chainText g}.length = UInt64.ofNat xs.length") ++
    pl.ghosts.flatMap (fun g => endsText g :: (voffOf g).toList.map (endsValsText g)) ++
    (if heapList then idx.map fun i =>
      s!"x.mem = heapOf {heapArgs pl} frame ({contents}.take {field i}.toNat ++ xs.drop {field i}.toNat)"
     else [])
  let inv := if conjuncts.isEmpty then "True" else " ∧ ".intercalate conjuncts
  let measures := idx.map (fun i => s!"xs.length - {field i}.toNat") ++ pl.ghosts.map (s!"{chainText ·}.length")
  let parts := idx.map (fun i => s!"xs.drop {field i}.toNat") ++ rests
  let heapTerm := s!"heapOf {heapArgs pl} frame {contents}"
  let accumulated := parts.flatMap fun rest => (accs ++ idx).map fun c => s!"{field c} + {wordOf rest}"
  let results :=
    match pl.kind with
    | .value =>
      if pl.val.isWord then accumulated
      -- a narrow value: the accumulator rule, then the constant (a scan that ends with a code returns the same value)
      else accumulated ++ [wordOf "xs"]
    | .heap => if heapList then [heapTerm] else []
    | .both =>
      if heapList then (accumulated ++ [wordOf "xs"]).map fun w => s!"({w}, {heapTerm})" else []
  (measures.flatMap fun m => results.map fun r => ({ inv, measure := m, result := r } : Triple)).eraseDups

/-- The template triples of the loop of the plan `pl` with the statement shape `sh` and the value offsets `vals` of its ghosts
(`valueLoads`; none: the loop reads no value of its nodes) (see the top of the file). A plan with no
single fixed head, or an input that is no list and no structure with one list field, gives none. -/
def loopTemplates (pl : UpperPlan) (sh : StmtShape) (vals : List (Reg64 × Nat) := []) : List Triple :=
  match pl.heads, inShapeOf sh with
  | [h], .ok shape => if h.generalized then [] else templatesAt pl sh shape h vals
  | _, _ => []

/-- The argument registers of System V, in order (`Lift/Trusted/Call.lean`, `argRegs`). -/
private def argRegs : List Reg64 := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]

/-- The first word of a term: the name of the function of an application. -/
private def headWord (t : String) : String := (t.splitOn " ").headD ""

/-- The name of a constant that the term `t` applies, for the unfold list of a simp call: the first word of `t` without the
parentheses before it, when it has the form of a constant name (it starts with a letter and has only letters, digits, `.`,
`_` and `'`) and it is no method of a local (its first component is none of `locals`: `ps.headD` applies `List.headD` to the
local `ps`, and the environment has no constant of that name). A numeral, a local, a method of a local and a term that
is no application of a name give none. -/
private def constWord (locals : List String) (t : String) : Option String :=
  let w := ((headWord t).dropWhile (· == '(')).toString
  let first := (w.splitOn ".").headD ""
  if (w.toList.headD ' ').isAlpha && w.all (fun c => c.isAlphanum || c == '.' || c == '_' || c == '\'') &&
      !locals.contains first then some w else none

/-- The lines of the fact `hchain` of a list input with one chain ghost (4.7), after the slot lines of `xs`: for each list
`xs`, binders and frame that the hypotheses of the statement admit and a memory holds, the chain from the argument of the
ghost register over the heap `objsP … xs ++ frame` is the list binder of the addresses, and the walk ends. The proof shows
that the objects of the statement are linked (`Lift.Sem.Heap.Linked`) by induction on `xs` with the definitions of the
objects and of the argument, then uses `Lift.Sem.Heap.chain_of_linked`. The closing step of the loop proof takes the fact
with the hypotheses of the row. A ghost with a value offset in `vals` (`valueLoads`) adds to the fact the walk with values
(`Lift.Sem.Heap.endsV`) and the equation `Lift.Sem.Heap.chainVals … = xs` (the value words of the chain are the list of the L3
input), shown with `Lift.Sem.Heap.LinkedVals` by a second induction and `Lift.Sem.Heap.chain_of_linked_v`. No line when the plan has no single ghost, no single head, no list binder, or the ghost
register at the head is no argument, or the statement has none or several inputs (no pilot function has a chain with a flat
input: the fact would generalize over each input). -/
private def chainFactOne (pl : UpperPlan) (sh : StmtShape) (vals : List (Reg64 × Nat)) (b : ShapeBinder) : List String :=
  match pl.ghosts, pl.heads, pl.params.find? (·.ty == .addrs) with
  | [g], [h], some ps =>
    match h.state.find? (·.1 == g.reg) with
    | some (_, .input s) =>
      match ((argRegs.zip sh.args).find? (·.1 == s)).map (·.2) with
      | some arg =>
        let x := b.name.s
        let voff := (vals.find? (·.1 == g.reg)).map (·.2)
        let names := " ".intercalate (pl.params.map (·.name.s))
        let heap := s!"(objsP {names} xs ++ frame)"
        let argT := renameVar x "xs" arg.term.s
        let hyps := sh.hyps.map fun hy => s!"({renameVar x "xs" hy.s}) → "
        let unders := " ".intercalate (sh.hyps.map fun _ => "_")
        let locals := x :: "xs" :: "frame" :: "a" :: pl.params.map (·.name.s) ++ sh.binders.map (·.name.s)
        let objsHead := (constWord locals sh.objs.s).toList
        let simpNames := ["objsP"] ++ objsHead ++ (constWord locals argT).toList
        let simpsWith (linked : String) := ", ".intercalate (simpNames ++ [linked, "Lift.Sem.Bridge.toObj",
          "Lift.Sem.Bridge.toCell", "Lift.Trusted.Encode.encode", "Lift.Sem.Obj.get", "Lift.Sem.offsets", "Lift.Sem.Cell.get"])
        -- the induction on the list that shows the objects linked: `Linked` of the next words, `LinkedVals` of the value words
        let induct (hname linked : String) (stmt : String) : List String :=
          [s!"  have {hname} : {stmt} := by",
           s!"    clear hh{if hname == "hl" then "" else " hl"}",
           s!"    induction xs generalizing {ps.name.s} with",
           s!"    | nil => cases {ps.name.s} <;> simp_all [{", ".intercalate ("objsP" :: objsHead)}, {linked}]",
           "    | cons v₀ vs₀ ih₀ =>",
           s!"      cases {ps.name.s} with",
           "      | nil => simp_all",
           "      | cons q₀ qs₀ =>",
           s!"        cases qs₀ <;> simp_all [{simpsWith linked}]"]
        let walk := s!"Lift.Sem.Heap.chain {heap} {g.off} ({argT}) = {ps.name.s} ∧ " ++
          s!"Lift.Sem.Heap.ends {heap} {g.off} ({argT}) = true" ++
          (voff.map fun v => s!" ∧ Lift.Sem.Heap.endsV {heap} {g.off} {v} ({argT}) = true ∧ " ++
            s!"Lift.Sem.Heap.chainVals {heap} {g.off} {v} ({argT}) = xs").getD ""
        [s!"have hchain : ∀ (xs : {b.type.s}) {" ".intercalate (pl.params.map binderText)} (frame : Lift.Sem.Heap) " ++
            s!"(policy : Lift.P2.Total.CpuPolicy) (m : DataMem), {String.join hyps}Lift.Sem.Heap.Holds policy {heap} m → " ++
            walk ++ " := by",
          s!"  intro xs {names} frame policy m {unders} hh"] ++
          induct "hl" "Lift.Sem.Heap.Linked" s!"Lift.Sem.Heap.Linked {g.off} (objsP {names} xs) {ps.name.s}" ++
          (voff.map fun v => induct "hlv" "Lift.Sem.Heap.LinkedVals"
            s!"Lift.Sem.Heap.LinkedVals {v} (objsP {names} xs) {ps.name.s} xs").getD [] ++
          [s!"  have e : {argT} = {ps.name.s}.headD 0 := by cases {ps.name.s} <;> rfl",
           "  rw [e]"] ++
          (match voff with
            | none => ["  exact Lift.Sem.Heap.chain_of_linked hh hl ‹_›"]
            | some _ =>
              ["  obtain ⟨hc, he, hv, hs⟩ := Lift.Sem.Heap.chain_of_linked_v hh hl hlv ‹_›",
               "  refine ⟨hc, he, hv, ?_⟩",
               "  unfold Lift.Sem.Heap.chainVals",
               "  rw [hc]",
               "  exact hs"])
      | none => []
    | _ => []
  | _, _, _ => []

/-- The lines of the fact `hchain` (see `chainFactOne`): the statement with one input has them, any other has none. -/
def chainFact (pl : UpperPlan) (sh : StmtShape) (vals : List (Reg64 × Nat) := []) : List String :=
  match sh.form with
  | .one b => chainFactOne pl sh vals b
  | .flat _ => []

/-- The lines of the loop proof that bind the names of the slot (4.7) after the `intro` of the binders: `xs` and each scalar
field, from the L3 input of the statement. `generalize` keeps the equation, so the closing step can substitute it. Several
inputs are variables already: the list input is named `xs` by one `generalize` (none when it has the name), and each scalar
has its name. A chain ghost is a term of the state (`chainText`); for it the lines end with the fact `hchain` (`chainFact`).
One input with no list form is the slot `inp` (`objectsInputSlot`), the name of the refute spec of the family `objects` (DISC-BOUND:
the result term of the discovery names `inp`; the statement names the input `x`, which `fun x =>` of `lift_loop!` hides). -/
def loopSlots (pl : UpperPlan) (sh : StmtShape) (vals : List (Reg64 × Nat) := []) : List String :=
  match inShapeOf sh with
  | .ok (.list x _) => [s!"generalize hxs : {x} = xs"] ++ chainFact pl sh vals
  | .ok (.record x _ l ss) => s!"generalize hxs : {x}.{l} = xs" :: ss.map fun s => s!"generalize h_{s} : {x}.{s} = {s}"
  | .ok (.flat _ l) => if l == "xs" then [] else [s!"generalize hxs : {l} = xs"]
  | .error _ =>
    match sh.form with
    | .one b => if b.name.s == objectsInputSlot then [] else [s!"generalize hinp : {b.name.s} = {objectsInputSlot}"]
    | .flat _ => []

/-- The names that the closing step of the loop proof (`lift_loop! … [names]`) unfolds: the `run` of the spec, `objsP`,
`heapOf` for a heap result, and the head of the object term of the statement when it is a name (such as `S.objects` of
`S.objects x p`). The closing step then sees the heap as a list
of `Obj.words` and the frame (the simp set `heap_norm`), and the result of the spec as a term of lists. -/
def loopUnfolds (pl : UpperPlan) (sh : StmtShape) : List String :=
  let head := (sh.objs.s.splitOn " ").headD ""
  let objsHead := if !head.isEmpty && head.all (fun c => c.isAlphanum || c == '.' || c == '_') &&
      (head.toList.headD ' ').isAlpha then [head] else []
  let heaps := if pl.kind == .heap then
    (match sh.form with | .one _ => ["heapOf"] | .flat _ => []) ++
      (if sh.runOutputObjs.isSome then ["outHeap"] else [])
    else []
  [runName sh, "objsP"] ++ heaps ++ objsHead

end Skel.Gen
