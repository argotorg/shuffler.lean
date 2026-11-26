import Skel.Gen.GenerateUpper
import Skel.Discover.SpecFeatures
import Skel.Render
import Skel.Io
import Skel.Toy.MachineDiscover
import Skel.Discover.Result
import Skel.Discover.Regions
import Skel.Discover.RegionTasks
import Skel.Report.Level3

/-! The discovery ladder on the loop rows of `generateUpper`, for any function (task DISC-WIRE). The input is a function with
its generated upper chain (`FnUnit`): the toys, level 2 and the pilot give one each (`Skel/Discover/Targets.lean`).

* `sitesOf`: each loop head of the plan is a site with a form (`Form`). The form comes from the blocks: the heads that the
  pass of the head reaches, and the heads that reach it. Only a head with the form `alone` (a loop from the entry whose pass
  reaches no other head) has the machine site of D11b now. The other forms are named errors (`SiteError.form`): loops in
  sequence need `lift_loop … exits [l]`, a nested loop needs `loop_vc_ih` in the outer step, and a head after a loop or inside
  a loop has carried values and no row of its own.
* `machineFor`: the machine (`MachineDiscover.Machine`) of a site: the refute spec, the loop row `loop.<head>`, the result
  term (given, else the result of the first template rule when the templates are on, else none), the spec context
  (`specCtxOf`, INV-D4c) and the check of the row with a triple.
* `discoverResult` (DISC-RESULT): the candidates of the result term (`Skel/Discover/Result.lean`: spec-suffix, spec-step,
  and the template results only when the templates are on), the screen of the candidates on the traces, then the ladder with
  each candidate that fits, until one closes.
* `discoverSite`: the template triples first (when `Config.useTemplates`), then `discoverResult`. A found quad gives the
  triple of the row; with no quad that closes, the row is open and the ledger is kept.
* `discoverFn`, `RunSummary`: all the sites of a function, and the summary file `discover-summary.json`. -/

namespace Skel.Discover.Upper

open Skel Skel.Gen Skel.Discover Skel.Toy.MachineDiscover
open System (FilePath)
open Lean (Json ToJson toJson)

/-- A function with its generated upper chain: the name, the upper chain, its plan, its statement shape, its blocks and the
header of its check files. -/
structure FnUnit where
  fn : String
  upper : Upper
  plan : UpperPlan
  shape : StmtShape
  blocks : List Block
  header : Header
  /-- The callees of the target (HARNESS-LOOP2 H5): a loop that calls one of them runs it by its model (`runnerOf`). -/
  callees : List Callee := []

/-- The form of a loop head, from the blocks.
* `alone`: the pass from the head reaches no other head (the machine site of D11b);
* `before later`: the loop exits to the later heads (loops in sequence);
* `outer inner`: the pass holds the heads of inner loops (a nested loop);
* `after earlier`: the head is after the loops of `earlier` (its state carries their values);
* `inner outer`: the head is inside the loops of `outer`. -/
inductive Form where
  | alone
  | before (later : List String)
  | outer (inner : List String)
  | after (earlier : List String)
  | inner (outer : List String)
  deriving DecidableEq, Repr

/-- The short name of a form. -/
def Form.tag : Form → String
  | .alone => "alone"
  | .before _ => "sequence"
  | .outer _ => "nested"
  | .after _ => "after-loop"
  | .inner _ => "inner-loop"

/-- The text of a form, with the heads that it names. -/
def Form.text : Form → String
  | .alone => "alone"
  | .before l => s!"sequence: the loop exits to the head {", ".intercalate l}"
  | .outer l => s!"nested: the pass holds the inner head {", ".intercalate l}"
  | .after l => s!"after-loop: the head takes carried values of the loop at {", ".intercalate l}"
  | .inner l => s!"inner-loop: the head is inside the loop at {", ".intercalate l}"

/-- A loop site of a function: the function, the head label (without `Lbl.`) and its form. -/
structure Site where
  fn : String
  head : String
  form : Form
  deriving DecidableEq, Repr

/-- Why a site has no machine. Each error names its cause. -/
inductive SiteError where
  /-- The form of the head has no machine site now. -/
  | form (f : Form)
  /-- The plan has no row `loop.<head>`. -/
  | noRow (head : String)
  /-- The sampler of the function has no refute spec. -/
  | noRefuteSpec (cause : String)
  /-- The plan has no template rule, so the loop has no result text. -/
  | noResult
  /-- The cycle of the head has a call: a machine site has no call (`machineStepExpr`). -/
  | callInLoop (callees : List String)
  deriving DecidableEq, Repr

/-- The form that a site of the form `f` needs, and why the machine site does not cover it now. -/
def need : Form → String
  | .alone => ""
  | .before _ => "the row needs `lift_loop … exits [l]` and the triple of each later head; the machine site has no exit to a later head"
  | .outer _ => "the outer step needs the result of the inner loop by `loop_vc_ih`; the pass of a machine site has no loop inside it"
  | .after _ => "its triple is a lemma in the proof of the earlier row (`Visits.exit`); it has no row of its own"
  | .inner _ => "its triple is the hypothesis of the outer step (`loop_vc_ih`); it has no row of its own"

/-- The text of an error: its name, then its cause. -/
def SiteError.text : SiteError → String
  | .form f => s!"form {f.tag}: {f.text}; {need f}"
  | .noRow h => s!"no-row: the plan has no row loop.{h}"
  | .noRefuteSpec c => s!"no-refute-spec: {c}"
  | .noResult => "no-result: the plan has no template rule for the result of the loop"
  | .callInLoop cs => s!"unsupported: call in loop: the cycle of the head calls {", ".intercalate cs}"

/-! ## The sites -/

/-- The offset of the block `name`. -/
def offsetOf (bs : List Block) (name : String) : Option Nat := (bs.find? (·.name.s == name)).map (·.offset)

/-- The block at the offset `a` reaches the offset `b`. -/
def reaches (bs : List Block) (a b : Option Nat) : Bool :=
  match a, b with
  | some x, some y => x != y && (reachFrom bs none x).contains y
  | _, _ => false

/-- Each path from the entry (offset 0) to `b` passes `a`. -/
def dominates (bs : List Block) (a b : Option Nat) : Bool :=
  match a, b with
  | some x, some y => !(reachFrom bs (some x) 0).contains y
  | _, _ => false

/-- The form of the head `h` among the heads `hs` of the blocks `bs`. Two heads on one cycle are an outer and an inner head: the
outer one dominates the inner one. Two heads that are not on one cycle are an earlier and a later head. -/
def formOf (bs : List Block) (hs : List String) (h : String) : Form :=
  let me := offsetOf bs h
  let others := hs.filter (· != h)
  let at_ (o : String) := offsetOf bs o
  let cycle (o : String) := reaches bs me (at_ o) && reaches bs (at_ o) me
  let outer := others.filter fun o => cycle o && dominates bs (at_ o) me
  let inner := others.filter fun o => cycle o && dominates bs me (at_ o)
  let earlier := others.filter fun o => reaches bs (at_ o) me && !cycle o
  let later := others.filter fun o => reaches bs me (at_ o) && !cycle o
  if !outer.isEmpty then .inner outer
  else if !earlier.isEmpty then .after earlier
  else if !inner.isEmpty then .outer inner
  else if !later.isEmpty then .before later
  else .alone

/-- The sites of the function `fn` with the blocks `bs` and the loop heads `hs`, in the order of the heads. -/
def sitesIn (fn : String) (bs : List Block) (hs : List String) : List Site :=
  hs.map fun h => { fn, head := h, form := formOf bs hs h }

/-- The sites of a function: one for each loop head of its plan. -/
def sitesOf (u : FnUnit) : List Site := sitesIn u.fn u.blocks (u.plan.heads.map (·.name.s))

/-! ## The goals of a head (DISC-WIRE2)

Each head has one loop goal `∀ x, INV x → blocksP.Returns noCall .H x (OUT x)`, the goals of `lift_loop` on it, and an entry.
The rules read the blocks only:
* entry: `start` for a head that the entry of the function reaches on a straight path (its state is the state of the plan);
  `exitOf l` for a head after the loops `l` (the entry goal is the exit goal of each loop of `l` to this head:
  `Visits.exit` with the loop goal of this head at the state that the earlier loop leaves); `inside l` for a head inside the
  loops `l` (the goal is proved in the step of the outer loop, by `loop_vc_ih`, with the outer invariant in the context);
* exits: one for each path of the pass from the head that does not jump back to it: a return at a block (`ret_k`), or a jump
  to another head (`exit_k`, the label for `lift_loop … exits [l]`);
* carried: the registers of the head state that an earlier or an outer loop gives (`HeadVal.carried` of the plan);
* live: the registers of the head state that a path after an exit of the cycle reads before it writes them (a return reads
  `rax`);
* calls: the callees of the blocks on the cycle of the head. -/

/-- Where the state at a head comes from. -/
inductive Entry where
  | start
  | exitOf (earlier : List String)
  | inside (outer : List String)
  deriving DecidableEq, Repr

/-- The text of an entry. -/
def Entry.text : Entry → String
  | .start => "start"
  | .exitOf l => s!"exit of {", ".intercalate l}"
  | .inside l => s!"inside {", ".intercalate l}"

/-- An end of a path of the pass from a head, other than the jump back to the head. -/
inductive End where
  | ret (block : String)
  | head (h : String)
  deriving DecidableEq, Repr

/-- The goals of one head (see above). -/
structure HeadGoals where
  head : String
  entry : Entry
  exits : List End
  carried : List Reg64
  live : List Reg64
  calls : List String
  deriving DecidableEq, Repr

/-- The entry of a head of the form `f`. -/
def Entry.ofForm : Form → Entry
  | .after l => .exitOf l
  | .inner l => .inside l
  | _ => .start

/-- The exits of a block term, in the order of the branch. -/
def termExits : Term → List Skel.Gen.Exit
  | .exit e => [e]
  | .branch _ y n => [y, n]

/-- The ends of the paths of the pass from the head at the offset `h`, in the order of the paths. A path stops at a return, at
a jump back to `h` (no end), at a jump to an offset of `heads` (another head), at a trap (no end) and at a block that it has
seen (no end; the pass of a head visits a block once). A call goes on at its continuation. -/
def passEnds (bs : List Block) (heads : List (Nat × String)) (h : Nat) : List End :=
  go (bs.length + 1) h []
where
  go : Nat → Nat → List Nat → List End
  | 0, _, _ => []
  | fuel + 1, o, seen =>
    if !seen.isEmpty && o == h then []
    else if !seen.isEmpty && (heads.lookup o).isSome then (heads.lookup o).toList.map .head
    else if seen.contains o then []
    else match blockAt bs o with
      | none => []
      | some b => (termExits b.term).flatMap fun
        | .ret => [.ret b.name.s]
        | .trap => []
        | .goto t => go fuel t (o :: seen)
        | .call _ k => go fuel k (o :: seen)

/-- The registers that the block `b` reads: its values, its accesses, its branch condition, and `rax` at a return. -/
def blockReads (b : Block) : List Reg64 :=
  b.regs.flatMap (readsOfVal ·.2) ++ b.accesses.flatMap (fun
    | .load _ a _ => readsOfVal a
    | .store _ a _ v => readsOfVal a ++ readsOfVal v) ++ readsOfTerm b.term ++
    (if (termExits b.term).any (· matches .ret) then [.rax] else [])

/-- The registers live at the start of each block (by offset): a backward fixpoint of at most `bs.length + 1` rounds of
`live b = reads b ∪ (live of the successors \ writes b)`. -/
def liveIn (bs : List Block) : List (Nat × List Reg64) :=
  go (bs.length + 1) (bs.map fun b => (b.offset, (blockReads b).eraseDups))
where
  round (cur : List (Nat × List Reg64)) : List (Nat × List Reg64) :=
    bs.map fun b =>
      let out := (successors b).flatMap fun s => (cur.lookup s).getD []
      let writes := b.regs.map (·.1)
      (b.offset, ((blockReads b) ++ out.filter (!writes.contains ·)).eraseDups)
  go : Nat → List (Nat × List Reg64) → List (Nat × List Reg64)
  | 0, cur => cur
  | fuel + 1, cur => let nxt := round cur; if nxt == cur then cur else go fuel nxt

/-- The offsets reached from `start` without entering an offset of `avoid` (as `reachFrom`, with a list). -/
def reachAvoid (bs : List Block) (avoid : List Nat) (start : Nat) : List Nat :=
  go (2 * bs.length + 1) [start] []
where
  go : Nat → List Nat → List Nat → List Nat
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, o :: stack, seen =>
    if seen.contains o || avoid.contains o then go fuel stack seen
    else go fuel (stack ++ ((blockAt bs o).map successors).getD []) (o :: seen)

/-- The cycle of the head at `h` inside the outer heads at `outer`: the blocks that `h` reaches and that reach `h`, each without
entering an outer head. With no outer head it is `cycleOf`. -/
def ownCycle (bs : List Block) (outer : List Nat) (h : Nat) : List Nat :=
  (reachAvoid bs outer h).filter fun o => (blockAt bs o).isSome && (reachAvoid bs outer o).contains h

/-- The registers of `state` that are live after an exit of the cycle of the head at `h` (inside the outer heads `outer`):
live at the target of an edge from the cycle to a block off it, or read by a return on the cycle. -/
def liveAfter (bs : List Block) (outer : List Nat) (h : Nat) (state : List Reg64) : List Reg64 :=
  let cyc := ownCycle bs outer h
  let live := liveIn bs
  let after := (bs.filter (cyc.contains ·.offset)).flatMap fun b =>
    (if (termExits b.term).any (· matches .ret) then [Reg64.rax] else []) ++
      ((successors b).filter (!cyc.contains ·)).flatMap fun s => (live.lookup s).getD []
  state.filter after.contains

/-- The callees of the blocks on the cycle of the head at `h` (inside the outer heads `outer`). -/
def callsOn (bs : List Block) (outer : List Nat) (h : Nat) : List String :=
  let cyc := ownCycle bs outer h
  ((bs.filter (cyc.contains ·.offset)).flatMap fun b => (termExits b.term).filterMap fun
    | .call c _ => some c
    | _ => none).eraseDups

/-- The goals of the head `h` with the state `state` (each register and whether it is carried), among the heads `hs` of the
blocks `bs`. -/
def headGoalsIn (bs : List Block) (hs : List String) (h : String) (state : List (Reg64 × Bool)) : HeadGoals :=
  let heads := hs.filterMap fun n => (offsetOf bs n).map (·, n)
  let off := (offsetOf bs h).getD 0
  let form := formOf bs hs h
  let outer := match form with
    | .inner l => l.filterMap (offsetOf bs ·)
    | _ => []
  { head := h, entry := .ofForm form, exits := passEnds bs heads off,
    carried := state.filterMap fun (r, c) => if c then some r else none,
    live := liveAfter bs outer off (state.map (·.1)), calls := callsOn bs outer off }

/-- The goals of each head of the plan of `u`, in the order of the heads. -/
def headGoalsOf (u : FnUnit) : List HeadGoals :=
  let hs := u.plan.heads.map (·.name.s)
  u.plan.heads.map fun h => headGoalsIn u.blocks hs h.name.s (h.state.map fun (r, v) => (r, v == .carried))

/-- The names of the goals of a head, as `lift_loop` tags them: `entry` (with its source), then `back` (the step goals of the
jump back), then `ret_k` and `exit_k` for the exits in their order. -/
def HeadGoals.names (g : HeadGoals) : List String :=
  let rets := (g.exits.filter (· matches .ret _)).length
  let outs := g.exits.filterMap fun | .head l => some l | _ => none
  [s!"entry ({g.entry.text})", "back"] ++ (List.range rets).map (s!"ret_{· + 1}") ++
    (outs.zipIdx.map fun (l, i) => s!"exit_{i + 1} ({l})")

/-- The loop goal of a head, as Lean text over `INV` and `OUT` of the head. -/
def HeadGoals.statement (g : HeadGoals) : String :=
  s!"∀ x, INV_{g.head} x → blocksP.Returns noCall .{g.head} x (OUT_{g.head} x)"

/-! ## The spec context and the machine -/

/-- The form of the L3 input of an input shape. -/
def l3Form : InShape → L3Form
  | .list .. => .list
  | .record _ ty l ss => .record ty l ss
  | .flat inputs l => .flat (inputs.map (·.1)) l

/-- The inputs of the spec items (INV-D4c) from the plan `pl` and the statement shape `sh`: the L3 function and the form of
its input, the slot names of the loop row (the list `xs`, the input `a` and its heap), the counters and the accumulators of the
state by their class, the chain ghosts of the plan, and the result kind (a heap result with its memory field and the
parameters of `heapOf`). A shape with no input form gives none. -/
def specCtxOf (pl : UpperPlan) (sh : StmtShape) : Option SpecCtx :=
  match inShapeOf sh with
  | .error _ => none
  | .ok shape =>
    let reg (r : Reg64) : List String := ["st", regLower r]
    let withClass (k : FieldClass) := pl.state.filterMap fun (r, c) => if c == k then some (reg r) else none
    let l3 : L3In := if sh.runCall.isSome || sh.resultFn.isSome then
        let taken := sh.names ++ pl.params.map (·.name.s) ++ ["xs", "a", "frame", "x", "st", "g", "y"]
        let part := freshAmong taken "xsRun"
        let y := freshAmong (part :: taken) "yRun"
        let call := if pl.kind == .value && sh.resultFn.isSome then
            s!"({sh.runApplication}).map (fun {y} => {resultWord pl.val sh.resultFn y})"
          else sh.runApplication
        { run := s!"(fun {part} => {shape.withInput part call})", form := .list }
      else { run := runName sh, form := l3Form shape }
    let isList := match shape with | .list .. => true | _ => false
    some { l3, xs := ["xs"], heap := ["a", "heap"],
           counters := withClass .counter, accumulators := withClass .accumulator,
           ghosts := pl.ghosts.map fun g => (reg g.reg, g.off),
           result := match pl.kind with
             | .value => .value
             | .heap => if pl.mem && (sh.runCall.isNone || isList) then .heap ["st", "mem"] (pl.params.map (·.name.s)) else .other
             | .both => .other }

/-- The atoms of the literal head values of the head `h` of `pl` (DISC-RESULT): `st.r.toNat = n` for each register `r` that is
the literal `n` at the head. -/
def headAtomsOf (pl : UpperPlan) (h : String) : List Atom :=
  match pl.heads.find? (·.name.s == h) with
  | some hd => hd.state.filterMap fun
    | (r, .lit n) => some (.eq (.field ["st", regLower r, "toNat"]) (.const n.toNat))
    | _ => none
  | none => []

/-! ## The context of the prompt (HARNESS-LOOP D5) -/

/-- The names that the `let` lines of a slot of the refute spec bind, in order: `let n := …`, `let n : T := …` and
`let (a, b) := …`. -/
def letNames (lets : List String) : List String :=
  lets.flatMap fun l =>
    if !l.startsWith "let " then [] else
    let lhs := (((l.drop 4).toString.splitOn " :=").headD "").trimAscii.toString
    if lhs.startsWith "(" && lhs.endsWith ")" then
      ((lhs.drop 1).dropEnd 1).toString.splitOn ", " |>.map (·.trimAscii.toString)
    else [((lhs.splitOn " : ").headD "").trimAscii.toString]

/-- The text of a field class. -/
def fieldClassWord : FieldClass → String
  | .pointer => "pointer"
  | .counter => "counter"
  | .accumulator => "accumulator"

/-- The context lines of the prompt of the site at the head `head` of `u`, with the loop row `ob` and the refute spec `spec`:
* the names that the slots of the refuter bind (`letNames`), each with its type: an input of the statement has the type of its
  binder, an address binder `BitVec 64`, `a` the input at the entry and `y` the L3 result;
* the statement of the loop row: its hypotheses hold at the entry;
* the entry value of each register of the head state (`headValText`) and its class;
* the L3 text of the statement (`StmtShape.l3Text`) and the text of `blocksP` in the model.
The rules read the statement, the plan and the model; they name no function. -/
def contextOf (u : FnUnit) (head : String) (ob : Obligation) (spec : Skel.Toy.RefuteCommon.RefuteSpec)
    (model : String) : List String :=
  let inputs := u.shape.inputs.map fun b => (b.name.s, b.type.s)
  let addrs := u.plan.params.map (·.name.s)
  let typed (n : String) : Option String :=
    match inputs.lookup n with
    | some t => some s!"  {n} : {t} (an input of the statement)"
    | none =>
      if addrs.contains n then some s!"  {n} : BitVec 64 (an address of an object of the statement)"
      else if n == "a" then some "  a : In2p (the input at the entry: st.input = a; In2p has no decidable equality, so compare its fields)"
      else if n == "y" then
        -- a state with memory (the family objects with kind both): the sampler binds the value part of the L3 result only
        if spec.resultTy == "UInt64 × Heap" then
          some "  y (the value part of the L3 result: the run of the spec is some (y, …); the other parts are not bound)"
        else some "  y (the L3 result: the run of the spec is some y)"
      else none
  let names := (letNames spec.lets).eraseDups.filterMap typed
  let heads := match u.plan.heads.find? (·.name.s == head) with
    | some h => h.state.map fun (r, v) =>
      let cls := ((u.plan.state.lookup r).map fun c => s!" ({fieldClassWord c})").getD ""
      s!"head register at the entry: {regLower r} = {headValText v}{cls}"
    | none => []
  let blocks := (declText model "blocksP").toList
  (if names.isEmpty then [] else
    "The names that an atom may use besides st (the refuter binds them; each is fixed for one run):" :: names) ++
  ["The statement of the loop row (its hypotheses hold at the entry; the state in its conclusion is the head state at the entry):",
   ob.statement,
   s!"The result of the loop (a result: term) has the type {spec.resultTy}" ++
     (if spec.proj.isEmpty then "." else s!"; the refuter compares {spec.proj} of it with the expected result.")] ++ heads ++
  -- the refute file opens the parent of the namespace of the spec, not the namespace itself (HARNESS-LOOP2 H6)
  let ns := ".".intercalate ((runName u.shape).splitOn ".").dropLast
  (if u.shape.l3Text.isEmpty then [] else
    [s!"The L3 spec of the statement (namespace {ns}; a term names its constants with the namespace, as {ns}.run):",
     u.shape.l3Text]) ++
  (if blocks.isEmpty then [] else ["The blocks of the model (the step runs them from the head):"] ++ blocks)

/-- The name of the refute file of the triple `t` of the row `id` in the namespace `ns`. -/
def refuteName (ns : String) (id : ObId) (t : Triple) : String :=
  s!"{ns}.refute.{id.name}.t{(hash (t.inv, t.measure, t.result)).toNat}"

/-- The check of the row `ob` with the triple `t`: the check file with the model text, `loopProof` of the triple with the slot
lines and the unfold names of the plan, run by `Io.checker`. The proof text, the outcome and the time. -/
def checkRow (cfg : Config) (h : Header) (u : Upper) (g : Generated) (ob : Obligation) (dir : FilePath) (t : Triple) :
    IO (String × Outcome × Nat) := do
  let proof := loopProof ob.statement t u.slots u.unfolds
  let text := Skel.checkFile h g.modelText [] ob proof
  let lf : LeanFile := { name := s!"{h.namespace_}.{ob.id.name}", limitMs := cfg.limitMs, text }
  let (o, ms) ← Io.checker dir cfg.gate lf
  pure (proof, o, ms)

/-- The modules of the constants of the call relation in the model text of a caller. -/
def callImports : List String := ["Lift.Sem.CallFrame", "Lift.Sem.CallArmBytes", "Lift.Sem.CallMem", "Lift.Sem.StackPush"]

/-- The name of the runner of the callee in the refute, pool and trace files. -/
def runnerName : String := "refuteCalleeRun"

/-- The runner of the one callee `c` of a loop (HARNESS-LOOP2 H5): the declaration of `runnerName`, which runs the L2+ model
`<c.model>.blocksP` of the callee (in the model text of the caller) from `<c.model>.initP` of the argument of the call. This is
the meaning that the model of the caller gives to the call (its callee relation is the `l2p` model of the callee), and the
callee rows `refines_l2p` and `refines_l3` relate that model to the machine code and to the L3 spec of the callee. A runner that
decodes the L3 inputs of the callee from the heap is not done: the harness has no decoder of the objects. -/
def runnerOf (c : Callee) : String × CalleeSpec :=
  let m := c.model
  (s!"def {runnerName} := fun (_ : Unit) (a : {m}.In2p) => {m}.blocksP.run (fun f => f.elim) 100000 {m}.Lbl.entry ({m}.initP a)",
   { name := c.name, run := s!"{m}.blocksP",
     text := s!"The call runs the L2+ model {m}.blocksP of the callee (in the blocks of the model, namespace {m}) from {m}.initP of the argument; the result is the pair of the word in rax and the memory. The rows refines_l2p and refines_l3 of the callee relate this model to its machine code and to its L3 spec." })

/-- The operands of the branch conditions of a condition: the two sides of each comparison. -/
def condOps : Cond → List Val
  | .eq a b | .ule a b | .ult a b | .slt a b | .slt32 a b => [a, b]
  | .not c => condOps c
  | .iff p q => condOps p ++ condOps q
  | .flag _ => []

/-- The declaration `refuteOps` of the guided search (HARNESS-LOOP3): for each block of `u` with a branch and only loads, the
words of the operands of its condition at its start state `x`. Loads read the current memory for a memory plan and the input
heap otherwise, as the blocks do. A stack access needs the model's stack forwarding, so it gives no operands here. Other
blocks and failed loads give `[]`. -/
def opsDecl (u : FnUnit) (stTy : String) : String :=
  let vs := vars u.blocks u.callees
  let ff := (frameFacts (u.callees.map fun c => (c.name, c.room)) u.blocks).toOption
  let load := if u.plan.call.bytePermits then "loadB" else "load"
  let heap := if u.plan.mem then "x.mem" else "x.input.heap"
  let arms := u.blocks.filterMap fun b =>
    match b.term with
    | .branch c _ _ =>
      let loads := b.accesses.filterMap fun | .load k addr w => some (k, addr, w) | .store .. => none
      if loads.length != b.accesses.length || loads.any (fun (_, addr, _) => addr.usesRsp) || (condOps c).isEmpty then none else
      let ctx : Ctx := { vars := vs, entry := "0", accs := b.accesses,
                         depth := ((ff.map (·.delta)).bind (·.lookup b.offset)).getD 0 }
      let ops := "[" ++ ", ".intercalate ((condOps c).map fun v => s!"({(u64Text ctx v).1})") ++ "]"
      let body := loads.foldr (fun (k, addr, w) inner =>
        s!"(match {heap}.{load} ({(bvText ctx addr).1}) {widthText w} with | .ok {loadName k} => {inner} | _ => [])") ops
      some s!"  | .{b.name.s}, x => {body}"
    | _ => none
  "\n".intercalate ([s!"def refuteOps : Lbl → {stTy} → List UInt64"] ++ arms ++ ["  | _, _ => []"])

/-- The machine of the site `s` of `u`, with the files below `dir`. `mutate` changes the model text of the generator (the refute
files and the check of the row read the changed text); a test uses it for a loop that does not follow the spec. A cycle with a
call of one callee of `u.callees` runs the callee by its model (`runnerOf`); a call of another callee, or of more than one, is
the error `callInLoop`. -/
def machineFor (cfg : Config) (u : FnUnit) (s : Site) (dir : FilePath) (mutate : String → String := id)
    (result? : Option String := none) (unfolds : List String := []) (bounds : List Atom := []) : Except SiteError Machine := do
  let cs := callsOn u.blocks [] ((offsetOf u.blocks s.head).getD 0)
  let runner : Option (String × CalleeSpec) ← match cs with
    | [] => pure none
    | [c] => match u.callees.find? (·.name == c) with
      | some callee => pure (some (runnerOf callee))
      | none => throw (.callInLoop cs)
    | _ => throw (.callInLoop cs)
  unless s.form == .alone do throw (.form s.form)
  let up := { u.upper with generated := { u.upper.generated with modelText := mutate u.upper.generated.modelText } }
  let spec ← up.spec.mapError fun e => .noRefuteSpec (repr e).pretty
  -- the model text of a caller names the constants of its call relation (`CallFrame.PermLift`, `Model.restrict`,
  -- `SysV.RoomAt`); the refute, pool and trace files of a site with a runner import their modules
  let spec := match runner with
    | some (decl, _) => { spec with runner := runnerName, helpers := spec.helpers ++ [decl],
                                    imports := spec.imports ++ callImports }
    | none => spec
  -- the pool and trace files read the model text, which can name constants of the check imports (`SysV.Mapped`)
  let spec := { spec with imports := (spec.imports ++ u.header.imports).eraseDups }
  -- the operands of the branch conditions for the guided search, when the sampler builds mutated inputs (HARNESS-LOOP3)
  let hasGuide : Bool := spec.helpers.any (·.startsWith "def refuteMutant ")
  let spec := if hasGuide then { spec with helpers := spec.helpers ++ [opsDecl u spec.stateTy] } else spec
  -- the refute files of a site with a runner or a guide come from this spec; the others are unchanged
  let up := if runner.isSome || hasGuide then { up with spec := .ok spec } else up
  let g := up.withRefute cfg.seed cfg.samples
  let some ob := g.obligations.find? (fun o => o.claim == .loop && o.id.name == s!"loop.{s.head}") | throw (.noRow s.head)
  -- the result term: the given one; else the first template result, only when the templates are on
  let result := result? <|> (if cfg.useTemplates then up.templates.head?.map (·.result) else none)
  let up' := { up with unfolds := (up.unfolds ++ unfolds).eraseDups }
  pure { spec, gen := g, ob, head := s.head, result,
         refuteName := refuteName s!"{u.header.namespace_}" ob.id,
         check := checkRow cfg u.header up' g ob dir,
         checkText := fun proof => Io.checker dir cfg.gate
           { name := s!"{u.header.namespace_}.{ob.id.name}", limitMs := cfg.limitMs,
             text := Skel.checkFile u.header g.modelText [] ob proof },
         request := Prove.request u.header g.modelText [] ob,
         dir, seed := cfg.seed, limitMs := cfg.limitMs, l3 := specCtxOf u.plan u.shape,
         headAtoms := (headAtomsOf u.plan s.head ++ bounds).eraseDups,
         edges := Cover.passEdges u.blocks s.head, context := contextOf u s.head ob spec g.modelText,
         runnerDecl := (runner.map (·.1)).getD "", callees := (runner.map (·.2)).toList }

/-! ## The result term (DISC-RESULT) -/

/-- The admitted runs of the screen of the result candidates. -/
def screenRuns : Nat := 100

/-- The candidates of the result term of the site `s` with the machine `m`: the template results (only with the templates
on), then spec-suffix, then spec-step. A text that an earlier candidate has is dropped. -/
def resultCands (cfg : Config) (u : FnUnit) (s : Site) (m : Machine) : IO (List Result.Cand) := do
  let some h := u.plan.heads.find? (·.name.s == s.head) | return []
  let tpl : List Result.Cand :=
    if cfg.useTemplates then u.upper.templates.map fun t => { source := "template", text := t.result } else []
  let step ← Result.stepOf m u.plan u.shape u.blocks h
  let all := tpl ++ Result.suffix u.plan u.shape u.blocks h ++ Result.prefixCands u.plan u.shape u.blocks h ++ step
  pure (all.foldl (fun acc c => if acc.any (·.text == c.text) then acc else acc ++ [c]) [])

/-- The run of the result term: each candidate with the admitted runs on which it fits, the candidate of the ladder run that
is kept (the one that closed, else the first one tried: the best ranked), the ladder result and the triple. -/
structure ResultRun where
  screened : List (Result.Cand × Nat × Nat)
  cand : Result.Cand
  result : Ladder.Result
  triple : Option Triple
  /-- The machine of the ladder run (the prove rung reads its triple, its request and its check). -/
  machine : Machine

/-- The lines of the screen: the source, the fits and the text of each candidate. -/
def ResultRun.lines (r : ResultRun) : List String :=
  r.screened.map fun (c, n, f) => s!"{c.source} {n}/{screenRuns}, free {f}/{screenRuns}: {c.text}"

/-- The candidates of the result (`resultCands`), the screen, then the ladder with each candidate that fits (at most 3), in
order, until one closes. With no candidate that fits, the ladder runs with the first candidate. An error: no candidate, or
the error of the machine or of the pool. -/
def discoverResult (cfg : Config) (u : FnUnit) (s : Site) (dir : FilePath) (limit : Nat := 6)
    (mutate : String → String := id) (ask : Option Ladder.AskFn := none) : IO (Except String ResultRun) := do
  match machineFor cfg u s dir mutate with
  | .error e => pure (.error e.text)
  | .ok m0 =>
    IO.FS.createDirAll dir
    let cs ← resultCands cfg u s m0
    let sc ← Result.screen m0 cs screenRuns
    let order := (Result.chosen screenRuns sc).take 3
    -- no source gives a result term: with a model, one ladder run with no result term of the site, so that the result of a quad
    -- comes from the model (a free term, HARNESS-LOOP2 H5)
    if order.isEmpty then
      if ask.isNone then return .error "no-result: no source gives a result term"
      match ← m0.discover limit (Smt.Rung.ofFlag cfg.solver) ask with
      | .error e => return .error e
      | .ok (r, t) =>
        return .ok { screened := sc, cand := { source := "model", text := "", unfolds := [] }, result := r, triple := t, machine := m0 }
    let bounds ← match u.plan.heads.find? (·.name.s == s.head) with
      | some h => Result.boundsOf m0 u.plan u.shape u.blocks h
      | none => pure []
    let mut first : Option ResultRun := none
    for c in order do
      match machineFor cfg u s dir mutate (result? := some c.text) (unfolds := c.unfolds) (bounds := bounds) with
      | .error e => return .error e.text
      | .ok m =>
        match ← m.discover limit (Smt.Rung.ofFlag cfg.solver) ask with
        | .error e => return .error e
        | .ok (r, t) =>
          let rr : ResultRun := { screened := sc, cand := c, result := r, triple := t, machine := m }
          if r.ledger.status == "closed" && t.isSome then return .ok rr
          if first.isNone then first := some rr
    match first with
    | some rr => pure (.ok rr)
    | none => pure (.error "no-result: no ladder run")

/-! ## The run of a site -/

/-- The result of a site: the site, the status (`closed`, `open` or `error`), the rung that closed it (`template` or `discover`),
the error, the rounds of the ladder, the closed or best quad (atoms and measure), the triple of the row, the ledger file and the
wall time. -/
structure SiteResult where
  fn : String
  head : String
  form : String
  status : String
  /-- The exact generated row for a joint certificate. Older single-head records use `loop.<head>`. -/
  row : Option String := none
  rung : Option String := none
  error : Option String := none
  rounds : Nat := 0
  inv : List String := []
  measure : Option String := none
  triple : Option (String × String × String) := none
  ledger : Option String := none
  ms : Nat := 0
  /-- The goals of the head (`HeadGoals`): the entry, the goal names, the carried and the live registers. -/
  entry : String := ""
  goals : List String := []
  carried : List String := []
  live : List String := []
  /-- The source of the result term of the triple (`Result.Cand.source`), or of the first candidate tried. -/
  resultSource : Option String := none
  /-- Each result candidate: its source, the admitted runs on which it fits, and its text (`ResultRun.lines`). -/
  results : List String := []
  /-- The proof of the row from the prove rung (`rung` is `prove`); none for any other rung. -/
  proof : Option String := none
  /-- The unfold names of the result term of the triple (`Result.Cand.unfolds`): the check of the row has them after the
  unfold names of the plan. -/
  unfolds : List String := []
  deriving ToJson, Repr

/-- A result with the goals `g` of its head. -/
def SiteResult.withGoals (r : SiteResult) (g : HeadGoals) : SiteResult :=
  { r with entry := g.entry.text, goals := g.names, carried := g.carried.map regLower, live := g.live.map regLower }

/-- The triple of the row of a closed result. -/
def SiteResult.rowTriple (r : SiteResult) : Option Triple :=
  if r.status == "closed" then r.triple.map fun (inv, measure, result) => { inv, measure, result } else none

/-- The first template triple that closes the row, by `m.check`. -/
def templateRung (m : Machine) : List Triple → IO (Option Triple)
  | [] => pure none
  | t :: ts => do
    match (← m.check t).2.1 with
    | .accepted _ => pure (some t)
    | _ => templateRung m ts

/-- The ledger file of a site below `out`: `discover-<fn>.<head>.json`. -/
def ledgerPath (out : FilePath) (s : Site) : FilePath := Ladder.Ledger.path out s!"{s.fn}.{s.head}"

/-- The errors of the failed checks of the loop row in a ledger, oldest first: the text of each open goal `loop`. -/
def loopErrors (l : Ladder.Ledger) : List String :=
  l.rounds.flatMap fun r => r.goals.filterMap fun (n, g) =>
    if n == "loop" && g.startsWith "open " then some (g.drop 5).toString else none

/-- The prove rung of an open site (RUNG-WIRE): with the prover on and a quad that the refuter passed, one run of the prover
on the loop row with the triple of the first such quad and the newest error of its check (`Machine.prove`). None: the prover
is off, or no quad passed. -/
def proveSite (pc : Option Prove.Cfg) (rr : ResultRun) (dir : FilePath) (log : String → IO Unit) :
    IO (Option (Triple × Close.Result)) := do
  match pc, rr.result.passed.head?.bind rr.machine.triple with
  | some c, some t => pure (some (t, ← rr.machine.prove c dir log t (loopErrors rr.result.ledger).getLast?.toList))
  | _, _ => pure none

/-- The run of the site `s` of `u`. The files of the site go below `out/<fn>/<head>`, its ledger to `ledgerPath out s`. With
`cfg.useTemplates`, the template triples are checked first. Then `discoverResult`: the ladder (at most `limit` rounds, the
solver rung with `cfg.solver`, the model of `rungs` with the reply store `out/replies.jsonl`) with each result candidate that
fits. A site that stays open with a quad that the refuter passed goes to the prove rung of `rungs` (`proveSite`); the frozen
files are below `out/<fn>/<head>/prove`, and the log of the rungs is `out/<fn>/<head>/rungs.log`. -/
def discoverSite (cfg : Config) (u : FnUnit) (s : Site) (out : FilePath) (limit : Nat := 6)
    (mutate : String → String := id) (rungs : RungFlags.Rungs := {}) : IO SiteResult := do
  let t0 ← IO.monoMsNow
  let dir := out / s.fn / s.head
  let base : SiteResult := { fn := s.fn, head := s.head, form := s.form.tag, status := "error" }
  let base := match (headGoalsOf u).find? (·.head == s.head) with
    | some g => base.withGoals g
    | none => base
  match machineFor cfg u s dir mutate with
  | .error e => pure { base with error := some e.text }
  | .ok m =>
    IO.FS.createDirAll dir
    let tpl ← if cfg.useTemplates then templateRung m u.upper.templates else pure none
    match tpl with
    | some t =>
      pure { base with status := "closed", rung := some "template", triple := some (t.inv, t.measure, t.result),
                       resultSource := some "template", ms := (← IO.monoMsNow) - t0 }
    | none =>
      let log (line : String) : IO Unit := IO.FS.withFile (dir / "rungs.log") .append fun h => h.putStrLn line
      match ← discoverResult cfg u s dir limit mutate (Ladder.proposerOf rungs (out / "replies.jsonl") log) with
      | .error e => pure { base with error := some e, ms := (← IO.monoMsNow) - t0 }
      | .ok rr =>
        let r := rr.result
        let base := { base with resultSource := some rr.cand.source, results := rr.lines }
        let l := { r.ledger with fn := s!"{s.fn}.{s.head}" }
        l.write out
        let discovered := if r.ledger.status == "closed" then rr.triple else none
        let proved ← if discovered.isSome then pure none else proveSite rungs.prove rr (dir / "prove") log
        let (found, rung, proof) : Option Triple × Option String × Option String :=
          match discovered, proved with
          | some t, _ => (some t, some "discover", none)
          | none, some (t, .closed _ p _) => (some t, some "prove", some p)
          | none, _ => (rr.triple, none, none)
        pure { base with status := if rung.isSome then "closed" else "open", rung, proof, unfolds := rr.cand.unfolds,
                         rounds := l.rounds.length, inv := (l.quad.map (·.inv)).getD [], measure := l.quad.map (·.measure),
                         triple := found.map fun t => (t.inv, t.measure, t.result),
                         error := match proved with
                           | some (_, .open why) => some why
                           | _ => none,
                         ledger := some (ledgerPath out s).toString, ms := (← IO.monoMsNow) - t0 }

/-- Replay saved joint proposals, then propose a complete map and search its independent proof rows.
Without a map proposer, keep the guarded joint proof path. -/
def discoverRegions (cfg : Config) (u : FnUnit) (out : FilePath) (rungs : RungFlags.Rungs := {}) : IO SiteResult := do
  let t0 ← IO.monoMsNow
  let base : SiteResult :=
    { fn := u.fn, head := "regions", form := "regions", status := "open", row := some "regions",
      goals := regionLabels u.plan }
  let some ob := u.upper.generated.obligations.find? (·.id.name == "regions")
    | return { base with status := "error", error := some "the region plan has no regions row" }
  let dir := out / u.fn / "regions"
  IO.FS.createDirAll dir
  let request ← match Prove.request u.header
      (u.upper.generated.modelText ++ Regions.calleeRowContext u.upper.generated.obligations) [] ob with
    | .ok request => pure request
    | .error e => return { base with status := "error", error := some e, ms := (← IO.monoMsNow) - t0 }
  let proposalPath := dir / "regions.proposal.json"
  let proposalExample := Lean.toJson (Regions.proposalExample (regionLabels u.plan))
  let requestJson := Lean.Json.mkObj
    [("kind", Lean.toJson "skel-prove"), ("row", Lean.toJson request.row),
     ("head", Lean.toJson request.head), ("decl", Lean.toJson request.decl), ("after", Lean.toJson request.after),
     ("regionProposal", Lean.Json.mkObj
       [("path", Lean.toJson proposalPath.toString), ("schema", proposalExample),
        ("checks", Lean.toJson "Every local region sees this complete map. All local proofs and the final generated regions row must pass Lean.")])]
  IO.FS.writeFile (dir / "regions.request.json") (requestJson.pretty ++ "\n")
  IO.FS.writeFile (dir / "regions.proposal.example.json") (proposalExample.pretty ++ "\n")
  IO.FS.writeFile (dir / "regions.lean") request.frozen
  let base ← if ← proposalPath.pathExists then do
    match (Lean.Json.parse (← IO.FS.readFile proposalPath)).bind (Regions.Proposal.parse (regionLabels u.plan)) with
    | .error e => pure { base with error := some s!"saved region proposal: {e}" }
    | .ok proposal =>
      let checked ← Regions.runProposal
        { plan := u.plan, shape := u.shape, callees := u.callees, header := u.header,
          model := u.upper.generated.modelText, row := ob, gate := cfg.gate, limitMs := cfg.limitMs, dir := dir / "checks" }
        proposal
      let attempts := checked.attempts.map fun a => Lean.Json.mkObj
        [("regions", Lean.toJson (a.regions.map fun (h, r) => (h, reprStr r.outcome))),
         ("composition", Lean.toJson (a.composition.map fun r => reprStr r.outcome))]
      IO.FS.writeFile (dir / "regions.checks.json") ((Lean.toJson attempts).pretty ++ "\n")
      match checked.closed with
      | some (_, result) =>
        pure { base with status := "closed", rung := some "regions", proof := some result.proof,
                         rounds := checked.attempts.length, ms := (← IO.monoMsNow) - t0 }
      | none => pure { base with error := some "the saved region proposal was refused", rounds := checked.attempts.length }
    else pure base
  if base.status == "closed" then return base
  let log (s : String) : IO Unit := IO.FS.withFile (dir / "rungs.log") .append fun h => h.putStrLn s
  let context : Regions.Context :=
    { plan := u.plan, shape := u.shape, callees := u.callees, header := u.header,
      model := u.upper.generated.modelText, row := ob, gate := cfg.gate, limitMs := cfg.limitMs,
      dir := dir / "map" }
  let asker := rungs.asker cfg.asks (dir / "prove") (out / "replies.jsonl") log
  match ← RegionTasks.loadOrPropose context asker rungs.ask.isSome log with
  | .error why => log why
  | .ok map =>
    match RegionTasks.attach context map u.upper.generated with
    | .error why => log s!"region tasks: {why}"
    | .ok generated =>
      let generated := RegionTasks.dependencySlice generated ob.id
      let fi : Skel.Report.Level3.FnInput :=
        { short := u.fn, entry := u.fn, instrs := 0, blocks := [], header := u.header,
          gen := .ok generated, upper := .ok { u.upper with generated, regions := none },
          loopHeads := u.plan.heads.map (·.name.s) }
      let taskDir := dir / "tasks"
      IO.FS.createDirAll taskDir
      let emit (row : Skel.Report.Level3.ObRow) : IO Unit :=
        IO.FS.withFile (taskDir / "rows.jsonl") .append fun h => h.putStrLn (Lean.toJson row).compress
      let noRefute : ObId → Subject → Refuter := fun _ _ _ =>
        throw (IO.userError "a region proof task has no refute rung")
      let report ← Skel.Report.Level3.runFn (Skel.Report.Level3.leanMeasured taskDir cfg.gate)
        noRefute taskDir cfg fi rungs (width := 1) (emit := emit)
      if let some proof := report.proofs.lookup ob.id.name then
        let helpers := generated.obligations.filterMap fun dep => do
          if dep.id == ob.id then none else
            let p ← report.proofs.lookup dep.id.name
            pure (theoremText (Skel.Toy.Held.answerName dep) dep.statement p)
        let proof := Proof.text { helpers := "\n\n".intercalate helpers, proof }
        let (outcome, _) ← Io.checker (taskDir / "composed") cfg.gate
          { name := s!"{u.header.namespace_}.{ob.id.name}", limitMs := cfg.limitMs,
            text := Skel.checkFile u.header u.upper.generated.modelText [] ob proof }
        if outcome matches .accepted _ then
          return { base with status := "closed", rung := some "region-tasks", proof := some proof,
                             error := none, rounds := report.rows.foldl (fun n row => n + row.attempts) 0,
                             ms := (← IO.monoMsNow) - t0 }
      return { base with error := some "one or more region proof tasks remain open",
                         rounds := report.rows.foldl (fun n row => n + row.attempts) 0, ms := (← IO.monoMsNow) - t0 }
  let some pc := rungs.prove | return { base with ms := (← IO.monoMsNow) - t0 }
  let (reply, _) ← Prove.asker (some pc) (dir / "prove") log requestJson.compress
  match reply.bind Prove.Reply.decode? with
  | none => return { base with error := some "the prover gave no reply", ms := (← IO.monoMsNow) - t0 }
  | some r =>
    let some proof := r.proof
      | return { base with error := some s!"prove: {r.outcome}: {r.why}", ms := (← IO.monoMsNow) - t0 }
    let (checked, _) ← Io.checker dir cfg.gate
      { name := s!"{u.header.namespace_}.{ob.id.name}", limitMs := cfg.limitMs,
        text := Skel.checkFile u.header u.upper.generated.modelText [] ob proof }
    match checked with
    | .accepted _ => return { base with status := "closed", rung := some "prove", proof := some proof, error := none, ms := (← IO.monoMsNow) - t0 }
    | _ => return { base with error := some s!"the joint proof was refused: {repr checked}", ms := (← IO.monoMsNow) - t0 }

/-- Single-head sites use the machine ladder. Region plans use one complete map and separate proof tasks. -/
def discoverFn (cfg : Config) (u : FnUnit) (out : FilePath) (limit : Nat := 6) (rungs : RungFlags.Rungs := {}) :
    IO (List SiteResult) := do
  if usesRegions u.plan then return [← discoverRegions cfg u out rungs]
  (sitesOf u).mapM fun s => discoverSite cfg u s out limit (rungs := rungs)

/-- The result of a function that has no unit (its generation failed): one error line with no head. -/
def failedFn (fn e : String) : SiteResult := { fn, head := "", form := "", status := "error", error := some s!"no-unit: {e}" }

/-- The results of a function with no unit and the blocks `bs`: a loop head with a call on its cycle is a site with the error
`callInLoop` (a call in a loop is the first cause), then the cause `e` of the unit; with no such head, `failedFn`. -/
def failedWithBlocks (fn e : String) (bs : List Block) : List SiteResult :=
  let hs := (loopHeads bs).map (·.name.s)
  let rs := hs.filterMap fun h =>
    let g := headGoalsIn bs hs h []
    if g.calls.isEmpty then none
    else
      let r : SiteResult := { fn, head := h, form := (formOf bs hs h).tag, status := "error",
                              error := some s!"{(SiteError.callInLoop g.calls).text}; no-unit: {e}" }
      some (r.withGoals g)
  if rs.isEmpty then [failedFn fn e] else rs

/-! ## The summary -/

/-- The summary of a run: the target, the flags, and each site result. -/
structure RunSummary where
  target : String
  templates : Bool
  solver : Bool
  sites : List SiteResult
  deriving ToJson

/-- The path of the summary in `out`. -/
def RunSummary.path (out : FilePath) : FilePath := out / "discover-summary.json"

/-- The summary line: the sites and the sites by status. -/
def RunSummary.line (s : RunSummary) : String :=
  let n (st : String) := s.sites.countP (·.status == st)
  s!"summary: sites {s.sites.length}, closed {n "closed"}, open {n "open"}, error {n "error"}"

/-- The line of a site: the function, the head, the status and the rung or the error. -/
def SiteResult.line (r : SiteResult) : String :=
  let what := match r.rung, r.error with
    | some k, _ => s!" by {k}"
    | none, some e => s!" ({e})"
    | none, none => s!" ({r.rounds} rounds)"
  s!"{r.fn}.{r.head}  {r.status}{what}"

/-- Writes the summary to `RunSummary.path out`. -/
def RunSummary.write (out : FilePath) (s : RunSummary) : IO Unit := do
  IO.FS.createDirAll out
  IO.FS.writeFile (RunSummary.path out) ((toJson s).pretty ++ "\n")

end Skel.Discover.Upper
