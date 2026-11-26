import Skel.TempDir
import Skel.Toy.Held
import Skel.Toy.Sum
import Skel.Toy.SumRefute
import Skel.Gen.Template
import Skel.Gen.RefinesL3
import Skel.Rungs
import Skel.Render
import Skel.Io
import Skel.Test.GenUpperPlan
import Skel.Test.ChainSum
import Skel.Discover.Upper

/-! The tests of `Skel/Gen/Template.lean` and `Skel/Gen/RefinesL3.lean` (suite `genloop`; task G3-21):
`lake exe skel-test --only genloop`. Each check that does not hold prints one `FAIL` line; a `NOTE` line gives a verdict.

- The template triples of `toyFind`, `toyWalk`, `toyFill` (from `Held.upperOf`) and of `toySum` (from the plan of
  `GenUpperPlanTests`) are the texts of the rules of `Template.lean`.
- Negative: a plan whose state registers have no role (pointers with no ghost), a plan with two heads, and a heap result
  or a both result with a structure input give no template; `refinesL3Proof` of a plan with no head is the text of `lift_straight`; with two heads it uses the joint region certificate.
- The slot lines: `generalize` of `xs` (and of each scalar field); `loopProof` puts them after the `intro`.
- `eachTemplate` gives the next triple after a `real` verdict; `templates` does not.
- The refuter: the refute file of each template triple of the three toys and of `toySum` elaborates (the verdict is not
  `unknown`), and each function has a triple with the verdict `pass` (seed 1, 200 samples, as `skel run`).
- Lean: the `det` text of `refines_l3` of each toy, with the loop row as the binder `hloop` of the theorem, is accepted with
  the three standard axioms; the loop row of each toy of `loopRowFns`, with the proof of its first template triple, is
  accepted with the three standard axioms.
- The unfold names of the loop proof (`loopUnfolds`), and `loopProof` with unfold names. -/

namespace GenLoopTests

open Skel Skel.Gen Skel.Toy.Held GenUpperPlanTests

def upperOk (fn : String) : Option Upper :=
  match upperOf fn with
  | .ok u => some u
  | .error _ => none

def hasText (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The expected template triples of each toy (the rules of `Template.lean`, applied by hand to the plans of 4.6). -/
def findTriples : List Triple :=
  [{ inv := "x.rcx.toNat ≤ xs.length ∧ x.rax = a.rsi", measure := "xs.length - x.rcx.toNat",
     result := "x.rcx + UInt64.ofBitVec (((let x := ({ xs := xs.drop x.rcx.toNat, key := key } : " ++
       "Lift.Toys.FindSpec.In); Lift.Toys.FindSpec.run x)).getD 0)" }]

def walkTriples : List Triple :=
  let rest := "(Lift.Sem.Heap.chain a.heap 8 x.rdi.toBitVec)"
  [{ inv := s!"x.rax + UInt64.ofNat {rest}.length = UInt64.ofNat xs.length ∧ Lift.Sem.Heap.ends a.heap 8 x.rdi.toBitVec = true",
     measure := s!"{rest}.length",
     result := s!"x.rax + UInt64.ofBitVec (((let x : Lift.Toys.WalkSpec.In := ({rest}); Lift.Toys.WalkSpec.run x)).getD 0)" }]

/-- The expected template of the old JSON fixture, which has no stored run expression. -/
def walkLegacyTriples : List Triple :=
  let rest := "(Lift.Sem.Heap.chain a.heap 8 x.rdi.toBitVec)"
  [{ inv := s!"x.rax + UInt64.ofNat {rest}.length = UInt64.ofNat xs.length ∧ Lift.Sem.Heap.ends a.heap 8 x.rdi.toBitVec = true",
     measure := s!"{rest}.length",
     result := s!"x.rax + UInt64.ofBitVec ((Lift.Toys.WalkSpec.run ({rest})).getD 0)" }]

def fillTriples : List Triple :=
  [{ inv := "x.rax.toNat ≤ xs.length ∧ x.mem = heapOf p frame ((((let x : Lift.Toys.FillSpec.In := (xs); " ++
       "Lift.Toys.FillSpec.run x)).getD []).take x.rax.toNat " ++
       "++ xs.drop x.rax.toNat)",
     measure := "xs.length - x.rax.toNat",
     result := "heapOf p frame (((let x : Lift.Toys.FillSpec.In := (xs); Lift.Toys.FillSpec.run x)).getD [])" }]

def sumTriples : List Triple :=
  let base : Triple := { inv := "x.rcx.toNat ≤ xs.length", measure := "xs.length - x.rcx.toNat", result := "" }
  [{ base with result := "x.rax + UInt64.ofBitVec ((Lift.Spike.SumSpec.run (xs.drop x.rcx.toNat)).getD 0)" },
   { base with result := "x.rcx + UInt64.ofBitVec ((Lift.Spike.SumSpec.run (xs.drop x.rcx.toNat)).getD 0)" }]

def sumPlan : Option UpperPlan := (planOf sums "toySum" sumShape hintSum).toOption

def findPlan : Option UpperPlan := (planOf toys "toyFind" findShape hintFind).toOption

def fillPlan : Option UpperPlan := (planOf toys "toyFill" fillShape hintFill).toOption

def templatesOf (fn : String) : List Triple := ((upperOk fn).map (·.templates)).getD []

def detOf (fn name : String) : Option String :=
  (upperOk fn).bind fun u => (u.generated.det.find? (·.1.name == name)).map (·.2)

def walkPlan : Option UpperPlan := (planOf toys "toyWalk" walkShape hintWalk).toOption

/-- The shape of `toyWalk` with the argument term `t` of its first argument (the pointer of the chain). -/
def walkShapeWith (t : String) : Option StmtShape := do
  let sh ← walkShape
  let src ← Src.parse t
  match sh.args with
  | a :: rest => pure { sh with args := { a with term := src } :: rest }
  | [] => none

/-- The `hchain` lines of `toyWalk` with the argument term `t`. -/
def walkChainWith (t : String) : Option (List String) := do
  let p ← walkPlan
  let sh ← walkShapeWith t
  pure (chainFact p sh)

/-- The simp list of the line that closes the cases of the induction of `hchain`. -/
def simpLineOf (ls : List String) : String := (ls.find? (hasText · "cases qs₀ <;> simp_all [")).getD ""

def forbidden : List String := ["sorry", "axiom", "native_decide", "variable", "maxHeartbeats", "maxRecDepth"]

/-- A ledger history with one attempt: the triple `t` with the verdict `v`. -/
def historyOf (t : Triple) (v : Verdict) : History :=
  { attempts := [{ candidate := .triple .template t, result := .refuted v, ms := 0 }], cexs := [] }

def realOf (t : Triple) : Verdict := .real { ob := ⟨"f", "loop"⟩, subject := .triple t, seed := 1, index := 0, shown := "", why := "" }

def anyOb : Obligation :=
  { id := ⟨"f", "loop"⟩, cls := .refine, origin := .loop "h", statement := "", deps := [], claim := .loop }

def pureChecks : List (String × Bool) :=
  [ ("toyFind: the template triples are those of the rules", templatesOf "toyFind" == findTriples),
    ("toyWalk: the template triples are those of the rules", templatesOf "toyWalk" == walkTriples),
    ("toyWalk: the reflected shape stores the exact run expression",
      ((Skel.Toy.Held.shapeOf "toyWalk").bind (fun sh => sh.runCall)).map (fun (call : Src) => call.s) ==
        some "Lift.Toys.WalkSpec.run x"),
    ("toyWalk: the old JSON fixture has no stored run expression",
      GenUpperPlanTests.walkShape.any (fun (sh : StmtShape) => sh.runCall.isNone)),
    ("toyFill: the template triples are those of the rules", templatesOf "toyFill" == fillTriples),
    ("toySum: the template triples are those of the rules",
      match sumPlan, sumShape with
      | some p, some sh => loopTemplates p sh == sumTriples
      | _, _ => false),
    -- negative cases: no role, two heads, a heap result of a structure input
    ("a plan whose state registers are pointers with no ghost gives no template",
      match findPlan, findShape with
      | some p, some sh => loopTemplates { p with state := p.state.map fun (r, _) => (r, .pointer) } sh == []
      | _, _ => false),
    ("a plan with two heads gives no template",
      match findPlan, findShape with
      | some p, some sh => loopTemplates { p with heads := p.heads ++ p.heads } sh == []
      | _, _ => false),
    ("a plan with no head gives no template",
      match findPlan, findShape with
      | some p, some sh => loopTemplates { p with heads := [] } sh == []
      | _, _ => false),
    ("a plan with a generalized head gives no fixed loop template",
      match findPlan, findShape with
      | some p, some sh =>
        loopTemplates { p with heads := p.heads.map fun h => { h with generalized := true } } sh == []
      | _, _ => false),
    ("a heap result with a structure input gives no template",
      match findPlan, findShape with
      | some p, some sh => loopTemplates { p with kind := .heap, mem := true } sh == []
      | _, _ => false),
    ("a result that is a value and a heap gives the pair of the word and the heap for a list input (L3-U7)",
      match fillPlan, fillShape with
      | some p, some sh =>
        let ts := loopTemplates { p with kind := .both } sh
        !ts.isEmpty && ts.all fun t => t.result.startsWith "(" && hasText t.result ", heapOf p frame "
      | _, _ => false),
    ("a result that is a value and a heap gives no template for a structure input",
      match findPlan, findShape with
      | some p, some sh => loopTemplates { p with kind := .both, mem := true } sh == []
      | _, _ => false),
    -- the slot lines
    ("toyFind: the slot lines generalize xs and key", ((upperOk "toyFind").map (·.slots)) ==
      some ["generalize hxs : x.xs = xs", "generalize h_key : x.key = key"]),
    ("toyFill: the slot line generalizes the list input", ((upperOk "toyFill").map (·.slots)) ==
      some ["generalize hxs : x = xs"]),
    ("loopProof puts the slot lines after the intro and before intros",
      loopProof "∀ (x : T) (a : A), P" { inv := "I", measure := "M", result := "R" } ["generalize hxs : x = xs"] ==
        "by\n  intro x a\n  generalize hxs : x = xs\n  intros\n  split_hyps\n" ++
        "  lift_loop! (fun x => x.input = a ∧ (I)) (fun x => (M)) (fun x => (R))"),
    ("toyFind: the unfold names are the spec, objsP and the objects of the statement",
      ((upperOk "toyFind").map (·.unfolds)) ==
        some ["Lift.Toys.FindSpec.run", "objsP", "Lift.Toys.FindStatement.objects"]),
    ("toyWalk: the unfold names have the node objects of the statement", ((upperOk "toyWalk").map (·.unfolds)) ==
      some ["Lift.Toys.WalkSpec.run", "objsP", "Lift.Toys.WalkStatement.nodes"]),
    ("toyWalk: the slot lines generalize xs, then state the fact hchain of the chain from the argument",
      match (upperOk "toyWalk").map (·.slots) with
      | some (g :: h :: _) => g == "generalize hxs : x = xs" && h.startsWith "have hchain : ∀ (xs : Lift.Toys.WalkSpec.In) " &&
          hasText h "Lift.Sem.Heap.chain (objsP ps xs ++ frame) 8 (Lift.Toys.WalkStatement.head ps) = ps"
      | _ => false),
    ("hchain: the head word of a named argument is a simp name",
      match walkChainWith "Lift.Toys.WalkStatement.head ps" with
      | some ls => hasText (simpLineOf ls) "Lift.Toys.WalkStatement.head, "
      | none => false),
    ("hchain: the argument `(Lift.Toys.WalkStatement.head ps)` gives the name with no parenthesis",
      match walkChainWith "(Lift.Toys.WalkStatement.head ps)" with
      | some ls => hasText (simpLineOf ls) "Lift.Toys.WalkStatement.head, " && !hasText (simpLineOf ls) "(Lift"
      | none => false),
    ("hchain: an argument that applies a method of a binder (`ps.headD 0`) gives no simp name",
      match walkChainWith "ps.headD 0" with
      | some ls => ls != [] && !hasText (simpLineOf ls) "ps.headD" && hasText (simpLineOf ls) "objsP, "
      | none => false),
    ("hchain: an argument that is a binder, or a literal, gives no simp name",
      ["ps", "0"].all fun t =>
        match walkChainWith t with
        | some ls => ls != [] && !hasText (simpLineOf ls) s!"objsP, Lift.Toys.WalkStatement.nodes, {t},"
        | none => false),
    ("toyFind and toyFill: no fact hchain (no chain ghost)",
      ((upperOk "toyFind").map (·.slots.any (·.startsWith "have hchain"))) == some false &&
      ((upperOk "toyFill").map (·.slots.any (·.startsWith "have hchain"))) == some false),
    ("toyFill: the unfold names have heapOf (a heap result)", ((upperOk "toyFill").map (·.unfolds)) ==
      some ["Lift.Toys.FillSpec.run", "objsP", "heapOf", "outHeap", "Lift.Toys.FillStatement.objects"]),
    ("loopProof puts the unfold names after the result",
      loopProof "∀ (x : T), P" { inv := "I", measure := "M", result := "R" } [] ["f", "g"] ==
        "by\n  intro x\n  intros\n  split_hyps\n  lift_loop! (fun x => x.input = a ∧ (I)) (fun x => (M)) (fun x => (R)) [f, g]"),
    ("loopProof with no slot lines is the text of before",
      loopProof "∀ (x : T), P" { inv := "I", measure := "M", result := "R" } ==
        "by\n  intro x\n  intros\n  split_hyps\n  lift_loop! (fun x => x.input = a ∧ (I)) (fun x => (M)) (fun x => (R))"),
    -- the rung
    ("eachTemplate gives the second triple after a real verdict of the first",
      match sumTriples with
      | [t1, t2] => eachTemplate sumTriples anyOb (historyOf t1 (realOf t1)) == some t2
      | _ => false),
    ("templates gives nothing after a real verdict of the first",
      match sumTriples with
      | [t1, _] => templates sumTriples anyOb (historyOf t1 (realOf t1)) == none
      | _ => false),
    ("eachTemplate gives nothing when each triple is tried",
      match sumTriples with
      | [t1, t2] =>
        let both := (historyOf t1 (realOf t1)).attempts ++ (historyOf t2 (.pass 1)).attempts
        eachTemplate sumTriples anyOb { attempts := both, cexs := [] } == none
      | _ => false),
    -- refines_l3
    ("toyFind: the det text of refines_l3 goes from the entry to the loop row by one jump",
      detOf "toyFind" "refines_l3" == some ("by\n  intro p frame\n  intro x a y hs hy\n" ++
        "  exact ⟨_, .goto rfl (loop.LBB2_1 p frame x a y hs hy), rfl⟩")),
    ("toyFill: the det text of refines_l3 gives the input heap and the result heap",
      detOf "toyFill" "refines_l3" == some ("by\n  intro p frame\n  intro x a y hs hy\n" ++
        "  exact ⟨_, .goto rfl (loop.LBB7_1 p frame x a y hs hy), ⟨by split_hyps; assumption, rfl⟩⟩")),
    ("the det texts of refines_l3 have no forbidden word",
      ["toyFind", "toyWalk", "toyFill"].all fun fn =>
        (detOf fn "refines_l3").any fun t => forbidden.all fun w => !hasText t w),
    ("refinesL3Proof of a plan with no head is the text of lift_straight (UP-STRAIGHT)",
      match findPlan, findShape, Skel.Gen.blocksFrom Lift.Toys.Code.code Skel.Toy.Held.source "toyFind" with
      | some p, some sh, .ok bs =>
        (refinesL3Proof ⟨"toyFind", bs, Skel.Gen.vars bs, ⟨[], 0⟩, none⟩ { p with heads := [] } sh).toOption.any fun t =>
          hasText t "lift_straight!" && !hasText t "loop."
      | _, _, _ => false),
    ("refinesL3Proof of a plan with two heads composes the joint region certificate",
      match findPlan, findShape, Skel.Gen.blocksFrom Lift.Toys.Code.code Skel.Toy.Held.source "toyFind" with
      | some p, some sh, .ok bs =>
        (refinesL3Proof ⟨"toyFind", bs, Skel.Gen.vars bs, ⟨[], 0⟩, none⟩ { p with heads := p.heads ++ p.heads } sh).toOption.any fun t =>
          hasText t "regions" && hasText t "cut_loop"
      | _, _, _ => false),
    ("blocksToHead: a head behind a branch is an error",
      match Skel.Gen.blocksFrom Lift.Toys.Code.code Skel.Toy.Held.source "toyFind" with
      | .ok bs =>
        match bs.find? (·.name.s == "LBB2_3") with
        | some b => (blocksToHead bs b (bs.length + 1) 0).toOption.isNone
        | none => false
      | .error _ => false) ]

/-! ## The refuter -/

def newDir (tag : String) : IO System.FilePath := do
  let dir ← Skel.tempDir s!"genloop-{tag}"
  return dir

/-- The verdict of the refute file `text` of the triple `t` of the row `ob` (seed 1), as the driver runs it. -/
def verdictOf (ob : ObId) (t : Triple) (text : String) : IO Verdict := do
  let (v, _) ← Io.refuter "lake" (← newDir ob.function) ob (.triple t) 1 { name := "check", text, limitMs := 300000 }
  return v

def isUnknown : Verdict → Bool
  | .unknown _ => true
  | _ => false

def isPass : Verdict → Bool
  | .pass _ => true
  | _ => false

def verdictLine : Verdict → String
  | .pass n => s!"pass {n}"
  | .real c => s!"real ({c.why}; {c.shown})"
  | .cti c => s!"cti ({c.why}; {c.shown})"
  | .unknown w => s!"unknown ({w})"

/-- The refute texts of the templates of a toy of `Held`: the refute text of the upper chain with the seed 1 and 200 samples. -/
def heldTexts (fn : String) : Option (ObId × List (Triple × String)) := do
  let u ← upperOk fn
  let g := u.withRefute 1 200
  let ob ← g.obligations.find? (·.claim == .loop)
  let texts ← u.templates.mapM fun t => (g.refuteText ob.id (.triple .template t)).map (t, ·)
  pure (ob.id, texts)

/-- The refute texts of the templates of `toySum`: the generated spec of its plan (G3-12b), with the model text of the hand
glue (`Skel.Toy.Sum.generate`), as `GenSamplerTests` makes it. -/
def sumTexts : IO (Option (ObId × List (Triple × String))) := do
  let sources : Skel.Toy.Sum.Sources :=
    { sum := ← IO.FS.readFile "Lift/Spike/Sum.lean", sites := ← IO.FS.readFile "Lift/Spike/Sites/Sum.lean" }
  let hand := Skel.Toy.SumRefute.spec
  let model : ModelSpec :=
    { names := hand.modelNames, imports := hand.imports.filter fun m => !m.startsWith "Skel.", fn := hand.fn,
      opens := ["Coordinator.Dst"] }
  match Skel.Toy.Sum.generate sources, sumPlan, sumShape with
  | .ok g0, some p, some sh =>
    match refuteSpec p hintSum sh model with
    | .ok r =>
      let g : Generated := { modelText := g0.modelText, obligations := [], refuteText := fun _ _ => none }
      return some (⟨"toySum", "loop"⟩, (loopTemplates p sh).map fun t => (t, r.files.loop g t (.print 1 200)))
    | .error _ => return none
  | _, _, _ => return none

/-- For each function: each refute file elaborates (no `unknown` verdict), and one triple has the verdict `pass`. The
verdicts are printed as `NOTE` lines. -/
def refuteChecks : IO (List (String × Bool × String)) := do
  let cases : List (String × Option (ObId × List (Triple × String))) :=
    (["toyFind", "toyWalk", "toyFill"].map fun fn => (fn, heldTexts fn)) ++ [("toySum", ← sumTexts)]
  let mut out := []
  for (fn, texts?) in cases do
    match texts? with
    | none => out := out ++ [(s!"{fn}: the refute texts of the templates", false, "no text")]
    | some (ob, texts) =>
      let mut vs : List Verdict := []
      for (t, text) in texts do
        let v ← verdictOf ob t text
        IO.println s!"NOTE  genloop: {fn}: {t.result}: {verdictLine v}"
        vs := vs ++ [v]
      out := out ++
        [(s!"{fn}: each refute file of a template elaborates", !vs.isEmpty && !vs.any isUnknown, ""),
         (s!"{fn}: a template triple has the verdict pass", vs.any isPass, "")]
  return out

/-! ## The Lean check of `refines_l3` -/

/-- The text of the check file of `refines_l3` of `fn`: the model text, and the theorem `refines_l3` with the loop row as its
first binder `hloop`. The `det` text names the row `loop.<head>`; here it names the binder. -/
def refinesFile (fn : String) (u : Upper) : Option String := do
  let g := u.generated
  let loop ← g.obligations.find? (·.claim == .loop)
  let refines ← g.obligations.find? (·.id.name == "refines_l3")
  let det ← (g.det.find? (·.1 == refines.id)).map (·.2)
  let body ← match det.splitOn "by\n" with
    | _ :: rest => some ("by\n".intercalate rest)
    | [] => none
  let proof := "by\n  intro hloop\n" ++ body.replace (loop.id.name ++ " ") "hloop "
  let ob : Obligation := { refines with statement := s!"({loop.statement}) → {refines.statement}" }
  pure (checkFile (upperHeader fn) g.modelText [] ob proof)

def standard : List String := ["Classical.choice", "Quot.sound", "propext"]

/-! ## The Lean check of the loop row -/

/-- The text of the check file of the loop row of `fn`: the model text, and the loop row with the proof of the first template
triple (`loopProof` with the slot lines and the unfold names of the upper chain), as `skel run` checks it. -/
def loopFile (fn : String) (u : Upper) : Option String := do
  let g := u.generated
  let loop ← g.obligations.find? (·.claim == .loop)
  let t ← u.templates.head?
  pure (checkFile (upperHeader fn) g.modelText [] loop (loopProof loop.statement t u.slots u.unfolds))

def loopRowCheck (fn : String) : IO (String × Bool × String) := do
  let label := s!"{fn}: the loop row with the first template triple is accepted"
  match (upperOk fn).bind (loopFile fn) with
  | none => pure (label, false, "no text")
  | some text =>
    let dir ← newDir s!"{fn}-loop"
    let path := dir / "check.lean"
    IO.FS.writeFile path text
    let name := match (upperOk fn).bind fun u => u.generated.obligations.find? (·.claim == .loop) with
      | some ob => ob.id.name
      | none => "loop"
    let (o, _) ← Io.checkFile .strict path s!"{(upperHeader fn).namespace_}.{name}" 600000
    match o with
    | .accepted axs => pure (label, axs.length == 3 && standard.all axs.contains, s!"axioms {axs}\nfile: {path}")
    | other => pure (label, false, s!"{repr other}\nfile: {path}")

def refinesCheck (fn : String) : IO (String × Bool × String) := do
  let label := s!"{fn}: refines_l3 with the loop row as a hypothesis is accepted"
  match (upperOk fn).bind (refinesFile fn) with
  | none => pure (label, false, "no text")
  | some text =>
    let dir ← newDir s!"{fn}-refines"
    let path := dir / "check.lean"
    IO.FS.writeFile path text
    let (o, _) ← Io.checkFile .strict path s!"{(upperHeader fn).namespace_}.refines_l3" 600000
    match o with
    | .accepted axs => pure (label, axs.length == 3 && standard.all axs.contains, s!"axioms {axs}\nfile: {path}")
    | other => pure (label, false, s!"{repr other}\nfile: {path}")

/-! ## A chain sum (AF2-C)

`Skel/Test/ChainSum.lean`: the code of `toyWalk` with `addq (%rdi), %rax` in place of `incq %rax`, with the L3 `run` of the wrapping
sum. The loop reads the value word of each node, so its plan gets the values ghost. -/

def chainSumBuilt : Option (List Block × UpperPlan × StmtShape × Upper) := (ChainSumFixture.build).toOption

def chainSumPure : List (String × Bool) :=
  [ ("chain sum: the loop reads the value word of each node (offset 0 of the ghost rdi)",
      match chainSumBuilt with
      | some (bs, p, _, _) => valueLoads bs p == [(.rdi, 0)]
      | none => false),
    ("chain sum: generateUpper gives the templates and the slots with the value offsets of its ghosts",
      match chainSumBuilt with
      | some (bs, p, sh, u) => u.templates == loopTemplates p sh (valueLoads bs p) && u.slots == loopSlots p sh (valueLoads bs p)
      | none => false),
    ("the four toys: generateUpper gives the templates of the plan with the value offsets of valueLoads (none for them)",
      ["toyFind", "toyWalk", "toyFill", "toySum"].all fun fn =>
        match upperOk fn, shapeOf fn, planOf fn, Skel.Gen.blocksFrom (upperCode fn).1 source fn with
        | some u, some sh, .ok p, .ok bs => valueLoads bs p == [] && u.templates == loopTemplates p sh (valueLoads bs p)
        | _, _, _, _ => false),
    ("toyWalk: the loop reads no value word",
      match Skel.Gen.blocksFrom Lift.Toys.Code.code Skel.Toy.Held.source "toyWalk", walkPlan with
      | .ok bs, some p => valueLoads bs p == []
      | _, _ => false),
    ("chain sum: the template with the values ghost has the sum conjunct, the walk with values and the values as the part",
      match chainSumBuilt with
      | some (bs, p, sh, _) =>
        match loopTemplates p sh (valueLoads bs p) with
        | [t] =>
          t.inv == "x.rax + UInt64.ofBitVec (((let x : Skel.Test.ChainSumSpec.In := " ++
            "((Lift.Sem.Heap.chainVals a.heap 8 0 x.rdi.toBitVec)); Skel.Test.ChainSumSpec.run x)).getD 0) = " ++
            "UInt64.ofBitVec (((let x : Skel.Test.ChainSumSpec.In := (xs); Skel.Test.ChainSumSpec.run x)).getD 0) ∧ " ++
            "Lift.Sem.Heap.ends a.heap 8 x.rdi.toBitVec = true ∧ " ++
            "Lift.Sem.Heap.endsV a.heap 8 0 x.rdi.toBitVec = true" &&
          t.measure == "(Lift.Sem.Heap.chain a.heap 8 x.rdi.toBitVec).length" &&
          t.result == "x.rax + UInt64.ofBitVec (((let x : Skel.Test.ChainSumSpec.In := " ++
            "((Lift.Sem.Heap.chainVals a.heap 8 0 x.rdi.toBitVec)); Skel.Test.ChainSumSpec.run x)).getD 0)"
        | _ => false
      | none => false),
    ("chain sum with no value offsets: the count identity of toyWalk, over the plan of the chain sum",
      match chainSumBuilt with
      | some (_, p, sh, _) =>
        match loopTemplates p sh with
        | [t] => hasText t.inv "x.rax + UInt64.ofNat (Lift.Sem.Heap.chain a.heap 8 x.rdi.toBitVec).length = UInt64.ofNat xs.length" &&
            !hasText t.inv "endsV"
        | _ => false
      | none => false),
    ("toyWalk: the templates have no values ghost (valueLoads of its code is none)",
      match Skel.Gen.blocksFrom Lift.Toys.Code.code Skel.Toy.Held.source "toyWalk", walkPlan, walkShape with
      | .ok bs, some p, some sh => loopTemplates p sh (valueLoads bs p) == walkLegacyTriples
      | _, _, _ => false),
    ("chain sum: the slot lines have the walk with values and the induction on the value words",
      match chainSumBuilt with
      | some (bs, p, sh, _) =>
        let ls := loopSlots p sh (valueLoads bs p)
        ls.any (hasText · "Lift.Sem.Heap.endsV (objsP ps xs ++ frame) 8 0 (Lift.Toys.WalkStatement.head ps) = true") &&
        ls.any (hasText · "have hlv : Lift.Sem.Heap.LinkedVals 0 (objsP ps xs) ps xs") &&
        ls.any (hasText · "Lift.Sem.Heap.chain_of_linked_v hh hl hlv")
      | none => false),
    ("toyWalk: the slot lines have no induction on value words",
      match (upperOk "toyWalk").map (·.slots) with
      | some ls => !ls.any (hasText · "LinkedVals") && !ls.any (hasText · "endsV")
      | none => false) ]

/-- The refute texts of the candidates of the chain sum: the template with the values ghost, then the count candidate that
the plan gives with no value offset. -/
def chainSumTexts : Option (ObId × List (Triple × String)) := do
  let (_, p, sh, u) ← chainSumBuilt
  let g := u.withRefute 1 200
  let ob ← g.obligations.find? (·.claim == .loop)
  let (bs, _, _, _) ← chainSumBuilt
  let ts := loopTemplates p sh (valueLoads bs p) ++ loopTemplates p sh
  let texts ← ts.mapM fun t => (g.refuteText ob.id (.triple .template t)).map (t, ·)
  pure (ob.id, texts)

/-- The refuter on the chain sum: the triple with the values ghost passes, the count candidate does not. -/
def chainSumRefute : IO (List (String × Bool × String)) := do
  match chainSumTexts with
  | none => return [("chain sum: the refute texts of the candidates", false, "no text")]
  | some (ob, texts) =>
    let mut vs : List (Triple × Verdict) := []
    for (t, text) in texts do
      let v ← verdictOf ob t text
      IO.println s!"NOTE  genloop: chain sum: {t.inv.take 60}: {verdictLine v}"
      vs := vs ++ [(t, v)]
    match vs with
    | [(_, v1), (_, v2)] =>
      return [("chain sum: the triple with the values ghost has the verdict pass", isPass v1, verdictLine v1),
              ("chain sum: the count identity of toyWalk is refuted (no pass)", !isPass v2 && !isUnknown v2, verdictLine v2)]
    | _ => return [("chain sum: two candidates", false, s!"{vs.length}")]

/-- The Lean check of the loop row of the chain sum with the proof of its template triple with the values ghost. -/
def chainSumLoopCheck : IO (String × Bool × String) := do
  let label := "chain sum: the loop row with the template triple is accepted"
  match ChainSumFixture.upper with
  | .error e => pure (label, false, causeText e)
  | .ok (_, u) =>
    let g := u.generated
    match g.obligations.find? (·.claim == .loop), u.templates.head? with
    | some loop, some t =>
      let text := checkFile ChainSumFixture.header g.modelText [] loop (loopProof loop.statement t u.slots u.unfolds)
      let dir ← newDir "chainsum-loop"
      let path := dir / "check.lean"
      IO.FS.writeFile path text
      let (o, _) ← Io.checkFile .strict path s!"{ChainSumFixture.header.namespace_}.{loop.id.name}" 600000
      match o with
      | .accepted axs => pure (label, axs.length == 3 && standard.all axs.contains, s!"axioms {axs}\nfile: {path}")
      | other => pure (label, false, s!"{repr other}\nfile: {path}")
    | _, _ => pure (label, false, "no loop row or no template")

/-- The toys whose loop row the suite checks in Lean. -/
def loopRowFns : List String := ["toyFind", "toyWalk", "toyFill"]

namespace ExactRun

structure Case where
  label : String
  plan : UpperPlan
  shape : StmtShape
  call : String → String
  index : String
  acc : String
  projected : Bool := false

def src (s : String) : Src := (Src.parse s).getD ⟨"True", by decide⟩

def cases : Option (List Case) := do
  let sp ← sumPlan
  let ss ← sumShape
  let fp ← findPlan
  let fs ← findShape
  let hp ← fillPlan
  let hs ← fillShape
  let withCall (sh : StmtShape) (name call : String) : StmtShape :=
    { sh with run := some (src name), runCall := some (src call) }
  let list := withCall ss "TemplateExactFixture.listRun" "TemplateExactFixture.listRun (xs.drop 1)"
  let flat := { ss with inputs :=
    [⟨nm "xs", src "List (BitVec 64)"⟩, ⟨nm "key", src "BitVec 64"⟩, ⟨nm "spare", src "BitVec 64"⟩] }
  pure [
    ⟨"computed list", sp, list, (fun rest => s!"TemplateExactFixture.listRun (({rest}).drop 1)"), "rcx", "rax", false⟩,
    ⟨"nullary", sp, withCall ss "TemplateExactFixture.fixed" "TemplateExactFixture.fixed",
      (fun _ => "TemplateExactFixture.fixed"), "rcx", "rax", false⟩,
    ⟨"inner binder", sp, withCall ss "TemplateExactFixture.listRun"
      "TemplateExactFixture.listRun (xs.map (fun xs => xs + 1))",
      (fun rest => s!"TemplateExactFixture.listRun (({rest}).map (fun xs => xs + 1))"), "rcx", "rax", false⟩,
    ⟨"reordered flat inputs and a parameter", sp, withCall flat "TemplateExactFixture.flatRun"
      "TemplateExactFixture.flatRun key (xs.drop 1) spare p",
      (fun rest => s!"TemplateExactFixture.flatRun key (({rest}).drop 1) spare p"), "rcx", "rax", false⟩,
    ⟨"named implicit parameter", sp, withCall ss "TemplateExactFixture.implicitRun"
      "TemplateExactFixture.implicitRun (extra := p) (xs.drop 1)",
      (fun rest => s!"TemplateExactFixture.implicitRun (extra := p) (({rest}).drop 1)"), "rcx", "rax", false⟩,
    ⟨"record computation and a parameter", fp, withCall fs "TemplateExactFixture.recordRun"
      "TemplateExactFixture.recordRun (x.xs.drop 1) (x.key + 1) p",
      (fun rest => s!"TemplateExactFixture.recordRun (({rest}).drop 1) (key + 1) p"), "rcx", "rcx", false⟩,
    ⟨"projected word", sp, { list with resultFn := some (src "fun (y : BitVec 64) => y + p") },
      (fun rest => s!"TemplateExactFixture.listRun (({rest}).drop 1)"), "rcx", "rax", true⟩,
    ⟨"encoded record projection", sp, { list with resultFn := some (src "fun (y : BitVec 64) => TemplateExactFixture.Encoded.mk (y + p)") },
      (fun rest => s!"TemplateExactFixture.listRun (({rest}).drop 1)"), "rcx", "rax", true⟩,
    ⟨"heap contents", hp, withCall hs "TemplateExactFixture.heapRun" "TemplateExactFixture.heapRun (x.drop 1)",
      (fun rest => s!"TemplateExactFixture.heapRun (({rest}).drop 1)"), "rax", "rax", false⟩,
    ⟨"value and heap contents", { hp with kind := .both },
      withCall hs "TemplateExactFixture.bothRun" "TemplateExactFixture.bothRun (x.drop 1)",
      (fun rest => s!"TemplateExactFixture.bothRun (({rest}).drop 1)"), "rax", "rax", false⟩]

def fixture : String := "\n".intercalate [
  "import Lift.Toys.FindSpec",
  "import Lift.Toys.FillSpec",
  "import Lift.Trusted.Encode",
  "namespace TemplateExactFixture",
  "structure State where\n  rcx : UInt64\n  rax : UInt64\n  mem : List (BitVec 64)",
  "def listRun (xs : List (BitVec 64)) : Option (BitVec 64) := some (BitVec.ofNat 64 xs.length)",
  "def fixed : Option (BitVec 64) := some 7",
  "structure Encoded where\n  word : BitVec 64",
  "instance : Lift.Trusted.Encode Encoded where\n  encode y := [⟨.W64, y.word⟩]\n  decode _ := none",
  "def flatRun (key : BitVec 64) (xs : List (BitVec 64)) (spare p : BitVec 64) : Option (BitVec 64) := some (key + BitVec.ofNat 64 xs.length + spare + p)",
  "def implicitRun {extra : BitVec 64} (xs : List (BitVec 64)) : Option (BitVec 64) := some (extra + BitVec.ofNat 64 xs.length)",
  "def recordRun (xs : List (BitVec 64)) (key p : BitVec 64) : Option (BitVec 64) := some (key + BitVec.ofNat 64 xs.length + p)",
  "def heapRun (xs : List (BitVec 64)) : Option (List (BitVec 64)) := some xs.reverse",
  "def bothRun (xs : List (BitVec 64)) : Option (BitVec 64 × List (BitVec 64)) := some (BitVec.ofNat 64 xs.length, xs.reverse)",
  "def heapOf (_ : BitVec 64) (frame xs : List (BitVec 64)) : List (BitVec 64) := xs ++ frame",
  "end TemplateExactFixture",
  "open TemplateExactFixture"]

def expected (c : Case) (part : String) (_template : Bool) : String :=
  let call := c.call part
  let word := if c.projected then
      s!"((({call}).map (fun y => UInt64.ofNat (y + p).toNat)).getD 0)"
    else if c.plan.kind == .both then s!"UInt64.ofBitVec ((({call}).getD (0, [])).1)"
    else s!"UInt64.ofBitVec (({call}).getD 0)"
  let whole := c.call "xs"
  let heap := if c.plan.kind == .both then s!"heapOf p frame ((({whole}).getD (0, [])).2)"
    else s!"heapOf p frame (({whole}).getD [])"
  match c.plan.kind with
  | .value => s!"x.{c.acc} + {word}"
  | .heap => heap
  | .both => s!"(x.{c.acc} + {word}, {heap})"

def checkTerm (label : String) (actual : Option String) (want : String) : IO (String × Bool) := do
  match actual with
  | none => pure (label ++ ": no candidate", false)
  | some actual =>
    let file := fixture ++ s!"\nexample (xs : List (BitVec 64)) (x st : State) (p key spare : BitVec 64) (frame : List (BitVec 64)) : ({actual}) = ({want}) := rfl"
    let ms ← ShapeTests.messagesOf "template-exact-run" file
    pure (s!"{label}: {ms.toList.filter (·.severity == .error) |>.map (·.text)}", !(ms.any (·.severity == .error)))

def checks : IO (List (String × Bool)) := do
  let some cs := cases | return [("exact-run fixture plans and shapes exist", false)]
  let some first := cs.head? | return [("exact-run fixture has a case", false)]
  let control ← checkTerm "control: expected fixture term elaborates" (some (expected first "xs" true)) (expected first "xs" true)
  let results ← cs.mapM fun c => do
    let rest := s!"xs.drop x.{c.index}.toNat"
    let template := (loopTemplates c.plan c.shape).head?.map (·.result)
    let tc ← checkTerm ("template " ++ c.label) template (expected c rest true)
    let some h := c.plan.heads.head? | return [tc, ("exact-run fixture has a head", false)]
    let r := if c.index == "rax" then Reg64.rax else .rcx
    let block (down : Bool) := blk h.name.s 0 []
      [(r, if down then .sub (.reg r) (.lit 1) else .add (.reg r) (.lit 1))] (goto 0)
    let suffix := (Skel.Discover.Result.suffix c.plan c.shape [block false] h).head?.map (·.text)
    let sc ← checkTerm ("discovery suffix " ++ c.label) suffix (expected c rest false)
    let prefixTerm := (Skel.Discover.Result.prefixCands c.plan c.shape [block true] h).head?.map (·.text)
    if c.plan.kind == .value then
      let pc ← checkTerm ("discovery prefix " ++ c.label) prefixTerm (expected c s!"xs.take x.{c.index}.toNat" false)
      pure [tc, sc, pc]
    else pure [tc, sc, ("discovery prefix excludes non-value " ++ c.label, prefixTerm.isNone)]
  let legacy := match sumPlan, sumShape with
    | some p, some sh => (loopTemplates p sh).head?.map (·.result) ==
        some "x.rax + UInt64.ofBitVec ((Lift.Spike.SumSpec.run (xs.drop x.rcx.toNat)).getD 0)"
    | _, _ => false
  pure (control :: ("control: old shapes keep their template text", legacy) :: results.flatten)


def concreteChecks : IO (List (String × Bool)) := do
  let some cs := cases | return [("concrete projection fixture exists", false)]
  let some c := cs.find? (·.projected) | return [("concrete projection case exists", false)]
  let some h := c.plan.heads.head? | return [("concrete projection head exists", false)]
  let block (down : Bool) := blk h.name.s 0 []
    [(.rcx, if down then .sub (.reg .rcx) (.lit 1) else .add (.reg .rcx) (.lit 1))] (goto 0)
  let terms (sh : StmtShape) : List (String × Option String × Nat) :=
    [("template", (loopTemplates c.plan sh).head?.map (·.result), 17),
     ("suffix", (Skel.Discover.Result.suffix c.plan sh [block false] h).head?.map (·.text), 17),
     ("prefix", (Skel.Discover.Result.prefixCands c.plan sh [block true] h).head?.map (·.text), 15)]
  let changed := { c.shape with resultFn := some (src "fun (y : BitVec 64) => y + p + 1") }
  let tests := (terms c.shape).map (fun (label, term, n) => (label, term, n, false)) ++
    (terms changed).map (fun (label, term, n) => (label, term, n, true))
  tests.mapM fun (label, term, n, changed) => do
    let some term := term | return ("concrete projection candidate " ++ label, false)
    let expr := "(let xs : List (BitVec 64) := [1, 2, 3]; " ++
      "let x : State := ⟨0, 5, []⟩; let p : BitVec 64 := 10; " ++ term ++ ")"
    let goal := if changed then s!"{expr} = ({n + 1} : UInt64) ∧ {expr} ≠ ({n} : UInt64)"
      else s!"{expr} = ({n} : UInt64)"
    let ms ← ShapeTests.messagesOf "template-projection-concrete" (fixture ++ s!"\nexample : {goal} := by decide\n")
    pure (s!"concrete projection {label}{if changed then " changes the result" else " gives the stated number"}: " ++
      toString (ms.toList.filter (·.severity == .error) |>.map (·.text)), !(ms.any (·.severity == .error)))

def featureChecks : IO (List (String × Bool)) := do
  let some cs := cases | return [("feature fixture plans and shapes exist", false)]
  let results ← (cs.filter (·.plan.kind == .value)).mapM fun c => do
    let some ctx := Skel.Discover.Upper.specCtxOf c.plan c.shape |
      return [("feature context " ++ c.label, false)]
    let (features, _) := Skel.Discover.specItems ctx
    [true, false].mapM fun take => do
      let term := features.findSome? fun f => match f, take with
        | .runTake _ _ (.field path), true | .runDrop _ _ (.field path), false =>
          if path == ["st", c.index, "toNat"] then some f.text else none
        | _, _ => none
      let part := s!"xs.{if take then "take" else "drop"} st.{c.index}.toNat"
      let call := c.call part
      let want := if c.projected then
          s!"((({call}).map (fun y => UInt64.ofNat (y + p).toNat)).getD 0).toNat"
        else s!"(({call}).getD 0).toNat"
      checkTerm (s!"feature {if take then "take" else "drop"} {c.label}") term want
  let boundary := match findPlan, findShape with
    | some p, some sh =>
      let exact := { sh with runCall := some (src "TemplateExactFixture.recordRun x.xs x.key p") }
      match Skel.Discover.Upper.specCtxOf { p with kind := .heap, mem := true } exact with
      | some c => c.result == .other
      | none => false
    | _, _ => false
  pure (("feature context excludes heap atoms for a record input", boundary) :: results.flatten)

end ExactRun


namespace ExactRunTrace

open Skel.Discover Skel.Discover.Upper Skel.Toy.MachineDiscover

def check : IO (List (String × Bool)) := do
  let sources : Skel.Toy.Sum.Sources :=
    { sum := ← IO.FS.readFile "Lift/Spike/Sum.lean", sites := ← IO.FS.readFile "Lift/Spike/Sites/Sum.lean" }
  let hand := Skel.Toy.SumRefute.spec
  let model : ModelSpec :=
    { names := hand.modelNames, imports := ("Lift.Trusted.Encode" :: hand.imports.filter fun m => !m.startsWith "Skel."),
      fn := hand.fn, opens := ["Coordinator.Dst"] }
  let .ok g0 := Skel.Toy.Sum.generate sources | return [("exact trace model exists", false)]
  let some p := sumPlan | return [("exact trace plan exists", false)]
  let some original := sumShape | return [("exact trace shape exists", false)]
  let sh := { original with
    runCall := Src.parse "Lift.Spike.SumSpec.run (xs ++ [p])",
    runResultType := Src.parse "BitVec 64",
    resultFn := Src.parse "fun (y : BitVec 64) => y + p" }
  let .ok r := refuteSpec p hintSum sh model | return [("exact trace refute spec exists", false)]
  let some ctx := specCtxOf p sh | return [("exact trace feature context exists", false)]
  let (features, _) := specItems ctx
  let some feature := features.find? (· matches .runDrop ..) | return [("exact trace suffix feature exists", false)]
  let atoms : List Atom :=
    [.eq (.field ["st₀", "rax", "toNat"]) (.field ["st", "rax", "toNat"]),
     .free "st₀.rax = st.rax", .frameEq ["st", "rax"],
     .free "(let st₀ := st.rax; st₀ = st.rax)"]
  let pool : Pool := { features := [(feature, 1)], atoms := atoms.map (·, 1) }
  let g : Generated := { modelText := g0.modelText, obligations := [], refuteText := fun _ _ => none }
  let m : Machine :=
    { spec := r, gen := g, ob := anyOb, head := r.loopLabel, result := none,
      refuteName := fun _ => "", check := fun _ => pure ("", .failed [], 0), dir := ".",
      seed := 1, limitMs := 180000, l3 := some ctx }
  let trace := m.traceSpec pool
  let .ok text := m.traceText trace | return [("exact trace text exists", false)]
  let expected :=
    "\nexample (gh : " ++ r.ghostTy ++ ") (s : " ++ r.stateTy ++ ") : traceFeatures (gh, s) = " ++
    "[((Lift.Spike.SumSpec.run ((wordsOf s.input.heap gh.2).drop s.rcx.toNat ++ [gh.2])).map " ++
    "(fun y => UInt64.ofNat (y + gh.2).toNat) |>.getD 0).toNat] := rfl\n" ++
    "example (gh : " ++ r.ghostTy ++ ") (s : " ++ r.stateTy ++ ") : " ++
    "traceFeatures (gh, { s with input := { s.input with rdi := 0 } }) = " ++
    "[((Lift.Spike.SumSpec.run ((wordsOf s.input.heap gh.2).drop s.rcx.toNat ++ [gh.2])).map " ++
    "(fun y => UInt64.ofNat (y + gh.2).toNat) |>.getD 0).toNat] := rfl\n" ++
    "example (gh gh₀ : " ++ r.ghostTy ++ ") (s s₀ : " ++ r.stateTy ++ ") : traceAtoms (gh₀, s₀) (gh, s) = " ++
    "[decide (s₀.rax.toNat = s.rax.toNat), decide (s₀.rax = s.rax), decide (s.rax = s₀.rax), decide (s.rax = s.rax)] := rfl\n"
  let ms ← ShapeTests.messagesOf "trace-exact-run" (text ++ expected)
  pure [("production trace keeps exact run, projection, captured parameter and entry atoms: " ++
      toString (ms.toList.filter (·.severity == .error) |>.map (·.text)), !(ms.any (·.severity == .error))),
    ("production trace uses optional admitted and free draws",
      (text.splitOn "Skel.Refute.admittedState?").length == 2 &&
      (text.splitOn "Skel.Refute.FreeFn.draw refuteFree").length == 2 &&
      (text.splitOn "Skel.Discover.Trace.ofOptionalRuns").length == 2),
    ("trace context leaves the machine state and source atoms unchanged",
      m.site.stateTy == r.stateTy && pool.atoms.map (·.1) == atoms &&
      (m.site.step.splitOn "st₀.2").length == 1)]

end ExactRunTrace


/-- Gives the number of failed checks. The suite runs when `only` is none or `genloop`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genloop" then return 0
  let mut failed := 0
  for (name, ok) in ((← ExactRun.checks) ++ (← ExactRun.featureChecks) ++ (← ExactRun.concreteChecks) ++ (← ExactRunTrace.check)) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genloop: {name}"
  for (name, ok) in pureChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genloop: {name}"
  for (name, ok) in chainSumPure do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genloop: {name}"
  for (name, ok, msg) in (← chainSumRefute) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genloop: {name} {msg}"
  let (name, ok, msg) ← chainSumLoopCheck
  unless ok do
    failed := failed + 1
    IO.println s!"FAIL  genloop: {name}\n{msg}"
  for (name, ok, msg) in (← refuteChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genloop: {name} {msg}"
  for fn in loopRowFns do
    let (name, ok, msg) ← loopRowCheck fn
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genloop: {name}\n{msg}"
  for fn in ["toyFind", "toyWalk", "toyFill"] do
    let (name, ok, msg) ← refinesCheck fn
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genloop: {name}\n{msg}"
  return failed

end GenLoopTests
