import Skel.Types
import Skel.Source
import Skel.Rungs
import Skel.Render
import Skel.Gen.Derived.Spike
import Skel.Gen.Generate
import Lift.Spike.Code

/-! The table of the 14 obligations of `toySum` (`docs/one-way-lift-skeleton-plan-20261118.md`, section 2.1), the
statement of the loop (2.3), and the generator (5.4). The rows 1 to 5 come from `Skel.Gen.generate` (G1-10) for the
function `toySum` of `Lift.Spike.Code.code`. The rows 6 to 14 and the L2⁺ and L3 declarations come from the hand file
`Lift/Spike/Sum.lean`, read as text. -/

namespace Skel.Toy.Sum

open Skel

/-- The texts of the two hand files. `sites` is not read by the generator since G1-11; `Skel/Main.lean` still fills it. -/
structure Sources where
  sum : String
  sites : String

/-- Where the statement and the replay text of an obligation come from: the generator (rows 1 to 5), a declaration of
`Sum`, or the loop of 2.3. -/
inductive Location where
  | generated
  | sum (name : String)
  | loop

/-- A row of the table of 2.1. The statement is not in the row; it comes from `Location`. -/
structure TableRow where
  (id : ObId) (cls : ObClass) (origin : Origin) (deps : List ObId) (claim : Claim) (loc : Location)

/-- The id of an obligation of `toySum`: the function `sum`, and the name that follows `sum.` in the table. -/
def sumId (name : String) : ObId := { function := "sum", name := name }

/-- The table of 2.1, in table order. Each dep comes earlier in the table. -/
def rows : List TableRow :=
  [ { id := sumId "block.entry", cls := .block, origin := .block "entry", deps := [], claim := .none,
      loc := .generated },
    { id := sumId "block.LBB1_1", cls := .block, origin := .block "LBB1_1", deps := [], claim := .none,
      loc := .generated },
    { id := sumId "block.o9", cls := .block, origin := .block "o9", deps := [], claim := .none,
      loc := .generated },
    { id := sumId "block.LBB1_3", cls := .block, origin := .block "LBB1_3", deps := [], claim := .none,
      loc := .generated },
    { id := sumId "decompiles_l2", cls := .block, origin := .unit,
      deps := [sumId "block.entry", sumId "block.LBB1_1", sumId "block.o9", sumId "block.LBB1_3"],
      claim := .none, loc := .generated },
    { id := sumId "refines_l2p", cls := .access, origin := .unit, deps := [], claim := .none,
      loc := .sum "refines_l2p" },
    { id := sumId "above_l2p", cls := .access, origin := .unit, deps := [sumId "refines_l2p"], claim := .none,
      loc := .sum "above_l2p" },
    { id := sumId "loop", cls := .refine, origin := .loop "LBB1_1", deps := [], claim := .loop, loc := .loop },
    { id := sumId "refines_l3", cls := .refine, origin := .unit, deps := [], claim := .models,
      loc := .sum "refines_l3" },
    { id := sumId "above_l3", cls := .refine, origin := .unit, deps := [sumId "refines_l3"], claim := .none,
      loc := .sum "above_l3" },
    { id := sumId "total", cls := .total, origin := .unit, deps := [], claim := .none, loc := .sum "total" },
    { id := sumId "decompiles", cls := .link, origin := .unit,
      deps := [sumId "decompiles_l2", sumId "above_l2p", sumId "above_l3"], claim := .none,
      loc := .sum "decompiles" },
    { id := sumId "decompiles_code", cls := .link, origin := .unit, deps := [sumId "decompiles"],
      claim := .none, loc := .sum "decompiles_code" },
    { id := sumId "contract", cls := .contract, origin := .unit,
      deps := [sumId "total", sumId "decompiles_code"], claim := .none, loc := .sum "contract" } ]

/-- The declarations of `Lift/Spike/Sum.lean` that the model text takes as text: the L2⁺ and L3 declarations (5.4). The
L2 declarations come from `Skel.Gen.generate`. -/
def handModelNames : List String := ["In2p", "blocksP", "l2p", "run", "C", "l3", "SimIn", "SimArr", "SimSt"]

/-- The target of `toySum`: the constants of `Lift/Spike/L1.lean` and `Lift/Spike/Sum.lean`. -/
def target : Skel.Gen.Target :=
  { step := "L1.step", lo := "toyJobPC", hi := "toyEndPC", entryPC := "toySumPC",
    imports := ["Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.SysV", "Lift.Spike.L1"], callees := [] }

/-- The id with the function `sum`: the generator names the function `toySum`, the table names it `sum`. -/
private def toSum (i : ObId) : ObId := { i with function := "sum" }

/-- The output of `Skel.Gen.generate` for `toySum` (rows 1 to 5 and their `det` text), with the function of each id
renamed to `sum`. The `det` text of the generator is the tactic block of the proof; the proof is `by` and that block. -/
def generatedOf : Except String Generated :=
  match Skel.Gen.generate target Skel.Gen.Hints.none .storeChain Lift.Spike.Code.code (.derived Skel.Gen.Derived.spike) "toySum" with
  | .ok g =>
    .ok { g with obligations := g.obligations.map fun o => { o with id := toSum o.id, deps := o.deps.map toSum },
                 det := g.det.map fun (i, t) => (toSum i, t) }
  | .error e => .error (reprStr e)

/-- The statement of obligation 8, the loop (2.3), as Lean text. -/
def loopStatement : String :=
  "∀ (xs : List (BitVec 64)) (a : In2p), SimArr xs a →\n    blocksP.Returns noCall .LBB1_1 (init a) (UInt64.ofBitVec xs.sum)"

/-- The first template triple, the triple T1 of 5.2 (input fixed only). -/
def template1 : Triple :=
  { inv := "True", measure := "xs.length - x.rcx.toNat", result := "x.rax + UInt64.ofBitVec (xs.drop x.rcx.toNat).sum" }

/-- The second template triple, the triple T2 of 5.2 (counter below length). -/
def template2 : Triple := { template1 with inv := "x.rcx.toNat ≤ xs.length" }

/-- The templates of `toySum`, in order. -/
def templateTriples : List Triple := [template1, template2]

/-- The replies of the model rung (5.1, item 3). Empty on the first day. -/
def replies : List (String × String) := []

/-- The lines `lo` to `hi` of `src` (1-based, inclusive), joined by newlines. `none` when `lo` is not in `1 .. hi`
or when `hi` is past the last line. -/
def lineRange (src : String) (lo hi : Nat) : Option String :=
  let picked := ((src.splitOn "\n").drop (lo - 1)).take (hi + 1 - lo)
  if decide (1 ≤ lo) && decide (lo ≤ hi) && picked.length == hi + 1 - lo then some ("\n".intercalate picked)
  else none

/-- The text of the declaration `name` (`declText`), or an error that names it. -/
def declOf (src name : String) : Except String String :=
  match declText src name with
  | some text => .ok text
  | none => .error s!"no declaration {name}"

/-- The model text (5.4): the L2 text of the generator, then the declarations of `handModelNames`, each in its own block.
It has no `theorem` and no `Sites.Sum`. -/
def modelText (src : Sources) (l2Text : String) : Except String String := do
  let decls ← handModelNames.mapM (declOf src.sum)
  return "\n\n".intercalate (l2Text :: decls)

/-- The texts of the prompt of the model rung, from `Lift/Spike/Sum.lean`: the L2+ text is the declarations `In2p`, `Lbl`,
`St` and `blocksP`; the L3 text is `run` and `C`; the loop rule text is `SimArr` and the proof of the loop with the
slots `INV`, `MEASURE` and `RESULT`. The hand step and the hand triple are not in these texts. -/
def promptTexts (src : Sources) : Except String PromptTexts := do
  let l2 ← ["In2p", "Lbl", "St", "blocksP"].mapM (declOf src.sum)
  let l3 ← ["run", "C"].mapM (declOf src.sum)
  let simArr ← declOf src.sum "SimArr"
  return { l2PlusText := "\n\n".intercalate l2, l3Text := "\n\n".intercalate l3,
           loopRule := simArr ++ "\n\n" ++ loopProof (squash loopStatement) { inv := "INV", measure := "MEASURE", result := "RESULT" } }

/-- The header and the proof of a declaration: the text before its first `:=` outside brackets, and the text after it.
`splitDecl` cuts at the first `:=`, which is inside `{ d with regs := ... }` in the header of `entry`. -/
private def splitHeader (acc : List Char) (depth : Nat) : List Char → Option (String × String)
  | [] => none
  | ':' :: '=' :: rest =>
    if depth == 0 then some (String.ofList acc.reverse, String.ofList rest)
    else splitHeader ('=' :: ':' :: acc) depth rest
  | c :: cs => splitHeader (c :: acc) (depthAfter depth c) cs

/-- The text without the whitespace at its ends; the lines inside it are kept. -/
private def trimEnds (s : String) : String :=
  let cs := s.toList.dropWhile Char.isWhitespace
  String.ofList (cs.reverse.dropWhile Char.isWhitespace).reverse

/-- The header and the proof of the declaration `name` (`splitHeader`), both trimmed, or an error that names it. -/
def partsOf (src name : String) : Except String (String × String) := do
  let text ← declOf src name
  match splitHeader [] 0 text.toList with
  | some (header, proof) => pure (trimEnds header, trimEnds proof)
  | none => throw s!"no := in declaration {name}"

/-- The text squashed to one line, without the spaces at its ends. -/
private def tidy (s : String) : String :=
  let cs := (squash s).toList.dropWhile (· == ' ')
  String.ofList (cs.reverse.dropWhile (· == ' ')).reverse

/-- The statement of the theorem `name` from its header: the binders become a `∀` in front of the type after the
colon. The result is squashed to one line. `none` when the header is not `theorem name` with a type. -/
def statementOf (name header : String) : Option String :=
  let start := "theorem " ++ name
  if !header.startsWith start then none
  else
    match splitAtTop ':' [] 0 (header.toList.drop start.length) with
    | none => none
    | some (binders, concl) =>
      let bs := tidy binders
      let t := tidy concl
      if t.isEmpty then none
      else some (if bs.isEmpty then t else s!"∀ {bs}, {t}")

/-- The proof with the introduction of the binder names `names` in front. The statement of a row is a `∀` over the
binders of the hand theorem, and the hand proof uses the names of the binders. A tactic proof gets an `intro`; a term
proof gets a `fun`. No names gives the proof as it is. -/
def introBinders (names : List String) (proof : String) : String :=
  let ns := " ".intercalate names
  if names.isEmpty then proof
  else if proof.startsWith "by\n" then
    let rest := String.ofList (proof.toList.drop 3)
    let indent := String.ofList (rest.toList.takeWhile (· == ' '))
    s!"by\n{indent}intro {ns}\n{rest}"
  else if proof.startsWith "by " then s!"by intro {ns}; {String.ofList (proof.toList.drop 3)}"
  else s!"fun {ns} => {proof}"

/-- The binder text of a header `theorem name binders : type`, squashed; `none` when the header has no type. -/
def bindersOf (name header : String) : Option String :=
  let start := "theorem " ++ name
  if !header.startsWith start then none
  else (splitAtTop ':' [] 0 (header.toList.drop start.length)).map fun (bs, _) => tidy bs

/-- The statement of a declaration of the file `src`, or an error that names it. -/
private def statementFrom (src name : String) : Except String String := do
  let (header, _) ← partsOf src name
  match statementOf name header with
  | some s => pure s
  | none => throw s!"no statement in declaration {name}"

/-- The proof of a declaration of the file `src`, with the introduction of its binders, or an error that names it. -/
private def proofFrom (src name : String) : Except String String := do
  let (header, proof) ← partsOf src name
  return introBinders (((bindersOf name header).map binderNames).getD []) proof

/-- The statement of a location of a hand row, as Lean text. The rows of the generator have their statements from it. -/
def statementOfLoc (src : Sources) : Location → Except String String
  | .generated => throw "a generated row has its statement from the generator"
  | .sum n => statementFrom src.sum n
  | .loop => pure (squash loopStatement)

/-- The replay text of a location: the proof of the declaration. The generated rows and the loop have none: their
proofs come from the generator and from a triple. -/
def replayText (src : Sources) : Location → Except String (Option String)
  | .generated => pure none
  | .sum n => some <$> proofFrom src.sum n
  | .loop => pure none

/-- The obligations of the table, in table order. A row of the generator is the obligation of `gen` with its id; the
other rows have their statements from the sources. -/
def obligationsOf (src : Sources) (gen : List Obligation) : Except String (List Obligation) :=
  rows.mapM fun r =>
    match r.loc with
    | .generated =>
      match gen.find? (·.id == r.id) with
      | some o => .ok o
      | none => .error s!"the generator has no row {r.id.name}"
    | loc => do
      let statement ← statementOfLoc src loc
      return ({ id := r.id, cls := r.cls, origin := r.origin, statement, deps := r.deps, claim := r.claim } : Obligation)

/-- The replay store (5.1, item 4): the replay text of each row that has one, with its id, in table order. -/
def replayStore (src : Sources) : Except String (List (ObId × String)) :=
  (rows.mapM fun (r : TableRow) => do
    let text ← replayText src r.loc
    return text.map (r.id, ·)).map List.reduceOption

/-- The generator (5.4): the model text, the 14 obligations and the `det` text of `decompiles_l2`. The refute text is
not set on the first day: it gives no candidate. -/
def generate (src : Sources) : Except String Generated := do
  let g ← generatedOf
  let text ← modelText src g.modelText
  let obs ← obligationsOf src g.obligations
  return { modelText := text, obligations := obs, refuteText := fun _ _ => none, det := g.det }

end Skel.Toy.Sum
