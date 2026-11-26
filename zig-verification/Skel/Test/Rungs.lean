import Skel.Rungs
import Skel.Gen.Link

/-! The tests of `Skel/Rungs.lean` (suite `rungs`): `lake exe skel-test --only rungs`. Each check is a value that must
hold. A check that does not hold prints one `FAIL` line; the suite gives the number of failed checks. The texts of the
link templates and the closing rung are copied from `docs/one-way-lift-skeleton-plan-20261118.md` (5.1). -/

namespace RungsTests

open Skel

/-- An obligation of the function `Sum` with the given class, origin and name. -/
def mkOb (cls : ObClass) (origin : Origin) (name : String) : Obligation :=
  { id := { function := "Sum", name := name }, cls := cls, origin := origin, statement := "", deps := [],
    claim := .none }

/-- A proof attempt with the given text; its result does not matter for the proposers. -/
def proofAttempt (text : String) : Attempt :=
  { candidate := .proof .closing text, result := .checked (.failed []), ms := 0 }

/-- A counterexample of the triple `t`. -/
def cex (t : Triple) : Cex :=
  { ob := { function := "Sum", name := "loop" }, subject := .triple t, seed := 1, index := 2,
    shown := "s", why := "w" }

/-- An attempt of the triple `t` on the template rung, refuted with `cti`. -/
def ctiAttempt (t : Triple) : Attempt :=
  { candidate := .triple .template t, result := .refuted (.cti (cex t)), ms := 0 }

/-- An attempt of the triple `t` on the template rung, refuted with `real`. -/
def realAttempt (t : Triple) : Attempt :=
  { candidate := .triple .template t, result := .refuted (.real (cex t)), ms := 0 }

/-- An attempt of the triple `t` on the template rung, passed by the refuter. -/
def passAttempt (t : Triple) : Attempt :=
  { candidate := .triple .template t, result := .refuted (.pass 200), ms := 0 }

/-- A history with the given attempts and no counterexample. -/
def hist (as : List Attempt) : History := { attempts := as, cexs := [] }

/-- The triple T1 of 5.2 (input fixed only). -/
def t1 : Triple :=
  { inv := "True", measure := "xs.length - x.rcx.toNat", result := "x.rax + UInt64.ofBitVec (xs.drop x.rcx.toNat).sum" }

/-- The triple T2 of 5.2 (counter below length). -/
def t2 : Triple := { t1 with inv := "x.rcx.toNat ≤ xs.length" }

/-- A third template, for the list of three. -/
def t3 : Triple := { t1 with inv := "x.rcx.toNat ≤ xs.length ∧ True" }

/-- Prompt texts that no check reads. -/
def noTexts : PromptTexts := { l2PlusText := "", l3Text := "", loopRule := "" }

/-- The five closing texts of 5.1, item 2, in order. -/
def closingTexts5 : List String :=
  ["by intros; exact ⟨_, rfl⟩", "by simp_all", "by grind", "by bv_omega", "by bv_decide"]

/-- The link template of `decompiles` (5.1, item 1). -/
def linkDecompiles : String :=
  "by intros; apply Decompiles.above (decompiles_l2.above above_l2p); apply above_l3"

/-- The link template of `decompiles_code` (5.1, item 1). -/
def linkDecompilesCode : String :=
  "by intros; exact (Sites.decompiles_l1Spec_iff Code.code L1.step L1.spec _).mp (by apply decompiles)"

/-- The link template of `contract` (5.1, item 1). -/
def linkContract : String :=
  "by intros; apply Decompiles.transfer _ C (fun xs y => run xs = some y) total (fun _ _ _ h => h) <;> first | assumption | apply decompiles_code"

/-- The names of the link templates of `toySum`: the hand file `Lift/Spike/Sum.lean` and its L1 module. -/
def sumLinks : Gen.LinkNames :=
  { code := "Code.code", step := "L1.step", spec := "L1.spec", c := "C", run := "run", inputs := ["xs"], contract := "C xs" }

/-- The `det` texts of the link rows of `Sum`: the texts of `Gen.linkText` for the names `sumLinks`, as `generateUpper` makes
them for its own names. -/
def linkDet : List (ObId × String) :=
  ["decompiles", "decompiles_code", "contract", "other"].filterMap fun n =>
    (Gen.linkText sumLinks n).map fun t => ({ function := "Sum", name := n }, t)

/-- The recorded replies of the test: two for `entry` and one for `head`, in this order. -/
def replies : List (String × String) := [("entry", "a"), ("head", "c"), ("entry", "b")]

/-- The replay store of the test: the hand proof of `total`. -/
def store : List (ObId × String) := [({ function := "Sum", name := "total" }, "by exact h")]

/-- Whether the text `c` is the text of an attempt of `h`. Independent of the code under test. -/
def mentions (c : String) (h : History) : Bool :=
  h.attempts.any fun a => match a.candidate with
    | .proof _ t => t == c
    | .triple _ _ | .ask _ => false

/-- The texts that a proposer gives when each text it gives is added to the history, at most `n` calls. -/
def walk (p : Proposer String) (o : Obligation) : Nat → List Attempt → List String
  | 0, _ => []
  | n + 1, as => match p o (hist as) with
    | some t => t :: walk p o n (as ++ [proofAttempt t])
    | none => []

/-- The texts of the test pool. -/
def pool : List String := ["p0", "p1", "p2", "p3", "p4", "p5", "p6", "p7"]

/-- The next state of a linear congruential generator. -/
def lcg (s : Nat) : Nat := (1103515245 * s + 12345) % 2147483648

/-- `n` values of a linear congruential generator from the seed `s`. -/
def stream : Nat → Nat → List Nat
  | _, 0 => []
  | s, n + 1 => (s / 65536) :: stream (lcg s) n

/-- A pool text from a number. -/
def pickText (n : Nat) : String := pool.getD (n % 8) "?"

/-- A list `cs` and a history `h` from the seed: up to five texts in `cs`, up to five attempts in `h`. -/
def genCase (seed : Nat) : List String × History :=
  let ns := stream seed 16
  let k := seed % 6
  let m := seed / 6 % 6
  ((ns.take k).map pickText, hist (((ns.drop 8).take m).map fun n => proofAttempt (pickText n)))

/-- The property of `firstNew` for the case of the seed: a result is in `cs` and is not in `h`. -/
def firstNewHolds (seed : Nat) : Bool :=
  let (cs, h) := genCase seed
  match firstNew cs h with
  | none => true
  | some c => cs.contains c && !mentions c h

/-- The checks, each with its name. -/
def checks : List (String × Bool) :=
  let entry := mkOb .block (.block "entry") "entry"
  let total := mkOb .total .unit "total"
  let decompiles := mkOb .link .unit "decompiles"
  [ ("block origin gets by intros; lift_block", liftBlock [] entry (hist []) == some "by intros; lift_block"),
    ("block origin does not get by lift_block", liftBlock [] entry (hist []) != some "by lift_block"),
    ("block origin gives none when by intros; lift_block is in the history",
      liftBlock [] entry (hist [proofAttempt "by intros; lift_block"]) == none),
    ("unit origin of class access gets none", liftBlock [] (mkOb .access .unit "refines_l2p") (hist []) == none),
    ("loop origin of class refine gets none", liftBlock [] (mkOb .refine (.loop "head") "loop") (hist []) == none),
    -- a link row has no text of the ladder: its text is its `det` text, from `Gen.linkText` of the names of the function
    ("link rows get no text of their own: no det, no text",
      [decompiles, mkOb .link .unit "decompiles_code", mkOb .contract .unit "contract", mkOb .link .unit "other"].all
        fun ob => liftBlock [] ob (hist []) == none),
    ("link decompiles gets its det text, the template of Gen.linkText",
      liftBlock linkDet decompiles (hist []) == some linkDecompiles),
    ("link decompiles gives none once its det text is in the history",
      liftBlock linkDet decompiles (hist [proofAttempt linkDecompiles]) == none),
    ("link decompiles_code gets its det text",
      liftBlock linkDet (mkOb .link .unit "decompiles_code") (hist []) == some linkDecompilesCode),
    ("contract gets its det text", liftBlock linkDet (mkOb .contract .unit "contract") (hist []) == some linkContract),
    ("Gen.linkText of an unknown name is none, so the row gets none", Gen.linkText sumLinks "nope" == none &&
      liftBlock linkDet (mkOb .link .unit "nope") (hist []) == none),
    ("closing gives the five texts in order", walk closing total 7 [] == closingTexts5),
    ("closing gives none after the five texts", closing total (hist (closingTexts5.map proofAttempt)) == none),
    ("firstNew of an empty list is none", firstNew [] (hist []) == none),
    ("firstNew gives the first text", firstNew ["a", "b"] (hist []) == some "a"),
    ("firstNew skips a text in the history", firstNew ["a", "b"] (hist [proofAttempt "a"]) == some "b"),
    ("firstNew skips two texts in the history",
      firstNew ["a", "b", "c"] (hist [proofAttempt "a", proofAttempt "b"]) == some "c"),
    ("firstNew gives none when all texts are in the history",
      firstNew ["a", "b"] (hist [proofAttempt "b", proofAttempt "a"]) == none),
    ("templates gives T1 first", templates [t1, t2] total (hist []) == some t1),
    ("templates gives T2 when T1 has cti", templates [t1, t2] total (hist [ctiAttempt t1]) == some t2),
    ("templates gives none when T1 passed", templates [t1, t2] total (hist [passAttempt t1]) == none),
    ("templates gives none when T1 has real", templates [t1, t2] total (hist [realAttempt t1]) == none),
    ("templates gives none when T1 has cti and T2 is in the history",
      templates [t1, t2] total (hist [ctiAttempt t2, ctiAttempt t1]) == none),
    ("templates [] gives none", templates [] total (hist []) == none),
    ("templates [] gives none with a history", templates [] total (hist [ctiAttempt t1]) == none),
    ("templates [t1] gives t1, then none after cti",
      templates [t1] total (hist []) == some t1 && templates [t1] total (hist [ctiAttempt t1]) == none),
    ("templates [t1, t2, t3] gives t3 only after cti on t1 and on t2",
      templates [t1, t2, t3] total (hist [ctiAttempt t1]) == some t2 &&
      templates [t1, t2, t3] total (hist [ctiAttempt t2, ctiAttempt t1]) == some t3 &&
      templates [t1, t2, t3] total (hist [realAttempt t2, ctiAttempt t1]) == none),
    ("a ladder with no templates has the template rung and it gives nothing",
      (ladders [] noTexts [] [] [] t1).triple.map (·.1) == ([.template, .model, .replay] : List InvRung) &&
      ((ladders [] noTexts [] [] [] t1).triple.head?.bind fun (_, p) => p total (hist [])) == none),
    ("replayTriple gives its triple", replayTriple t2 total (hist []) == some t2),
    ("replayTriple gives none once its triple is in the history",
      replayTriple t2 total (hist [ctiAttempt t2]) == none),
    ("replay gives none for an obligation not in the store",
      replay store (mkOb .access .unit "other") (hist []) == none),
    ("replay gives the stored text", replay store total (hist []) == some "by exact h"),
    ("replay gives none once the stored text is in the history",
      replay store total (hist [proofAttempt "by exact h"]) == none),
    ("model [] gives none", model [] total (hist []) == none),
    ("model gives the replies of the name in order",
      walk (model replies) (mkOb .block (.block "entry") "entry") 4 [] == ["a", "b"]),
    ("model gives the replies of another name", model replies (mkOb .refine .unit "head") (hist []) == some "c"),
    ("ladders give the proof rungs in order",
      (ladders [t1, t2] noTexts [] [] [] t1).proof.map (·.1) == ([.liftBlock, .closing, .model, .replay] : List Rung)),
    ("ladders give the triple rungs in order",
      (ladders [t1, t2] noTexts [] [] [] t1).triple.map (·.1) == ([.template, .model, .replay] : List InvRung))
  ]

/-- Gives the number of failed checks. The suite runs when `only` is none or `rungs`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "rungs" then return 0
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  rungs: {name}"
  unless (List.range cases).all (fun i => firstNewHolds (seed + i)) do
    failed := failed + 1
    IO.println s!"FAIL  rungs: firstNew gives a text that is not in cs or is in h (seeds {seed} to {seed + cases})"
  return failed

end RungsTests
