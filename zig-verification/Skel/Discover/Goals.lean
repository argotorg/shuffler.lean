import Skel.Types
import Skel.Discover.Lang
import Skel.Discover.Site

/-! The Lean goal texts of a quad for a loop site (`docs/research/invariant-discovery-design-20261119.md`, sections 3.5
and 5, task D8). Pure, except `Step.Unfolds`, which the texts use.

A text is a complete Lean file: the imports, then `namespace <fn>` with the step of the site (the text of D2), the
definitions `INV`, `MEASURE`, `ENTRY` of the quad and the site, and one `Prop` definition `<name>_goal` for each proof
obligation. Each definition takes the parameters of the site. `Goals.header` is that file. `Goals.text` adds one theorem
`<name> : <name>_goal` for each obligation with a proof text that a later rung gives, then the closing theorems.

A fueled site has the obligations

- `INV_entry`: `ENTRY st → INV st st ∧ MEASURE st ≤ BOUND st`;
- `INV_step`: `INV st₀ st → step st = .cont st' → INV st₀ st' ∧ MEASURE st' < MEASURE st`;
- `zero_case`: `INV st₀ st → MEASURE st ≤ fuel → fuel ≠ 0`.

The header also has `loop` (the call of the function at the fuel `fuel` and the state `st`), `BOUND` (the fuel
expression of the site, or the constant of the bound), the lemma `unfold` (one unfolding of the function is one step,
and no step is a fault; its proof is generated), and `fuel_enough_of`: from the three goals as hypotheses, the loop
from an entry state with a fuel of at least `BOUND st` gives the value of an exit of the step. Its proof is a generated
induction on the fuel. `Goals.text` adds `fuel_enough`, which applies `fuel_enough_of` to the three theorems.

The zero case is not the form `MEASURE st = 0 → step st ≠ .cont _` of the design: the function at the fuel `0` gives
its out-of-fuel value without a step, so a measure that is `0` at the last step (an exit) does not bound the fuel. With
`zero_case`, the measure counts the steps that are left, the exit step included.

The zero case follows the equations of the function (task DISC-FUEL, G6). When the value at the fuel `0` reads the state
(`LoopSite.zero`: the function tests its exit before its fuel), the header has `ZERO` (that value), the lemma `zero_eq`
(`loop 0 st = ZERO st`, by the unfolding equation), and the obligation is
- `zero_case`: `INV st₀ st → MEASURE st = 0 → Step.Ends (ZERO st) (step st)`: a state of the measure `0` exits, with the
  value that the loop gives at the fuel `0`. Here the measure counts the steps that are left, without the exit step.
`fuel_enough_of` is then `Step.ends_of_measure` (below), the one theorem of the soundness of this form. A function whose
value at the fuel `0` does not read the state keeps the form `fuel ≠ 0` above.

A `wf` site has the obligations `INV_entry` (`ENTRY st → INV st st`), `INV_step` (the invariant after a step that goes
on) and `decreasing` (the goal of `decreasing_by` with `INV` as a hypothesis; a tuple measure falls in `Prod.Lex`). It
has no closing theorem. A machine site gives the `Triple` of the quad for `lift_loop!`, without the bound.

A fueled site has a second form, the fuel-indexed form (`docs/research/invariant-discovery-solver-20261119.md`, section 7). A
quad with the measure `Measure.fuel` selects it: the invariant `INV st fuel` takes the fuel that is left, and its atoms may
read `fuel`. The obligations are

- `INV_entry`: `ENTRY st → INV st (BOUND st)`;
- `INV_step`: `INV st (fuel + 1) → step st = .cont st' → INV st' fuel`;
- `INV_zero`: `¬ INV st 0`.

It has no separate measure, and no zero-case risk: a head at the fuel `0` is not in the invariant. `fuel_enough` is at the
fuel `BOUND st` exactly (the invariant need not be monotone in the fuel). The state in the texts is `st`; an atom of the entry
state (`frameEq`) has no place in this form. A quad with a `permSlice` atom (the solver gives it for a permutation, task S6)
has the entry form: `INV st₀ st fuel`, with `INV_entry`: `ENTRY st → INV st st (BOUND st)`, `INV_step` and `INV_zero` for
each `st₀`. The lemmas `range_map_getElem!` and `toList_swap_perm` are for the proofs of its goals.

The state in the texts is `st` and the entry state is `st₀`, as in the atom texts of D1. -/

namespace Skel.Discover

universe u v

/-- The elements of a vector by index, as a list: its list. -/
theorem range_map_getElem! {α : Type u} [Inhabited α] {n : Nat} (v : Vector α n) :
    (List.range n).map (fun j => v[j]!) = v.toList := by
  apply List.ext_getElem
  · simp
  · intro k h1 _
    simp at h1
    simp [h1, getElem!_def, Vector.getElem?_eq_getElem h1]

/-- A swap is a permutation. -/
theorem toList_swap_perm {α : Type u} {n : Nat} (v : Vector α n) (i j : Nat) (hi : i < n) (hj : j < n) :
    (v.swap i j hi hj).toList.Perm v.toList := by
  have h := Vector.swap_perm (xs := v) hi hj
  rw [Vector.perm_iff_toList_perm] at h
  exact h

/-- The measure of the fuel-indexed form: the fuel that is left. -/
def Measure.fuel : Measure := .one (.field ["fuel"])

/-- Whether the quad is of the fuel-indexed form. -/
def Quad.fuelIndexed (q : Quad) : Bool := q.measure == Measure.fuel

/-- Whether a quad of the fuel-indexed form has the entry form: it has a `permSlice` atom. -/
def Quad.entryForm (q : Quad) : Bool := q.inv.any (· matches .permSlice ..)

/-- One step of a fueled loop agrees with one unfolding: `v`, the loop at the fuel `n + 1`, is `k s`, the loop at the
fuel `n` at the next state, or the value of the exit. A fault does not agree. -/
def Step.Unfolds {σ : Type u} {R : Type v} (k : σ → R) (v : R) : Step σ R → Prop
  | .cont s => v = k s
  | .exit r => v = r
  | .fault => False

/-- A step agrees with the value `v` of the loop at the fuel `0`: it exits with `v`. -/
def Step.Ends {σ : Type u} {R : Type v} (v : R) : Step σ R → Prop
  | .exit r => v = r
  | _ => False

/-- The soundness of the goals of the measure form with the zero case of the equations (task DISC-FUEL, G6): a loop whose
steps agree with its unfoldings, an invariant that a step keeps with a measure that falls, and a zero case where a state
of the measure `0` exits with the value of the loop at the fuel `0`, give from each state of the invariant with a measure
of at most `n` the value of an exit of the step at the fuel `n`. The order of the checks of the loop (the exit test or the
fuel test first) is in `loop 0`. -/
theorem Step.ends_of_measure {σ : Type u} {R : Type v} (loop : Nat → σ → R) (step : σ → Step σ R) (inv : σ → Prop)
    (μ : σ → Nat) (unfold : ∀ n x, Step.Unfolds (loop n) (loop (n + 1) x) (step x))
    (hstep : ∀ x x', inv x → step x = .cont x' → inv x' ∧ μ x' < μ x)
    (hzero : ∀ x, inv x → μ x = 0 → Step.Ends (loop 0 x) (step x)) :
    ∀ n x, inv x → μ x ≤ n → ∃ s r, step s = .exit r ∧ loop n x = r := by
  intro n
  induction n with
  | zero =>
    intro x hI hμ
    have hz := hzero x hI (by omega)
    cases hs : step x with
    | cont x' => rw [hs] at hz; exact hz.elim
    | exit r => rw [hs] at hz; exact ⟨x, r, hs, hz⟩
    | fault => rw [hs] at hz; exact hz.elim
  | succ n ih =>
    intro x hI hμ
    have hu := unfold n x
    cases hs : step x with
    | cont x' =>
      rw [hs] at hu
      obtain ⟨hI', hμ'⟩ := hstep x x' hI hs
      rw [hu]
      exact ih x' hI' (by omega)
    | exit r => rw [hs] at hu; exact ⟨x, r, hs, hu⟩
    | fault => rw [hs] at hu; exact hu.elim

/-- A proof obligation: its name, the name of its `Prop` definition, and the text of that `Prop`. -/
structure Goal where
  name : String
  goal : String
  statement : String
  deriving DecidableEq, Repr

/-- The goal texts of a quad for a site. `header` is a complete file; `closing` follows the theorems of the
obligations. -/
structure Goals where
  ns : String
  params : List (String × String)
  header : String
  obligations : List Goal
  closing : String
  /-- The fuel-indexed form with the entry state: `INV st₀ st fuel`. -/
  entry : Bool := false
  /-- The measure form with the zero case of the equations: `zero_case` reads `ZERO`, the value at the fuel `0`. -/
  zeroArm : Bool := false
  deriving DecidableEq, Repr

/-- The names that the texts bind. A parameter of the site must not have one of them. -/
def reserved : List String :=
  ["st", "st₀", "st'", "fuel", "n", "x", "x'", "s", "r", "h", "hI", "hμ", "hI'", "hμ'", "hs", "hu", "ih", "run",
    "hentry", "hstep", "hzero", "hfuel"]

/-- The binders of the parameters, each with a space before it: ` (lim : Nat)`. -/
private def binders (ps : List (String × String)) : String :=
  String.join (ps.map fun (n, t) => s!" ({n} : {t})")

/-- The parameters as arguments, each with a space before it: ` lim`. -/
private def args (ps : List (String × String)) : String :=
  String.join (ps.map fun (n, _) => " " ++ n)

/-- The invariant text of a quad: the conjunction of its atoms, `True` for none. -/
private def invText (q : Quad) : String :=
  if q.inv.isEmpty then "True" else " ∧ ".intercalate (q.inv.map Atom.text)

/-- The parameters of the site, or the error that names one with a reserved name. -/
private def checkParams (s : LoopSite) : Except String (List (String × String)) :=
  match s.params.find? (reserved.contains ·.1) with
  | some (n, _) => .error s!"the parameter {n} of {s.fn} has a name that the goal texts bind"
  | none => .ok s.params

/-- The lines of the file head: the imports and the opens. -/
private def head (imports opens : List String) : List String :=
  (("Skel.Discover.Goals" :: imports).eraseDups.map ("import " ++ ·)) ++
    ["set_option linter.unusedVariables false", "set_option linter.unusedSimpArgs false"] ++
    (if opens.isEmpty then [] else ["open " ++ " ".intercalate opens])

/-- The definition of the `Prop` of an obligation. -/
private def goalDef (ps : List (String × String)) (o : Goal) : String :=
  s!"def {o.goal}{binders ps} : Prop :=\n  {o.statement}"

/-- The definitions that every kind of site has: the step, the invariant and the entry. -/
private def common (s : LoopSite) (q : Quad) (ps : List (String × String)) : List String :=
  let σ := s.stateTy
  [ s!"def step := {s.step}",
    s!"def INV{binders ps} (st₀ st : {σ}) : Prop := {invText q}",
    s!"def ENTRY{binders ps} (st : {σ}) : Prop := {s.entry}" ]

/-- The fuel of the first call of a quad of the fuel-indexed form: the fuel expression of the site, or the constant of the
bound. The errors: no bound and no fuel expression, a bound by the fuel with no fuel expression. -/
private def indexedBound (s : LoopSite) (q : Quad) : Except String String :=
  match q.bound, s.fuelExpr with
  | some .fuel, some e => pure e
  | some .fuel, none => throw s!"the bound is the fuel, and {s.fn} has no fuel expression"
  | some (.const k), _ => pure (toString k)
  | none, some e => pure e
  | none, none => throw s!"{s.fn} has no fuel expression and the quad has no bound"

/-- The goal texts of a quad of the fuel-indexed form for a fueled site (see the head of this file). `call` is as for
`fueledGoals`. The errors: a site of another kind, an atom of the entry state, no fuel, a reserved parameter name. -/
def fuelIndexedGoals (s : LoopSite) (q : Quad) (call : String) (imports opens : List String) : Except String Goals := do
  unless s.kind == .fueled do throw s!"{s.fn} is not a fueled site"
  let ps ← checkParams s
  if q.inv.any (· matches .frameEq _) then throw "an atom of the entry state has no place in the fuel-indexed form"
  let bound ← indexedBound s q
  let σ := s.stateTy
  let a := args ps
  let e := q.entryForm
  -- the entry state, as a binder, a bound name and an argument
  let s0 := if e then "st₀ " else ""
  let i0 := if e then " st₀" else ""
  let i1 := if e then " st" else ""
  let obligations : List Goal :=
    [ { name := "INV_entry", goal := "INV_entry_goal",
        statement := s!"∀ (st : {σ}), ENTRY{a} st → INV{a}{i1} st (BOUND{a} st)" },
      { name := "INV_step", goal := "INV_step_goal",
        statement := s!"∀ ({s0}st st' : {σ}) (fuel : Nat), INV{a}{i0} st (fuel + 1) → step{a} st = Skel.Discover.Step.cont st' → " ++
          s!"INV{a}{i0} st' fuel" },
      { name := "INV_zero", goal := "INV_zero_goal", statement := s!"∀ ({s0}st : {σ}), ¬ INV{a}{i0} st 0" } ]
  let ends := s!"∃ s r, step{a} s = Skel.Discover.Step.exit r ∧ loop{a}"
  let header := "\n".intercalate (head imports opens ++
    [ "", s!"namespace {s.fn}", "",
      s!"def step := {s.step}",
      s!"def INV{binders ps} ({s0}st : {σ}) (fuel : Nat) : Prop := {invText q}",
      s!"def ENTRY{binders ps} (st : {σ}) : Prop := {s.entry}",
      s!"def loop{binders ps} (fuel : Nat) (st : {σ}) := {call}",
      s!"def BOUND{binders ps} (st : {σ}) : Nat := {bound}",
      "",
      "/-- One unfolding of the loop is one step, and no step is a fault. -/",
      s!"theorem unfold{binders ps} (n : Nat) (st : {σ}) :",
      s!"    Skel.Discover.Step.Unfolds (loop{a} n) (loop{a} (n + 1) st) (step{a} st) := by",
      s!"  simp only [loop, step]",
      s!"  rw [{s.fn}.eq_def]",
      s!"  try simp only [Skel.Discover.Step.bindOption, Skel.Discover.Step.bindExcept]",
      s!"  repeat' split",
      s!"  all_goals simp_all [loop, Skel.Discover.Step.Unfolds, bind, Except.bind]",
      "" ] ++
    obligations.map (goalDef ps) ++
    [ "",
      "/-- From the obligations: the loop from an entry state, at the fuel of the bound, gives the value of an exit of the",
      "step. -/",
      s!"theorem fuel_enough_of{binders ps} (hentry : INV_entry_goal{a}) (hstep : INV_step_goal{a})",
      s!"    (hzero : INV_zero_goal{a}) (st : {σ}) (h : ENTRY{a} st) :",
      s!"    {ends} (BOUND{a} st) st = r := by",
      s!"  have run : ∀ (n : Nat) (x : {σ}), INV{a}{i1} x n → {ends} n x = r := by",
      "    intro n",
      "    induction n with",
      s!"    | zero => intro x hI; exact absurd hI (hzero{i1} x)",
      "    | succ n ih =>",
      "      intro x hI",
      s!"      have hu := unfold{a} n x",
      s!"      cases hs : step{a} x with",
      "      | cont x' =>",
      "        rw [hs] at hu",
      "        rw [hu]",
      s!"        exact ih x' (hstep{i1} x x' n hI hs)",
      "      | exit r => rw [hs] at hu; exact ⟨x, r, hs, hu⟩",
      "      | fault => rw [hs] at hu; exact hu.elim",
      s!"  exact run (BOUND{a} st) st (hentry st h)",
      "",
      s!"end {s.fn}",
      "" ])
  let closing := "\n".intercalate
    [ "/-- The loop from an entry state, at the fuel of the bound, gives the value of an exit of the step. -/",
      s!"theorem fuel_enough{binders ps} (st : {σ}) (h : ENTRY{a} st) :",
      s!"    {ends} (BOUND{a} st) st = r :=",
      s!"  fuel_enough_of{a} (INV_entry{a}) (INV_step{a}) (INV_zero{a}) st h" ]
  pure { ns := s.fn, params := ps, header, obligations, closing, entry := e }

/-- The goal texts of a quad for a fueled site. `call` is the call of the function at the fuel `fuel` and the state
`st`, over the parameters (`DiscoverSiteTests.vecLoop lim fuel st`). The errors: a site of another kind, a measure that
is not one feature, a quad with no bound, a fuel bound for a site with no fuel expression, a reserved parameter name. -/
private def measureGoals (s : LoopSite) (q : Quad) (call : String) (imports opens : List String) : Except String Goals := do
  unless s.kind == .fueled do throw s!"{s.fn} is not a fueled site"
  let ps ← checkParams s
  let m ← match q.measure with
    | .one a => pure a
    | _ => throw "a fueled site needs a measure of one feature"
  let bound ← match q.bound, s.fuelExpr with
    | some .fuel, some e => pure e
    | some .fuel, none => throw s!"the bound is the fuel, and {s.fn} has no fuel expression"
    | some (.const k), _ => pure (toString k)
    | none, _ => throw "a fueled site needs a bound"
  let σ := s.stateTy
  let a := args ps
  let zeroGoal : Goal := match s.zero with
    | some _ =>
      { name := "zero_case", goal := "zero_case_goal",
        statement := s!"∀ (st₀ st : {σ}), INV{a} st₀ st → MEASURE{a} st = 0 → Skel.Discover.Step.Ends (ZERO{a} st) (step{a} st)" }
    | none =>
      { name := "zero_case", goal := "zero_case_goal",
        statement := s!"∀ (st₀ st : {σ}) (fuel : Nat), INV{a} st₀ st → MEASURE{a} st ≤ fuel → fuel ≠ 0" }
  let obligations : List Goal :=
    [ { name := "INV_entry", goal := "INV_entry_goal",
        statement := s!"∀ (st : {σ}), ENTRY{a} st → INV{a} st st ∧ MEASURE{a} st ≤ BOUND{a} st" },
      { name := "INV_step", goal := "INV_step_goal",
        statement := s!"∀ (st₀ st st' : {σ}), INV{a} st₀ st → step{a} st = Skel.Discover.Step.cont st' → " ++
          s!"INV{a} st₀ st' ∧ MEASURE{a} st' < MEASURE{a} st" },
      zeroGoal ]
  let ends := s!"∃ s r, step{a} s = Skel.Discover.Step.exit r ∧ loop{a}"
  -- the zero arm: its definition and its equation, from the unfolding equation of the function
  let zeroLines : List String := match s.zero with
    | some z =>
      [ s!"def ZERO{binders ps} (st : {σ}) := {z}",
        "",
        "/-- The loop at the fuel `0` is the zero arm of its unfolding equation. -/",
        s!"theorem zero_eq{binders ps} (st : {σ}) : loop{a} 0 st = ZERO{a} st := by",
        s!"  simp only [loop, ZERO]",
        s!"  rw [{s.fn}.eq_def]",
        s!"  try rfl",
        "" ]
    | none => []
  let header := "\n".intercalate (head imports opens ++
    [ "", s!"namespace {s.fn}", "" ] ++ common s q ps ++
    [ s!"def loop{binders ps} (fuel : Nat) (st : {σ}) := {call}",
      s!"def MEASURE{binders ps} (st : {σ}) : Nat := {m.text}",
      s!"def BOUND{binders ps} (st : {σ}) : Nat := {bound}",
      "",
      "/-- One unfolding of the loop is one step, and no step is a fault. -/",
      s!"theorem unfold{binders ps} (n : Nat) (st : {σ}) :",
      s!"    Skel.Discover.Step.Unfolds (loop{a} n) (loop{a} (n + 1) st) (step{a} st) := by",
      s!"  simp only [loop, step]",
      s!"  rw [{s.fn}.eq_def]",
      s!"  try simp only [Skel.Discover.Step.bindOption, Skel.Discover.Step.bindExcept]",
      s!"  repeat' split",
      s!"  all_goals simp_all [loop, Skel.Discover.Step.Unfolds, bind, Except.bind]",
      "" ] ++ zeroLines ++
    obligations.map (goalDef ps) ++
    (if s.zero.isSome then
    [ "",
      "/-- From the obligations, by `Skel.Discover.Step.ends_of_measure`: the loop from an entry state, with a fuel of at",
      "least the bound, gives the value of an exit of the step. -/",
      s!"theorem fuel_enough_of{binders ps} (hentry : INV_entry_goal{a}) (hstep : INV_step_goal{a})",
      s!"    (hzero : zero_case_goal{a}) (st : {σ}) (h : ENTRY{a} st) (fuel : Nat) (hfuel : BOUND{a} st ≤ fuel) :",
      s!"    {ends} fuel st = r := by",
      "  obtain ⟨hI, hμ⟩ := hentry st h",
      s!"  exact Skel.Discover.Step.ends_of_measure (loop{a}) (step{a}) (INV{a} st) (MEASURE{a}) (unfold{a})",
      s!"    (fun x x' hI hs => hstep st x x' hI hs)",
      s!"    (fun x hI hμ => by rw [zero_eq{a}]; exact hzero st x hI hμ) fuel st hI (Nat.le_trans hμ hfuel)",
      "",
      s!"end {s.fn}",
      "" ]
    else
    [ "",
      "/-- From the obligations: the loop from an entry state, with a fuel of at least the bound, gives the value of an",
      "exit of the step. -/",
      s!"theorem fuel_enough_of{binders ps} (hentry : INV_entry_goal{a}) (hstep : INV_step_goal{a})",
      s!"    (hzero : zero_case_goal{a}) (st : {σ}) (h : ENTRY{a} st) (fuel : Nat) (hfuel : BOUND{a} st ≤ fuel) :",
      s!"    {ends} fuel st = r := by",
      s!"  have run : ∀ (n : Nat) (x : {σ}), INV{a} st x → MEASURE{a} x ≤ n → {ends} n x = r := by",
      "    intro n",
      "    induction n with",
      s!"    | zero => intro x hI hμ; exact absurd rfl (hzero st x 0 hI hμ)",
      "    | succ n ih =>",
      "      intro x hI hμ",
      s!"      have hu := unfold{a} n x",
      s!"      cases hs : step{a} x with",
      "      | cont x' =>",
      "        rw [hs] at hu",
      s!"        obtain ⟨hI', hμ'⟩ := hstep st x x' hI hs",
      "        rw [hu]",
      "        exact ih x' hI' (by omega)",
      "      | exit r => rw [hs] at hu; exact ⟨x, r, hs, hu⟩",
      "      | fault => rw [hs] at hu; exact hu.elim",
      "  obtain ⟨hI, hμ⟩ := hentry st h",
      "  exact run fuel st hI (Nat.le_trans hμ hfuel)",
      "",
      s!"end {s.fn}",
      "" ]))
  let closing := "\n".intercalate
    [ "/-- The loop from an entry state, with a fuel of at least the bound, gives the value of an exit of the step. -/",
      s!"theorem fuel_enough{binders ps} (st : {σ}) (h : ENTRY{a} st) (fuel : Nat) (hfuel : BOUND{a} st ≤ fuel) :",
      s!"    {ends} fuel st = r :=",
      s!"  fuel_enough_of{a} (INV_entry{a}) (INV_step{a}) (zero_case{a}) st h fuel hfuel" ]
  pure { ns := s.fn, params := ps, header, obligations, closing, zeroArm := s.zero.isSome }

/-- The goal texts of a quad for a fueled site: the fuel-indexed form for a quad of the measure `Measure.fuel`, else the form
with the measure. -/
def fueledGoals (s : LoopSite) (q : Quad) (call : String) (imports opens : List String) : Except String Goals :=
  if q.fuelIndexed then fuelIndexedGoals s q call imports opens else measureGoals s q call imports opens

/-- The order of a measure: `<` for one feature, `Prod.Lex` for a tuple (as `termination_by` orders a tuple). -/
private def decreases (m : Measure) (lhs rhs : String) : String :=
  match m with
  | .one _ => s!"{lhs} < {rhs}"
  | .two _ _ => s!"Prod.Lex (· < ·) (· < ·) ({lhs}) ({rhs})"
  | .three _ _ _ => s!"Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) ({lhs}) ({rhs})"

/-- The type of a measure: `Nat`, or the tuple of its features. -/
private def measureTy : Measure → String
  | .one _ => "Nat"
  | .two _ _ => "Nat × Nat"
  | .three _ _ _ => "Nat × Nat × Nat"

/-- The goal texts of a quad for a `wf` site. The bound of the quad is not used. The errors: a site of another kind, a
reserved parameter name. -/
def wfGoals (s : LoopSite) (q : Quad) (imports opens : List String) : Except String Goals := do
  unless s.kind == .wf do throw s!"{s.fn} is not a wf site"
  let ps ← checkParams s
  let σ := s.stateTy
  let a := args ps
  let stepPre := s!"INV{a} st₀ st → step{a} st = Skel.Discover.Step.cont st' → "
  let obligations : List Goal :=
    [ { name := "INV_entry", goal := "INV_entry_goal", statement := s!"∀ (st : {σ}), ENTRY{a} st → INV{a} st st" },
      { name := "INV_step", goal := "INV_step_goal", statement := s!"∀ (st₀ st st' : {σ}), {stepPre}INV{a} st₀ st'" },
      { name := "decreasing", goal := "decreasing_goal",
        statement := s!"∀ (st₀ st st' : {σ}), {stepPre}" ++
          decreases q.measure s!"MEASURE{a} st'" s!"MEASURE{a} st" } ]
  let header := "\n".intercalate (head imports opens ++
    [ "", s!"namespace {s.fn}", "" ] ++ common s q ps ++
    [ s!"def MEASURE{binders ps} (st : {σ}) : {measureTy q.measure} := {q.measure.text}", "" ] ++
    obligations.map (goalDef ps) ++
    [ "", s!"end {s.fn}", "" ])
  pure { ns := s.fn, params := ps, header, obligations, closing := "" }

/-- The triple of a quad for a machine site, for `lift_loop!`: the bound is not used (`loop_vc` has no fuel). The
result is the result of the quad, else the result of the site. The errors: a site of another kind, no result. -/
def machineTriple (s : LoopSite) (q : Quad) : Except String Triple := do
  unless s.kind matches .machine _ do throw s!"{s.fn} is not a machine site"
  let some r := q.result <|> s.exitResult | throw s!"no result for the machine site {s.fn}"
  match { q with result := some r }.toTriple with
  | some t => pure t
  | none => throw s!"no result for the machine site {s.fn}"

/-- The full text: the header, then a theorem for each obligation with its proof text, in order, then the closing. A site with
parameters has the theorem `∀ params, goal params` (the statement of the proofs of D9, which start with `intro`). The error: a
number of proofs that is not the number of obligations. -/
def Goals.text (g : Goals) (proofs : List String) : Except String String := do
  unless proofs.length == g.obligations.length do
    throw s!"{g.obligations.length} obligations, {proofs.length} proofs"
  let theorems := (g.obligations.zip proofs).map fun (o, p) =>
    let statement := if g.params.isEmpty then o.goal else s!"∀{binders g.params}, {o.goal}{args g.params}"
    s!"theorem {o.name} : {statement} :=\n  {p}\n"
  pure ("\n".intercalate ([g.header, s!"namespace {g.ns}", ""] ++ theorems ++ [g.closing, "", s!"end {g.ns}", ""]))

end Skel.Discover
