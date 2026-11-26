import Skel.Types
import Skel.Discover.Houdini

/-! The pure part of the Houdini rung of the invariant ladder (`docs/research/class-r-coordinator-deepseek-20261118.md`,
section 3). The grammar has two atom forms: a bound below `2^64` for each word state field, and a length bound for each
pair of a word state field and a list input. The form `∀ j < x.f, P xs[j]` is not here: `P` comes from the body `run`
of L3, and this module does not read it. Each function is pure: no IO, no call of the checker or the refuter. -/

namespace Skel.Houdini

open Skel (Verdict Cex)

/-- The kinds that the grammar uses: a 64-bit word and a list. -/
inductive Kind where
  | word
  | list
  deriving DecidableEq, Repr

/-- A name that the Lean text can use: a letter, then letters, digits or `_`. Only `parse?` makes one. -/
structure Ident where
  text : String
  deriving DecidableEq, Repr

/-- A state field or an L3 input, with its name and its kind. -/
structure Field where
  name : Ident
  kind : Kind
  deriving DecidableEq, Repr

/-- The state fields and the L3 inputs. Within each list, the names are distinct. -/
structure Fields where
  state : List Field
  inputs : List Field
  deriving DecidableEq, Repr

/-- An atom of the grammar. -/
inductive Atom where
  /-- `x.f.toNat < 2^64` -/
  | wordBelow (field : Ident)
  /-- `x.f.toNat ≤ xs.length` -/
  | countBound (field list : Ident)
  deriving DecidableEq, Repr

/-- The kind with the given name. -/
def Kind.parse? : String → Option Kind
  | "word" => some .word
  | "list" => some .list
  | _ => none

/-- The name `s` when it is a letter, then letters, digits or `_`. -/
def Ident.parse? (s : String) : Option Ident :=
  match s.toList with
  | c :: cs => if c.isAlpha && cs.all (fun d => d.isAlphanum || d == '_') then some ⟨s⟩ else none
  | [] => none

/-- A field from its name and its kind, both as text. -/
def Field.parse? (p : String × String) : Option Field := do
  let name ← Ident.parse? p.1
  let kind ← Kind.parse? p.2
  pure { name, kind }

/-- Whether a list has a repeated element. -/
def hasRepeat {α : Type} [DecidableEq α] (xs : List α) : Bool := xs.eraseDups.length != xs.length

/-- The boundary parser: the state fields and the L3 inputs, each as (name, kind) text. It refuses a bad name, an unknown
kind, and a name that repeats within its list. -/
def Fields.parse? (state inputs : List (String × String)) : Option Fields := do
  let s ← state.mapM Field.parse?
  let i ← inputs.mapM Field.parse?
  if hasRepeat (s.map (·.name)) || hasRepeat (i.map (·.name)) then none
  else pure { state := s, inputs := i }

/-- The Lean text of an atom. -/
def Atom.text : Atom → String
  | .wordBelow f => s!"x.{f.text}.toNat < 2^64"
  | .countBound f l => s!"x.{f.text}.toNat ≤ {l.text}.length"

/-- The atoms of the fields, in a fixed order: the bound below `2^64` of each word state field, then the length bound of
each word state field with each list input (the list input changes fastest). The names are distinct, so no atom repeats. -/
def atoms (f : Fields) : List Atom :=
  let words := (f.state.filter (·.kind == .word)).map (·.name)
  let lists := (f.inputs.filter (·.kind == .list)).map (·.name)
  words.map Atom.wordBelow ++ words.flatMap (fun w => lists.map (Atom.countBound w))

/-- The invariant text of a conjunction of atoms; `True` for no atom. -/
def conj : List Atom → String
  | [] => "True"
  | cs => " ∧ ".intercalate (cs.map Atom.text)

/-- The atoms whose index is not in `idx`. An index out of range has no effect, and a repeated index counts once. -/
def drop (ats : List Atom) (idx : List Nat) : List Atom :=
  ((List.range ats.length).zip ats).filter (fun p => !idx.contains p.1) |>.map Prod.snd

/-! ## The drop loop (R-C)

The refuter gives one verdict for a whole triple, and a `cti` names no atom. So the atom that a failing verdict blames is found
by leaving out one atom at a time: the triple of the conjunction `S` minus the atom `a` is refuted too. `a` is a culprit of the
counterexample `c` of `S` when `S` minus `a` passes, or fails at a later sample than `c` (the sample of `c` is then no longer a
counterexample). The loop drops all culprits and goes on with the rest. It stops with no triple when the verdict is `unknown`, when
no atom is a culprit, or when the conjunction has one atom left that fails (all atoms dropped). `True`, the empty conjunction, is
the invariant of the first template, so the loop never gives it. -/

/-- The most atoms that a Houdini run takes. The candidates of a run are the subsets of its atoms (`candidates`); the run lists
them as refute targets, so their number is bounded. -/
def maxAtoms : Nat := 8

/-- What a Houdini run reads: the atoms of the loop (at most `maxAtoms`), and the measure and the result of its triples, from
the template rule (`tails`). A loop that the template rule does not cover has no tail, so no triple. -/
structure Spec where
  atoms : List Atom
  tails : List (String × String)
  small : atoms.length ≤ maxAtoms

/-- The spec of the fields `f` and the tails, or `none` when `f` has more than `maxAtoms` atoms. -/
def Spec.make? (f : Fields) (tails : List (String × String)) : Option Spec :=
  if h : (Skel.Houdini.atoms f).length ≤ maxAtoms then some ⟨Skel.Houdini.atoms f, tails.eraseDups, h⟩ else none

/-- The next set of atoms to refute, given the verdicts known so far (`v`), or `none` when the loop ends. The loop is
`Skel.Discover.Houdini.step` over the index sets of `ats`: see there for the rules. `fuel` bounds the rounds: the atom list has at
most `fuel` atoms, and a round drops at least one. `none` for a `pass` (the loop checks that triple), an `unknown`, no atom, one
failing atom, or no culprit. -/
def next (v : List Atom → Option Verdict) (fuel : Nat) (ats : List Atom) : Option (List Atom) :=
  match Skel.Discover.Houdini.step (fun m => v (Skel.Discover.Houdini.pick ats m)) ats.length fuel
      (Skel.Discover.Houdini.Mask.full ats.length) with
  | .ask m => some (Skel.Discover.Houdini.pick ats m)
  | _ => none

/-- The triples that a run can refute: each non-empty conjunction of atoms with each tail, one for each non-empty index set of
the atoms. The run asks for the refute file of each by name, so the run lists them as refute targets. -/
def Spec.candidates (s : Spec) : List Skel.Triple :=
  ((List.range (2 ^ s.atoms.length - 1)).map (· + 1)).flatMap fun m =>
    s.tails.map fun (t, r) => { inv := conj (Skel.Discover.Houdini.pick s.atoms m), measure := t, result := r }

end Skel.Houdini
