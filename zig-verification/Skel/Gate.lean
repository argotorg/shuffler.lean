import Skel.Types

/-! The axiom gate of fixed decision 8 (`docs/one-way-lift-skeleton-plan-20261118.md`, section 3). Pure. -/

namespace Skel

/-- The axioms that every gate admits. -/
private def standardAxioms : List String := ["propext", "Classical.choice", "Quot.sound"]

/-- The part of the name of a `bv_decide` axiom. A name that has it followed by a dot is a `bv_decide` axiom. -/
private def bvDecidePart : String := "._native.bv_decide."

/-- The axioms that the gate `g` admits: the standard axioms for every gate, and a `bv_decide` axiom for `bvDecide`. -/
def Gate.admits (g : Gate) (axioms : List String) : Bool :=
  axioms.all fun a =>
    standardAxioms.contains a || (g == .bvDecide && (a.splitOn bvDecidePart).length > 1)

end Skel
