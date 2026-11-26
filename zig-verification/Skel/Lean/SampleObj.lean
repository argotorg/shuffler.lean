import Skel.Lean.Sample
import Lean

/-! The samples of the L3 input of a statement by its type (task DISC-RESULT): the family `objects` of the generated
samplers (`Skel/Gen/Sampler.lean`), for an input that is no list of words and no chain of nodes, such as a structure with an
array of structures (`Vector Slot 1024`). The heap is the objects of the statement (`objsP`) of the drawn input.

* instances of `Sample` for `BitVec n` (the word of `Sample.word`, cut to `n` bits), `Bool`, `Nat` (`0` to `maxLen`),
  `Fin n`, `List α` (`0` to `maxLen` elements) and `Vector α n` (each element from its own stream);
* `#derive_sample T`: for each structure with no parameters in the type `T` (`T` itself, or `Slot` of `List Slot`), an
  instance of `Sample`, each field from its own stream; first, the same for
  each structure in the types of its fields that has no instance;
* `drawWhere ok g`: the first draw of `redraws + 1` that `ok` accepts (the admitted inputs: `run` gives a value), else the
  draw of `g`. -/

namespace Skel.Sample

open Coordinator.Dst

instance (priority := low) {n : Nat} : Sample (BitVec n) := ⟨fun g => BitVec.ofNat n (word g).toNat⟩

instance : Sample Bool := ⟨fun g => (g.natIn 0 1).1 == 1⟩

instance : Sample Nat := ⟨fun g => (g.natIn 0 maxLen).1⟩

instance {n : Nat} [NeZero n] : Sample (Fin n) := ⟨fun g => Fin.ofNat n (g.natIn 0 (n - 1)).1⟩

instance (priority := low) {α : Type} [Sample α] : Sample (List α) where
  draw g :=
    let n := ((g.stream 0).natIn 0 maxLen).1
    (List.range n).map fun k => Sample.draw (g.stream (k + 1))

instance {α : Type} {n : Nat} [Sample α] : Sample (Vector α n) := ⟨fun g => Vector.ofFn fun i => Sample.draw (g.stream i.val)⟩

/-- The first of `redraws + 1` draws that `ok` accepts, else the draw of `g`. A draw is made only when the draws before it are
not accepted: a draw of a large input (`Vector Slot 1024`) takes about 0.2 s in the interpreter (REFUTE-COV), and the draw of
each candidate before the search cost `redraws + 1` draws for each sample. -/
def drawWhere {α : Type} [Sample α] (ok : α → Bool) (g : Rng) : α :=
  match (List.range (redraws + 1)).findSome? fun i => let x : α := Sample.draw (g.stream i); if ok x then some x else none with
  | some x => x
  | none => Sample.draw g

/-- The first of `redraws + 1` draws that `ok` accepts, else none (HARNESS-LOOP2): the admitted sampler of the family `objects`
gives no admitted sample for a draw that the spec refuses, where `drawWhere` gives a draw that no entry reaches. -/
def drawWhere? {α : Type} [Sample α] (ok : α → Bool) (g : Rng) : Option α :=
  (List.range (redraws + 1)).findSome? fun i => let x : α := Sample.draw (g.stream i); if ok x then some x else none

open Lean Meta Elab Command in
/-- The structures in `e` (the head and the arguments, at each depth), the inner ones first. -/
partial def structsIn (env : Environment) (e : Expr) : List Name :=
  let inner := e.getAppArgs.toList.flatMap (structsIn env)
  match e.getAppFn.constName? with
  -- a structure with no parameters (not `BitVec n` or `Vector α n`, which have instances)
  | some c => if isStructure env c && ((env.find? c).map (·.type.isSort)).getD false then inner ++ [c] else inner
  | none => inner

open Lean Meta Elab Command in
/-- `#derive_sample T` (see the top of the file). -/
partial def deriveSample (n : Name) : CommandElabM Unit := do
  let env ← getEnv
  let has ← liftTermElabM do
    let inst ← mkAppM ``Sample #[mkConst n]
    pure (← synthInstance? inst).isSome
  if has then return
  let fields := getStructureFields env n
  let mut tys : Array Expr := #[]
  for f in fields do
    if let some p := getProjFnForField? env n f then
      if let some ci := env.find? p then
        let ty ← liftTermElabM (forallTelescope ci.type fun _ b => pure b)
        tys := tys.push ty
        for s in structsIn env ty do
          if s != n then deriveSample s
  -- a field whose type is the element type of a list or vector field is, half of the time, one of its first elements (a
  -- searched value is often in the input, as `memberOr` of the array samplers)
  let elemOf (t : Expr) : Option Expr :=
    if t.isAppOfArity ``List 1 then t.getArg! 0 else if t.isAppOfArity ``Vector 2 then t.getArg! 0 else none
  let args : Array (TSyntax `term) ← fields.mapIdxM fun i _ => do
    let own ← `((Skel.Sample.Sample.draw (g.stream $(quote i))))
    let ti := tys[i]!
    match (tys.toList.zipIdx.find? fun (t, j) => j != i && !ti.hasLooseBVars && elemOf t == some ti) with
    | some (t, j) =>
      let tStx ← liftTermElabM (PrettyPrinter.delab t)
      let list ← if t.isAppOf ``Vector then `(Vector.toList (Skel.Sample.Sample.draw (g.stream $(quote j)) : $tStx))
        else `((Skel.Sample.Sample.draw (g.stream $(quote j)) : $tStx))
      `(Skel.Sample.memberOr (g.stream $(quote (64 + i))) (List.take Skel.Sample.maxLen $list) $own)
    | none => pure own
  let cmd ← `(instance : Skel.Sample.Sample $(mkIdent n) := ⟨fun g => (⟨$args,*⟩ : $(mkIdent n))⟩)
  elabCommand cmd

open Lean Elab Command in
elab "#derive_sample " t:term : command => do
  let ty ← liftTermElabM (do let e ← Term.elabType t; instantiateMVars e)
  for s in structsIn (← getEnv) ty do
    deriveSample s

open Lean Meta Elab Command in
/-- `#derive_repr T` (HARNESS-LOOP2): for each structure with no parameters in the type `T`, the inner ones first, an instance
of `Repr` when it has none, so that the render of a counterexample shows the inputs of its run. -/
elab "#derive_repr " t:term : command => do
  let ty ← liftTermElabM (do let e ← Term.elabType t; instantiateMVars e)
  for s in (structsIn (← getEnv) ty).eraseDups do
    let has ← liftTermElabM do pure (← synthInstance? (← mkAppM ``Repr #[mkConst s])).isSome
    unless has do
      -- a structure with a field that has no `Repr` gets no instance, and no error: its render is `ShowGhost`'s default
      -- a failed deriving adds an instance with `sorry`: the environment and the messages go back to their state before it
      let before ← get
      elabCommand (← `(deriving instance Repr for $(mkIdent s)))
      if (← get).messages.hasErrors && !before.messages.hasErrors then
        modify fun st => { st with env := before.env, messages := before.messages }

/-! ## Mutations of an input (HARNESS-LOOP3)

`Mutate.mutate g d v` changes one part of `v`, drawn from `g`, with the words `d` (the operands of the branch conditions of a
run, `Skel.Refute.Guide`). A word part is set to a word of `d` (cut to its width, at a byte offset), to 0, to all ones, to a
neighbour, or to a new draw. A list changes one element, copies one element onto another, or grows or shrinks by one; a vector
changes one of its first 16 entries; a pair changes one of its parts (the parts of nested pairs have the same chance);
`#derive_mutate T` gives each structure in `T` an instance that sets its word fields from one word of `d` (the fields in order
from the low bits, as a packed record), or changes one field. -/

/-- A mutation of a value. `parts` is the number of parts of a pair (1 for other values). -/
class Mutate (α : Type) where
  parts : Nat := 1
  mutate : Rng → List UInt64 → α → α

/-- The word of `d` that `g` picks, or 0 for no word. -/
def pickWord (g : Rng) (d : List UInt64) : UInt64 := d[(g.natIn 0 (d.length - 1)).1]?.getD 0

instance (priority := low) {n : Nat} : Mutate (BitVec n) where
  mutate g d v :=
    match (g.natIn 0 5).1 with
    | 0 => BitVec.ofNat n ((pickWord (g.stream 1) d).toNat >>> (8 * ((g.stream 2).natIn 0 7).1))
    | 1 => BitVec.ofNat n (pickWord (g.stream 1) d).toNat
    | 2 => 0
    | 3 => BitVec.allOnes n
    | 4 => v + 1
    | _ => Sample.draw (g.stream 3)

instance : Mutate Bool := ⟨1, fun _ _ b => !b⟩

instance : Mutate Nat where
  mutate g d n :=
    match (g.natIn 0 3).1 with
    | 0 => (pickWord (g.stream 1) d).toNat % (maxLen + 1)
    | 1 => n + 1
    | 2 => n - 1
    | _ => Sample.draw (g.stream 3)

instance {n : Nat} [NeZero n] : Mutate (Fin n) := ⟨1, fun g _ _ => Sample.draw g⟩

instance (priority := low) {α : Type} [Sample α] [Mutate α] : Mutate (List α) where
  mutate g d xs :=
    let i := ((g.stream 1).natIn 0 (xs.length - 1)).1
    match (g.natIn 0 3).1, xs[i]? with
    | 0, some x => xs.set i (Mutate.mutate (g.stream 2) d x)
    | 1, some x => xs.set ((g.stream 3).natIn 0 (xs.length - 1)).1 x
    | 2, _ => if xs.length < maxLen then xs ++ [Sample.draw (g.stream 4)] else xs.dropLast
    | _, _ => if xs.length ≤ 1 then xs ++ [Sample.draw (g.stream 4)] else xs.dropLast

instance {α : Type} {n : Nat} [Mutate α] : Mutate (Vector α n) where
  mutate g d v :=
    let i := (g.natIn 0 (min (n - 1) 15)).1
    if h : i < n then v.set i (Mutate.mutate (g.stream 1) d v[i]) else v

instance {α β : Type} [Mutate α] [Mutate β] : Mutate (α × β) where
  parts := Mutate.parts α + Mutate.parts β
  mutate g d p :=
    if (g.natIn 0 (Mutate.parts α + Mutate.parts β - 1)).1 < Mutate.parts α then (Mutate.mutate (g.stream 1) d p.1, p.2)
    else (p.1, Mutate.mutate (g.stream 1) d p.2)

open Lean Meta Elab Command in
/-- `#derive_mutate T` (see above): the structures of `T`, the inner ones first, each once, with no instance before. -/
partial def deriveMutate (n : Name) : CommandElabM Unit := do
  let env ← getEnv
  let has ← liftTermElabM do pure (← synthInstance? (← mkAppM ``Mutate #[mkConst n])).isSome
  if has then return
  let fields := getStructureFields env n
  let mut tys : Array Expr := #[]
  for f in fields do
    if let some p := getProjFnForField? env n f then
      if let some ci := env.find? p then
        let ty ← liftTermElabM (forallTelescope ci.type fun _ b => pure b)
        tys := tys.push ty
        for s in structsIn env ty do
          if s != n then deriveMutate s
  -- the bit width of a word field (`BitVec k` with a literal `k`), else none
  let widths ← liftTermElabM <| tys.mapM fun t => do
    if t.isAppOfArity ``BitVec 1 && !t.hasLooseBVars then (evalNat (t.getArg! 0)).run else pure none
  -- the names of the instance are plain identifiers, so that the pieces and the instance agree
  let (gI, dI, vI, wI, jI) := (mkIdent `g, mkIdent `d, mkIdent `v, mkIdent `w, mkIdent `j)
  -- the fields from one word: each word field takes the next bits from the low end; the packing stops at another field
  let mut off : Option Nat := some 0
  let mut packed : Array (TSyntax `term) := #[]
  for (f, w) in fields.zip widths do
    match off, w with
    | some o, some k =>
      off := some (o + k)
      packed := packed.push (← `(BitVec.ofNat $(quote k) (UInt64.toNat $wI >>> $(quote o))))
    | _, _ =>
      off := none
      packed := packed.push (← `($(mkIdent (n ++ f)) $vI))
  let one : Array (TSyntax `term) ← fields.mapIdxM fun i f => do
    `(if $jI = $(quote i) then Skel.Sample.Mutate.mutate (Coordinator.Dst.Rng.stream $gI 2) $dI ($(mkIdent (n ++ f)) $vI)
      else $(mkIdent (n ++ f)) $vI)
  let k := fields.size
  let cmd ← `(instance : Skel.Sample.Mutate $(mkIdent n) where
    mutate := fun $gI $dI $vI =>
      if (Coordinator.Dst.Rng.natIn $gI 0 1).1 == 0 then
        let $wI := Skel.Sample.pickWord (Coordinator.Dst.Rng.stream $gI 1) $dI
        (⟨$packed,*⟩ : $(mkIdent n))
      else
        let $jI := (Coordinator.Dst.Rng.natIn (Coordinator.Dst.Rng.stream $gI 3) 0 ($(quote k) - 1)).1
        (⟨$one,*⟩ : $(mkIdent n)))
  elabCommand cmd

open Lean Elab Command in
elab "#derive_mutate " t:term : command => do
  let ty ← liftTermElabM (do let e ← Term.elabType t; instantiateMVars e)
  for s in (structsIn (← getEnv) ty).eraseDups do
    deriveMutate s

/-- The text of `reprStr v`, cut to `n` characters (a `…` marks a cut). -/
def cutRepr {α : Type} [Repr α] (n : Nat) (v : α) : String :=
  let s := reprStr v
  if s.length ≤ n then s else (s.take n).toString ++ "…"

/-- The render of a ghost input: `cutRepr` with a `Repr` instance, else `(no render)`. -/
class ShowGhost (α : Type) where
  render : Nat → α → String

instance (priority := low) {α : Type} : ShowGhost α := ⟨fun _ _ => "(no render)"⟩

instance {α : Type} [Repr α] : ShowGhost α := ⟨cutRepr⟩

/-- The render of the ghost input `v`, cut to `n` characters. -/
def showGhost {α : Type} [ShowGhost α] (n : Nat) (v : α) : String := ShowGhost.render n v

end Skel.Sample
