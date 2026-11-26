import Lean
import Coordinator.Dst.Rng

/-! The random states of the invariant discovery, derived from the type of the state (task SAMPLE-DERIVE).

The search of D9 and the traces of D3 need a sampler `Rng → σ` of the loop state. A hand-written sampler was wrong twice
in the held-out run D15a (every trace timed out; then every run ended at its first step). This module derives the sampler
from the type, and derives its printer and parser with it.

* `Draw σ` is the class of the samplers: `Draw.draw bounds rng : σ`. The instances cover `Nat`, `Int`, `Bool`, `BitVec n`,
  `UInt8` to `UInt64`, `Fin n`, `Option`, `List`, `Array`, `Vector` and `Prod`. The handler `deriving Draw` makes the
  instance of a structure (each field has its own stream of the generator) and of an inductive type that is not recursive
  (an enum, or a type whose constructors have fields).
* `Bounds` sets the sizes and the ranges: the largest `Nat`, the largest word, the share of the extreme words, the longest
  list, the number of elements of a `Vector` that are drawn, the share of `none`, and the number of tries of a filter.
  A `Vector` of `n` elements has `min n active` drawn elements. The others are the quiet value of the element type (`0`,
  `false`, `none`, the empty list, the first constructor), so a vector of 1024 slots costs the same as a vector of `active`.
* The printer and the parser are `ToJson` and `FromJson`. Core has them for `Nat`, `Int`, `Bool`, `UInt64`, `Option`, `List`
  and `Array`; this module adds `BitVec n`, `UInt8`, `UInt16`, `UInt32`, `Fin n` and `Vector α n` (a number, or an array;
  a value that does not fit the type is an error). The printed state is the state of the stored counterexamples (`StateJson`
  of `Site.lean`), and the stored state is read back by the trace decoder.
* `derive_state T` derives `Draw`, `ToJson`, `FromJson` and `Repr` for `T` and for each type that its fields use and that is
  not in core, innermost first. A class that a type has already is not derived again. A type that the module defines needs
  no `deriving` line, and a type of a library needs no change.
* `drawRuns` draws the states of the runs of a seed and filters them with the entry condition of the loop: a run tries at most
  `tries` candidates, and a run with no candidate that passes is skipped. `Stats` counts what the filter did; its line starts
  with `#`, so a trace parser skips it. -/

namespace Skel.Discover.Rand

open Lean Coordinator.Dst

universe u

/-! ## The bounds -/

/-- The sizes and the ranges of a draw. `natMax`: a `Nat` is from `0` to `natMax` (a `Fin n` is below `n` and at most `natMax`).
`wordMax`: a `BitVec`, `UIntN` is from `0` to `wordMax` (cut to the type). `edgePercent`: the share in percent of a word that is
`2^n - 1` or `2^n - 2`. `maxLen`: a `List` or `Array` has at most this many elements. `active`: a `Vector` has this many drawn
elements, the others are quiet. `nonePercent`: the share in percent of `none`. `tries`: the candidates of one filtered draw.
`calm`: every draw gives the quiet value (the first constructor, `0`, `false`). -/
structure Bounds where
  natMax : Nat := 7
  wordMax : Nat := 7
  edgePercent : Nat := 0
  maxLen : Nat := 4
  active : Nat := 4
  nonePercent : Nat := 25
  tries : Nat := 20
  calm : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- The bounds of a quiet value: every size and range is zero, and an `Option` is `none`. -/
def Bounds.quiet (b : Bounds) : Bounds :=
  { b with natMax := 0, wordMax := 0, edgePercent := 0, maxLen := 0, nonePercent := 100, calm := true }

/-- The bounds as a Lean term of the type `Bounds`, for a generated file. -/
def Bounds.text (b : Bounds) : String :=
  s!"(\{ natMax := {b.natMax}, wordMax := {b.wordMax}, edgePercent := {b.edgePercent}, maxLen := {b.maxLen}, " ++
    s!"active := {b.active}, nonePercent := {b.nonePercent}, tries := {b.tries}, calm := {b.calm} } : " ++
    "Skel.Discover.Rand.Bounds)"

/-! ## The class and its instances -/

/-- The sampler of a type: a value from the bounds and a generator. The same generator gives the same value. -/
class Draw (α : Type u) where
  draw : Bounds → Rng → α

/-- A number from `0` to `hi`. -/
def natUpTo (g : Rng) (hi : Nat) : Nat := (g.natIn 0 hi).1

instance : Draw Nat := ⟨fun b g => natUpTo g b.natMax⟩

instance : Draw Int :=
  ⟨fun b g => if b.calm then 0 else Int.ofNat (natUpTo g (2 * b.natMax)) - Int.ofNat b.natMax⟩

instance : Draw Bool := ⟨fun b g => if b.calm then false else g.bool.1⟩

/-- A word of `bits` bits as a number: from `0` to `wordMax`, and with the chance `edgePercent` the top value or the one before. -/
def wordNat (bits : Nat) (b : Bounds) (g : Rng) : Nat :=
  let top := 2 ^ bits - 1
  if natUpTo (g.stream 1) 99 < b.edgePercent then top - natUpTo (g.stream 2) (min 1 top)
  else natUpTo g (min b.wordMax top)

instance {n : Nat} : Draw (BitVec n) := ⟨fun b g => BitVec.ofNat n (wordNat n b g)⟩
instance : Draw UInt8 := ⟨fun b g => UInt8.ofNat (wordNat 8 b g)⟩
instance : Draw UInt16 := ⟨fun b g => UInt16.ofNat (wordNat 16 b g)⟩
instance : Draw UInt32 := ⟨fun b g => UInt32.ofNat (wordNat 32 b g)⟩
instance : Draw UInt64 := ⟨fun b g => UInt64.ofNat (wordNat 64 b g)⟩

instance {n : Nat} [NeZero n] : Draw (Fin n) := ⟨fun b g => Fin.ofNat n (natUpTo g (min b.natMax (n - 1)))⟩

instance {α : Type u} [Draw α] : Draw (Option α) :=
  ⟨fun b g => if natUpTo (g.stream 0) 99 < b.nonePercent then none else some (Draw.draw b (g.stream 1))⟩

instance {α : Type u} [Draw α] : Draw (List α) :=
  ⟨fun b g => (List.range (natUpTo (g.stream 0) b.maxLen)).map fun k => Draw.draw b (g.stream (k + 1))⟩

instance {α : Type u} [Draw α] : Draw (Array α) := ⟨fun b g => (Draw.draw b g : List α).toArray⟩

instance {α : Type u} {n : Nat} [Draw α] : Draw (Vector α n) :=
  ⟨fun b g =>
    let quiet := Draw.draw b.quiet (Rng.ofSeed 0)
    (List.range (min n b.active)).foldl
      (fun v i => if h : i < n then v.set i (Draw.draw b (g.stream i)) h else v) (Vector.replicate n quiet)⟩

instance {α : Type u} {β : Type u} [Draw α] [Draw β] : Draw (α × β) :=
  ⟨fun b g => (Draw.draw b (g.stream 0), Draw.draw b (g.stream 1))⟩

/-! ## The printer and the parser -/

private def natOfJson (what : String) (bound : Nat) (j : Json) : Except String Nat := do
  let n ← fromJson? (α := Nat) j
  if n < bound then pure n else throw s!"{what}: {n} is not below {bound}"

instance {n : Nat} : ToJson (BitVec n) := ⟨fun x => toJson x.toNat⟩
instance {n : Nat} : FromJson (BitVec n) := ⟨fun j => (BitVec.ofNat n) <$> natOfJson s!"BitVec {n}" (2 ^ n) j⟩
instance : ToJson UInt8 := ⟨fun x => toJson x.toNat⟩
instance : FromJson UInt8 := ⟨fun j => UInt8.ofNat <$> natOfJson "UInt8" (2 ^ 8) j⟩
instance : ToJson UInt16 := ⟨fun x => toJson x.toNat⟩
instance : FromJson UInt16 := ⟨fun j => UInt16.ofNat <$> natOfJson "UInt16" (2 ^ 16) j⟩
instance : ToJson UInt32 := ⟨fun x => toJson x.toNat⟩
instance : FromJson UInt32 := ⟨fun j => UInt32.ofNat <$> natOfJson "UInt32" (2 ^ 32) j⟩
instance {n : Nat} : ToJson (Fin n) := ⟨fun x => toJson x.val⟩
instance {n : Nat} [NeZero n] : FromJson (Fin n) := ⟨fun j => (Fin.ofNat n) <$> natOfJson s!"Fin {n}" n j⟩

instance {α : Type u} {n : Nat} [ToJson α] : ToJson (Vector α n) := ⟨fun v => toJson v.toArray⟩
instance {α : Type u} {n : Nat} [FromJson α] : FromJson (Vector α n) :=
  ⟨fun j => do
    let a ← fromJson? (α := Array α) j
    if h : a.size = n then pure ⟨a, h⟩ else throw s!"Vector {n}: the array has {a.size} elements"⟩

/-! ## The deriving handler -/

open Elab Command Term Meta Parser.Term Deriving

/-- The body of the sampler of a structure: each field is drawn from the stream of its position. -/
private def mkStructBody (b g : Ident) (indName : Name) : TermElabM Term := do
  let fields := getStructureFieldsFlattened (← getEnv) indName (includeSubobjectFields := false)
  let vals ← fields.mapIdxM fun i _ => `(Draw.draw $b (Rng.stream $g $(quote i)))
  let names := fields.map mkIdent
  `({ $[$names:ident := $vals],* })

/-- The body of the sampler of an inductive type: the constructor from the generator (the first when the bounds are calm), then
the fields of the constructor, each from the stream of its position. -/
private def mkInductBody (b g : Ident) (indVal : InductiveVal) : TermElabM Term := do
  let k := mkIdent `drawCtor
  let n := indVal.ctors.length
  let mut alts : Array (TSyntax ``matchAlt) := #[]
  for (c, i) in indVal.ctors.zipIdx do
    let ctor ← getConstInfoCtor c
    let args ← (List.range ctor.numFields).toArray.mapM fun j => `(Draw.draw $b (Rng.stream $g $(quote (j + 1))))
    let rhs ← `($(mkIdent c):ident $args*)
    alts := alts.push (← if i + 1 == n then `(matchAltExpr| | _ => $rhs) else `(matchAltExpr| | $(quote i):num => $rhs))
  `(let $k := if Bounds.calm $b then 0 else (Rng.natIn $g 0 $(quote (n - 1))).1
    match $k:ident with $alts:matchAlt*)

private def mkDrawInstance (declName : Name) : TermElabM (Array Command) := do
  let indVal ← getConstInfoInduct declName
  if indVal.isRec || indVal.all.length > 1 || indVal.numIndices > 0 then
    throwError "deriving Draw: {declName} is recursive, mutual or indexed"
  let ctx ← mkContext ``Draw "draw" declName
  let header ← mkHeader ``Draw 0 indVal
  let b := mkIdent `drawBounds
  let g := mkIdent `drawRng
  let binders := header.binders ++ #[← `(bracketedBinderF| ($b : Bounds)), ← `(bracketedBinderF| ($g : Rng))]
  let body ← if isStructure (← getEnv) declName then mkStructBody b g declName else mkInductBody b g indVal
  let aux ← `(def $(mkIdent ctx.auxFunNames[0]!):ident $binders:bracketedBinder* : $header.targetType := $body:term)
  return #[aux] ++ (← mkInstanceCmds ctx ``Draw #[declName])

private def mkDrawHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) && declNames.size > 0 then
    for declName in declNames do
      (← liftTermElabM <| mkDrawInstance declName).forM elabCommand
    return true
  else
    return false

initialize registerDerivingHandler ``Draw mkDrawHandler

/-! ## `derive_state` -/

/-- Whether the constant comes from core (`Init`, `Std`, `Lean`, `Lake`): the library has the instances of these types. -/
private def fromCore (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some i => (env.header.moduleNames[i.toNat]!.getRoot) ∈ [`Init, `Std, `Lean, `Lake]
  | none => false

/-- The inductive types that the fields of `c` use and that are not in core: the constants of the types of the constructors. -/
private def fieldTypes (c : Name) : MetaM (List Name) := do
  let env ← getEnv
  let some (.inductInfo v) := env.find? c | return []
  let mut out : List Name := []
  for k in v.ctors do
    let some info := env.find? k | continue
    for d in info.type.getUsedConstants do
      if d != c && !fromCore env d && (env.find? d).any (·.isInductive) && !out.contains d then out := out ++ [d]
  return out

/-- The depth-first order of the types of `c`: the visited types, and the types innermost first. -/
private partial def stateGo (st : List Name × List Name) (c : Name) : MetaM (List Name × List Name) := do
  let (visited, out) := st
  if visited.contains c then return st
  let (visited, out) ← (← fieldTypes c).foldlM stateGo (c :: visited, out)
  return (visited, out ++ [c])

/-- The types that `c` needs, innermost first, and `c` last. -/
private def stateOrder (c : Name) : MetaM (List Name) := do
  return (← stateGo ([], []) c).2

/-- Whether `cls` has an instance for the type `t`. A type with no parameters is asked by instance search. A type with parameters
has an instance when the instance of the name that `deriving` gives exists. -/
private def hasInstance (cls t : Name) : TermElabM Bool := do
  let env ← getEnv
  let some (.inductInfo v) := env.find? t | return true
  if v.numParams > 0 then return env.contains (← Lean.Elab.Deriving.mkInstName cls t)
  let ty := Lean.mkConst t (v.levelParams.map fun _ => Level.zero)
  try pure (← synthInstance? (← mkAppM cls #[ty])).isSome catch _ => pure false

/-- `derive_state T ...`: the instances `Draw`, `ToJson`, `FromJson` and `Repr` of each type, and of the types that its fields
use (not core types), where they do not exist. -/
elab "derive_state " ids:ident+ : command => do
  for id in ids do
    let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let order ← liftTermElabM (stateOrder c)
    for t in order do
      for cls in [``Draw, ``ToJson, ``FromJson, ``Repr] do
        unless ← liftTermElabM (hasInstance cls t) do
          let tid := mkIdent (`_root_ ++ t)
          elabCommand (← `(deriving instance $(mkIdent (`_root_ ++ cls)):ident for $tid:ident))

/-! ## The filtered draws and their counts -/

/-- What the filter did over the runs: the runs, the candidates drawn, the candidates that the filter rejected, and the runs
that had no candidate that passes. -/
structure Stats where
  runs : Nat
  drawn : Nat
  rejected : Nat
  skipped : Nat
  deriving DecidableEq, Repr

/-- The share of the rejected candidates in percent (`0` when there is no candidate). -/
def Stats.percent (s : Stats) : Nat := if s.drawn = 0 then 0 else 100 * s.rejected / s.drawn

/-- The line of the counts. It starts with `#`: a trace parser skips it. -/
def Stats.line (s : Stats) : String :=
  s!"# draws runs={s.runs} drawn={s.drawn} rejected={s.rejected} skipped={s.skipped}\n"

/-- The counts of a line of `Stats.line`, or none. -/
def Stats.ofLine? (l : String) : Option Stats :=
  match l.trimAscii.toString.splitOn " " with
  | ["#", "draws", a, b, c, d] =>
    let num (p k : String) : Option Nat := if k.startsWith p then (k.drop p.length).toString.toNat? else none
    match num "runs=" a, num "drawn=" b, num "rejected=" c, num "skipped=" d with
    | some runs, some drawn, some rejected, some skipped => some { runs, drawn, rejected, skipped }
    | _, _, _, _ => none
  | _ => none

/-- The note of the counts: the share of the candidates that the filter rejected. -/
def Stats.note (s : Stats) : String :=
  s!"sampler: {s.drawn} draws for {s.runs} runs, the entry condition rejected {s.rejected} ({s.percent} %), {s.skipped} runs skipped"

/-- The state of the run `i` of the seed `seed`: the first candidate of the streams `0 .. tries - 1` that the filter `ok`
accepts, and the number of candidates that it rejected. A run with no accepted candidate has no state. -/
def drawOne {σ : Type u} [Draw σ] (b : Bounds) (ok : σ → Bool) (root : Rng) : Option σ × Nat :=
  let rec go (j : Nat) : Nat → Option σ × Nat
    | 0 => (none, j)
    | fuel + 1 =>
      let x : σ := Draw.draw b (root.stream j)
      if ok x then (some x, j) else go (j + 1) fuel
  go 0 (max 1 b.tries)

/-- The candidates drawn and the candidates rejected by one filtered draw. -/
private def counted {σ : Type u} (x : Option σ × Nat) : Nat × Nat := (x.2 + (if x.1.isSome then 1 else 0), x.2)

/-- The counts with one filtered draw added. -/
private def Stats.add {σ : Type u} (st : Stats) (x : Option σ × Nat) : Stats :=
  { st with drawn := st.drawn + (counted x).1, rejected := st.rejected + (counted x).2 }

/-- The states of the runs `0 .. runs - 1` of the seed `seed`, each with its index, and the counts of the filter. -/
def drawRuns {σ : Type u} [Draw σ] (b : Bounds) (ok : σ → Bool) (seed runs : Nat) : List (Nat × σ) × Stats :=
  let (xs, st) := (List.range runs).foldl
    (fun (acc : List (Nat × σ) × Stats) i =>
      let d := drawOne b ok ((Rng.ofSeed seed).stream i)
      match d.1 with
      | some x => ((i, x) :: acc.1, acc.2.add d)
      | none => (acc.1, { acc.2.add d with skipped := acc.2.skipped + 1 }))
    ([], { runs, drawn := 0, rejected := 0, skipped := 0 })
  (xs.reverse, st)

/-- The search for a state that falsifies a test: for the samples `0 .. samples - 1` of the seed, the entry state `st₀` (a state
that `ok₀` accepts), the state `st` (one that `ok` accepts) and the fuel from `0` to `fuelMax`, until `bad st₀ st fuel` is
true. The result is the index, the states and the fuel of the first sample with `bad`, and the counts of the filters. A sample
for which a filter accepts no candidate is skipped. -/
def findHit {σ : Type u} [Draw σ] (b : Bounds) (ok₀ ok : σ → Bool) (bad : σ → σ → Nat → Bool) (seed samples fuelMax : Nat) :
    Option (Nat × σ × σ × Nat) × Stats :=
  let root := Rng.ofSeed seed
  let rec go (i : Nat) (left : Nat) (st : Stats) : Option (Nat × σ × σ × Nat) × Stats :=
    match left with
    | 0 => (none, st)
    | left + 1 =>
      let r := root.stream i
      let a := drawOne b ok₀ (r.stream 0)
      let c := drawOne b ok (r.stream 1)
      let st := (st.add a).add c
      match a.1, c.1 with
      | some x₀, some x =>
        let fuel := ((r.stream 2).natIn 0 fuelMax).1
        if bad x₀ x fuel then (some (i, x₀, x, fuel), st) else go (i + 1) left st
      | _, _ => go (i + 1) left { st with skipped := st.skipped + 1 }
  go 0 samples { runs := samples, drawn := 0, rejected := 0, skipped := 0 }

end Skel.Discover.Rand
