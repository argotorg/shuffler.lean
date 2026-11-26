import Skel.Gen.UpperModel
import Skel.Source

/-! The mutants of the typed blocks of a function, for the check of a sampler (`docs/one-way-lift-g3-plan-20261118.md`,
section 5.6; task G3-15). A mutant is the summary of the function with one change in one block. Its `blocksP` text is
`blocksPText` of the same plan. The changes are made on the typed `Block`, never on the text. The five forms:
* `cond`: a comparison with one operand `+ 1` (the left one, or the right one); each comparison of a branch and of an `ite`;
* `scale`: a scaled address with scale `k → k / 2` (`k` even), `k - 1` (`k` odd, `k > 1`) or `2` (`k = 1`); each `mul _ (lit k)`
  of an access address, `k ≠ 0` (`8 → 4`, `4 → 2`, `12 → 6`);
* `disp`: a displacement `c → 0`, and `0 → 1`; each `add _ (lit c)` and `sub _ (lit c)` of an access address (`c` is any
  displacement: `0` and `2^64 - n`, a negative one, included);
* `regUpd`: a register update `± lit n → ± lit (n + 1)` (the value of a register, `add _ (lit n)` or `sub _ (lit n)` at its top);
* `storedVal`: a stored value `v → v + 1` (the value of each store).
A mutant whose `blocksP` text is the text of the original, or of an earlier mutant, after `squash`, is dropped. A mutant that the
emitter refuses is dropped and counted (`Mutants.refused`). -/

namespace Skel.Gen

/-- The forms of the mutants (5.6). -/
inductive MutForm where
  | cond | scale | disp | regUpd | storedVal
  deriving DecidableEq, Repr

/-- The forms, in the order of 5.6. -/
def MutForm.all : List MutForm := [.cond, .scale, .disp, .regUpd, .storedVal]

/-- A mutant: its form, its summary (the original with one change), and the `blocksP` text of that summary. -/
structure Mutant where
  (form : MutForm) (summary : Summary) (blocksP : String)

/-- `oneOf f xs`: the lists that replace one element `x` of `xs` by one of the elements of `f x`, in the order of `xs`. -/
def oneOf {α : Type} (f : α → List α) : List α → List (List α)
  | [] => []
  | x :: xs => (f x).map (· :: xs) ++ (oneOf f xs).map (x :: ·)

/-- The rewrites of one node: `val` gives the variants of a value node, `cond` the variants of a condition node. -/
structure Rw where
  (val : Val → List Val) (cond : Cond → List Cond)

mutual
/-- The values that differ from `v` at one node: the variants of the node `v` by `rw.val`, then those at a node below it. -/
def valSites (rw : Rw) (v : Val) : List Val :=
  rw.val v ++
    (match v with
    | .reg _ | .lit _ | .load _ | .retAddr _ => []
    | .add a b => (valSites rw a).map (fun x => Val.add x b) ++ (valSites rw b).map (fun x => Val.add a x)
    | .sub a b => (valSites rw a).map (fun x => Val.sub x b) ++ (valSites rw b).map (fun x => Val.sub a x)
    | .mul a b => (valSites rw a).map (fun x => Val.mul x b) ++ (valSites rw b).map (fun x => Val.mul a x)
    | .shr a k => (valSites rw a).map (fun x => Val.shr x k)
    | .zext32 a => (valSites rw a).map (fun x => Val.zext32 x)
    | .and a b => (valSites rw a).map (fun x => Val.and x b) ++ (valSites rw b).map (fun x => Val.and a x)
    | .or a b => (valSites rw a).map (fun x => Val.or x b) ++ (valSites rw b).map (fun x => Val.or a x)
    | .xor a b => (valSites rw a).map (fun x => Val.xor x b) ++ (valSites rw b).map (fun x => Val.xor a x)
    | .not a => (valSites rw a).map (fun x => Val.not x)
    | .neg a => (valSites rw a).map (fun x => Val.neg x)
    | .shl a k => (valSites rw a).map (fun x => Val.shl x k)
    | .extract lo len a h => (valSites rw a).map (fun x => Val.extract lo len x h)
    | .zext w a => (valSites rw a).map (fun x => Val.zext w x)
    | .sext w a => (valSites rw a).map (fun x => Val.sext w x)
    | .replaceLow w a b =>
      (valSites rw a).map (fun x => Val.replaceLow w x b) ++ (valSites rw b).map (fun x => Val.replaceLow w a x)
    | .setcc c => (condSites rw c).map (fun x => Val.setcc x)
    | .ite c a b =>
      (condSites rw c).map (fun x => Val.ite x a b) ++ (valSites rw a).map (fun x => Val.ite c x b) ++
        (valSites rw b).map (fun x => Val.ite c a x))

/-- The conditions that differ from `c` at one node, as `valSites` does for the values. -/
def condSites (rw : Rw) (c : Cond) : List Cond :=
  rw.cond c ++
    (match c with
    | .eq a b => (valSites rw a).map (fun x => Cond.eq x b) ++ (valSites rw b).map (fun x => Cond.eq a x)
    | .ule a b => (valSites rw a).map (fun x => Cond.ule x b) ++ (valSites rw b).map (fun x => Cond.ule a x)
    | .ult a b => (valSites rw a).map (fun x => Cond.ult x b) ++ (valSites rw b).map (fun x => Cond.ult a x)
    | .slt a b => (valSites rw a).map (fun x => Cond.slt x b) ++ (valSites rw b).map (fun x => Cond.slt a x)
    | .slt32 a b => (valSites rw a).map (fun x => Cond.slt32 x b) ++ (valSites rw b).map (fun x => Cond.slt32 a x)
    | .not d => (condSites rw d).map (fun x => Cond.not x)
    | .iff p q => (condSites rw p).map (fun x => Cond.iff x q) ++ (condSites rw q).map (fun x => Cond.iff p x)
    | .flag _ => [])
end

/-- `v + 1`. -/
private def plusOne (v : Val) : Val := .add v (.lit 1)

/-- The comparisons with one operand `+ 1`, the left one or the right one (form `cond`). `not` has none: its operand is a
condition of its own, which `condSites` visits. -/
private def condPlusOne : Cond → List Cond
  | .eq a b => [.eq (plusOne a) b, .eq a (plusOne b)]
  | .ule a b => [.ule (plusOne a) b, .ule a (plusOne b)]
  | .ult a b => [.ult (plusOne a) b, .ult a (plusOne b)]
  | .slt a b => [.slt (plusOne a) b, .slt a (plusOne b)]
  | .slt32 a b => [.slt32 (plusOne a) b, .slt32 a (plusOne b)]
  | .not _ | .iff _ _ | .flag _ => []

/-- The scale `k` of `x * k`, with the next smaller width step: `k / 2` for an even `k` (`8 → 4`, `4 → 2`, `2 → 1`,
`12 → 6`), `k - 1` for an odd `k > 1` (a byte stride), and `2` for `1`. No step for `0`. The result is never `k`. -/
private def scaleStep (k : UInt64) : Option UInt64 :=
  if k == 0 then none else if k == 1 then some 2 else if k % 2 == 0 then some (k / 2) else some (k - 1)

/-- The scaled address `x * k`, with the scale `scaleStep k` (form `scale`). -/
private def scaleOf : Val → List Val
  | .mul x (.lit k) => (scaleStep k).toList.map fun k' => .mul x (.lit k')
  | _ => []

/-- The displacement `c`, with `0`; the displacement `0`, with `1` (the result is never `c`). -/
private def dispStep (c : UInt64) : UInt64 := if c == 0 then 1 else 0

/-- The displacement `x + c` or `x - c`, any `c` (`0` and a negative displacement `2^64 - n` included), with the
displacement `dispStep c` (form `disp`). -/
private def dispOf : Val → List Val
  | .add x (.lit c) => [.add x (.lit (dispStep c))]
  | .sub x (.lit c) => [.sub x (.lit (dispStep c))]
  | _ => []

/-- The register update `x + n` or `x - n`, with `n + 1`, at the top of the value (form `regUpd`). -/
private def regUpdOf : Val → List Val
  | .add x (.lit n) => [.add x (.lit (n + 1))]
  | .sub x (.lit n) => [.sub x (.lit (n + 1))]
  | _ => []

/-- The stored value `v`, with `v + 1` (form `storedVal`). -/
private def storedOf (v : Val) : List Val := [plusOne v]

/-- No variant. -/
private def noVal : Val → List Val := fun _ => []

/-- No variant. -/
private def noCond : Cond → List Cond := fun _ => []

/-- The positions of a block that a form changes: an access address, a stored value, a register value, and the condition
of the branch of the term. Each is the variants of the node at that position. -/
private structure Places where
  (addr stored reg : Val → List Val) (term : Cond → List Cond)

/-- The positions of each form. The form `cond` changes any comparison, at any position. -/
private def placesOf : MutForm → Places
  | .cond =>
    let rw : Rw := ⟨noVal, condPlusOne⟩
    ⟨valSites rw, valSites rw, valSites rw, condSites rw⟩
  | .scale => ⟨valSites ⟨scaleOf, noCond⟩, noVal, noVal, noCond⟩
  | .disp => ⟨valSites ⟨dispOf, noCond⟩, noVal, noVal, noCond⟩
  | .regUpd => ⟨noVal, noVal, regUpdOf, noCond⟩
  | .storedVal => ⟨noVal, storedOf, noVal, noCond⟩

/-- The variants of an access with one change in its address or in its stored value. -/
private def accessVariants (p : Places) : Access → List Access
  | .load k a w => (p.addr a).map fun a' => Access.load k a' w
  | .store k a w v =>
    (p.addr a).map (fun a' => Access.store k a' w v) ++ (p.stored v).map fun v' => Access.store k a w v'

/-- The variants of a term with one change in its branch condition. -/
private def termVariants (p : Places) : Term → List Term
  | .exit _ => []
  | .branch c y n => (p.term c).map fun c' => Term.branch c' y n

/-- The variants of a block with one change at one of its positions. -/
private def blockVariants (p : Places) (b : Block) : List Block :=
  (oneOf (fun (rv : Reg64 × Val) => (p.reg rv.2).map fun v => (rv.1, v)) b.regs).map (fun rs => { b with regs := rs }) ++
  (oneOf (accessVariants p) b.accesses).map (fun as => { b with accesses := as }) ++
  (termVariants p b.term).map fun t => { b with term := t }

/-- The summaries that differ from `s` by one change of the form `f`. -/
private def summaryVariants (f : MutForm) (s : Summary) : List Summary :=
  (oneOf (blockVariants (placesOf f)) s.blocks).map fun bs => { s with blocks := bs }

/-- The mutants of one form: the kept ones, and the number of mutants that the emitter refused. -/
structure Mutants where
  (kept : List Mutant) (refused : Nat)

/-- The mutants whose `squash`ed text is not in `seen`, in their order; each text added to `seen` as it is kept. -/
private def keepDistinct (seen : List String) : List Mutant → List Mutant
  | [] => []
  | m :: ms =>
    let k := squash m.blocksP
    if seen.contains k then keepDistinct seen ms else m :: keepDistinct (k :: seen) ms

/-- Render with the fixed input type. A new stack argument has no field in that type. -/
def mutantBlocksPText (t : Target) (s : Summary) (p : UpperPlan) : Except GenError String := do
  for b in s.blocks do
    let depth := (s.frame.delta.lookup b.offset).getD 0
    for a in b.accesses do
      if let some k := stackArg depth a then
        if p.stackArgs ≤ k then
          throw (.unsupported b.offset s!"a stack load names stk{k}, but the fixed plan has {p.stackArgs} stack arguments")
  blocksPText t s p

/-- The mutants of the form `f` of `s`, for the target `t` and the plan `p`. The text of the original is `squash`ed into the
seen texts, so a mutant with the text of the original is dropped. A mutant that `blocksPText` refuses (a change can move an
address to a stack word that the text does not model) is dropped and counted in `refused`; the other mutants of the form stay.
An error of `blocksPText` on the original is the error of the list. -/
def mutantsOf (t : Target) (p : UpperPlan) (f : MutForm) (s : Summary) : Except GenError Mutants := do
  let orig ← mutantBlocksPText t s p
  let texts := (summaryVariants f s).map fun m => (m, mutantBlocksPText t m p)
  let ms := texts.filterMap fun (m, r) => r.toOption.map fun txt => Mutant.mk f m txt
  pure { kept := keepDistinct [squash orig] ms, refused := (texts.filter fun (_, r) => r.toOption.isNone).length }

end Skel.Gen
