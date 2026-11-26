module

/-
A load through a chain of stores: `(m.storeInt a n v).loadInt x k` becomes
`some (Int.ofBytes (Int.toBytes n v))` when `x = a` and `k = n`, and `m.loadInt x k` when the blocks
`[(x, k)]` and `[(a, n)]` are disjoint; then the same for the next store of the chain. Also
`Mem.Blocks.Inside x n bs`, block by block.

The addresses are compared as linear forms: sums and differences of atoms, of literals and of
products of an atom with a literal (`b + 8#64`, `16#64 * i + b + 24#64`, `rsp - 16#64 + 8#64`).
Before that, `norm` puts each node in one spelling by definitional steps (`let` values, projections
of structure literals, and with `push`: `r.get64 .rsp` and the registers and memory of
`s.push64 v`). When `x` and `a` have the same atoms with the same coefficients, `x - a` is a
constant, and the constant decides the case (modulo `2 ^ w`, so wrap-around is included); a
reflection lemma proves it with `rfl`. An overlap that is not the same block leaves the load as it
is.

The forms:
- in `grind` by default: only the `grind` lemmas `Inside.of_stackSlots_toNat` and
  `MachineData.loadInt_push64_rsp` (the return slot that `s.push64 ra` wrote, read at its `rsp`).
  The simprocs `MemSimp.loadStore` (loads) and `MemSimp.subToNat` (`(x - a).toNat`), with `norm`
  without `push`, are declared but not in the `seval` set, and `Inside.of_toNat` has no
  `grind_pattern`: in `grind` by default they broke `kfinish` proofs that worked before (a
  regression set of accepted proofs: a store through one pointer and a load and store through
  another; `whnf` timeouts). `attribute [local seval] MemSimp.loadStore MemSimp.subToNat` is the
  opt-in, for a frame under `autoframes`;
- the tactic `mem_simp`: it substitutes the equations of the local variables of the memories and
  addresses (`t = s.push64 ra`), then the same rewrite with `push`, `Inside` decided to `True` or
  `False`, and the register reads written in the spelling of `norm`; `at h ⊢` and `at *`;
- `mem_simp [h₁, …]` (also `mem_simp []`): in addition, for addresses with different atoms, it
  proves the two side conditions of `Mem.Blocks.Disjoint.of_sub` with `bv_omega` from the facts
  `h₁, …` only, with a small heartbeat budget. When a side condition fails, that load stays; the
  tactic does not fail;
- `mem_simp` in `grind` mode, for `vcgen … with`: on the target, without substitution.

In `grind`'s preprocessing the instances of lemmas are rewritten too, and a rewritten conclusion
loses its link to the congruent term of the VC: with `push` there, or with `Inside` decided there,
`kfinish` proofs of the tests failed. So these steps are only in `mem_simp`.

Two different pointers (`rdi` and `rsi`) have different atoms: the simproc leaves such a load, and
a hypothesis `Mem.Blocks.Disjoint …` with Kraken's `grind` lemmas proves it.
-/
public import Kraken.SeparationMem
import all Kraken.SeparationMem
public import Kraken.X64.WP.Spec
public meta import Lean.Elab.Tactic
public meta import Lean.Elab.Tactic.Grind

@[expose] public section

namespace MemSimp

/-- An address: atoms (indexes into a list of terms), literals, `+`, `-`, and products with a
literal. -/
inductive Addr where
  | atom (i : Nat)
  | lit (n : Nat)
  | add (a b : Addr)
  | sub (a b : Addr)
  | mulL (k : Nat) (a : Addr)
  | mulR (a : Addr) (k : Nat)

variable {w : Nat}

def Addr.denote (ρ : List (BitVec w)) : Addr → BitVec w
  | .atom i => ρ.getD i 0
  | .lit n => BitVec.ofNat w n
  | .add a b => a.denote ρ + b.denote ρ
  | .sub a b => a.denote ρ - b.denote ρ
  | .mulL k a => BitVec.ofNat w k * a.denote ρ
  | .mulR a k => a.denote ρ * BitVec.ofNat w k

/-- The coefficient of atom `i`. -/
def Addr.coeff : Addr → Nat → Int
  | .atom j, i => if i = j then 1 else 0
  | .lit _, _ => 0
  | .add a b, i => a.coeff i + b.coeff i
  | .sub a b, i => a.coeff i - b.coeff i
  | .mulL k a, i => k * a.coeff i
  | .mulR a k, i => a.coeff i * k

/-- The constant part. -/
def Addr.const : Addr → Int
  | .atom _ => 0
  | .lit n => n
  | .add a b => a.const + b.const
  | .sub a b => a.const - b.const
  | .mulL k a => k * a.const
  | .mulR a k => a.const * k

/-- `∑ i, c i * ρ[i]`. -/
def dot (c : Nat → Int) : List (BitVec w) → BitVec w
  | [] => 0
  | x :: xs => BitVec.ofInt w (c 0) * x + dot (fun i => c (i + 1)) xs

theorem ofInt_sub (x y : Int) : BitVec.ofInt w (x - y) = BitVec.ofInt w x - BitVec.ofInt w y := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

theorem dot_zero (ρ : List (BitVec w)) : dot (fun _ => 0) ρ = 0 := by
  induction ρ with
  | nil => rfl
  | cons x xs ih => simp [dot, ih]

theorem dot_add (c d : Nat → Int) (ρ : List (BitVec w)) :
    dot (fun i => c i + d i) ρ = dot c ρ + dot d ρ := by
  induction ρ generalizing c d with
  | nil => simp [dot]
  | cons x xs ih => simp only [dot, ih, BitVec.ofInt_add]; grind

theorem dot_sub (c d : Nat → Int) (ρ : List (BitVec w)) :
    dot (fun i => c i - d i) ρ = dot c ρ - dot d ρ := by
  induction ρ generalizing c d with
  | nil => simp [dot]
  | cons x xs ih => simp only [dot, ih, ofInt_sub]; grind

theorem dot_mul (k : Int) (c : Nat → Int) (ρ : List (BitVec w)) :
    dot (fun i => k * c i) ρ = BitVec.ofInt w k * dot c ρ := by
  induction ρ generalizing c with
  | nil => simp [dot]
  | cons x xs ih => simp only [dot, ih, BitVec.ofInt_mul]; grind

theorem dot_atom (j : Nat) (ρ : List (BitVec w)) :
    dot (fun i => if i = j then 1 else 0) ρ = ρ.getD j 0 := by
  induction ρ generalizing j with
  | nil => simp [dot]
  | cons x xs ih =>
    cases j with
    | zero => simp [dot, dot_zero]
    | succ j => simp [dot, ih j]

theorem dot_congr {c d : Nat → Int} {ρ : List (BitVec w)} (h : ∀ i < ρ.length, c i = d i) :
    dot c ρ = dot d ρ := by
  induction ρ generalizing c d with
  | nil => rfl
  | cons x xs ih =>
    simp only [dot, h 0 (by simp)]
    rw [ih fun i hi => h (i + 1) (by simp; omega)]

theorem Addr.denote_eq (ρ : List (BitVec w)) (a : Addr) :
    a.denote ρ = dot a.coeff ρ + BitVec.ofInt w a.const := by
  induction a with
  | atom j => simp [denote, coeff, const, dot_atom]
  | lit n => simp [denote, coeff, const, dot_zero]
  | add a b iha ihb => simp only [denote, coeff, const, iha, ihb, dot_add, BitVec.ofInt_add]; grind
  | sub a b iha ihb => simp only [denote, coeff, const, iha, ihb, dot_sub, ofInt_sub]; grind
  | mulL k a ih =>
    simp only [denote, coeff, const, ih, dot_mul, BitVec.ofInt_mul, BitVec.ofInt_natCast]; grind
  | mulR a k ih =>
    simp only [denote, coeff, const, ih, Int.mul_comm _ (k : Int), dot_mul, BitVec.ofInt_mul,
      BitVec.ofInt_natCast]; grind

/-- The coefficients of `x` and `a` agree on the atoms of `ρ`. -/
def Addr.sameAtoms (ρ : List (BitVec w)) (x a : Addr) : Bool :=
  (List.range ρ.length).all fun i => x.coeff i == a.coeff i

theorem Addr.sub_denote {ρ : List (BitVec w)} {x a : Addr} (hc : x.sameAtoms ρ a = true) :
    x.denote ρ - a.denote ρ = BitVec.ofInt w (x.const - a.const) := by
  have h : ∀ i < ρ.length, x.coeff i = a.coeff i := fun i hi => by
    simpa [sameAtoms, hi] using List.all_eq_true.mp hc i (List.mem_range.mpr hi)
  rw [denote_eq, denote_eq, dot_congr h, ofInt_sub]
  grind

theorem Addr.sameAtoms_comm {ρ : List (BitVec w)} {x a : Addr} (hc : x.sameAtoms ρ a = true) :
    a.sameAtoms ρ x = true := by
  simp only [sameAtoms, List.all_eq_true, beq_iff_eq] at *
  exact fun i hi => (hc i hi).symm

/-- A load at `x` skips a store at `a`: `x - a` is a constant that puts the blocks apart. The
simproc gives both conditions as `rfl`. -/
theorem loadInt_storeInt_skip (m : Mem w) (ρ : List (BitVec w)) (x a : Addr) (n k : Nat) (v : Int)
    (hc : x.sameAtoms ρ a = true)
    (h : (decide (n ≤ ((x.const - a.const) % (2 ^ w : Nat)).toNat)
      && decide (k ≤ ((a.const - x.const) % (2 ^ w : Nat)).toNat)) = true) :
    (m.storeInt (a.denote ρ) n v).loadInt (x.denote ρ) k = m.loadInt (x.denote ρ) k := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine Mem.loadInt_storeInt_of_disjoint (Mem.Blocks.Disjoint.of_sub ?_ ?_) v
  · rw [Addr.sub_denote hc, BitVec.toNat_ofInt]; exact h.1
  · rw [Addr.sub_denote (Addr.sameAtoms_comm hc), BitVec.toNat_ofInt]; exact h.2

/-- A load at `x` of the bytes that a store at `a` wrote: `x - a` is `0`. -/
theorem loadInt_storeInt_same (m : Mem w) (ρ : List (BitVec w)) (x a : Addr) (n : Nat) (v : Int)
    (hc : x.sameAtoms ρ a = true)
    (h : ((x.const - a.const) % (2 ^ w : Nat) == 0 && decide (n ≤ 2 ^ w)) = true) :
    (m.storeInt (a.denote ρ) n v).loadInt (x.denote ρ) n = some (Int.ofBytes (Int.toBytes n v)) := by
  rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  have h0 : BitVec.ofInt w (x.const - a.const) = 0 :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofInt, h.1]; rfl)
  have hs := Addr.sub_denote hc
  rw [h0] at hs
  have hx : x.denote ρ = a.denote ρ := by grind
  rw [hx]
  exact Mem.loadInt_storeInt m _ n v h.2

/-- The return slot: a function body starts in `s.push64 v`, and its `ret` reads `v` at `rsp`.
After the simproc has removed the stores of the body from the chain, this is the load that is
left. Without it `grind` did not prove the return address of a body with a stack frame. -/
@[grind =] theorem _root_.MachineData.loadInt_push64_rsp (s : MachineData) (v : Int64) :
    (s.push64 v).dmem.loadInt (s.push64 v).regs.rsp.toBitVec 8
      = some (Int.ofBytes (Int.toBytes 8 v.toBitVec.toInt)) :=
  Mem.loadInt_storeInt_64 _ _ _

/-! ## `Mem.Blocks.Inside`, block by block

`Mem.Blocks.Inside` and `Mem.Block.ofStackSlots` have no exposed body, so these lemmas use their
equations, and an element `p` of the list comes with an equation `p = (a, len)`. -/

theorem ofStackSlots_eq (rsp : UInt64) (k : Nat) :
    Mem.Block.ofStackSlots rsp k = (rsp.toBitVec - BitVec.ofNat 64 (8 * (k + 1)), 8 * (k + 1)) := by
  unfold Mem.Block.ofStackSlots; rfl

/-- The access at `x` is inside the block at `a`: `x - a` is a constant that fits. -/
theorem inside_head (ρ : List (BitVec w)) (x a : Addr) (n : Nat) (p : BitVec w × Nat) (len : Nat)
    (bs : List (BitVec w × Nat)) (hc : x.sameAtoms ρ a = true)
    (h : decide (((x.const - a.const) % (2 ^ w : Nat)).toNat + n ≤ len) = true)
    (hp : p = (a.denote ρ, len)) :
    Mem.Blocks.Inside (x.denote ρ) n (p :: bs) := by
  subst hp
  simp only [Mem.Blocks.Inside]
  refine Or.inl ?_
  rw [Addr.sub_denote hc, BitVec.toNat_ofInt]
  exact of_decide_eq_true h

/-- The access at `x` is not inside the block at `a`, nor inside the later blocks. -/
theorem not_inside_cons (ρ : List (BitVec w)) (x a : Addr) (n : Nat) (p : BitVec w × Nat) (len : Nat)
    (bs : List (BitVec w × Nat)) (hc : x.sameAtoms ρ a = true)
    (h : decide (len < ((x.const - a.const) % (2 ^ w : Nat)).toNat + n) = true)
    (hp : p = (a.denote ρ, len)) (ht : ¬ Mem.Blocks.Inside (x.denote ρ) n bs) :
    ¬ Mem.Blocks.Inside (x.denote ρ) n (p :: bs) := by
  subst hp
  simp only [Mem.Blocks.Inside, not_or]
  refine ⟨?_, ht⟩
  rw [Addr.sub_denote hc, BitVec.toNat_ofInt]
  have := of_decide_eq_true h
  omega

theorem inside_tail (x : BitVec w) (n : Nat) (p : BitVec w × Nat) (bs : List (BitVec w × Nat))
    (h : Mem.Blocks.Inside x n bs) : Mem.Blocks.Inside x n (p :: bs) := by
  obtain ⟨a, len⟩ := p
  simp only [Mem.Blocks.Inside]
  exact Or.inr h

theorem not_inside_nil (x : BitVec w) (n : Nat) : ¬ Mem.Blocks.Inside x n [] := by
  simp [Mem.Blocks.Inside]

/-- For `grind`: a block contains the access when `(x - a).toNat + n ≤ len`. The simproc
`subToNat` computes `(x - a).toNat` when `x - a` is a constant. -/
theorem _root_.Mem.Blocks.Inside.of_toNat {x a : BitVec w} {n len : Nat} {bs : List (BitVec w × Nat)}
    (h : (x - a).toNat + n ≤ len) : Mem.Blocks.Inside x n ((a, len) :: bs) := by
  simp only [Mem.Blocks.Inside]
  exact Or.inl h

/-- The same for the stack slots of `Mem.Block.ofStackSlots`. -/
theorem _root_.Mem.Blocks.Inside.of_stackSlots_toNat {x : BitVec 64} {rsp : UInt64} {k n : Nat}
    {bs : List (BitVec 64 × Nat)}
    (h : (x - (rsp.toBitVec - BitVec.ofNat 64 (8 * (k + 1)))).toNat + n ≤ 8 * (k + 1)) :
    Mem.Blocks.Inside x n (Mem.Block.ofStackSlots rsp k :: bs) := by
  rw [ofStackSlots_eq]
  exact Mem.Blocks.Inside.of_toNat h

-- No `grind_pattern` for `Inside.of_toNat`: with it, `grind` timed out (`whnf`) in a proof of the
-- regression set that worked before.
grind_pattern Mem.Blocks.Inside.of_stackSlots_toNat => Mem.Blocks.Inside x n (Mem.Block.ofStackSlots rsp k :: bs)

/-- `(x - a).toNat` of two addresses that differ by a constant. -/
theorem toNat_sub_eq (ρ : List (BitVec w)) (x a : Addr) (d : Nat) (hc : x.sameAtoms ρ a = true)
    (h : (((x.const - a.const) % (2 ^ w : Nat)).toNat == d) = true) :
    (x.denote ρ - a.denote ρ).toNat = d := by
  rw [Addr.sub_denote hc, BitVec.toNat_ofInt]
  exact beq_iff_eq.mp h

/-! ## Memory loads at offsets from one base -/

theorem _root_.Mem.loadInt_storeInt_add_base {m : Mem w} {b c : BitVec w} {n k : Nat}
    (h₁ : n ≤ (-c).toNat) (h₂ : k ≤ c.toNat) (v : Int) :
    (m.storeInt (b + c) n v).loadInt b k = m.loadInt b k :=
  Mem.loadInt_storeInt_of_disjoint
    (Mem.Blocks.Disjoint.of_sub (by rwa [show b - (b + c) = -c by grind])
      (by rwa [show b + c - b = c by grind])) v

theorem _root_.Mem.loadInt_storeInt_base_add {m : Mem w} {b d : BitVec w} {n k : Nat}
    (h₁ : n ≤ d.toNat) (h₂ : k ≤ (-d).toNat) (v : Int) :
    (m.storeInt b n v).loadInt (b + d) k = m.loadInt (b + d) k :=
  Mem.loadInt_storeInt_of_disjoint
    (Mem.Blocks.Disjoint.of_sub (by rwa [show b + d - b = d by grind])
      (by rwa [show b - (b + d) = -d by grind])) v

theorem _root_.Mem.loadInt_storeInt_base_add' {m : Mem w} {b d : BitVec w} {n k : Nat}
    (h₁ : n ≤ d.toNat) (h₂ : k ≤ (-d).toNat) (v : Int) :
    (m.storeInt b n v).loadInt (d + b) k = m.loadInt (d + b) k := by
  rw [BitVec.add_comm d b]
  exact Mem.loadInt_storeInt_base_add h₁ h₂ v

theorem _root_.Mem.loadInt_storeInt_add_add' {m : Mem w} {b c d : BitVec w} {n k : Nat}
    (h₁ : n ≤ (d - c).toNat) (h₂ : k ≤ (c - d).toNat) (v : Int) :
    (m.storeInt (b + c) n v).loadInt (d + b) k = m.loadInt (d + b) k := by
  rw [BitVec.add_comm d b]
  exact Mem.loadInt_storeInt_add h₁ h₂ v

/-- Subtractions from one base (a frame below `rsp`). -/
theorem _root_.Mem.loadInt_storeInt_sub_sub {m : Mem w} {b c d : BitVec w} {n k : Nat}
    (h₁ : n ≤ (c - d).toNat) (h₂ : k ≤ (d - c).toNat) (v : Int) :
    (m.storeInt (b - c) n v).loadInt (b - d) k = m.loadInt (b - d) k :=
  Mem.loadInt_storeInt_of_disjoint
    (Mem.Blocks.Disjoint.of_sub (by rwa [show b - d - (b - c) = c - d by grind])
      (by rwa [show b - c - (b - d) = d - c by grind])) v

theorem _root_.Mem.loadInt_storeInt_sub_base {m : Mem w} {b c : BitVec w} {n k : Nat}
    (h₁ : n ≤ c.toNat) (h₂ : k ≤ (-c).toNat) (v : Int) :
    (m.storeInt (b - c) n v).loadInt b k = m.loadInt b k :=
  Mem.loadInt_storeInt_of_disjoint
    (Mem.Blocks.Disjoint.of_sub (by rwa [show b - (b - c) = c by grind])
      (by rwa [show b - c - b = -c by grind])) v

theorem _root_.Mem.loadInt_storeInt_base_sub {m : Mem w} {b d : BitVec w} {n k : Nat}
    (h₁ : n ≤ (-d).toNat) (h₂ : k ≤ d.toNat) (v : Int) :
    (m.storeInt b n v).loadInt (b - d) k = m.loadInt (b - d) k :=
  Mem.loadInt_storeInt_of_disjoint
    (Mem.Blocks.Disjoint.of_sub (by rwa [show b - d - b = -d by grind])
      (by rwa [show b - (b - d) = d by grind])) v

grind_pattern Mem.loadInt_storeInt_sub_sub => Mem.loadInt (Mem.storeInt m (b - c) n v) (b - d) k
grind_pattern Mem.loadInt_storeInt_sub_base => Mem.loadInt (Mem.storeInt m (b - c) n v) b k
grind_pattern Mem.loadInt_storeInt_base_sub => Mem.loadInt (Mem.storeInt m b n v) (b - d) k
grind_pattern Mem.loadInt_storeInt_add_base => Mem.loadInt (Mem.storeInt m (b + c) n v) b k
grind_pattern Mem.loadInt_storeInt_base_add => Mem.loadInt (Mem.storeInt m b n v) (b + d) k
grind_pattern Mem.loadInt_storeInt_base_add' => Mem.loadInt (Mem.storeInt m b n v) (d + b) k
grind_pattern Mem.loadInt_storeInt_add_add' => Mem.loadInt (Mem.storeInt m (b + c) n v) (d + b) k

/-! ## The simproc -/

open Lean Meta Elab

/-- The linear form of an address: the coefficient of each atom, and the constant. -/
meta structure Lin where
  coeffs : Array Int := #[]
  const : Int := 0

meta def Lin.coeff (l : Lin) (i : Nat) : Int := l.coeffs.getD i 0

meta def Lin.zipWith (f : Int → Int → Int) (a b : Lin) : Lin :=
  { coeffs := (Array.range (max a.coeffs.size b.coeffs.size)).map fun i => f (a.coeff i) (b.coeff i)
    const := f a.const b.const }

meta def Lin.scale (k : Int) (a : Lin) : Lin :=
  { coeffs := a.coeffs.map (k * ·), const := k * a.const }

/-- The literal value of `e : BitVec w`; `BitVec.ofNat w (8 * (2 + 1))` counts as a literal. -/
meta def bvLit? (w : Nat) (e : Expr) : MetaM (Option Nat) := do
  if let some ⟨w', v⟩ ← getBitVecValue? e then
    return if w' == w then some v.toNat else none
  let_expr BitVec.ofNat w' n := e | return none
  let some w' ← (evalNat w').run | return none
  let some n ← (evalNat n).run | return none
  return if w' == w then some (n % 2 ^ w) else none

/-- The head of `e` in one spelling, by definitional steps only (so that the proofs need no
rewrite): a `let` variable is its value; `r.get64 .rsp` is `r.rsp.toBitVec`; a projection of a
structure literal is the field (`{ toBitVec := e }.toBitVec` is `e`); the `regs` and `dmem` of
`s.push64 v` are those of `MachineData.regs_push64` and `MachineData.dmem_push64`; a register of
`r.set64 .rsp e` is `UInt64.ofBitVec e` for `rsp` and the register of `r` for the others. -/
meta partial def norm (push : Bool) (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  if let .fvar fv := e then
    if let some val ← fv.getValue? then return ← norm push val
  if push && e.isAppOfArity ``Reg64s.get64 2 then
    if let .const c _ := e.appArg! then
      let f := ``Reg64s ++ .mkSimple c.getString!
      if (← getProjectionFnInfo? f).isSome then
        return ← norm push (mkApp (mkConst ``UInt64.toBitVec) (mkApp (mkConst f) e.appFn!.appArg!))
  let .const fn lvls := e.getAppFn | return e
  let some info ← getProjectionFnInfo? fn | return e
  let args := e.getAppArgs
  unless args.size == info.numParams + 1 do return e
  let s ← norm push args[info.numParams]!
  let ctor ← getConstInfoCtor info.ctorName
  if s.isAppOfArity info.ctorName (ctor.numParams + ctor.numFields) then
    return ← norm push (s.getArg! (ctor.numParams + info.i))
  if push && s.isAppOfArity ``MachineData.push64 2 && (fn == ``MachineData.regs || fn == ``MachineData.dmem) then
    let lemma := if fn == ``MachineData.regs then ``MachineData.regs_push64 else ``MachineData.dmem_push64
    let some (_, _, rhs) := (← inferType (mkAppN (mkConst lemma) s.getAppArgs)).eq? | return e
    return ← norm push rhs
  if s.isAppOfArity ``Reg64s.set64 3 then
    if let .const c _ := s.getArg! 1 then
      if c.getString! == fn.getString! then
        return mkApp (mkConst ``UInt64.ofBitVec) (s.getArg! 2)
      return ← norm push (mkApp (mkConst fn lvls) (s.getArg! 0))
  return mkAppN (mkConst fn lvls) (args.set! info.numParams s)

/-- `e : BitVec w` as an `Addr` over the atoms of the state, with its linear form. Each node is
first put in the spelling of `norm`; atoms are then compared syntactically. -/
meta partial def reify (push : Bool) (w : Nat) (ty e : Expr) : StateT (Array Expr) MetaM (Expr × Lin) := do
  let e ← norm push e
  if let some n ← bvLit? w e then
    return (mkApp (mkConst ``Addr.lit) (mkNatLit n), { const := n })
  match_expr e with
  | HAdd.hAdd α β γ _ a b => if ← isHom α β γ then binop ``Addr.add (· + ·) a b else atom e
  | HSub.hSub α β γ _ a b => if ← isHom α β γ then binop ``Addr.sub (· - ·) a b else atom e
  | HMul.hMul α β γ _ a b =>
    if !(← isHom α β γ) then atom e
    else if let some k ← bvLit? w a then
      let (eb, lb) ← reify push w ty b
      return (mkApp2 (mkConst ``Addr.mulL) (mkNatLit k) eb, lb.scale k)
    else if let some k ← bvLit? w b then
      let (ea, la) ← reify push w ty a
      return (mkApp2 (mkConst ``Addr.mulR) ea (mkNatLit k), la.scale k)
    else atom e
  | _ => atom e
where
  isHom (α β γ : Expr) : MetaM Bool := withReducible do
    return (← isDefEq α ty) && (← isDefEq β ty) && (← isDefEq γ ty)
  binop (c : Name) (f : Int → Int → Int) (a b : Expr) : StateT (Array Expr) MetaM (Expr × Lin) := do
    let (ea, la) ← reify push w ty a
    let (eb, lb) ← reify push w ty b
    return (mkApp2 (mkConst c) ea eb, la.zipWith f lb)
  atom (e : Expr) : StateT (Array Expr) MetaM (Expr × Lin) := do
    let atoms ← get
    let i ← match atoms.findIdx? (· == e) with
      | some i => pure i
      | none => do set (atoms.push e); pure atoms.size
    return (mkApp (mkConst ``Addr.atom) (mkNatLit i), { coeffs := (Array.replicate i 0).push 1 })

/-- The heartbeat budget (in thousands) of one `bv_omega` attempt of `mem_simp [facts]`. -/
meta def factBudget : Nat := 4000

/-- A proof of `goal` by `bv_omega` with only the facts in its context, within `factBudget`; `none`
when it fails or runs out of heartbeats. -/
meta def proveByFacts (facts : Array Expr) (goal : Expr) : MetaM (Option Expr) := do
  let s ← saveState
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context ({ · with maxHeartbeats := factBudget * 1000 }) do
      let g ← mkFreshExprMVar goal
      let mut mv := g.mvarId!
      let mut keep := #[]
      for f in facts do
        let (fv, mv') ← (← mv.assert `h (← inferType f) f).intro1P
        mv := mv'
        keep := keep.push fv
      mv ← mv.withContext do mv.tryClearMany ((← getLCtx).getFVarIds.filter (!keep.contains ·))
      -- Without recovery a failure is an exception: no error message and no `sorry` in the proof.
      let rest ← Term.TermElabM.run' <| Term.withoutErrToSorry do
        Tactic.run mv (Tactic.withoutRecover (Tactic.evalTactic (← `(tactic| bv_omega))))
      unless rest.isEmpty do throwError "mem_simp: bv_omega left goals"
      return some (← instantiateMVars g))
    fun _ => do s.restore; return none

/-- `@Eq.refl Bool true`, the proof of a side condition that the kernel evaluates. -/
meta def eqTrue : Expr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)

/-- One step: `(m.storeInt a n v).loadInt x k` to `some …` or to `m.loadInt x k`. With `some facts`,
addresses with different atoms are tried with `bv_omega` from the facts. -/
meta def step (push : Bool) (facts : Option (Array Expr)) : Simp.Simproc := fun e => do
  let_expr Mem.loadInt w mem x k := e | return .continue
  let_expr Mem.storeInt _ m a n v := (← norm push mem) | return .continue
  if x.hasLooseBVars || a.hasLooseBVars then return .continue
  let some wv ← getNatValue? (← instantiateMVars w) | return .continue
  let some kv ← getNatValue? (← instantiateMVars k) | return .continue
  let some nv ← getNatValue? (← instantiateMVars n) | return .continue
  let ty := mkApp (mkConst ``BitVec) w
  let ((ex, lx), atoms) ← (reify push wv ty x).run #[]
  let ((ea, la), atoms) ← (reify push wv ty a).run atoms
  let skipped := mkApp4 (mkConst ``Mem.loadInt) w m x k
  if (List.range atoms.size).all fun i => lx.coeff i == la.coeff i then
    let ρ ← mkListLit ty atoms.toList
    let d := ((lx.const - la.const) % (2 ^ wv : Nat)).toNat
    let d' := ((la.const - lx.const) % (2 ^ wv : Nat)).toNat
    if d == 0 && kv == nv && nv ≤ 2 ^ wv then
      let p := mkAppN (mkConst ``loadInt_storeInt_same) #[w, m, ρ, ex, ea, n, v, eqTrue, eqTrue]
      let some (_, _, rhs) := (← inferType p).eq? | return .continue
      return .visit { expr := rhs, proof? := some (← mkExpectedTypeHint p (← mkEq e rhs)) }
    else if nv ≤ d && kv ≤ d' then
      let p := mkAppN (mkConst ``loadInt_storeInt_skip) #[w, m, ρ, ex, ea, n, k, v, eqTrue, eqTrue]
      return .visit { expr := skipped, proof? := some (← mkExpectedTypeHint p (← mkEq e skipped)) }
    else
      return .continue
  else if let some facts := facts then
    -- `omega` takes a `let` variable as an atom: the side conditions get the values.
    let x' ← zetaReduce x
    let a' ← zetaReduce a
    let some h₁ ← proveByFacts facts (← mkAppM ``LE.le #[n, ← mkAppM ``BitVec.toNat #[← mkAppM ``HSub.hSub #[x', a']]])
      | return .continue
    let some h₂ ← proveByFacts facts (← mkAppM ``LE.le #[k, ← mkAppM ``BitVec.toNat #[← mkAppM ``HSub.hSub #[a', x']]])
      | return .continue
    let hd := mkAppN (mkConst ``Mem.Blocks.Disjoint.of_sub) #[w, x', a', k, n, h₁, h₂]
    let p := mkAppN (mkConst ``Mem.loadInt_storeInt_of_disjoint) #[w, m, a', x', n, k, hd, v]
    return .visit { expr := skipped, proof? := some (← mkExpectedTypeHint p (← mkEq e skipped)) }
  else
    return .continue

/-- A load through a store, for `mem_simp` (see the module doc). Not in `grind`'s preprocessing (the
`seval` set): there it broke `kfinish` proofs that worked before (all five CallDepth-like proofs of
a regression set of accepted proofs, a store through `(%rdi)` and a load and store at `(%rsi)`). -/
simproc_decl loadStore (Mem.loadInt _ _ _) := step false none

/-- An element of the list of `Mem.Blocks.Inside x n bs`: the element `p` as written, the rest of
the list, and when `p` is a pair `(a, len)` with a literal `len` (also `Mem.Block.ofStackSlots rsp
k`, by `ofStackSlots_eq`): the `Addr` of `a`, its linear form, `len` and a proof of
`p = (a, len)`. -/
meta structure Block where
  pair : Expr
  rest : Expr
  addr? : Option (Expr × Lin × Expr × Nat × Expr)

/-- The elements of the list `bs`, and whether it ends in `[]`. -/
meta partial def blocks (push : Bool) (w : Nat) (ty bs : Expr) : StateT (Array Expr) MetaM (Array Block × Bool) := do
  let bs ← norm push bs
  if bs.isAppOfArity ``List.nil 1 then return (#[], true)
  let_expr List.cons _ p rest := bs | return (#[], false)
  let (p', hp) ← if p.isAppOfArity ``Mem.Block.ofStackSlots 2 then do
      let hp := mkAppN (mkConst ``ofStackSlots_eq) p.getAppArgs
      let some (_, _, rhs) := (← inferType hp).eq? | pure (p, ← mkEqRefl p)
      pure (rhs, hp)
    else do pure (← norm push p, ← mkEqRefl p)
  let addr? ← match_expr p' with
    | Prod.mk _ _ a len => do
      match ← (evalNat len).run with
      | some l => let (ea, la) ← reify push w ty a; pure (some (ea, la, len, l, hp))
      | none => pure none
    | _ => pure none
  let (bs', nil) ← blocks push w ty rest
  return (#[{ pair := p, rest, addr? }] ++ bs', nil)

/-- A proof of `Inside x n bs` for a suffix `bs` of the list, of its negation, or neither. -/
meta inductive Dec where
  | yes (p : Expr)
  | no (p : Expr)
  | unknown

/-- `Mem.Blocks.Inside x n bs` to `True` when a block of `bs` contains the access by a constant
difference (the blocks before it may be undecided), to `False` when each block is decided not to
contain it and the list ends in `[]`. Else it stays. -/
meta def insideStep (push : Bool) : Simp.Simproc := fun e => do
  let_expr Mem.Blocks.Inside w x n bs := e | return .continue
  if x.hasLooseBVars || bs.hasLooseBVars then return .continue
  let some wv ← getNatValue? (← instantiateMVars w) | return .continue
  let some nv ← (evalNat n).run | return .continue
  let ty := mkApp (mkConst ``BitVec) w
  let (((ex, lx), bls, nil), atoms) ← (do
    let xl ← reify push wv ty x
    let (bls, nil) ← blocks push wv ty bs
    return (xl, bls, nil)).run #[]
  let ρ ← mkListLit ty atoms.toList
  let inside? (b : Block) : Option Bool := b.addr?.bind fun (_, la, _, len, _) =>
    if (List.range atoms.size).all fun i => lx.coeff i == la.coeff i then
      some (((lx.const - la.const) % (2 ^ wv : Nat)).toNat + nv ≤ len)
    else none
  let init : Dec := if nil then .no (mkApp3 (mkConst ``not_inside_nil) w x n) else .unknown
  let d := bls.foldr (init := init) fun b acc =>
    match inside? b, b.addr?, acc with
    | some true, some (ea, _, len, _, hp), _ =>
      .yes (mkAppN (mkConst ``inside_head) #[w, ρ, ex, ea, n, b.pair, len, b.rest, eqTrue, eqTrue, hp])
    | _, _, .yes p => .yes (mkAppN (mkConst ``inside_tail) #[w, x, n, b.pair, b.rest, p])
    | some false, some (ea, _, len, _, hp), .no p =>
      .no (mkAppN (mkConst ``not_inside_cons) #[w, ρ, ex, ea, n, b.pair, len, b.rest, eqTrue, eqTrue, hp, p])
    | _, _, _ => .unknown
  match d with
  | .yes p => return .done { expr := mkConst ``True, proof? := some (← mkEqTrue (← mkExpectedTypeHint p e)) }
  | .no p => return .done { expr := mkConst ``False, proof? := some (← mkEqFalse (← mkExpectedTypeHint p (mkNot e))) }
  | .unknown => return .continue

/-- `Mem.Blocks.Inside` with constant differences, in `mem_simp`. (Not in `grind`'s preprocessing:
there a decided `Inside` in the conclusion of a lemma instance lost the link to the congruent term
of the VC, and a `kfinish` proof of a mapped load failed. `grind` gets `subToNat` and the lemmas
`Inside.of_toNat` and `Inside.of_stackSlots_toNat` instead.) -/
simproc_decl insideDecide (Mem.Blocks.Inside _ _ _) := insideStep true

/-- `(x - a).toNat` to a literal when `x - a` is a constant, for `grind`'s preprocessing. -/
meta def subToNatStep : Simp.Simproc := fun e => do
  let_expr BitVec.toNat w d := e | return .continue
  let_expr HSub.hSub _ _ _ _ x a := d.consumeMData | return .continue
  if x.hasLooseBVars || a.hasLooseBVars then return .continue
  let some wv ← getNatValue? (← instantiateMVars w) | return .continue
  let ty := mkApp (mkConst ``BitVec) w
  let (((ex, lx), (ea, la)), atoms) ← (do return (← reify false wv ty x, ← reify false wv ty a)).run #[]
  unless (List.range atoms.size).all fun i => lx.coeff i == la.coeff i do return .continue
  let δ := ((lx.const - la.const) % (2 ^ wv : Nat)).toNat
  let ρ ← mkListLit ty atoms.toList
  let p := mkAppN (mkConst ``toNat_sub_eq) #[w, ρ, ex, ea, mkNatLit δ, eqTrue, eqTrue]
  return .done { expr := mkNatLit δ, proof? := some (← mkExpectedTypeHint p (← mkEq e (mkNatLit δ))) }

-- Not in `seval` by default: with it, `grind` timed out (`whnf`) in a proof of the regression set.
simproc_decl subToNat (BitVec.toNat (_ - _)) := subToNatStep

/-- In `mem_simp`: a register read in the spelling of `norm true`, by definitional steps
(`(s.push64 v).regs.rsp` to `UInt64.ofBitVec (s.regs.get64 .rsp - 8#64)`, `r.get64 .rsp` to
`r.rsp.toBitVec`), so that the instances of `kfinish`'s lemmas get the terms of `s`. -/
meta def spellStep : Simp.Simproc := fun e => do
  let .const fn _ := e.getAppFn | return .continue
  let reg ← if fn == ``Reg64s.get64 then pure (e.getAppNumArgs == 2) else do
    let some info ← getProjectionFnInfo? fn | return .continue
    pure (info.ctorName == ``Reg64s.mk && e.getAppNumArgs == 1)
  unless reg do return .continue
  let e' ← norm true e
  return if e' == e then .continue else .visit { expr := e' }

/-- `step facts` and `insideStep` on the hypotheses `fvarIds` and (with `target`) the target of
`g`, with the projections of structure literals reduced (`{ dmem := t, … }.dmem` to `t`) and `a = a`
closed. `none` when the goal is closed. -/
meta def memSimpGoal (facts : Option (Array Expr)) (g : MVarId) (fvarIds : Array FVarId := #[])
    (target := true) : MetaM (Option MVarId) := g.withContext do
  let some lk ← Simp.getSimprocDeclKeys? ``loadStore | throwError "mem_simp: no keys for loadStore"
  let some ik ← Simp.getSimprocDeclKeys? ``insideDecide | throwError "mem_simp: no keys for insideDecide"
  let procs := (Simp.Simprocs.addCore {} lk `MemSimp.memSimpFacts true (.inl (step true facts))).addCore
    ik ``insideDecide true (.inl (insideStep true)) |>.addCore #[.star] `MemSimp.spell true (.inl spellStep)
  let thms ← ({} : SimpTheorems).addConst ``eq_self
  let ctx ← Simp.mkContext (config := { failIfUnchanged := false }) (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  return (← simpGoal g ctx #[procs] (simplifyTarget := target) (fvarIdsToSimp := fvarIds)).1.map (·.2)

/-- The memories, addresses and block lists of the loads, stores and `Inside` terms in `e`. -/
meta partial def memArgs (e : Expr) : Array Expr :=
  let here := match_expr e with
    | Mem.loadInt _ m x _ => #[m, x]
    | Mem.storeInt _ m a _ _ => #[m, a]
    | Mem.Blocks.Inside _ x _ bs => #[x, bs]
    | _ => #[]
  here ++ match e with
    | .app f a => memArgs f ++ memArgs a
    | .lam _ t b _ | .forallE _ t b _ => memArgs t ++ memArgs b
    | .letE _ t v b _ => memArgs t ++ memArgs v ++ memArgs b
    | .mdata _ b | .proj _ _ b => memArgs b
    | _ => #[]

/-- Substitutes, as `subst` does, an equation `x = e` or `e = x` for each local variable `x` that
occurs in the memories and addresses of `es g` (the terms that `mem_simp` rewrites). -/
meta partial def substVars (g : MVarId) (es : MVarId → MetaM (Array Expr)) : MetaM MVarId := do
  let fvs := ((← es g).foldl (fun s e => (memArgs e).foldl collectFVars s) {}).fvarIds
  for fv in fvs do
    if let some g' ← substVar? g fv then return ← substVars g' es
  return g

/-- The facts of `mem_simp [h₁, …]`, elaborated in the context of `g`; `none` without a list. -/
meta def elabFacts (g : MVarId) (hs : Option (Array Syntax)) : TermElabM (Option (Array Expr)) :=
  g.withContext do hs.mapM (·.mapM fun h => do instantiateMVars (← Term.elabTerm h none))

/-- The hypotheses named in `loc`, in the context of `g` (all of them for `at *`). -/
meta def locHyps (loc : Tactic.Location) (g : MVarId) : MetaM (Array FVarId) := g.withContext do
  match loc with
  | .wildcard => g.getNondepPropHyps
  | .targets hyps _ => hyps.mapM fun h => return (← getLocalDeclFromUserName h.getId).fvarId

/-- `mem_simp`: rewrites each load through a chain of stores, and decides `Mem.Blocks.Inside` with
constant differences, in the goal (see the module doc). First it substitutes the equations
`x = e` and `e = x` of the local variables `x` of the memories and addresses there, as `subst`
does (a VC with `t = s.push64 ra`). `mem_simp [h₁, …]` (also `mem_simp []`): in addition, for
addresses with different atoms (`b + 4#64` against `8#64 * i + b + 8#64`), it proves the side
conditions `n ≤ (x - a).toNat` and `k ≤ (a - x).toNat` by `bv_omega` from the facts only; a load
whose side conditions fail stays. `at h ⊢` and `at *` as for `simp`. It does not fail when nothing
changes. -/
syntax (name := memSimp) "mem_simp" (" [" term,* "]")? (Lean.Parser.Tactic.location)? : tactic

@[tactic memSimp] meta def evalMemSimp : Tactic.Tactic := fun stx => Tactic.withMainContext do
  let `(tactic| mem_simp $[[$hs,*]]? $[$loc?]?) := stx | throwUnsupportedSyntax
  let loc := match loc? with
    | some l => Tactic.expandLocation l
    | none => .targets #[] true
  let target := match loc with
    | .wildcard => true
    | .targets _ t => t
  let es (g : MVarId) : MetaM (Array Expr) := g.withContext do
    let hyps ← (← observing? (locHyps loc g)).getDM (pure #[])
    let tys ← hyps.mapM fun h => do instantiateMVars (← h.getType)
    let t ← instantiateMVars (← g.getType)
    return if target then tys.push t else tys
  let g ← substVars (← Tactic.getMainGoal) es
  let facts ← elabFacts g (hs.map (·.getElems.map (·.raw)))
  Tactic.replaceMainGoal (← memSimpGoal facts g (← locHyps loc g) target).toList

/-- `mem_simp [h₁, …]` in `grind` mode, for the `with` clause of `vcgen`:
`vcgen [prog] with (mem_simp [hwrap]; kfinish)`. On the target only, and without the
substitution of equations. -/
syntax (name := memSimpGrind) "mem_simp" (" [" term,* "]")? : grind

@[grind_tactic memSimpGrind] meta def evalMemSimpGrind : Tactic.Grind.GrindTactic := fun stx => do
  let `(grind| mem_simp $[[$hs,*]]?) := stx | throwUnsupportedSyntax
  let goal ← Tactic.Grind.getMainGoal
  let facts ← elabFacts goal.mvarId (hs.map (·.getElems.map (·.raw)))
  match ← memSimpGoal facts goal.mvarId with
  | none => Tactic.Grind.replaceMainGoal []
  | some mvarId => Tactic.Grind.replaceMainGoal [{ goal with mvarId }]

/-! ## General memory lemmas -/

/-- A store maps its own block, also where the memory had no bytes before (Kraken's
`Mem.Mapped.storeInt` keeps a mapping that exists). -/
theorem _root_.Mem.Mapped.storeInt_self {m : Mem w} {a : BitVec w} {n : Nat} (v : Int)
    (hw : n ≤ 2 ^ w) : Mem.Mapped [(a, n)] (m.storeInt a n v) := by
  intro b hb
  have hi : (b - a).toNat < n := by
    obtain h | h := hb
    · omega
    · exact (not_inside_nil _ _ h).elim
  rw [Mem.storeInt, Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.union_eq,
    Std.ExtHashMap.getElem?_union, get?_At _ _ _ (by rw [Int.toBytes_length]; exact hw)]
  rw [BitVec.toNat_sub] at hi
  simp [Int.toBytes_length]
  exact Or.inl hi

/-- Disjointness both ways. -/
theorem _root_.Mem.Blocks.Disjoint.symm {bs bs' : List (BitVec w × Nat)}
    (h : Mem.Blocks.Disjoint bs bs') : Mem.Blocks.Disjoint bs' bs :=
  fun b h' hb => h b hb h'

end MemSimp
