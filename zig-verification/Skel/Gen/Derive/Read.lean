import Skel.Gen.Derive.Walk
import Skel.Gen.Types

/-! The reader from the terms of a walk to the values and conditions of the generator (tasks N7 and N10 of
`docs/research/symexec-pilot-20261118.md`, section 5; decisions D41 and D43 of the plan).

`readVal` reads an expression of a walk (`Walk.lean`) as a `Val`: the registers of the start state, the load values of
the walk (`Val.load k`, numbered in the order of the loads), the literals of `UInt64`, `BitVec w` (cut to `w` bits) and
`Width.bytesv`, the operations `+`, `-`, `*`, `&&&`, `|||`, `^^^`, `~~~`, `-x`, `<<<` and `>>>` by a literal, `setWidth`,
`extractLsb'`, `signExtend` from 8, 16 or 32 bits (`Val.sext`), `replaceLow` of 8 or 16 bits, `ite` (a `cmov`), and the `setcc` byte `BitVec.ofNat w b.toNat`. The
wrappers `UInt64.ofBitVec` (also the structure form `{ toBitVec := v }`, the same constructor), `UInt64.toBitVec`,
`Int64.ofBitVec` and `Int64.toBitVec` are removed. Any other head is the error `unsupported`, which names it.

A term of `BitVec w` with `w < 64` is read as its zero extension to 64 bits: a load of `w` bits is `load k` (as the
model has it), an operation at `w` bits that can set higher bits (`+`, `-`, `*`, `~~~`, `-x`, `<<<`) gets `lowBits w`.
The low bits have one normal form (`lowBits`): `zext .b8 a`, `zext .b16 a`, `zext32 a` (the form of the table
`Sym.lean`), else `extract 0 w a`. The reader does not give `zext .b32`, nor `extract 0 w` for `w` = 8, 16 or 32.

`readCond` reads a condition (a `Prop`) and `readBool` a `Bool` condition. Each raw form is the left side of one lemma
of `Lift/Tactic/Cond.lean`, and its `Cond` is the right side of that lemma: the reader applies the lemma, it does not run
`simp`. The order follows the open points of the lemmas: the conjunction and disjunction forms read their parts first and
then combine them (`nocarry_and_ne_iff_lt`, `nocarry_lit_and_ne_iff_lt`, `not_nocarry_or_zero_iff_le`), the `setcc`
xor (`setcc_xor_iff`) comes before the general narrow equation (`extract8_zero_iff`, `byte_zero_iff`), and the literal
borrow forms give the literal `k` from the numerals of the term. The signed branches of `cmpq` (`jl`, `jge`, `jg`, `jle`, `setl`, `cmovl`, ...) are `slt` (`readSigned`, `conj`, `disj`;
the lemmas `msb_sub_eq_of_iff_not_slt` and the others of `Cond.lean`); the signed branches of `cmpb`, `cmpw`, `cmpl` are
`slt` of the sign extensions (8 and 16 bits) and `slt32` (`readSignedN`, `msbn_sub_eq_of_iff_not_slt`). An operand of a
literal borrow form may be shifted by a literal (`readIntOp`), and the sum of `nocarry32_lit_iff_le` may have a `notl` term
(`readSum32`, `natCast_sub_mod_eq`). A condition form that no lemma covers is the error
`unsupported`. The flag `f` of the block start (`d.status.f`) is the flag input `Cond.flag f` (decision D43).

`readAddr` reads an access address as base + Σ index · scale + displacement (each part optional, each scale a literal), in
the form of `address` of `Sym.lean` for a base and at most one index. `readWalk` reads the registers, the accesses and the exit of a walk, with the
condition of a branch. `Val.norm` and `Cond.norm` are the normal forms for the comparison with the table. -/

open Lean

namespace Skel.Gen.Derive

/-! ## Errors and the context -/

/-- Why an expression is not a `Val` or a `Cond`. -/
inductive ReadError where
  /-- A head with no `Val` or `Cond` form: its constant (or `lambda`, `literal`, `bvar`, `other` for a head that is not
  a constant). An equation of `Int` that is no borrow form is `Int`; a conjunction or a disjunction that is no `ja` or
  `jbe` form is `And` or `Or`. -/
  | unsupported (head : Name)
  /-- A free variable that is not a load value of the walk: the start state alone, a memory, an undefined value. -/
  | freeVar (name : Name)
  /-- A shift by 64 or more. -/
  | shift (k : Nat)
  /-- An exit target before the start of the function. -/
  | outside (pc : Nat)
  deriving Repr, BEq, Inhabited

/-- The free variables of a walk: the start state, and the load values with their widths, in the order of the loads. -/
structure ReadCtx where
  start : FVarId
  loads : Array (FVarId × Width)

/-- The context of the walk `w`. -/
def ReadCtx.ofWalk (w : Walk) : ReadCtx :=
  { start := w.start, loads := w.accesses.filterMap fun | .load _ wd _ v => some (v, wd) | .store .. => none }

/-- The number of bits of the load `k` (64 for a number that is no load). -/
def ReadCtx.loadBits (cx : ReadCtx) (k : Nat) : Nat := (cx.loads[k]?.map (·.2.bits)).getD 64

/-! ## Literals -/

private def bytesOf? (e : Expr) : Option Nat :=
  if e.isConstOf ``Width.W8 then some 1
  else if e.isConstOf ``Width.W16 then some 2
  else if e.isConstOf ``Width.W32 then some 4
  else if e.isConstOf ``Width.W64 then some 8
  else none

/-- A numeral of `Nat`: a literal, or `Width.bits w` of a width literal. -/
private def natOf? (e : Expr) : Option Nat :=
  e.nat? <|> e.rawNatLit? <|>
    if e.isAppOfArity ``Width.bits 1 then (bytesOf? (e.getArg! 0)).map (8 * ·) else none

/-- The number of bits of a value type: 64 for `UInt64` and `Int64`, `n` for `BitVec n` and `w.bits` for
`Width.type w`. -/
private def typeBits? (ty : Expr) : Option Nat :=
  let ty := ty.consumeMData
  if ty.isConstOf ``UInt64 || ty.isConstOf ``Int64 then some 64
  else if ty.isAppOfArity ``BitVec 1 then natOf? (ty.getArg! 0)
  else if ty.isAppOfArity ``Width.type 1 then (bytesOf? (ty.getArg! 0)).map (8 * ·)
  else none

/-- The value of a literal: `OfNat.ofNat` of `UInt64`, `BitVec w`, `Width.type w` or `Nat`, `BitVec.ofNat w n`, `UInt64.ofNat n`,
`Width.bytesv w` and a raw literal. A literal of `BitVec w` is cut to `w` bits. -/
def lit? (e : Expr) : Option Nat :=
  if e.isAppOfArity ``OfNat.ofNat 3 then do
    -- the numeral is a raw literal, or a numeral of `Nat` (a literal that `normLits` leaves)
    let n ← natOf? (e.getArg! 1)
    let ty := e.getArg! 0
    if ty.isConstOf ``Nat then pure n else pure (n % 2 ^ (← typeBits? ty))
  else if e.isAppOfArity ``BitVec.ofNat 2 then do
    pure ((← natOf? (e.getArg! 1)) % 2 ^ (← natOf? (e.getArg! 0)))
  else if e.isAppOfArity ``UInt64.ofNat 1 then do
    pure ((← natOf? (e.getArg! 0)) % 2 ^ 64)
  else if e.isAppOfArity ``Width.bytesv 2 then bytesOf? (e.getArg! 0)
  else e.rawNatLit?

/-- A literal of `Int` that is not negative. -/
private def intLit? (e : Expr) : Option Int :=
  let e := e.consumeMData
  if e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 0).isConstOf ``Int then (e.getArg! 1).rawNatLit?.map Int.ofNat
  else none

/-- The two operands of a binary operation `f` (`HAdd.hAdd` and the others: 6 arguments). -/
private def binop? (f : Name) (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity f 6 then some (e.getArg! 4, e.getArg! 5) else none

/-- `b` of `Bool.toNat b`. -/
private def boolToNat? (e : Expr) : Option Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``Bool.toNat 1 then some (e.getArg! 0) else none

/-- `x` of the cast `↑x : Int` of a `Nat`. -/
private def natCast? (e : Expr) : Option Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``Nat.cast 3 then some (e.getArg! 2)
  else if e.isAppOfArity ``Int.ofNat 1 then some (e.getArg! 0)
  else none

/-! ## The low bits -/

/-- The low `bits` bits of `v`, zero-extended to 64 bits, in the normal form of the reader: `zext .b8`, `zext .b16`,
`zext32`, else `extract 0 bits`. A literal is cut. A value that has no bit at `bits` or above is itself: a `setcc`, a
narrower zero extension or extraction, a load of at most `bits` bits (`loadBits`). The low bits of a wider zero extension
of `x` (or extraction from bit 0), and of `replaceLow w a x` for `bits ≤ w`, are the low bits of `x`. -/
def lowBits (loadBits : Nat → Nat) (bits : Nat) (v : Val) : Val :=
  if bits ≥ 64 then v
  else match v with
    | .lit n => .lit (UInt64.ofNat (n.toNat % 2 ^ bits))
    | .setcc _ => if bits ≥ 1 then v else mk
    | .load k => if loadBits k ≤ bits then v else mk
    | .zext32 x => if 32 ≤ bits then v else lowBits loadBits bits x
    | .zext w x => if w.bits ≤ bits then v else lowBits loadBits bits x
    | .extract lo len x _ => if len ≤ bits then v else if lo == 0 then lowBits loadBits bits x else mk
    | .replaceLow w _ b => if bits ≤ w.bits then lowBits loadBits bits b else mk
    | _ => mk
where
  mk : Val :=
    if bits == 8 then .zext .b8 v else if bits == 16 then .zext .b16 v else if bits == 32 then .zext32 v
    else if h : bits ≤ 64 then .extract 0 bits v (by omega) else v

/-! ## Values and conditions -/

private def headName (e : Expr) : Name :=
  match e.getAppFn with
  | .const n _ => n
  | .fvar _ => `fvar
  | .lam .. => `lambda
  | .lit _ => `literal
  | .bvar _ => `bvar
  | _ => `other

/-- The register of the projection `Reg64s.r`. -/
private def regOfProj? (n : Name) : Option Reg64 := allRegs.find? (regProj · == n)

/-- The flag of the projection `StatusFlags.f`. -/
private def flagOfProj? (n : Name) : Option Flag := Flag.all.find? (·.proj == n)

/-- The `Bool` conditions `p`, `q` of the `setcc` bytes of `xorb ; je` (the left side of `setcc_xor_iff`):
`extractLsb' 0 8 (a.replaceLow (BitVec.ofNat 8 p.toNat))`. -/
private def setccByte? (e : Expr) : Option Expr := do
  let e := e.consumeMData
  guard (e.isAppOfArity ``BitVec.extractLsb' 4 && natOf? (e.getArg! 1) == some 0 && natOf? (e.getArg! 2) == some 8)
  let x := (e.getArg! 3).consumeMData
  guard (x.isAppOfArity ``BitVec.replaceLow 4 && natOf? (x.getArg! 0) == some 64 && natOf? (x.getArg! 1) == some 8)
  let y := (x.getArg! 3).consumeMData
  guard (y.isAppOfArity ``BitVec.ofNat 2 && natOf? (y.getArg! 0) == some 8)
  boolToNat? (y.getArg! 1)

/-- `a`, `b` of `(a ^^^ b) <<< 16` at 64 bits (the left side of `shlxor_zero_iff_and`). -/
private def shlXor16? (e : Expr) : Option (Expr × Expr) := do
  let (x, k) ← binop? ``HShiftLeft.hShiftLeft e
  guard (typeBits? (e.consumeMData.getArg! 0) == some 64 && lit? k.consumeMData == some 16)
  binop? ``HXor.hXor x

/-- The mask of the low 48 bits. -/
private def mask48 : Val := .lit 281474976710655

mutual
/-- A text of the value, for the reports, the checks of the reader and the key of the normal form. -/
def _root_.Skel.Gen.Val.show : Val → String
  | .reg r => s!"{repr r}"
  | .lit n => s!"{n}"
  | .load k => s!"load{k}"
  | .retAddr o => s!"retAddr{o}"
  | .add a b => s!"({a.show} + {b.show})"
  | .sub a b => s!"({a.show} - {b.show})"
  | .mul a b => s!"({a.show} * {b.show})"
  | .shr a k => s!"({a.show} >>> {k})"
  | .zext32 a => s!"zext32 {a.show}"
  | .ite c a b => s!"(if {c.show} then {a.show} else {b.show})"
  | .and a b => s!"({a.show} &&& {b.show})"
  | .or a b => s!"({a.show} ||| {b.show})"
  | .xor a b => s!"({a.show} ^^^ {b.show})"
  | .not a => s!"(~~~{a.show})"
  | .neg a => s!"(-{a.show})"
  | .shl a k => s!"({a.show} <<< {k})"
  | .extract lo len a _ => s!"(extract {lo} {len} {a.show})"
  | .zext w a => s!"(zext{w.bits} {a.show})"
  | .sext w a => s!"(sext{w.bits} {a.show})"
  | .replaceLow w a b => s!"(replaceLow{w.bits} {a.show} {b.show})"
  | .setcc c => s!"(setcc {c.show})"

/-- A text of the condition. -/
def _root_.Skel.Gen.Cond.show : Cond → String
  | .eq a b => s!"({a.show} = {b.show})"
  | .ule a b => s!"({a.show} ≤ {b.show})"
  | .ult a b => s!"({a.show} < {b.show})"
  | .slt a b => s!"({a.show} <s {b.show})"
  | .slt32 a b => s!"({a.show} <s32 {b.show})"
  | .not c => s!"¬{c.show}"
  | .iff p q => s!"({p.show} ↔ {q.show})"
  | .flag f => s!"flag {f.name}"
end

/-- The two pairs are the same values, in this order or swapped (the text of the values). -/
def samePair (p q : Val × Val) : Bool :=
  (p.1.show == q.1.show && p.2.show == q.2.show) || (p.1.show == q.2.show && p.2.show == q.1.show)

/-- The condition without its double negations (`!!p` of the `Bool` forms). -/
def dropNotNot : Cond → Cond
  | .not (.not c) => dropNotNot c
  | c => c

/-- The signed `<` of `w` bits below 64 (`readSigned`): the operands, `w`, and the constructor of the condition:
`slt (sext w a) (sext w b)` for 8 and 16 bits, `slt32 a b` for 32 bits. -/
def narrowSlt? : Cond → Option (Val × Val × Nat × (Val → Val → Cond))
  | .slt (.sext w a) (.sext w' b) => if w == w' then some (a, b, w.bits, fun p q => .slt (.sext w p) (.sext w q)) else none
  | .slt32 a b => some (a, b, 32, .slt32)
  | _ => none

/-- The equation `c = d` is the equation of the operands of the signed `<` `s`: of the 64-bit values, or of their low `w`
bits for a signed `<` of `w` bits (`low w`, the low bits of the reader). The swapped signed `<` (`b < a`), or `none`. -/
def swapSlt (low : Nat → Val → Val) (c d : Val) (s : Cond) : Option Cond :=
  match s with
  | .slt a b =>
    if samePair (c, d) (a, b) then some (.slt b a)
    else match narrowSlt? s with
      | some (a, b, w, mk) => if samePair (c, d) (low w a, low w b) then some (mk b a) else none
      | none => none
  | _ => match narrowSlt? s with
    | some (a, b, w, mk) => if samePair (c, d) (low w a, low w b) then some (mk b a) else none
    | none => none

/-- A flag of the block start or its negation (L2-FLAGS). A conjunction or a disjunction of two of them (`seta` of the flags
of a compare in an earlier block, `!cf && !zf`) has no pattern: it is the equation of the bytes of their `setcc`
(`p ∧ q` is `setcc p &&& setcc q = 1`, `p ∨ q` is `¬ (setcc p ||| setcc q = 0)`). -/
def flagLit : Cond → Bool
  | .flag _ | .not (.flag _) => true
  | _ => false

/-- The value `a` of the zero test `a = 0` (or `0 = a`). -/
def zeroTest? : Cond → Option Val
  | .eq a (.lit 0) | .eq (.lit 0) a => some a
  | _ => none

/-- `ja`: no borrow and not zero, `a ≤ b ∧ ¬ b = a`, is `a < b` (`nocarry_and_ne_iff_lt`, `nocarry_lit_and_ne_iff_lt`,
`nocarryn_and_ne_iff_lt`, `nocarryn_lit_and_ne_iff_lt`). `jg`: not zero and the flags of the signed compare agree,
`¬ a = b ∧ ¬ a <s b`, is `b <s a` (`ne_and_msb_sub_eq_of_iff_slt`, `ne_and_msb_sub_lit_eq_of_iff_slt`, and for `w` bits
`ne_and_msbn_sub_eq_of_iff_slt`; `swapSlt`). Two zero tests (READER, D1: the zero flag of `orb` of two `setcc` bytes,
`orq` after `notq`), `a = 0 ∧ b = 0`, are `a ||| b = 0`. Another conjunction is the error `unsupported n`. -/
def conj (n : Name) (low : Nat → Val → Val) (p q : Cond) : Except ReadError Cond :=
  match dropNotNot p, dropNotNot q with
  | .ule a b, .not (.eq c d) => if samePair (c, d) (b, a) then .ok (.ult a b) else .error (.unsupported n)
  | .not (.eq c d), .not s => match swapSlt low c d s with
    | some c' => .ok c'
    | none => .error (.unsupported n)
  | p', q' =>
    if flagLit p' && flagLit q' then .ok (.eq (.and (.setcc p') (.setcc q')) (.lit 1))
    else match zeroTest? p', zeroTest? q' with
      | some a, some b => .ok (.eq (.or a b) (.lit 0))
      | _, _ => .error (.unsupported n)

/-- `jbe`: a borrow or zero, `¬ a ≤ b ∨ b = a`, is `b ≤ a` (`not_nocarry_or_zero_iff_le`, `not_nocarryn_or_zero_iff_le`,
`not_nocarryn_lit_or_zero_iff_le`). `jle`: the flags of the signed compare differ or the operands are equal,
`a <s b ∨ a = b`, is `¬ b <s a` (`not_msb_sub_eq_of_or_zero_iff_not_slt`, `not_msb_sub_lit_eq_of_or_zero_iff_not_slt`, and
for `w` bits `not_msbn_sub_eq_of_or_zero_iff_not_slt`; `swapSlt`). Another disjunction is the error `unsupported n`. -/
def disj (n : Name) (low : Nat → Val → Val) (p q : Cond) : Except ReadError Cond :=
  match dropNotNot p, dropNotNot q with
  | .not (.ule a b), .eq c d => if samePair (c, d) (b, a) then .ok (.ule b a) else .error (.unsupported n)
  | s, .eq c d => match swapSlt low c d s with
    | some c' => .ok (.not c')
    | none => .error (.unsupported n)
  | p', q' =>
    if flagLit p' && flagLit q' then .ok (.not (.eq (.or (.setcc p') (.setcc q')) (.lit 0))) else .error (.unsupported n)

mutual
/-- The value of `e`. -/
partial def readVal (cx : ReadCtx) (e : Expr) : Except ReadError Val := do
  let e := e.consumeMData
  if let some k := lit? e then return .lit (UInt64.ofNat k)
  if let .fvar x := e then
    match cx.loads.findIdx? (·.1 == x) with
    | some k => return .load k
    | none => throw (.freeVar x.name)
  let some n := e.getAppFn.constName? | throw (.unsupported (headName e))
  let args := e.getAppArgs
  let low (bits : Nat) (v : Val) : Val := lowBits cx.loadBits bits v
  -- the width of an operation at the type `ty`: at most 64 bits
  let opBits (ty : Expr) : Except ReadError Nat :=
    match typeBits? ty with
    | some w => if w ≤ 64 then pure w else throw (.unsupported n)
    | none => throw (.unsupported n)
  -- the narrow width of `w` bits
  let narrowOf (w : Nat) : Except ReadError Narrow :=
    if w == 8 then pure .b8 else if w == 16 then pure .b16 else if w == 32 then pure .b32 else throw (.unsupported n)
  -- a shift count: a literal; a `UInt64` count is taken modulo 64, a `Nat` or `BitVec` count of 64 or more is refused
  let count (ty c : Expr) : Except ReadError (Fin 64) := do
    let some k := lit? c.consumeMData | throw (.unsupported n)
    let k := if ty.isConstOf ``UInt64 then k % 64 else k
    if h : k < 64 then pure ⟨k, h⟩ else throw (.shift k)
  match n, args.size with
  | ``UInt64.ofBitVec, 1 | ``UInt64.toBitVec, 1 | ``Int64.ofBitVec, 1 | ``Int64.toBitVec, 1 => readVal cx args[0]!
  | ``HAdd.hAdd, 6 => return low (← opBits args[0]!) (.add (← readVal cx args[4]!) (← readVal cx args[5]!))
  | ``HSub.hSub, 6 => return low (← opBits args[0]!) (.sub (← readVal cx args[4]!) (← readVal cx args[5]!))
  | ``HMul.hMul, 6 => return low (← opBits args[0]!) (.mul (← readVal cx args[4]!) (← readVal cx args[5]!))
  | ``HAnd.hAnd, 6 => do let _ ← opBits args[0]!; return .and (← readVal cx args[4]!) (← readVal cx args[5]!)
  | ``HOr.hOr, 6 => do let _ ← opBits args[0]!; return .or (← readVal cx args[4]!) (← readVal cx args[5]!)
  | ``HXor.hXor, 6 => do let _ ← opBits args[0]!; return .xor (← readVal cx args[4]!) (← readVal cx args[5]!)
  | ``Complement.complement, 3 => return low (← opBits args[0]!) (.not (← readVal cx args[2]!))
  | ``Neg.neg, 3 => return low (← opBits args[0]!) (.neg (← readVal cx args[2]!))
  | ``HShiftRight.hShiftRight, 6 =>
    let _ ← opBits args[0]!
    return .shr (← readVal cx args[4]!) (← count args[1]! args[5]!)
  | ``HShiftLeft.hShiftLeft, 6 =>
    return low (← opBits args[0]!) (.shl (← readVal cx args[4]!) (← count args[1]! args[5]!))
  | ``BitVec.setWidth, 3 =>
    -- `setWidth v x` with `x : BitVec w`: the zero extension when `w ≤ v`, else the low `v` bits
    let some w := natOf? args[0]! | throw (.unsupported n)
    let some v := natOf? args[1]! | throw (.unsupported n)
    if w > 64 || v > 64 then throw (.unsupported n)
    let x ← readVal cx args[2]!
    return if w ≤ v then x else low v x
  | ``BitVec.signExtend, 3 =>
    -- `signExtend v x` with `x : BitVec w`: the low `v` bits when `v ≤ w`, else `sext w x` (and its low `v` bits)
    let some w := natOf? args[0]! | throw (.unsupported n)
    let some v := natOf? args[1]! | throw (.unsupported n)
    if w > 64 || v > 64 then throw (.unsupported n)
    let x ← readVal cx args[2]!
    if v ≤ w then return low v x
    -- `sext w` takes the low `w` bits of its operand, so the zero extension that the read of `x` has is dropped
    let y := match w, x with
      | 8, .zext .b8 y | 16, .zext .b16 y | 32, .zext32 y => y
      | _, _ => x
    return low v (.sext (← narrowOf w) y)
  | ``BitVec.extractLsb', 4 =>
    let some lo := natOf? args[1]! | throw (.unsupported n)
    let some len := natOf? args[2]! | throw (.unsupported n)
    let x ← readVal cx args[3]!
    if lo == 0 then return low len x
    if h : lo + len ≤ 64 then return .extract lo len x h
    throw (.unsupported n)
  | ``BitVec.replaceLow, 4 =>
    -- the write of the low 8 or 16 bits of a 64-bit register
    let w := natOf? args[1]!
    if natOf? args[0]! != some 64 then throw (.unsupported n)
    let old ← readVal cx args[2]!
    let new ← readVal cx args[3]!
    if w == some 8 then return .replaceLow .b8 old new
    if w == some 16 then return .replaceLow .b16 old new
    throw (.unsupported n)
  | ``ite, 5 => return .ite (← readCond cx args[1]!) (← readVal cx args[3]!) (← readVal cx args[4]!)
  | ``BitVec.ofNat, 2 | ``UInt64.ofNat, 1 | ``OfNat.ofNat, 3 =>
    -- the `setcc` byte: a number `b.toNat` of a `Bool` `b` (the literals are above)
    let some b := boolToNat? args[if n == ``OfNat.ofNat then 1 else args.size - 1]! | throw (.unsupported n)
    if n == ``BitVec.ofNat && natOf? args[0]! == some 0 then throw (.unsupported n)
    return .setcc (← readBool cx b)
  | _, 1 =>
    -- a register of the start: `Reg64s.r (MachineData.regs d)`
    let some r := regOfProj? n | throw (.unsupported n)
    match args[0]!.consumeMData with
    | .app (.const ``MachineData.regs _) (.fvar x) => if x == cx.start then return .reg r else throw (.freeVar x.name)
    | _ => throw (.unsupported n)
  | _, _ => throw (.unsupported n)

/-- The condition `e`, a `Prop`. -/
partial def readCond (cx : ReadCtx) (e : Expr) : Except ReadError Cond := do
  let e := e.consumeMData
  -- READER, D1: the implication `p → q` (the form of `simp` for `¬ (p ∧ ¬ q)`, `jne` after `orb`) is `¬ (p ∧ ¬ q)`
  if let .forallE _ p q _ := e then
    if q.hasLooseBVars then throw (.unsupported `other)
    return .not (← conj `other (lowBits cx.loadBits) (← readCond cx p) (dropNotNot (.not (← readCond cx q))))
  let some n := e.getAppFn.constName? | throw (.unsupported (headName e))
  let args := e.getAppArgs
  match n, args.size with
  | ``Not, 1 => return .not (← readCond cx args[0]!)
  | ``Iff, 2 => return .iff (← readCond cx args[0]!) (← readCond cx args[1]!)
  | ``And, 2 => conj n (lowBits cx.loadBits) (← readCond cx args[0]!) (← readCond cx args[1]!)
  | ``Or, 2 => disj n (lowBits cx.loadBits) (← readCond cx args[0]!) (← readCond cx args[1]!)
  | ``Eq, 3 => readEq cx args[0]! args[1]! args[2]!
  | ``LE.le, 4 =>
    if typeBits? args[0]! != some 64 then throw (.unsupported n)
    let a ← readVal cx args[2]!
    let b ← readVal cx args[3]!
    -- the order of `Int64` is the signed order: `a ≤ b` is `¬ b < a`
    return if args[0]!.consumeMData.isConstOf ``Int64 then .not (.slt b a) else .ule a b
  | ``LT.lt, 4 =>
    if typeBits? args[0]! != some 64 then throw (.unsupported n)
    let a ← readVal cx args[2]!
    let b ← readVal cx args[3]!
    return if args[0]!.consumeMData.isConstOf ``Int64 then .slt a b else .ult a b
  | _, _ => throw (.unsupported n)

/-- The condition `e`, a `Bool`: `!`, `&&` and `||` (the `ja` and `jbe` forms), `==`, `!=`, `decide`, and a flag of the
start. -/
partial def readBool (cx : ReadCtx) (e : Expr) : Except ReadError Cond := do
  let e := e.consumeMData
  let some n := e.getAppFn.constName? | throw (.unsupported (headName e))
  let args := e.getAppArgs
  match n, args.size with
  | ``Bool.not, 1 => return .not (← readBool cx args[0]!)
  | ``Bool.and, 2 => conj n (lowBits cx.loadBits) (← readBool cx args[0]!) (← readBool cx args[1]!)
  | ``Bool.or, 2 => disj n (lowBits cx.loadBits) (← readBool cx args[0]!) (← readBool cx args[1]!)
  | ``BEq.beq, 4 => readEq cx args[0]! args[2]! args[3]!
  | ``bne, 4 => return .not (← readEq cx args[0]! args[2]! args[3]!)
  | ``Decidable.decide, 2 => readCond cx args[0]!
  | ``BitVec.slt, 3 =>
    -- `cmovl` after `cmpl`: the signed compare of the low 32 bits, which `slt32` reads (the zero extension is dropped)
    if natOf? args[0]! != some 32 then throw (.unsupported n)
    let low32 : Val → Val := fun | .zext32 v => v | v => v
    return .slt32 (low32 (← readVal cx args[1]!)) (low32 (← readVal cx args[2]!))
  | _, 1 =>
    -- a flag of the start: `StatusFlags.f (MachineData.status d)`, a flag input (D43)
    let some f := flagOfProj? n | throw (.unsupported n)
    match args[0]!.consumeMData with
    | .app (.const ``MachineData.status _) (.fvar x) => if x == cx.start then return .flag f else throw (.freeVar x.name)
    | s =>
      -- READER, D2: the zero flag of a result that `simp` left as `from_result` (`zf_from_result`): `r = 0`
      if f == .zf && s.isAppOfArity ``StatusFlags.from_result 3 then
        let w := s.getArg! 0
        return ← readEq cx (mkApp (mkConst ``BitVec) w) (s.getArg! 1) (mkApp2 (mkConst ``BitVec.ofNat) w (mkRawNatLit 0))
      throw (.unsupported n)
  | _, _ => throw (.unsupported n)

/-- The equation `l = r` of the type `ty` (also `l == r`). -/
partial def readEq (cx : ReadCtx) (ty l r : Expr) : Except ReadError Cond := do
  let ty := ty.consumeMData
  let r := r.consumeMData
  if ty.isConstOf ``Int then return ← readBorrow cx l r
  if ty.isConstOf ``Bool then
    if r.isConstOf ``Bool.true then return ← readBool cx l
    if r.isConstOf ``Bool.false then return .not (← readBool cx l)
    if let some c ← readSigned cx l r then return c
    return .iff (← readBool cx l) (← readBool cx r)
  let some bits := typeBits? ty | throw (.unsupported ``Eq)
  if bits > 64 then throw (.unsupported ``Eq)
  -- `setcc_xor_iff` before the narrow equation
  if let (some p, some q) := (setccByte? l, setccByte? r) then return .iff (← readBool cx p) (← readBool cx q)
  if lit? r == some 0 then
    -- `sub_zero_iff` (64 bits), `sub32_zero_iff` (`cmpl`), and any width: `a - b = 0` is `a = b`
    if let some (a, b) := binop? ``HSub.hSub l then return .eq (← readVal cx a) (← readVal cx b)
    -- `shlxor_zero_iff_and`
    if let some (a, b) := shlXor16? l then return .eq (.and (← readVal cx a) mask48) (.and (← readVal cx b) mask48)
    -- `and_zero_iff`
    if let some (k, a) := binop? ``HAnd.hAnd l then return .eq (.and (← readVal cx a) (← readVal cx k)) (.lit 0)
  -- `eq_zero_iff`, `extract8_zero_iff`, `extract16_zero_iff`, `extract8_shr32_zero_iff`, `byte_zero_iff`
  return .eq (← readVal cx l) (← readVal cx r)

/-- The `Nat` term `e` of a sum of `Int` casts, as a value: `x.toNat` of a `UInt64` or a `BitVec 64`, and (READER, D3:
`andq` with a literal mask before `cmpq; sbb`, `UInt64.toNat_and`) `a &&& b` of two such terms or literals below `2^64`. -/
partial def readNat (cx : ReadCtx) (e : Expr) : Except ReadError Val := do
  let e := e.consumeMData
  if e.isAppOfArity ``UInt64.toNat 1 then readVal cx (e.getArg! 0)
  else if e.isAppOfArity ``BitVec.toNat 2 && natOf? (e.getArg! 0) == some 64 then readVal cx (e.getArg! 1)
  else if let some (a, b) := binop? ``HAnd.hAnd e then
    unless (e.getArg! 0).consumeMData.isConstOf ``Nat do throw (.unsupported ``Int)
    let part (x : Expr) : Except ReadError Val :=
      match (x.consumeMData.nat? <|> x.consumeMData.rawNatLit?) with
      | some k => if k < 2 ^ 64 then pure (.lit (UInt64.ofNat k)) else throw (.unsupported ``Int)
      | none => readNat cx x
    return .and (← part a) (← part b)
  else throw (.unsupported ``Int)

/-- An `Int` operand of a borrow form: the cast `↑x.toNat` of `readNat`, or the shift `X >>> k` of such an operand by a
literal `k < 64` (`int_toNat_shiftRight`: `↑x.toNat >>> k = ↑(x >>> k).toNat`; `shrq $32; cmpb $2` of `l2zBits`). -/
partial def readIntOp (cx : ReadCtx) (e : Expr) : Except ReadError Val := do
  let err := ReadError.unsupported ``Int
  let e := e.consumeMData
  if let some (x, k) := binop? ``HShiftRight.hShiftRight e then
    unless (e.getArg! 0).consumeMData.isConstOf ``Int do throw err
    let some k := lit? k.consumeMData | throw err
    if h : k < 64 then return .shr (← readIntOp cx x) ⟨k, h⟩
    throw err
  let some x := natCast? e | throw err
  readNat cx x

/-- READER, D3: an `Int` term that is not negative, as its value modulo `2^64`: an operand of `readIntOp`, a literal that
is not negative, `+` of `Int`, and `% 2^32` (`zext32`) and `% 2^64` (the value itself). A 32-bit `lea` before `cmpb`
gives `(x + K) % 2^32 % 2^64`, `addq` before `cmpq` gives `↑a.toNat + ↑b.toNat`. Only the forms whose condition reads the
term modulo `2^w` with `w ≤ 64` use it. -/
partial def readIntSum (cx : ReadCtx) (e : Expr) : Except ReadError Val := do
  let err := ReadError.unsupported ``Int
  let e := e.consumeMData
  if let some k := intLit? e then return .lit (UInt64.ofNat k.toNat)
  let isInt := (e.getAppNumArgs == 6 && (e.getArg! 0).consumeMData.isConstOf ``Int)
  if let some (a, b) := binop? ``HAdd.hAdd e then
    unless isInt do throw err
    return .add (← readIntSum cx a) (← readIntSum cx b)
  if let some (x, m) := binop? ``HMod.hMod e then
    unless isInt do throw err
    match intLit? m with
    | some 4294967296 => return .zext32 (← readIntSum cx x)
    | some 18446744073709551616 => return ← readIntSum cx x
    | _ => throw err
  readIntOp cx e

/-- The `Int` sum `S` of `nocarry32_lit_iff_le`, as a value modulo `2^32`: the literals, `+`, the casts of `readNat`, and
`↑(c - y % 2^32)` with `2^32 ≤ c + 1` (the subtraction of `Nat` does not cut at 0), which is `c - y` modulo `2^32`
(`natCast_sub_mod_eq`): `-y` for `c = 2^32`, `c - y` for another `c` (`notl` gives `c = 2^32 - 1`). -/
partial def readSum32 (cx : ReadCtx) (e : Expr) : Except ReadError Val := do
  let err := ReadError.unsupported ``Int
  let e := e.consumeMData
  if let some n := intLit? e then return .lit (UInt64.ofNat n.toNat)
  if let some (a, b) := binop? ``HAdd.hAdd e then return .add (← readSum32 cx a) (← readSum32 cx b)
  let some x := natCast? e | throw err
  match binop? ``HSub.hSub x with
  | some (t, ym) =>
    let some (y, m) := binop? ``HMod.hMod ym | throw err
    let some c := lit? t.consumeMData | throw err
    unless lit? m.consumeMData == some 4294967296 && 4294967296 ≤ c + 1 do throw err
    if c == 4294967296 then return .neg (← readNat cx y)
    return .sub (.lit (UInt64.ofNat c)) (← readNat cx y)
  | none => readNat cx x

/-- The sign flag equals the overflow flag of a 64-bit subtraction, `l = r` with `l = msb (x - y)` and `r = bne (bmod X 2^64) X`
for `X = x.toInt - y.toInt` (`msb_sub_eq_of_iff_not_slt`), or with a literal `y`, `X = x.toInt - K` or `x.toInt + J` with
`K` the signed value of `y` and `J = -K` (`msb_sub_lit_eq_of_iff_not_slt`): the condition `¬ x <s y`. `none` when the
equation is not of this form: it is then read as the equation of two `Bool` conditions, which refuses `msb`. -/
partial def readSigned (cx : ReadCtx) (l r : Expr) : Except ReadError (Option Cond) := do
  let l := l.consumeMData
  let r := r.consumeMData
  unless l.isAppOfArity ``BitVec.msb 2 && r.isAppOfArity ``bne 4 do return none
  let some w := natOf? (l.getArg! 0) | return none
  if w == 8 || w == 16 || w == 32 then return ← readSignedN cx w l r
  unless w == 64 do return none
  let some (x, y) := binop? ``HSub.hSub (l.getArg! 1) | return none
  let ov := (r.getArg! 2).consumeMData
  let xi := (r.getArg! 3).consumeMData
  unless ov.isAppOfArity ``Int.bmod 2 && ov.getArg! 0 == xi && natOf? (ov.getArg! 1) == some 18446744073709551616 do
    return none
  -- `x.toInt` of a `BitVec 64` term `x`
  let toInt? (e : Expr) : Option Expr :=
    let e := e.consumeMData
    if e.isAppOfArity ``BitVec.toInt 2 && natOf? (e.getArg! 0) == some 64 then some (e.getArg! 1) else none
  let vx ← readVal cx x
  let vy ← readVal cx y
  -- the signed value of a literal
  let signed : Val → Option Int
    | .lit n => some (if n.toNat < 2 ^ 63 then (n.toNat : Int) else (n.toNat : Int) - 2 ^ 64)
    | _ => none
  let same (e : Expr) (v : Val) : Except ReadError Bool := do pure ((← readVal cx e).show == v.show)
  let ok : Bool ←
    if let some (p, q) := binop? ``HSub.hSub xi then
      match toInt? p with
      | none => pure false
      | some a =>
        if !(← same a vx) then pure false
        else match toInt? q with
          | some b => same b vy
          | none => pure ((intLit? q.consumeMData).isSome && intLit? q.consumeMData == signed vy)
    else if let some (p, q) := binop? ``HAdd.hAdd xi then
      match toInt? p, intLit? q.consumeMData with
      | some a, some j => do pure ((← same a vx) && some (-j) == signed vy)
      | _, _ => pure false
    else pure false
  return if ok then some (.not (.slt vx vy)) else none

/-- The signed compare of `w` = 8, 16 or 32 bits (`cmpb`, `cmpw`, `cmpl` then `jge`; AF2-E2): `l = msb (x - y)` of the
`w`-bit operands, `r = bne ((A - B).bmod 2^w) (A.bmod 2^w - B.bmod 2^w)` with the `Int` operands `A`, `B` of `readIntOp`
whose low `w` bits are `x`, `y` (`msbn_sub_eq_of_iff_not_slt`); with a literal `y` of the signed value `K`,
`r = bne ((A - K).bmod 2^w) (A.bmod 2^w - K)`, or `+ J` for `K = -J` (`msbn_sub_lit_eq_of_iff_not_slt`). The condition is
`¬ x <s y` of `w` bits: `slt32` for 32 bits, `slt` of the sign extensions for 8 and 16 bits (`signExtend_slt_iff`). `none`
when the equation is not of this form. -/
partial def readSignedN (cx : ReadCtx) (w : Nat) (l r : Expr) : Except ReadError (Option Cond) := do
  let some (x, y) := binop? ``HSub.hSub (l.getArg! 1) | return none
  let M := 2 ^ w
  let bmod? (e : Expr) : Option Expr :=
    let e := e.consumeMData
    if e.isAppOfArity ``Int.bmod 2 && natOf? (e.getArg! 1) == some M then some (e.getArg! 0) else none
  let low (v : Val) : Val := lowBits cx.loadBits w v
  let vx ← readVal cx x
  let vy ← readVal cx y
  -- the `Int` operand `e` has the low `w` bits `v`
  let same (e : Expr) (v : Val) : Except ReadError Bool := do
    match readIntOp cx e with
    | .ok u => pure ((low u).show == v.show)
    | .error _ => pure false
  -- the signed value of a literal of `w` bits
  let signed : Val → Option Int
    | .lit n => let k := n.toNat % M; some (if k < M / 2 then (k : Int) else (k : Int) - M)
    | _ => none
  -- `A - K` (`K ≥ 0`) or `A + J`, as `(A, -K)` or `(A, J)`: the operand and the literal added
  let litTerm (e : Expr) : Option (Expr × Int) :=
    match binop? ``HSub.hSub e, binop? ``HAdd.hAdd e with
    | some (a, k), _ => (intLit? k).map fun k => (a, -k)
    | none, some (a, j) => (intLit? j).map fun j => (a, j)
    | none, none => none
  let some ov := bmod? (r.getArg! 2) | return none
  let xi := (r.getArg! 3).consumeMData
  let ok : Bool ←
    match signed vy, litTerm ov, litTerm xi with
    | some k, some (a, j), some (p, j') =>
      -- the literal form: `(A + J).bmod M != A.bmod M + J` with `J = -K`
      match bmod? p with
      | some a' => do pure (j == -k && j' == j && (← same a vx) && (← same a' vx))
      | none => pure false
    | _, _, _ =>
      match binop? ``HSub.hSub ov, binop? ``HSub.hSub xi with
      | some (a, b), some (p, q) =>
        match bmod? p, bmod? q with
        | some a', some b' => do pure ((← same a vx) && (← same a' vx) && (← same b vy) && (← same b' vy))
        | _, _ => pure false
      | _, _ => pure false
  unless ok do return none
  -- the operands without the zero extension of `w` bits that the read of a `w`-bit value has
  let strip : Val → Val
    | .zext .b8 v => if w == 8 then v else .zext .b8 v
    | .zext .b16 v => if w == 16 then v else .zext .b16 v
    | .zext32 v => if w == 32 then v else .zext32 v
    | v => v
  let a := strip vx
  let b := strip vy
  return some (.not (if w == 32 then .slt32 a b else if w == 16 then .slt (.sext .b16 a) (.sext .b16 b)
    else .slt (.sext .b8 a) (.sext .b8 b)))

/-- The borrow forms, equations of `Int`: `nocarry_iff_le`, `nocarry_lit_iff_le` (the literal `k` is `2^64 - C`) and, for
the modulus `2^w` of 8, 16 or 32 bits, `nocarryn_iff_le` and `nocarryn_lit_iff_le` (the literal `k` is `2^w - C`;
`nocarry8_lit_iff_le` is the case `w = 8` of the second). The operands of the narrow forms are read as their low `w`
bits (`lowBits`). The operand of a literal form is an `Int` operand of `readIntOp` (a cast, or its shift by a literal). The
forms of `sbb` (NB) are also read: `nocarry8_load_lit_iff_le` (`2^8 - C`, a byte load with no `% 256` on the right) and
`nocarry32_lit_iff_le` (`2^32 - C`, the sum `S` modulo `2^32`). -/
partial def readBorrow (cx : ReadCtx) (l r : Expr) : Except ReadError Cond := do
  let err := ReadError.unsupported ``Int
  let some (sum, m) := binop? ``HMod.hMod l | throw err
  let some (s1, s2) := binop? ``HAdd.hAdd sum | throw err
  let some (r1, r2) := binop? ``HSub.hSub r | throw err
  let toNat (e : Option Expr) : Except ReadError Val := do
    let some e := e | throw err
    let e := e.consumeMData
    if e.isAppOfArity ``BitVec.toNat 2 && natOf? (e.getArg! 0) == some 64 then readVal cx (e.getArg! 1)
    else if e.isAppOfArity ``UInt64.toNat 1 then readVal cx (e.getArg! 0)
    else throw err
  let m := intLit? m
  if m == some 18446744073709551616 then
    match intLit? s1, intLit? r2 with
    | some c, some k =>
      -- `(C + ↑b.toNat) % 2^64 = ↑b.toNat - K` with `C + K = 2^64`; the operand of `readIntOp`
      let b ← readIntOp cx s2
      let b' ← readIntOp cx r1
      if c + k == 18446744073709551616 && 0 ≤ k && b.show == b'.show then return .ule (.lit (UInt64.ofNat k.toNat)) b
      throw err
    | _, _ =>
      -- `(↑(2^64 - a.toNat) + ↑b.toNat) % 2^64 = ↑b.toNat - ↑a.toNat`
      let some d := natCast? s1 | throw err
      let some (t, ta) := binop? ``HSub.hSub d | throw err
      if lit? t.consumeMData != some 18446744073709551616 then throw err
      let a ← toNat (some ta)
      let (b, b') ← match natCast? s2 with
        | some _ => do pure (← toNat (natCast? s2), ← toNat (natCast? r1))
        | none => do
          -- READER, D3: an `Int` sum `S` (`addq` before `cmpq`) with `S % 2^64` on the right
          let some (t, m') := binop? ``HMod.hMod r1 | throw err
          unless intLit? m' == some 18446744073709551616 do throw err
          pure (← readIntSum cx s2, ← readIntSum cx t)
      let a' ← toNat (natCast? r2)
      if a.show == a'.show && b.show == b'.show then return .ule a b
      throw err
  -- the narrow borrow: the modulus is `2^w` for 8, 16 or 32 bits, and the operands are taken modulo `2^w`
  let w? : Option Nat := if m == some 256 then some 8 else if m == some 65536 then some 16
    else if m == some 4294967296 then some 32 else none
  if let some w := w? then
    let M : Int := 2 ^ w
    let isM (e : Expr) : Bool := intLit? e == some M || lit? e.consumeMData == some M.toNat
    let low (v : Val) : Val := lowBits cx.loadBits w v
    -- `e % M`: the operand `e`
    let modM (e : Expr) : Except ReadError Expr := do
      let some (x, m') := binop? ``HMod.hMod e | throw err
      if isM m' then pure x else throw err
    match intLit? s1, intLit? r2 with
    | some c, some k =>
      if (binop? ``HMod.hMod r1).isNone then
        -- NB, `nocarry8_load_lit_iff_le`: `(C + ↑v.toNat) % 256 = ↑v.toNat - K` of a `BitVec 8` value `v`
        if w != 8 then throw err
        let toNat8 (e : Option Expr) : Except ReadError Val := do
          let some e := e | throw err
          let e := e.consumeMData
          if e.isAppOfArity ``BitVec.toNat 2 && natOf? (e.getArg! 0) == some 8 then readVal cx (e.getArg! 1) else throw err
        let v ← toNat8 (natCast? s2)
        let v' ← toNat8 (natCast? r1)
        if c + k == 256 && 0 ≤ k && v.show == v'.show then return .ule (.lit (UInt64.ofNat k.toNat)) (low v)
        throw err
      else if w == 32 && (binop? ``HMod.hMod s2).isSome then
        -- NB, `nocarry32_lit_iff_le`: `(C + (S % 2^32) % 2^64) % 2^32 = S % 2^32 - K` with `C + K = 2^32`
        let some (t, m64) := binop? ``HMod.hMod s2 | throw err
        let some (sum, m32) := binop? ``HMod.hMod t | throw err
        let some (sum', m32') := binop? ``HMod.hMod r1 | throw err
        if intLit? m64 != some 18446744073709551616 || intLit? m32 != some 4294967296 || intLit? m32' != some 4294967296 then
          throw err
        let v ← readSum32 cx sum
        let v' ← readSum32 cx sum'
        if c + k == 4294967296 && 0 ≤ k && v.show == v'.show then return .ule (.lit (UInt64.ofNat k.toNat)) (low v)
        throw err
      else
        -- `(C + ↑x.toNat) % M = ↑x.toNat % M - K` with `C + K = M` (`nocarry8_lit_iff_le`, `nocarryn_lit_iff_le`); the
        -- operand of `readIntOp`, or (READER, D3) an `Int` sum of `readIntSum`: the condition reads both sides modulo `M`,
        -- so their low `w` bits must agree
        let x ← readIntSum cx s2
        let x' ← readIntSum cx (← modM r1)
        if c + k == M && 0 ≤ k && (low x).show == (low x').show then return .ule (.lit (UInt64.ofNat k.toNat)) (low x)
        throw err
    | _, _ =>
      -- `(↑(M - a.toNat % M) + ↑b.toNat) % M = ↑b.toNat % M - ↑a.toNat % M` (`nocarryn_iff_le`)
      let some d := natCast? s1 | throw err
      let some (t, ta) := binop? ``HSub.hSub d | throw err
      unless isM t do throw err
      let a ← toNat (some (← modM ta))
      let b ← toNat (natCast? s2)
      let b' ← toNat (natCast? (← modM r1))
      let a' ← toNat (natCast? (← modM r2))
      if a.show == a'.show && b.show == b'.show then return .ule (low a) (low b)
      throw err
  throw err

end

/-! ## The normal form -/

/-- A linear form over `UInt64`: a constant and the atoms with their coefficients, in the order of their first
appearance. An atom is a value that is not a sum, a difference, a negation, a complement, a left shift, a product with a
literal or a literal. -/
structure Lin where
  const : UInt64
  terms : List (Val × UInt64)

namespace Lin

def atom (v : Val) : Lin := ⟨0, [(v, 1)]⟩

def scale (c : UInt64) (l : Lin) : Lin := ⟨c * l.const, l.terms.map fun (v, k) => (v, c * k)⟩

/-- The sum: the coefficients of the same atom (the same text) are added. -/
def add (a b : Lin) : Lin :=
  ⟨a.const + b.const, b.terms.foldl (init := a.terms) fun ts (v, k) =>
    if ts.any (·.1.show == v.show) then ts.map fun (u, j) => if u.show == v.show then (u, j + k) else (u, j)
    else ts ++ [(v, k)]⟩

/-- The terms with a coefficient other than 0. -/
def nonzero (l : Lin) : List (Val × UInt64) := l.terms.filter (·.2 != 0)

/-- The value of a linear form: the atoms sorted by their text, each one times its coefficient, then the constant when
it is not 0. -/
def toVal (l : Lin) : Val :=
  let ts := l.nonzero.mergeSort fun a b => decide (a.1.show ≤ b.1.show)
  let term : Val × UInt64 → Val := fun (v, k) => if k == 1 then v else .mul v (.lit k)
  match ts with
  | [] => .lit l.const
  | t :: rest =>
    let s := rest.foldl (fun acc t => Val.add acc (term t)) (term t)
    if l.const == 0 then s else .add s (.lit l.const)

/-- The form of a value in normal form: a literal is the constant, another value an atom. -/
def ofNorm : Val → Lin
  | .lit n => ⟨n, []⟩
  | v => .atom v

end Lin

/-- The two values in the order of their text. -/
private def ordered (a b : Val) : Val × Val := if a.show ≤ b.show then (a, b) else (b, a)

/-- The low bits of a value in normal form, as a linear form (no load width is known: a load has 64 bits). The low bits
of an `ite` are the `ite` of the low bits of its arms. -/
private def lowLin (bits : Nat) : Val → Lin
  | .ite c a b => .atom (.ite c (lowLin bits a).toVal (lowLin bits b).toVal)
  | v => .ofNorm (lowBits (fun _ => 64) bits v)

/-- `a &&& b` of two values in normal form: the literals folded, a mask of the low 8, 16 or 32 bits as the low bits. -/
private def andLin (a b : Val) : Lin :=
  let mask (x : Val) (m : UInt64) : Option Lin :=
    if m == 0xFF then some (lowLin 8 x) else if m == 0xFFFF then some (lowLin 16 x)
    else if m == 0xFFFFFFFF then some (lowLin 32 x) else none
  match a, b with
  | .lit m, .lit n => ⟨m &&& n, []⟩
  | x, .lit m | .lit m, x => (mask x m).getD (.atom (.and x (.lit m)))
  | x, y => let (x, y) := ordered x y; .atom (.and x y)

mutual
/-- The linear form of `v`. Inside an atom, the values are in normal form. The literals are folded; an `ite` has a
condition that is not a negation, and the low bits of an `ite` are an `ite` of low bits; the low bits have
the normal form of `lowBits` (`zext .b32`, `extract 0 32`, `replaceLow .b32` and `&&& 0xFFFFFFFF` are `zext32`); the
operands of `&&&`, `|||`, `^^^` are in the order of their text. -/
def _root_.Skel.Gen.Val.lin : Val → Lin
  | .lit n => ⟨n, []⟩
  | .add a b => a.lin.add b.lin
  | .sub a b => a.lin.add (b.lin.scale (0 - 1))
  | .neg a => a.lin.scale (0 - 1)
  | .not a => (a.lin.scale (0 - 1)).add ⟨0 - 1, []⟩
  | .shl a k => a.lin.scale ((1 : UInt64) <<< UInt64.ofNat k.val)
  | .mul a b =>
    let la := a.lin
    let lb := b.lin
    if la.nonzero.isEmpty then lb.scale la.const
    else if lb.nonzero.isEmpty then la.scale lb.const
    else .atom (.mul la.toVal lb.toVal)
  | .shr a k =>
    let la := a.lin
    if la.nonzero.isEmpty then ⟨la.const >>> UInt64.ofNat k.val, []⟩ else .atom (.shr la.toVal k)
  | .zext32 a => lowLin 32 a.lin.toVal
  | .zext w a => lowLin w.bits a.lin.toVal
  | .extract lo len a h =>
    if lo == 0 then lowLin len a.lin.toVal
    else match a.lin.toVal with
      | .lit n => ⟨UInt64.ofNat ((n.toNat >>> lo) % 2 ^ len), []⟩
      | x => .atom (.extract lo len x h)
  | .replaceLow .b32 _ b => lowLin 32 b.lin.toVal
  | .replaceLow w a b => .atom (.replaceLow w a.lin.toVal b.lin.toVal)
  | .and a b => andLin a.lin.toVal b.lin.toVal
  | .or a b =>
    match a.lin.toVal, b.lin.toVal with
    | .lit m, .lit n => ⟨m ||| n, []⟩
    | x, y => let (x, y) := ordered x y; .atom (.or x y)
  | .xor a b =>
    match a.lin.toVal, b.lin.toVal with
    | .lit m, .lit n => ⟨m ^^^ n, []⟩
    | x, y => let (x, y) := ordered x y; .atom (.xor x y)
  | .sext w a => .atom (.sext w a.lin.toVal)
  | .setcc c => .atom (.setcc c.norm)
  | .ite c a b =>
    -- `if ¬ c then a else b` is `if c then b else a`
    match c.norm with
    | .not d => .atom (.ite d b.lin.toVal a.lin.toVal)
    | d => .atom (.ite d a.lin.toVal b.lin.toVal)
  | .reg r => .atom (.reg r)
  | .load k => .atom (.load k)
  | .retAddr o => .atom (.retAddr o)

/-- The normal form of `c`: the values in normal form; `¬ a < b` is `b ≤ a`, `¬ a ≤ b` is `b < a`, `¬ ¬ c` is `c`; the
two sides of `=` and `↔` in the order of their text. -/
def _root_.Skel.Gen.Cond.norm : Cond → Cond
  | .eq a b => let (x, y) := ordered a.lin.toVal b.lin.toVal; .eq x y
  | .ule a b => .ule a.lin.toVal b.lin.toVal
  | .ult a b => .ult a.lin.toVal b.lin.toVal
  | .slt a b => .slt a.lin.toVal b.lin.toVal
  | .slt32 a b => .slt32 a.lin.toVal b.lin.toVal
  | .not c =>
    match c.norm with
    | .ult a b => .ule b a
    | .ule a b => .ult b a
    | .not d => d
    | d => .not d
  | .iff p q =>
    let p := p.norm
    let q := q.norm
    if p.show ≤ q.show then .iff p q else .iff q p
  | .flag f => .flag f
end

/-- The normal form of `v`: the linear form over `UInt64` (`Val.lin`), as a value. Two values with the same normal form
are equal for all register, load and flag values. -/
def _root_.Skel.Gen.Val.norm (v : Val) : Val := v.lin.toVal

/-- The two values have the same normal form. -/
def _root_.Skel.Gen.Val.sameNorm (a b : Val) : Bool := a.norm.show == b.norm.show

/-- The two conditions have the same normal form. -/
def _root_.Skel.Gen.Cond.sameNorm (a b : Cond) : Bool := a.norm.show == b.norm.show

/-! ## Addresses -/

/-- The address `e`: base + Σ index · scale + displacement, each part optional; in the form of `address` of `Sym.lean`
(the parts that are present in this order, the displacement when it is not 0). The base is the term of coefficient 1
that comes first in `e`; the indexes are the other terms in the order of their first appearance, each with its
coefficient as the scale: 1, 2, 4 or 8 from the instruction, or another literal when the walk has folded a product into
the address (`imulq $12` before an indexed access, `leaq` before an indexed access). The address is the linear form of
the value read (`Val.lin`), so that any sum of terms with literal coefficients is an address. -/
def readAddr (cx : ReadCtx) (e : Expr) : Except ReadError Val := do
  let l := (← readVal cx e).lin
  let terms : List (Val × UInt64) := l.nonzero
  let (base, idx) := match terms.findIdx? (fun t => t.2 == 1) with
    | some i => (terms[i]?.map Prod.fst, terms.take i ++ terms.drop (i + 1))
    | none => (none, terms)
  let disp := if l.const == 0 then none else some (Val.lit l.const)
  let parts : List (Option Val) := [base] ++ idx.map (fun (x, k) => some (Val.mul x (.lit k))) ++ [disp]
  match parts.filterMap id with
  | [] => pure (.lit 0)
  | p :: ps => pure (ps.foldl Val.add p)

/-! ## Blocks -/

/-- The exit of a read block. The targets are offsets from the start of the function, except the callee of a call (a
PC). A branch goes to `yes` when its condition holds, else to `no`. -/
inductive ReadExit where
  | goto (target : Nat)
  | branch (c : Cond) (yes no : Nat)
  | call (callee cont : Nat)
  | ret
  | indirect (target : Val)
  | trap

/-- The parts of a table `Block`: the accesses (loads and stores numbered on their own, as `Sym.lean` numbers them),
the changed registers (in the order of `allRegs`) and the exit. -/
structure ReadBlock where
  accesses : List Access
  regs : List (Reg64 × Val)
  exit : ReadExit

/-- The read block of the walk `w` of a block of the function that starts at `base`. The stored value of a call (the
return address, a literal) is `retAddr` of the offset of the continuation. -/
def readWalk (base : Nat) (w : Walk) : Except ReadError ReadBlock := do
  let cx := ReadCtx.ofWalk w
  let off (pc : Nat) : Except ReadError Nat := if pc < base then throw (.outside pc) else pure (pc - base)
  let regs ← w.regs.toList.mapM fun (r, e) => do pure (r, ← readVal cx e)
  let (accs, _, _) ← w.accesses.toList.foldlM (init := ([], 0, 0)) fun (acc, nl, ns) a =>
    match a with
    | .load addr wd _ _ => do pure (acc ++ [Access.load nl (← readAddr cx addr) wd], nl + 1, ns)
    | .store addr wd v _ _ => do pure (acc ++ [Access.store ns (← readAddr cx addr) wd (← readVal cx v)], nl, ns + 1)
  let exit ← match w.exit with
    | .goto pc => pure (ReadExit.goto (← off pc))
    | .branch c _ y n => pure (.branch (← readCond cx c) (← off y) (← off n))
    | .call callee cont => pure (.call callee (← off cont))
    | .ret => pure .ret
    | .indirect t => pure (.indirect (← readVal cx t))
    | .trap => pure .trap
  -- the walk gives a call only when the last access is the store of the literal `cont` with the width 64. The address of
  -- that store is `rsp` after the call, and the proof of a call takes it as that term (`retAddr_writeRam`): it is the value
  -- of `rsp`, not its normal form as an address (`rsp - 8 - 8`, not `rsp - 16`)
  let accs ← match w.exit, accs.getLast? with
    | .call _ cont, some (.store k a .W64 _) =>
      do pure (accs.dropLast ++ [.store k ((regs.lookup .rsp).getD a) .W64 (.retAddr (← off cont))])
    | _, _ => pure accs
  pure { accesses := accs, regs, exit }

end Skel.Gen.Derive
