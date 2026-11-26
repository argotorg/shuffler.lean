import Lean
import Skel.Gen.Derive.Read
import Skel.Gen.Asm
import Skel.Gen.Frame
import Skel.Gen.Split

/-! The derived blocks of a function (task N11 of `docs/research/symexec-pilot-20261118.md`, section 5; decisions D41
and D43): the `Block` parts from the derived terms, in the form of `symBlock` (`Skel/Gen/Sym.lean`).

For each raw block of `split`: the term of N2 (`blockTerm`, with the site equations of N1), the walk of N3 (`walkTerm`),
the diff of N4 (`Walk.diff` with the live flags), and the read of N7 and N10 (`readWalk`). The name of a block comes from
`split`, so a `Part` has no name.

* **Live flags (D43).** The flags at the end of a block that a later block reads: the fixpoint of
  `live b = ⋃ (inputs s (live s) ∪ (live s \ changed s))` over the successors `s` of `b` (a goto and the two sides of a
  branch; a call, a return and a trap pass no flag on). A block whose kept parts read a flag of its start has a flag input.
  The part keeps each live flag with its value at the exit (`Part.flags`, L2-FLAGS): the read of the flag value of the
  walk, or `.flag f` when the block does not change `f`. A flag input of the entry or of the return of a call is an error
  (no block keeps the flags for it), and so are a live `pf` or `af` and a flag value that the reader does not read (`sf`
  or `of` alone): `GenError.derive`.
* **Exits.** `ReadExit.call` gives the callee as a PC. The callee of a `Part` is the label of the call instruction (as
  `symBlock` gives it), and the PC must be the address of that label. An indirect exit is an error.
* **Registers** are in the order of `allRegs` (`readWalk`), not in the order of the first write; the statements put
  `rsp` last (`Stmt.lean`). A sum with `rsp` and a literal of 2^63 or more is a difference (`subForm`: `rsp - 8`, not
  `rsp + 18446744073709551608`): the closers of `lift_block_split` do not prove the one equal to the other. A sum with no
  `rsp` keeps its literal (`rdi + 2^63` is not `rdi - 2^63`). The operands of a sum keep the order of the composed term
  (`rax := v1 + rax` for `addq (%rdi), %rax`): the closers of `lift_block_split` read the order of the site lemmas.
* **Errors.** A block with no finished term, no walk, or no read is `GenError.derive` at its offset, with the cause.
* **Budget (N16).** Each unit has the whole `maxHeartbeats` budget (`withCurrHeartbeats`): a site, the table walk and
  the simp set of a function, a block (its term and its walk), and the definition. The sum of the units of a function can
  pass the budget (the 230 sites of the shuffler function `buildBottomUp` need about 185,000 units of 1000 heartbeats). A
  block that passes a limit is the error `derive` with its label and the limit (`limitError`); the command does not fail.
  The live flags read each expression of a walk once (`FlagUse`), and the fixpoint stops at the first pass that changes
  nothing.

`#derive_blocks name step code ["fn", …]` defines `name : Derived` (`Skel/Gen/Types.lean`) at elaboration time: the parts
of the functions of `code`. The site equations are theorems `name.site<addr>` of the module. -/

open Lean Meta Elab Term Skel.Gen

namespace Skel.Gen.Derive

/-! ## Addresses -/

/-- The address of the label `l` of `code`. -/
def labelAddr (code : Executable) (l : String) : Option Nat :=
  ((Kraken.Executable.withAddresses code).find? (·.directive.label? == some l)).map (·.addr.toBitVec.toNat)

/-- The label of the direct call at the end of a raw block. -/
def callLabel (b : RawBlock) : Option String :=
  match b.sites.getLast? with
  | some ⟨_, .regular _ _ (.call (.rel (.sub (.label l) .after_current_instruction)))⟩ => some l
  | _ => none

/-! ## Live flags -/

/-- The successors of an exit for the flags: a goto and the two sides of a branch. A call does not keep the flags (the
callee does not preserve them), a return and a trap end the function. -/
def flagSuccs : BlockExit → List Nat
  | .goto t => [t]
  | .branch _ _ y n => [y, n]
  | _ => []

/-- The flag reads of a walk, for the live flags: the flags of its start that its accesses, its exit and its registers read
(`always`), and each flag that it changes with the flags of its start that the value reads (`through`). The fixpoint
reads these lists, not the expressions of the walk: `flagReads` of an expression runs once for each walk, not once for each
pass and each predecessor. -/
structure FlagUse where
  always : List Flag
  through : List (Flag × List Flag)

/-- The flag reads of the walk `w`. -/
def FlagUse.ofWalk (w : Walk) : FlagUse :=
  { always := ((w.accesses.toList.flatMap MemAccess.exprs) ++ w.exit.reads ++ w.regs.toList.map (·.2)).flatMap
      (flagReads w.start),
    through := w.flags.toList.map fun (f, v) => (f, flagReads w.start v) }

/-- The flags at the start of the walk that a later block reads, when `live` is live at its end: the flag inputs of
`Walk.diff live` and the live flags that the walk does not change. -/
def FlagUse.liveIn (u : FlagUse) (live : List Flag) : List Flag :=
  u.always ++ ((u.through.filter fun (f, _) => live.contains f).flatMap (·.2)) ++
    live.filter fun f => !u.through.any (·.1 == f)

/-- `f` applied up to `n` times from `a`, until a value is a fixpoint. -/
def iterateFix {α : Type} [BEq α] (f : α → α) : Nat → α → α
  | 0, a => a
  | n + 1, a => let b := f a; if b == a then a else iterateFix f n b

/-- The live flags at the end of each walk (keyed by its PC): the least fixpoint of `liveIn` over the successors. -/
def liveFlags (ws : List (Nat × Walk)) : List (Nat × List Flag) :=
  let us := ws.map fun (pc, w) => (pc, flagSuccs w.exit, FlagUse.ofWalk w)
  let pass (live : List (Nat × List Flag)) : List (Nat × List Flag) :=
    us.map fun (pc, succs, _) =>
      let out := succs.flatMap fun s =>
        match us.find? (·.1 == s) with
        | some (_, _, u) => u.liveIn ((live.lookup s).getD [])
        | none => []
      (pc, Flag.all.filter out.contains)
  -- each pass that changes the map adds a flag, and there are at most `6 · ws.length` of them
  iterateFix pass (6 * ws.length + 1) (ws.map fun (pc, _) => (pc, []))

/-! ## Parts -/

/-- The text of a list of flags. -/
private def flagsText (fs : List Flag) : String := ", ".intercalate (fs.map (·.name))

/-- A sum `a + c` with `rsp` in `a` and a literal `c` of 2^63 or more as the difference `a - (2^64 - c)` (`rsp - 8`, the
form of the table and of the composed terms of `lift_block_split`); a literal of a sum last (`rsp + 8`, not `8 + rsp`: the
frame rules of `Frame.lean` read `rsp` plus a constant); the parts of a sum or a difference, in the same form. A sum with no
`rsp` keeps its literal: a value of a register is not rewritten by its sign. -/
def subForm : Val → Val
  | .add a (.lit c) | .add (.lit c) a =>
    if c.toNat ≥ 2 ^ 63 && a.usesRsp then .sub (subForm a) (.lit (0 - c)) else .add (subForm a) (.lit c)
  | .add a b => .add (subForm a) (subForm b)
  | .sub a b => .sub (subForm a) (subForm b)
  | v => v

/-- The accesses with their addresses and stored values in `subForm`. -/
private def accessSubForm : Access → Access
  | .load k a w => .load k (subForm a) w
  | .store k a w v => .store k (subForm a) w (subForm v)

/-- The flags that the exits of `decompiles_l2` keep (L2-FLAGS). -/
def keptFlags : List Flag := [.cf, .zf, .sf, .of]

/-- The live flags `live` at the end of the walk `w`, each with its value at the exit as a condition of the block start:
the read of the value of the walk, or `.flag f` when the block does not change `f`. -/
def liveValues (w : Walk) (live : List Flag) : Except String (List (Flag × Cond)) :=
  live.mapM fun f => do
    unless keptFlags.contains f do throw s!"a live flag {f.name}: the exits keep only cf, zf, sf and of (L2-FLAGS)"
    match w.flags.find? (·.1 == f) with
    | none => pure (f, Cond.flag f)
    | some (_, e) =>
      match readBool (ReadCtx.ofWalk w) e with
      | .ok c => pure (f, c)
      | .error e => throw s!"the value of the live flag {f.name}: the reader: {repr e}"

/-- The part of the raw block `b` of the function at `base` from its walk `w`, with the live flags `live` at its end.
`kept`: the block is not the entry, a goto or a branch reaches it and no call returns to it, so the exits of the blocks
before it keep its flag inputs. -/
def partOf (code : Executable) (base : Nat) (b : RawBlock) (w : Walk) (live : List Flag) (kept : Bool) :
    Except GenError Part := do
  let err (what : String) : GenError := .derive b.offset what
  let d := w.diff live
  unless kept || d.inputs.isEmpty do
    throw (err s!"a flag input {flagsText d.inputs.toList} at the start of the entry or of the return of a call (D43): no block keeps the flags for it")
  let flags ← (liveValues w live).mapError err
  let rb ← (readWalk base w).mapError fun e => err s!"the reader: {repr e}"
  let term ← match rb.exit with
    | .goto t => pure (Term.exit (.goto t))
    | .branch c y n => pure (.branch c (.goto y) (.goto n))
    | .call callee cont =>
      match callLabel b with
      | none => throw (err "a call with no label")
      | some l =>
        if labelAddr code l == some callee then pure (.exit (.call l cont))
        else throw (err s!"the call goes to {callee}, which is not the address of {l}")
    | .ret => pure (.exit .ret)
    | .trap => pure (.exit .trap)
    | .indirect v => throw (err s!"an indirect exit to {v.show}")
  pure ⟨b.offset, rb.accesses.map accessSubForm, rb.regs.map fun (r, v) => (r, subForm v), term, flags⟩

/-- The error of a block that passes a limit: it names the block by its label and the limit. -/
def limitError (b : RawBlock) (l : Limit) : GenError :=
  .derive b.offset s!"the block {b.name.s} passes a limit: {repr l}"

/-- The error of a block term. -/
def blockError (b : RawBlock) : BlockError → GenError
  | .notFinished _ c => .derive b.offset s!"the derived term is not finished: {c}"
  | .limit _ l => limitError b l
  | .failed _ msg => .derive b.offset s!"the derived term: {msg}"

/-- The walk of the raw block `b` of the function at `base`. The block has the whole `maxHeartbeats` budget for its term
and its walk, not the rest of the budget of the command. A block that passes a limit, in its term or in its walk, is the
error of the block (`limitError`); another exception is an error of the block too. -/
def blockWalk (step : Name) (ctx : Simp.Context) (base : Nat) (b : RawBlock) : TermElabM (Except GenError Walk) :=
  withCurrHeartbeats do
    let core ← readThe Core.Context
    tryCatchRuntimeEx
      (do match ← blockTerm step ctx (base + b.offset) b.sites.length with
          | .error e => pure (.error (blockError b e))
          | .ok t =>
            match ← walkTerm ctx t with
            | .error e => pure (.error (.derive b.offset s!"the walk: {repr e}"))
            | .ok w => pure (.ok w))
      fun ex => do
      if ex.isMaxRecDepth then pure (.error (limitError b (.maxRecDepth core.maxRecDepth)))
      else if ex.isMaxHeartbeat then pure (.error (limitError b (.maxHeartbeats (core.maxHeartbeats / 1000))))
      else pure (.error (.derive b.offset s!"the walk: {← ex.toMessageData.toString}"))

/-- The parts of the raw blocks `raws` of the function at `base`, with the simp set `ctx` (`blockContext`). -/
def partsWith (step : Name) (ctx : Simp.Context) (code : Executable) (base : Nat) (raws : List RawBlock) :
    TermElabM (List (Nat × Except GenError Part)) := do
  let walks ← raws.mapM fun b => return (b, ← blockWalk step ctx base b)
  let ws := walks.filterMap fun (b, r) => r.toOption.map (base + b.offset, ·)
  let live := liveFlags ws
  -- the PCs that a goto or a branch reaches, and the PCs that a call returns to
  let reached := ws.flatMap fun (_, w) => flagSuccs w.exit
  let conts := ws.filterMap fun (_, w) => match w.exit with | .call _ c => some c | _ => none
  pure (walks.map fun (b, r) =>
    let pc := base + b.offset
    let kept := b.offset != 0 && reached.contains pc && !conts.contains pc
    (b.offset, r >>= fun w => partOf code base b w ((live.lookup pc).getD []) kept))

/-- The raw blocks of the function `fn` of `code` and its address. -/
def rawsOf (code : Executable) (fn : String) : Except GenError (List RawBlock × Nat) := do
  let raws ← split (← sites code fn) (← labels code fn)
  let some base := labelAddr code fn | throw (.noFunction fn)
  pure (raws, base)

/-- The parts of the function `fn` of `code` for the L1 step `step`. The site equations are theorems `pfx.site<addr>`.
A function that `split` refuses has no part (`generate` gives the error of `split`). The simp set has the whole
`maxHeartbeats` budget, as each site and each block has; when it fails (also at a limit), each block has its message. -/
def deriveFn (step pfx : Name) (code : Executable) (fn : String) : TermElabM (List (Nat × Except GenError Part)) := do
  let .ok (raws, base) := rawsOf code fn | return []
  let eqs ← siteEqs step pfx (raws.flatMap fun b => b.sites.map (base + ·.offset))
  let ctx : Except String Simp.Context ← withCurrHeartbeats <|
    tryCatchRuntimeEx (Except.ok <$> blockContext (eqs.filterMap (·.toOption)))
      fun ex => Except.error <$> ex.toMessageData.toString
  match ctx with
  | .ok ctx => partsWith step ctx code base raws
  | .error msg => return raws.map fun b => (b.offset, .error (.derive b.offset s!"the simp set of the function: {msg}"))

/-! ## The cross-check with the table -/

/-- The value of `r` in a list of changed registers; the start value when the list does not have `r`. -/
private def regVal (rs : List (Reg64 × Val)) (r : Reg64) : Val := ((rs.find? (·.1 == r)).map (·.2)).getD (.reg r)

/-- The first difference of the derived part `p` and the table block `t` (`symBlock`), or `none`: the accesses (kind,
number, width, and the normal forms of the address and of the stored value), each register that one of them lists (the
normal forms; the start value when the other does not list it), and the exit (the targets; a branch condition up to the
normal form, negated when the targets are swapped). -/
def _root_.Skel.Gen.Part.differs (p : Part) (t : Block) : Option String := Id.run do
  if p.accesses.length != t.accesses.length then
    return some s!"{p.accesses.length} accesses, the table has {t.accesses.length}"
  for (i, a, b) in (p.accesses.zip t.accesses).zipIdx.map fun ((a, b), i) => (i, a, b) do
    match a, b with
    | .load k x w, .load k' y w' =>
      if k != k' || w != w' || !x.sameNorm y then return some s!"access {i}: load {x.show}, table {y.show}"
    | .store k x w v, .store k' y w' u =>
      if k != k' || w != w' || !x.sameNorm y || !v.sameNorm u then
        return some s!"access {i}: store {v.show} at {x.show}, table {u.show} at {y.show}"
    | _, _ => return some s!"access {i}: a load and a store"
  for r in allRegs do
    if p.regs.any (·.1 == r) || t.regs.any (·.1 == r) then
      let x := regVal p.regs r
      let y := regVal t.regs r
      unless x.sameNorm y do return some s!"register {repr r}: {x.show}, table {y.show}"
  match p.term, t.term with
  | .exit (.goto a), .exit (.goto b) => if a != b then return some s!"goto {a}, table goto {b}"
  | .exit .ret, .exit .ret | .exit .trap, .exit .trap => pure ()
  | .exit (.call f c), .exit (.call g c') => if f != g || c != c' then return some s!"call {f} {c}, table call {g} {c'}"
  | .branch c (.goto y) (.goto n), .branch tc (.goto a) (.goto b) =>
    if y == a && n == b then
      unless c.sameNorm tc do return some s!"condition {c.show}, table {tc.show}"
    else if y == b && n == a then
      unless c.sameNorm (.not tc) do return some s!"condition {c.show}, table ¬{tc.show}"
    else return some s!"branch to {y}, {n}, table {a}, {b}"
  | _, _ => return some "the exits differ in kind"
  return none

/-! ## The definition -/

deriving instance ToExpr for Reg64
deriving instance ToExpr for Width
deriving instance ToExpr for Skel.Gen.Flag
deriving instance ToExpr for Skel.Gen.Narrow
deriving instance ToExpr for GenError

mutual
/-- The term of a value. -/
def valExpr : Val → Expr
  | .reg r => mkApp (mkConst ``Val.reg) (toExpr r)
  | .lit n => mkApp (mkConst ``Val.lit) (toExpr n)
  | .load k => mkApp (mkConst ``Val.load) (toExpr k)
  | .retAddr o => mkApp (mkConst ``Val.retAddr) (toExpr o)
  | .add a b => mkApp2 (mkConst ``Val.add) (valExpr a) (valExpr b)
  | .sub a b => mkApp2 (mkConst ``Val.sub) (valExpr a) (valExpr b)
  | .mul a b => mkApp2 (mkConst ``Val.mul) (valExpr a) (valExpr b)
  | .shr a k => mkApp2 (mkConst ``Val.shr) (valExpr a) (toExpr k)
  | .zext32 a => mkApp (mkConst ``Val.zext32) (valExpr a)
  | .ite c a b => mkApp3 (mkConst ``Val.ite) (condExpr c) (valExpr a) (valExpr b)
  | .and a b => mkApp2 (mkConst ``Val.and) (valExpr a) (valExpr b)
  | .or a b => mkApp2 (mkConst ``Val.or) (valExpr a) (valExpr b)
  | .xor a b => mkApp2 (mkConst ``Val.xor) (valExpr a) (valExpr b)
  | .not a => mkApp (mkConst ``Val.not) (valExpr a)
  | .neg a => mkApp (mkConst ``Val.neg) (valExpr a)
  | .shl a k => mkApp2 (mkConst ``Val.shl) (valExpr a) (toExpr k)
  | .extract lo len a _ =>
    -- the proof of `lo + len ≤ 64`: `Nat.le_of_ble_eq_true rfl`
    let sum := mkApp2 (mkConst ``Nat.add) (toExpr lo) (toExpr len)
    let h := mkApp3 (mkConst ``Nat.le_of_ble_eq_true) sum (toExpr (64 : Nat))
      (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
    mkApp4 (mkConst ``Val.extract) (toExpr lo) (toExpr len) (valExpr a) h
  | .zext w a => mkApp2 (mkConst ``Val.zext) (toExpr w) (valExpr a)
  | .sext w a => mkApp2 (mkConst ``Val.sext) (toExpr w) (valExpr a)
  | .replaceLow w a b => mkApp3 (mkConst ``Val.replaceLow) (toExpr w) (valExpr a) (valExpr b)
  | .setcc c => mkApp (mkConst ``Val.setcc) (condExpr c)

/-- The term of a condition. -/
def condExpr : Cond → Expr
  | .eq a b => mkApp2 (mkConst ``Cond.eq) (valExpr a) (valExpr b)
  | .ule a b => mkApp2 (mkConst ``Cond.ule) (valExpr a) (valExpr b)
  | .ult a b => mkApp2 (mkConst ``Cond.ult) (valExpr a) (valExpr b)
  | .slt a b => mkApp2 (mkConst ``Cond.slt) (valExpr a) (valExpr b)
  | .slt32 a b => mkApp2 (mkConst ``Cond.slt32) (valExpr a) (valExpr b)
  | .not c => mkApp (mkConst ``Cond.not) (condExpr c)
  | .iff p q => mkApp2 (mkConst ``Cond.iff) (condExpr p) (condExpr q)
  | .flag f => mkApp (mkConst ``Cond.flag) (toExpr f)
end

instance : ToExpr Val := ⟨valExpr, mkConst ``Val⟩
instance : ToExpr Cond := ⟨condExpr, mkConst ``Cond⟩

deriving instance ToExpr for Access
deriving instance ToExpr for Exit
deriving instance ToExpr for Term
deriving instance ToExpr for Part

instance {ε α : Type} [ToExpr ε] [ToExpr α] : ToExpr (Except ε α) where
  toExpr
    | .ok a => mkApp3 (mkConst ``Except.ok [0, 0]) (toTypeExpr ε) (toTypeExpr α) (toExpr a)
    | .error e => mkApp3 (mkConst ``Except.error [0, 0]) (toTypeExpr ε) (toTypeExpr α) (toExpr e)
  toTypeExpr := mkApp2 (mkConst ``Except [0, 0]) (toTypeExpr ε) (toTypeExpr α)

/-- `#derive_blocks name step code ["fn", …]`: defines `name : Derived`, the parts of the functions of `code` (a
constant) for the L1 step `step`. -/
syntax (name := deriveBlocks) "#derive_blocks " ident ident ident " [" str,* "]" : command

private unsafe def evalCodeUnsafe (n : Name) : TermElabM Executable := evalConst Executable n

@[implemented_by evalCodeUnsafe] private opaque evalCode (n : Name) : TermElabM Executable

open Command in
@[command_elab deriveBlocks] def elabDeriveBlocks : CommandElab
  | `(#derive_blocks $name $step $code [$fns,*]) => do
    let declName := (← getCurrNamespace) ++ name.getId
    liftTermElabM do
      let step ← realizeGlobalConstNoOverloadWithInfo step
      let code ← evalCode (← realizeGlobalConstNoOverloadWithInfo code)
      let items ← fns.getElems.toList.mapM fun fn => do
        pure (fn.getString, ← deriveFn step (declName ++ `site) code fn.getString)
      let value := toExpr items
      let ty := Lean.mkConst ``Derived
      -- the definition has the whole budget, as each site and each block has
      withCurrHeartbeats <| addAndCompile (.defnDecl (mkDefinitionValEx declName [] ty value .opaque .safe []))
  | _ => throwUnsupportedSyntax

end Skel.Gen.Derive
