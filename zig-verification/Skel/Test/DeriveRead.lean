import Skel.Gen.Derive.Read
import Skel.Test.DeriveWalk

/-! The tests of `Skel/Gen/Derive/Read.lean` (tasks N7 and N10 of `docs/research/symexec-pilot-20261118.md`, section 5).
The module is checked by `lake build Skel.Test.DeriveRead`: each `#eval` throws when a check fails. No `set_option`
changes a limit.

The table check: on the 73 table blocks (25 pilot, 48 level 2), the read block against the table block (`symBlock`).
For each register that the walk changes or that the table lists, the read value and the table value (the start value
when one side does not list the register) have the same normal form (`Val.norm`). For each access: the kind, the number,
the width, and the normal forms of the address and of the stored value. The exit: the targets, and for a branch the
condition (`Cond.norm`; the negation of the table condition when the targets are swapped).

The conditions: the 25 pilot and 29 level 2 branch conditions (E2, section 2; E1, section 4) are each read. The blocks:
`readWalk` reads 49 of 49 pilot blocks and 79 of 79 level 2 blocks (NB: the two borrow forms of `sbb`); no head is refused.

The meaning: on each read block, the raw terms of the walk (the register values, the addresses, the stored values and the
branch condition) are compiled and run on random start states (registers, flags, load values), and compared with the
value of the read `Val` and `Cond` (the oracle `evalV`, written here from the `UInt64` operations). This checks the
reader, the lemma forms that it applies and the normal form against the Kraken semantics. -/

open Lean Meta Elab Term Skel.Gen Skel.Gen.Derive DeriveSiteTests DeriveRunTests DeriveWalkTests

namespace DeriveReadTests

/-- The value of `r` in a list of changed registers; the start value when the list does not have `r`. -/
def regVal (rs : List (Reg64 × Val)) (r : Reg64) : Val := ((rs.find? (·.1 == r)).map (·.2)).getD (.reg r)

/-- One compared item: its name, the read value and the table value. -/
abbrev Item := String × Val × Val

/-- The items of a read block and its table block: the registers that one of them lists, then for each access its
address and its stored value. `none` when the accesses differ in number, kind, load or store number, or width. -/
def items (b : ReadBlock) (t : Block) : Option (List Item) := do
  let regs := allRegs.filter fun r => b.regs.any (·.1 == r) || t.regs.any (·.1 == r)
  let regItems : List Item := regs.map fun r => (s!"reg {repr r}", regVal b.regs r, regVal t.regs r)
  guard (b.accesses.length == t.accesses.length)
  let accItems ← (b.accesses.zip t.accesses).mapM fun
    | (.load k x w, .load k' y w') => if k == k' && w == w' then some [(s!"load {k} address", x, y)] else none
    | (.store k x w v, .store k' y w' u) =>
      if k == k' && w == w' then some [(s!"store {k} address", x, y), (s!"store {k} value", v, u)] else none
    | _ => none
  pure (regItems ++ accItems.flatten)

/-- The exit of the read block against the exit of the table block (a branch: the targets as a set). -/
def exitAgrees (e : ReadExit) (t : Skel.Gen.Term) : Bool :=
  match e, t with
  | .goto p, .exit (.goto x) => p == x
  | .ret, .exit .ret => true
  | .trap, .exit .trap => true
  | .call _ c, .exit (.call _ c') => c == c'
  | .branch _ y n, .branch _ (.goto a) (.goto b) => (y == a && n == b) || (y == b && n == a)
  | _, _ => false

/-- The condition of the table for the targets of the read branch: the table condition when the `yes` targets agree,
its negation when they are swapped. -/
def tableCond (e : ReadExit) (t : Skel.Gen.Term) : Option (Cond × Cond) :=
  match e, t with
  | .branch c y _, .branch tc (.goto a) _ => some (c, if y == a then tc else .not tc)
  | _, _ => none

/-- The counts of a table comparison. -/
structure Counts where
  blocks : Nat := 0
  items : Nat := 0
  syntactic : Nat := 0
  normal : Nat := 0
  conds : Nat := 0
  condSyntactic : Nat := 0
  differ : List String := []

/-- The table comparison of the walks `ws` (the functions at their `base`). -/
def compare (ws : List (Spec × Walk)) : Except String Counts := do
  let mut c : Counts := {}
  for (s, w) in ws do
    let some t := s.table | continue
    let base := s.pc - t.offset
    let b ← match readWalk base w with
      | .ok b => pure b
      | .error e => throw s!"{name s}: read error {repr e}"
    let some its := items b t | throw s!"{name s}: the accesses differ from the table"
    unless exitAgrees b.exit t.term do throw s!"{name s}: the exit differs from the table"
    c := { c with blocks := c.blocks + 1, items := c.items + its.length }
    for (what, x, y) in its do
      if x.show == y.show then c := { c with syntactic := c.syntactic + 1 }
      else if x.sameNorm y then c := { c with normal := c.normal + 1 }
      else c := { c with differ := c.differ ++ [s!"{name s} {what}: read {x.show}, table {y.show}"] }
    if let some (rc, tc) := tableCond b.exit t.term then
      c := { c with conds := c.conds + 1 }
      if rc.show == tc.show then c := { c with condSyntactic := c.condSyntactic + 1 }
      else unless rc.sameNorm tc do
        c := { c with differ := c.differ ++ [s!"{name s} condition: read {rc.show}, table {tc.show}"] }
  pure c

/-- The values of a walk: the changed registers, the addresses and the stored values. -/
def values (w : Walk) : List (Bool × Expr) :=
  (w.regs.toList.map fun (_, v) => (false, v)) ++ w.accesses.toList.flatMap fun
    | .load a _ _ _ => [(true, a)]
    | .store a _ v _ _ => [(true, a), (false, v)]

/-- The refused heads of the walks: for each head, the number of values and the number of blocks. A value is a
register, an address, a stored value or a branch condition. Other errors are listed by their `repr`. -/
def refused (ws : List (Spec × Walk)) : List (Name × Nat × Nat) × List String := Id.run do
  let mut heads : List (Name × Nat × Nat) := []
  let mut others : List String := []
  for (s, w) in ws do
    let cx := ReadCtx.ofWalk w
    let mut seen : List Name := []
    let conds : List (Except ReadError Unit) := match w.exit with
      | .branch c _ _ _ => [(readCond cx c).map fun _ => ()]
      | _ => []
    let vals := (values w).map fun (isAddr, e) => (if isAddr then readAddr cx e else readVal cx e).map fun _ => ()
    for r in vals ++ conds do
      match r with
      | .ok _ => pure ()
      | .error (.unsupported h) =>
        let first := !seen.contains h
        seen := if first then h :: seen else seen
        heads := match heads.find? (·.1 == h) with
          | some _ => heads.map fun (h', v, b) => if h' == h then (h', v + 1, if first then b + 1 else b) else (h', v, b)
          | none => heads ++ [(h, 1, 1)]
      | .error e => others := others ++ [s!"{name s}: {repr e}"]
  pure (heads, others)

def showHeads (hs : List (Name × Nat × Nat)) : String :=
  ", ".intercalate (hs.map fun (h, v, b) => s!"{h} {v} values in {b} blocks")

/-- The start of the function of a block. -/
def baseOf (fns : List (String × Nat)) (s : Spec) : Nat := ((fns.find? (·.1 == s.fn)).map (·.2)).getD 0

/-- The names of the walks that `readWalk` does not read, with the error. -/
def notWhole (fns : List (String × Nat)) (ws : List (Spec × Walk)) : List String :=
  ws.filterMap fun (s, w) => match readWalk (baseOf fns s) w with
    | .ok _ => none
    | .error e => some s!"{name s}: {repr e}"

/-- The branch conditions of the walks, each read: the name of the block and the result. -/
def branchConds (ws : List (Spec × Walk)) : List (String × Except ReadError Cond) :=
  ws.filterMap fun (s, w) => match w.exit with
    | .branch c _ _ _ => some (name s, readCond (ReadCtx.ofWalk w) c)
    | _ => none

mutual
/-- The flags that a value reads. -/
def valFlags : Val → List Flag
  | .reg _ | .lit _ | .load _ | .retAddr _ => []
  | .add a b | .sub a b | .mul a b | .and a b | .or a b | .xor a b | .replaceLow _ a b => valFlags a ++ valFlags b
  | .shr a _ | .zext32 a | .not a | .neg a | .shl a _ | .extract _ _ a _ | .zext _ a | .sext _ a => valFlags a
  | .setcc c => condFlags c
  | .ite c a b => condFlags c ++ valFlags a ++ valFlags b

/-- The flags that a condition reads. -/
def condFlags : Cond → List Flag
  | .eq a b | .ule a b | .ult a b | .slt a b | .slt32 a b => valFlags a ++ valFlags b
  | .not c => condFlags c
  | .iff p q => condFlags p ++ condFlags q
  | .flag f => [f]
end

end DeriveReadTests

open DeriveReadTests

/-! ## The table: 25 pilot and 48 level 2 blocks -/

/- The refused heads (a value is one register, address, stored value or branch condition; a block counts once for each
head): none. Before NB, level 2 had `Int` in `l2Arith` entry and `l2TwoLoops` o9: the borrow of `cmpl $1` of a 32-bit sum
and the borrow of `cmpb $1` of a byte load, each read by `sbb` as a value (`nocarry32_lit_iff_le` and
`nocarry8_load_lit_iff_le` of `Lift/Tactic/Cond.lean` have these forms). -/

#eval show TermElabM Unit from do
  let ws ← walkAll pilotStep `Skel.Test.DeriveRead.l3 pilotSpecs
  let c ← match compare ws with
    | .ok c => pure c
    | .error e => throwError e
  logInfo m!"pilot: {c.blocks} table blocks, {c.items} items: {c.syntactic} the same, {c.normal} the same normal form; {c.conds} conditions, {c.condSyntactic} the same; {c.differ.length} different {c.differ}"
  check (c.blocks == 25) s!"25 pilot table blocks, got {c.blocks}"
  check c.differ.isEmpty s!"pilot: values that differ from the table: {c.differ}"
  check (c.items == 70 && c.syntactic == 58 && c.normal == 12) "pilot: 70 items, 58 the same, 12 the same normal form"
  check (c.conds == 7) s!"pilot: 7 table conditions, got {c.conds}"
  let (hs, others) := refused ws
  logInfo m!"pilot refused heads (49 blocks): {showHeads hs}; other errors: {others}; not read: {notWhole pilotFns ws}"
  check others.isEmpty s!"pilot: errors that are not a refused head: {others}"
  check hs.isEmpty s!"pilot: the refused heads {showHeads hs}"
  check (notWhole pilotFns ws).isEmpty "pilot: 49 of 49 blocks read whole"

#eval show TermElabM Unit from do
  let ws ← walkAll level2Step `Skel.Test.DeriveRead.l2 level2Specs
  let c ← match compare ws with
    | .ok c => pure c
    | .error e => throwError e
  logInfo m!"level 2: {c.blocks} table blocks, {c.items} items: {c.syntactic} the same, {c.normal} the same normal form; {c.conds} conditions, {c.condSyntactic} the same; {c.differ.length} different {c.differ}"
  check (c.blocks == 48) s!"48 level 2 table blocks, got {c.blocks}"
  check c.differ.isEmpty s!"level 2: values that differ from the table: {c.differ}"
  check (c.items == 173 && c.syntactic == 128 && c.normal == 45) "level 2: 173 items, 128 the same, 45 the same normal form"
  check (c.conds == 8) s!"level 2: 8 table conditions, got {c.conds}"
  let (hs, others) := refused ws
  let rest := notWhole level2Fns ws
  logInfo m!"level 2 refused heads (79 blocks): {showHeads hs}; other errors: {others}; not read: {rest}"
  check others.isEmpty s!"level 2: errors that are not a refused head: {others}"
  check hs.isEmpty s!"level 2: the refused heads {showHeads hs}"
  check (ws.length == 79) s!"level 2: 79 blocks, got {ws.length}"
  check rest.isEmpty s!"level 2: 79 of 79 blocks read whole, not read: {rest}"

/-! ## The branch conditions: 25 pilot, 29 level 2 -/

#eval show TermElabM Unit from do
  let pilot := branchConds (← walkAll pilotStep `Skel.Test.DeriveRead.c3 pilotSpecs)
  let level2 := branchConds (← walkAll level2Step `Skel.Test.DeriveRead.c2 level2Specs)
  for (what, cs) in [("pilot", pilot), ("level 2", level2)] do
    let shown := cs.map fun (n, r) => match r with | .ok c => s!"{n}: {c.show}" | .error e => s!"{n}: {repr e}"
    logInfo m!"{what}: {cs.length} branch conditions\n{"\n".intercalate shown}"
    for (n, r) in cs do check r.toBool s!"{what} {n}: the condition is not read"
  check (pilot.length == 25) s!"25 pilot conditions, got {pilot.length}"
  check (level2.length == 29) s!"29 level 2 conditions, got {level2.length}"
  -- one form of each family (E2, section 2; E1, section 4)
  let shows := (pilot ++ level2).filterMap fun (n, r) => r.toOption.map fun c => (n, c.show)
  let has (n s : String) : Bool := shows.contains (n, s)
  check (has ".Lshuffler.Emission.pop o14" "(10240 ≤ load0)") "the literal borrow"
  check (has ".Lshuffler.MappingBuilder.closestCopy LBB29_7" "(load0 ≤ Reg64.r9)") "the borrow of two values"
  check (has "l2Field entry" "(7 < Reg64.rsi)") "the literal ja"
  check (has "l2Exit3 o17" "(Reg64.rcx < Reg64.rax)") "the ja of two registers"
  check (has ".Lshuffler.SpillSet.add o15" "((Reg64.rsi &&& 280375465082880) = 0)") "the mask"
  check (has ".Lshuffler.MappingBuilder.closestCopy o51"
    "((load2 &&& 281474976710655) = (load3 &&& 281474976710655))") "the shifted xor"
  check (has ".Lshuffler.SpillSet.add entry" "((zext8 (Reg64.rsi >>> 32)) = 0)") "the byte of a shift"
  check (has ".Lshuffler.MappingBuilder.mapInPlace o88" "((zext16 Reg64.rax) = 0)") "the 16-bit test"
  check (has ".Lshuffler.SpillSet.add o30" "(load1 = 0)") "a byte load"
  check (has ".Lshuffler.MappingBuilder.closestCopy o114" "(((load0 <<< 32) = Reg64.r10) ↔ ¬((zext8 Reg64.rdx) = 0))")
    "the setcc xor"
  check (has "l2Narrow o10" "(load0 = load1)") "the cmpl of two 32-bit loads"
  check (has "l2Bits o11"
    "(2 ≤ (zext8 ((zext8 Reg64.rax) - 1)))") "the 8-bit borrow after decb: the low byte of the decb result"
  check (has ".Lshuffler.MappingBuilder.closestCopy o156"
    "((if (Reg64.rsi ≤ Reg64.rax) then (Reg64.rax - Reg64.rsi) else (Reg64.rsi - Reg64.rax)) < (if (Reg64.r9 ≤ Reg64.rsi) then Reg64.r11 else (Reg64.r8 + Reg64.r9)))")
    "the ja over two cmov results"

/-! ## The flag input of `l2Flags` LBB0_1

`cmovb` at the start of LBB0_1 reads the carry of the `cmpq` of `entry` (decision D43): the read value of `rax` has the
flag input `Cond.flag .cf`, and no other block reads a flag of its start. -/

#eval show TermElabM Unit from do
  let ws ← walkAll level2Step `Skel.Test.DeriveRead.f2 level2Specs
  let pilot ← walkAll pilotStep `Skel.Test.DeriveRead.f3 pilotSpecs
  let mut withFlag : List String := []
  for (fns, ws) in [(level2Fns, ws), (pilotFns, pilot)] do
    for (s, w) in ws do
      let .ok b := readWalk (baseOf fns s) w | continue
      let fs := b.regs.flatMap (valFlags ·.2) ++ (b.accesses.flatMap fun
        | .load _ a _ => valFlags a | .store _ a _ v => valFlags a ++ valFlags v) ++
        (match b.exit with | .branch c _ _ => condFlags c | _ => [])
      unless fs.isEmpty do withFlag := withFlag ++ [s!"{name s}: {repr fs.eraseDups}"]
  logInfo m!"blocks with a flag input: {withFlag}"
  check (withFlag == ["l2Flags LBB0_1: [Skel.Gen.Flag.cf]"]) s!"the flag inputs: {withFlag}"
  let some (_, lbb1) := ws.find? fun (s, _) => s.fn == "l2Flags" && s.name == "LBB0_1" | throwError "no l2Flags LBB0_1"
  let .ok b := readWalk 0 lbb1 | throwError "LBB0_1 is not read"
  let rax := regVal b.regs .rax
  check ((valFlags rax).contains .cf) s!"rax of LBB0_1 reads the flag cf: {rax.show}"
  check ((rax.show.splitOn "(if flag cf then").length > 1) "the cmovb is an ite of the flag cf"

/-! ## The meaning of the read values

A start state is a list of 16 register values, 6 flags and the load values (each below `2^w` for a load of `w` bits). The
raw terms of a walk are compiled once for each block (`evalExpr`), with the start `d` replaced by the state of these
values and each load value by its number. The oracle `evalV` gives the value of the read `Val` for the same state; a
load is its value zero-extended. -/

namespace DeriveReadTests

/-- A start state: the registers (in the order of `allRegs`), the flags (in the order of `Flag.all`) and the load values
(zero-extended). -/
structure Env where
  regs : Array UInt64
  flags : Array Bool
  loads : Array UInt64

def Env.reg (e : Env) (r : Reg64) : UInt64 := e.regs[allRegs.idxOf r]!
def Env.flag (e : Env) (f : Flag) : Bool := e.flags[Flag.all.idxOf f]!

private def lowNat (bits : Nat) (n : UInt64) : UInt64 := UInt64.ofNat (n.toNat % 2 ^ bits)

mutual
/-- The value of `v` in the state `env` (from the `UInt64` operations); `none` for a return address. -/
def evalV (env : Env) : Val → Option UInt64
  | .reg r => some (env.reg r)
  | .lit n => some n
  | .load k => env.loads[k]?
  | .retAddr _ => none
  | .add a b => do pure ((← evalV env a) + (← evalV env b))
  | .sub a b => do pure ((← evalV env a) - (← evalV env b))
  | .mul a b => do pure ((← evalV env a) * (← evalV env b))
  | .shr a k => do pure ((← evalV env a) >>> UInt64.ofNat k.val)
  | .shl a k => do pure ((← evalV env a) <<< UInt64.ofNat k.val)
  | .zext32 a => do pure (lowNat 32 (← evalV env a))
  | .and a b => do pure ((← evalV env a) &&& (← evalV env b))
  | .or a b => do pure ((← evalV env a) ||| (← evalV env b))
  | .xor a b => do pure ((← evalV env a) ^^^ (← evalV env b))
  | .not a => do pure (~~~ (← evalV env a))
  | .neg a => do pure (0 - (← evalV env a))
  | .extract lo len a _ => do pure (UInt64.ofNat (((← evalV env a).toNat >>> lo) % 2 ^ len))
  | .zext w a => do pure (lowNat w.bits (← evalV env a))
  | .sext w a => do pure (UInt64.ofBitVec ((BitVec.ofNat w.bits (← evalV env a).toNat).signExtend 64))
  | .replaceLow .b32 _ b => do pure (lowNat 32 (← evalV env b))
  | .replaceLow w a b => do
    let m := 2 ^ w.bits
    pure (UInt64.ofNat ((← evalV env a).toNat / m * m + (← evalV env b).toNat % m))
  | .setcc c => do pure (if (← evalC env c) then 1 else 0)
  | .ite c a b => do if (← evalC env c) then evalV env a else evalV env b

/-- The value of `c` in the state `env`. -/
def evalC (env : Env) : Cond → Option Bool
  | .eq a b => do pure ((← evalV env a) == (← evalV env b))
  | .ule a b => do pure (decide ((← evalV env a) ≤ (← evalV env b)))
  | .ult a b => do pure (decide ((← evalV env a) < (← evalV env b)))
  | .slt a b => do pure (BitVec.slt (← evalV env a).toBitVec (← evalV env b).toBitVec)
  | .slt32 a b => do pure (BitVec.slt ((← evalV env a).toBitVec.truncate 32) ((← evalV env b).toBitVec.truncate 32))
  | .not c => do pure (!(← evalC env c))
  | .iff p q => do pure ((← evalC env p) == (← evalC env q))
  | .flag f => some (env.flag f)
end

/-- The start state of the arrays: the registers and the flags; the other fields are the defaults. -/
def mkData (r : Array UInt64) (f : Array Bool) : MachineData :=
  { regs := { rax := r[0]!, rbx := r[1]!, rcx := r[2]!, rdx := r[3]!, rsi := r[4]!, rdi := r[5]!, rsp := r[6]!,
              rbp := r[7]!, r8 := r[8]!, r9 := r[9]!, r10 := r[10]!, r11 := r[11]!, r12 := r[12]!, r13 := r[13]!,
              r14 := r[14]!, r15 := r[15]! },
    status := ⟨f[0]!, f[1]!, f[2]!, f[3]!, f[4]!, f[5]!⟩ }

/-- A raw term of a walk to compare: a `UInt64`, a `BitVec w` or a condition. -/
inductive Raw where
  | u64 (e : Expr)
  | bv (w : Nat) (e : Expr)
  | prop (e : Expr)

/-- The raw terms of a walk and the read items, in the same order: the changed registers, then each access (the address,
and the stored value), then the branch condition. -/
def rawItems (w : Walk) (b : ReadBlock) : List (Raw × Sum Val Cond) :=
  let regs := (w.regs.toList.zip b.regs).map fun ((_, e), (_, v)) => (Raw.u64 e, Sum.inl v)
  let accs := (w.accesses.toList.zip b.accesses).flatMap fun
    | (.load a _ _ _, .load _ x _) => [(Raw.bv 64 a, Sum.inl x)]
    | (.store a wd e _ _, .store _ x _ v) => [(Raw.bv 64 a, Sum.inl x), (Raw.bv wd.bits e, Sum.inl v)]
    | _ => []
  let cond := match w.exit, b.exit with
    | .branch c _ _ _, .branch rc _ _ => [(Raw.prop c, Sum.inr rc)]
    | _, _ => []
  regs ++ accs ++ cond

/-- The type `Array UInt64 → Array Bool → Array UInt64 → Array Nat`. -/
def evalType : MetaM Expr := do
  let arr (t : Expr) := mkApp (mkConst ``Array [.zero]) t
  mkArrow (arr (mkConst ``UInt64)) (← mkArrow (arr (mkConst ``Bool)) (← mkArrow (arr (mkConst ``UInt64))
    (arr (mkConst ``Nat))))

unsafe def evalRawUnsafe (e : Expr) : MetaM (Array UInt64 → Array Bool → Array UInt64 → Array Nat) := do
  evalExpr (Array UInt64 → Array Bool → Array UInt64 → Array Nat) (← evalType) e

@[implemented_by evalRawUnsafe]
opaque evalRaw (e : Expr) : MetaM (Array UInt64 → Array Bool → Array UInt64 → Array Nat)

/-- The compiled raw terms of the walk `w`: a function of the registers, the flags and the load values to the numbers of
the terms (a condition is 1 or 0). `none` when a term has a free variable that is not the start or a load value. -/
def compileRaw (w : Walk) (raws : List Raw) : MetaM (Option (Array UInt64 → Array Bool → Array UInt64 → Array Nat)) := do
  let arr (t : Expr) := mkApp (mkConst ``Array [.zero]) t
  withLocalDeclD `r (arr (mkConst ``UInt64)) fun r =>
  withLocalDeclD `f (arr (mkConst ``Bool)) fun f =>
  withLocalDeclD `l (arr (mkConst ``UInt64)) fun l => do
    let loads := w.accesses.toList.filterMap fun | .load _ wd _ v => some (v, wd) | .store .. => none
    let get (a : Expr) (i : Nat) : MetaM Expr := mkAppM ``getElem! #[a, mkNatLit i]
    let mut vals := #[mkApp2 (mkConst ``mkData) r f]
    for (i, (_, wd)) in loads.zipIdx.map (fun ((v, wd), i) => (i, (v, wd))) do
      let li ← get l i
      vals := vals.push (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit wd.bits) (mkApp (mkConst ``UInt64.toNat) li))
    let fvars := #[mkFVar w.start] ++ (loads.map fun (v, _) => mkFVar v).toArray
    let subst (e : Expr) : Expr := e.replaceFVars fvars vals
    let mut items : List Expr := []
    for x in raws do
      let it ← match x with
        | .u64 e => pure (mkApp (mkConst ``UInt64.toNat) (subst e))
        | .bv wd e => pure (mkApp2 (mkConst ``BitVec.toNat) (mkNatLit wd) (subst e))
        | .prop e => do pure (mkApp (mkConst ``Bool.toNat) (← mkDecide (subst e)))
      items := items ++ [it]
    let body ← mkArrayLit (mkConst ``Nat) items
    if body.hasAnyFVar (fun x => x != r.fvarId! && x != f.fvarId! && x != l.fvarId!) then return none
    some <$> evalRaw (← mkLambdaFVars #[r, f, l] body)

/-- A linear congruential generator. -/
def next (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- The values of the samples: the boundaries of the compares of the blocks, so that equal operands and the edges of
`≤` and `<` occur. -/
def pool : List Nat :=
  [0, 1, 2, 3, 6, 7, 8, 14, 15, 16, 0x7F, 0x80, 255, 256, 0x7FFF, 0x8000, 0xFFFF, 0x10000, 0x7FFFFFFF, 0x80000000,
   0xFFFFFFFF, 0x100000000, 0x100000001, 0x1000000000000, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 63 + 1, 2 ^ 64 - 2, 2 ^ 64 - 1]

/-- A number of the sample: from the pool or a random number, and the next seed. -/
def draw (s : Nat) : UInt64 × Nat :=
  let s := next s
  if (s / 7) % 2 == 0 then (UInt64.ofNat (pool.getD ((s / 31) % pool.length) 0), s) else (UInt64.ofNat (s / 3), s)

/-- A random start state with `nloads` load values of the widths `bits`, and the next seed. -/
def sample (bits : List Nat) (s : Nat) : Env × Array UInt64 × Nat := Id.run do
  let mut s := s
  let mut regs := #[]
  for _ in [:16] do
    let (v, s') := draw s
    regs := regs.push v
    s := s'
  let mut flags := #[]
  for _ in [:6] do
    s := next s
    flags := flags.push ((s / 11) % 2 == 0)
  let mut raw := #[]
  for _ in bits do
    let (v, s') := draw s
    raw := raw.push v
    s := s'
  let loads := (raw.toList.zip bits).map fun (v, b) => lowNat b v
  pure (⟨regs, flags, loads.toArray⟩, raw, s)

/-- The oracle value of an item: the number of a value, 1 or 0 for a condition; `none` for a return address. -/
def oracle (env : Env) : Sum Val Cond → Option Nat
  | .inl v => (evalV env v).map (·.toNat)
  | .inr c => (evalC env c).map fun b => if b then 1 else 0

/-- The disagreements (block, item, the sample) of the compiled raw terms `run` of the items `its` of the block `s` with
the read items on the states `states` (each with its raw load values), and the number of compared values. Each item is
also compared in its normal form. -/
def runStates (s : Spec) (its : List (Raw × Sum Val Cond))
    (run : Array UInt64 → Array Bool → Array UInt64 → Array Nat) (states : List (Env × Array UInt64)) :
    Nat × List String := Id.run do
  let mut compared := 0
  let mut bad : List String := []
  for (env, raw) in states do
    let got := run env.regs env.flags raw
    for ((_, it), i) in its.zipIdx do
      let normed : Sum Val Cond := match it with | .inl v => .inl v.norm | .inr c => .inr c.norm
      match oracle env it, oracle env normed with
      | some x, some y =>
        compared := compared + 1
        if got[i]? != some x || x != y then
          bad := bad ++ [s!"{name s} item {i}: raw {got[i]?}, read {x}, normal form {y}, regs {env.regs}, flags {env.flags}, loads {env.loads}"]
      | none, none => pure ()
      | _, _ => bad := bad ++ [s!"{name s} item {i}: the normal form has another oracle result"]
  pure (compared, bad)

/-- The random states of a block with the load widths `bits`, and the next seed. -/
def randomStates (bits : List Nat) (samples seed : Nat) : List (Env × Array UInt64) × Nat := Id.run do
  let mut seed := seed
  let mut states := []
  for _ in [:samples] do
    let (env, raw, s') := sample bits seed
    seed := s'
    states := states ++ [(env, raw)]
  pure (states, seed)

/-- The meaning check of the read blocks of `ws`: the number of blocks, items and compared values, the blocks that are
not compiled, and the disagreements (block, item, the sample). -/
def meaning (fns : List (String × Nat)) (ws : List (Spec × Walk)) (samples : Nat) :
    MetaM (Nat × Nat × Nat × List String × List String) := do
  let mut blocks := 0
  let mut nitems := 0
  let mut compared := 0
  let mut skipped : List String := []
  let mut bad : List String := []
  let mut seed := 12345
  for (s, w) in ws do
    let .ok b := readWalk (baseOf fns s) w | continue
    let its := rawItems w b
    let run ← match ← compileRaw w (its.map (·.1)) with
      | some run => pure run
      | none => skipped := skipped ++ [name s]; continue
    blocks := blocks + 1
    nitems := nitems + its.length
    let bits := w.accesses.toList.filterMap fun | .load _ wd _ _ => some wd.bits | .store .. => none
    let (states, seed') := randomStates bits samples seed
    seed := seed'
    let (c, bs) := runStates s its run states
    compared := compared + c
    bad := bad ++ bs
  pure (blocks, nitems, compared, skipped, bad)

end DeriveReadTests

#eval show TermElabM Unit from do
  let pilot ← walkAll pilotStep `Skel.Test.DeriveRead.m3 pilotSpecs
  let level2 ← walkAll level2Step `Skel.Test.DeriveRead.m2 level2Specs
  for (what, fns, ws, nblocks) in [("pilot", pilotFns, pilot, 49), ("level 2", level2Fns, level2, 79)] do
    let (blocks, nitems, compared, skipped, bad) ← meaning fns ws 64
    logInfo m!"{what}: {blocks} blocks, {nitems} items, {compared} values compared, not compiled {skipped}, {bad.length} different {bad.take 5}"
    check (blocks == nblocks && skipped.isEmpty) s!"{what}: {nblocks} blocks compiled, got {blocks}, not compiled {skipped}"
    check bad.isEmpty s!"{what}: the raw terms and the read values differ: {bad.take 5}"

/-! ## The boundaries of the two borrow forms of `sbb` (NB)

The random states of the meaning check rarely have a 32-bit sum of 0 or 1. Here the states of `l2Arith` entry have the low
32 bits of `edx + esi - 1 - edi` in 0, 1, 2 and `2^32 - 1` (the high bits of `rdi` random), and the states of
`l2TwoLoops` o9 have the byte load 0, 1, 2 and 255. The compiled raw terms and the read values agree on all of them. -/

#eval show TermElabM Unit from do
  let ws ← walkAll level2Step `Skel.Test.DeriveRead.nb level2Specs
  let find (n : String) : TermElabM (Spec × Walk) := do
    let some x := ws.find? fun (s, _) => name s == n | throwError "no block {n}"
    pure x
  let mut compared := 0
  let mut bad : List String := []
  -- `l2Arith entry`
  let (s, w) ← find "l2Arith entry"
  let .ok b := readWalk (baseOf level2Fns s) w | throwError "{name s} is not read"
  let its := rawItems w b
  let some run ← compileRaw w (its.map (·.1)) | throwError "{name s} is not compiled"
  let bits := w.accesses.toList.filterMap fun | .load _ wd _ _ => some wd.bits | .store .. => none
  let (base, _) := randomStates bits 40 777
  let ix (r : Reg64) := allRegs.idxOf r
  let states := base.flatMap fun (env, raw) =>
    [0, 1, 2, 0xFFFFFFFF, 0x100000000, 0x100000001].map fun t =>
      let sum := env.regs[ix .rdx]! + env.regs[ix .rsi]! - 1 - UInt64.ofNat t
      let rdi := (sum &&& 0xFFFFFFFF) ||| (env.regs[ix .rdi]! &&& 0xFFFFFFFF00000000)
      ({ env with regs := env.regs.set! (ix .rdi) rdi }, raw)
  let (c, bs) := runStates s its run states
  compared := compared + c
  bad := bad ++ bs
  -- `l2TwoLoops o9`
  let (s, w) ← find "l2TwoLoops o9"
  let .ok b := readWalk (baseOf level2Fns s) w | throwError "{name s} is not read"
  let its := rawItems w b
  let some run ← compileRaw w (its.map (·.1)) | throwError "{name s} is not compiled"
  let bits := w.accesses.toList.filterMap fun | .load _ wd _ _ => some wd.bits | .store .. => none
  let (base, _) := randomStates bits 10 778
  let states := base.flatMap fun (env, _) =>
    [0, 1, 2, 255].map fun v => ({ env with loads := #[UInt64.ofNat v] }, #[UInt64.ofNat v])
  let (c, bs) := runStates s its run states
  compared := compared + c
  bad := bad ++ bs
  logInfo m!"the boundaries of the borrow forms: {compared} values compared, {bad.length} different {bad.take 5}"
  check (compared > 0) "the boundary states compare values"
  check bad.isEmpty s!"the borrow forms differ from the raw terms at a boundary: {bad.take 5}"

/-! ## The normal form

Equal normal forms for values that are equal over `UInt64`, and different normal forms for values that differ for some
register values. A property test: for random values and conditions, the normal form has the same value as the value. -/

namespace DeriveReadTests

def r (x : Reg64) : Val := .reg x
def n (k : Nat) : Val := .lit (UInt64.ofNat k)

def regsOf : List Reg64 := [.rax, .rbx, .rcx, .rsp]

/-- A random leaf. -/
def leaf (s : Nat) : Val :=
  let k := (s / 7) % 3
  if k == 0 then r (regsOf.getD ((s / 31) % 4) .rax)
  else if k == 1 then .load ((s / 31) % 3)
  else n (if (s / 31) % 2 == 0 then (s / 101) % 16 else if (s / 31) % 3 == 0 then 255 else s)

def cnt (k : Nat) : Fin 64 := ⟨k % 64, Nat.mod_lt _ (by decide)⟩

def narrowOf (s : Nat) : Narrow := match (s / 13) % 3 with | 0 => .b8 | 1 => .b16 | _ => .b32

mutual
/-- A random value of depth at most `d` and the next seed. -/
def gen : Nat → Nat → Val × Nat
  | 0, s => let s := next s; (leaf s, s)
  | d + 1, s =>
    let s := next s
    let k := (s / 7) % 22
    let (a, s1) := gen d s
    let (b, s2) := gen d s1
    match k with
    | 0 => (.add a b, s2)
    | 1 => (.sub a b, s2)
    | 2 => (.mul a b, s2)
    | 3 => (.shr a (cnt (s / 31)), s1)
    | 4 => (.zext32 a, s1)
    | 5 => (.mul a (n ((s / 31) % 9)), s1)
    | 6 => (.and a b, s2)
    | 7 => (.or a b, s2)
    | 8 => (.xor a b, s2)
    | 9 => (.not a, s1)
    | 10 => (.neg a, s1)
    | 11 => (.shl a (cnt (s / 31)), s1)
    | 12 => if h : (s / 31) % 64 + (s / 37) % 33 ≤ 64 then (.extract ((s / 31) % 64) ((s / 37) % 33) a h, s1) else (a, s1)
    | 13 => (.zext (narrowOf s) a, s1)
    | 14 => (.sext (narrowOf s) a, s1)
    | 15 => (.replaceLow (narrowOf s) a b, s2)
    | 16 => let (c, s3) := genC d s2; (.setcc c, s3)
    | 17 => let (c, s3) := genC d s2; (.ite c a b, s3)
    | 18 => (.and a (n (if (s / 31) % 3 == 0 then 0xFF else if (s / 31) % 3 == 1 then 0xFFFF else 0xFFFFFFFF)), s1)
    | 19 => (.extract 0 32 a (by decide), s1)
    | _ => (leaf s, s)

/-- A random condition of depth at most `d` and the next seed. -/
def genC : Nat → Nat → Cond × Nat
  | 0, s => let s := next s; (.flag (if s % 2 == 0 then .cf else .zf), s)
  | d + 1, s =>
    let s := next s
    let (a, s1) := gen d s
    let (b, s2) := gen d s1
    match (s / 7) % 8 with
    | 0 => (.eq a b, s2)
    | 1 => (.ule a b, s2)
    | 2 => (.ult a b, s2)
    | 3 => (.slt32 a b, s2)
    | 6 => (.slt a b, s2)
    | 4 => let (c, s3) := genC d s2; (.not c, s3)
    | 5 => let (p, s3) := genC d s2; let (q, s4) := genC d s3; (.iff p q, s4)
    | _ => (.flag (if s % 2 == 0 then .cf else .zf), s2)
end

end DeriveReadTests

#eval show TermElabM Unit from do
  -- equal over UInt64
  check ((Val.add (.sub (r .rsp) (n 8)) (n 8)).sameNorm (r .rsp)) "(rsp - 8) + 8 is rsp"
  check ((Val.zext32 (n 3)).sameNorm (n 3)) "zext32 3 is 3"
  check ((Val.zext32 (n 0x100000003)).sameNorm (n 3)) "zext32 cuts a literal to 32 bits"
  check ((Val.add (r .rax) (r .rbx)).sameNorm (.add (r .rbx) (r .rax))) "the sum is commutative"
  check ((Val.mul (r .rcx) (n 1)).sameNorm (r .rcx)) "rcx * 1 is rcx"
  check ((Val.add (.add (r .rdi) (.mul (r .rsi) (n 8))) (n 8)).sameNorm (.add (n 8) (.add (.mul (n 8) (r .rsi)) (r .rdi))))
    "a sum in another order"
  check ((Val.add (n 0xFFFFFFFFFFFFFFFF) (n 1)).sameNorm (n 0)) "the literals wrap at 2^64"
  check ((Val.sub (r .rax) (r .rax)).sameNorm (n 0)) "rax - rax is 0"
  check ((Val.shr (.add (n 1) (r .rax)) 3).sameNorm (.shr (.add (r .rax) (n 1)) 3)) "the normal form inside a shift"
  -- the low 32 bits: one normal form (`zext32`)
  check ((Val.zext .b32 (r .rax)).norm.show == (Val.zext32 (r .rax)).show) "zext .b32 is zext32"
  check ((Val.extract 0 32 (r .rax) (by decide)).norm.show == (Val.zext32 (r .rax)).show) "extract 0 32 is zext32"
  check ((Val.replaceLow .b32 (r .rbx) (r .rax)).norm.show == (Val.zext32 (r .rax)).show) "replaceLow .b32 is zext32"
  check ((Val.and (r .rax) (n 0xFFFFFFFF)).norm.show == (Val.zext32 (r .rax)).show) "and 0xFFFFFFFF is zext32"
  check ((Val.and (n 255) (r .rax)).norm.show == (Val.zext .b8 (r .rax)).show) "and 255 is zext8"
  check ((Val.extract 0 16 (r .rax) (by decide)).norm.show == (Val.zext .b16 (r .rax)).show) "extract 0 16 is zext16"
  check ((Val.zext .b8 (.zext32 (r .rax))).sameNorm (.zext .b8 (r .rax))) "zext8 of zext32 is zext8"
  check ((Val.zext32 (.zext .b8 (r .rax))).sameNorm (.zext .b8 (r .rax))) "zext32 of zext8 is zext8"
  check ((Val.zext .b8 (.setcc (.flag .cf))).sameNorm (.setcc (.flag .cf))) "the setcc byte has 8 bits"
  check ((Val.neg (r .rax)).sameNorm (.sub (n 0) (r .rax))) "neg is 0 -"
  check ((Val.not (r .rax)).sameNorm (.sub (n 0xFFFFFFFFFFFFFFFF) (r .rax))) "not is -1 -"
  check ((Val.shl (r .rax) 3).sameNorm (.mul (r .rax) (n 8))) "shl 3 is * 8"
  check ((Val.xor (r .rax) (r .rbx)).sameNorm (.xor (r .rbx) (r .rax))) "xor is commutative"
  -- conditions
  check ((Cond.not (.ult (r .rax) (r .rbx))).sameNorm (.ule (r .rbx) (r .rax))) "¬ a < b is b ≤ a"
  check ((Cond.not (.ule (r .rax) (r .rbx))).sameNorm (.ult (r .rbx) (r .rax))) "¬ a ≤ b is b < a"
  check ((Cond.eq (r .rax) (r .rbx)).sameNorm (.eq (r .rbx) (r .rax))) "= is symmetric"
  check ((Cond.not (.not (.flag .cf))).sameNorm (.flag .cf)) "¬ ¬ c is c"
  check ((Cond.iff (.flag .cf) (.flag .zf)).sameNorm (.iff (.flag .zf) (.flag .cf))) "↔ is symmetric"
  -- different for some register values
  check (!(Val.add (r .rsp) (n 8)).sameNorm (r .rsp)) "rsp + 8 is not rsp"
  check (!(Val.shr (r .rax) 1).sameNorm (.shr (r .rax) 2)) "shr 1 is not shr 2"
  check (!(Val.mul (r .rax) (r .rbx)).sameNorm (r .rax)) "rax * rbx is not rax"
  check (!(Val.zext32 (r .rax)).sameNorm (r .rax)) "zext32 rax is not rax"
  check (!(Val.zext .b8 (r .rax)).sameNorm (.zext .b16 (r .rax))) "zext8 is not zext16"
  check (!(Val.load 0).sameNorm (.load 1)) "load 0 is not load 1"
  check (!(Val.retAddr 3).sameNorm (n 3)) "retAddr 3 is not 3"
  check (!(Cond.ult (r .rax) (r .rbx)).sameNorm (.ule (r .rax) (r .rbx))) "< is not ≤"
  check (!(Cond.flag .cf).sameNorm (.flag .zf)) "cf is not zf"
  -- the property: the normal form has the value of the value
  let mut s := 17
  let mut fails : List String := []
  let mut withCond := 0
  for _ in [:3000] do
    let (v, s1) := gen 4 s
    let (c, s2) := genC 3 s1
    let (env, _, s3) := sample [64, 8, 32] s2
    if evalV env v != evalV env v.norm then fails := fails ++ [v.show]
    if evalC env c != evalC env c.norm then fails := fails ++ [c.show]
    if (v.show.splitOn "flag").length > 1 then withCond := withCond + 1
    s := s3
  check fails.isEmpty s!"the normal form changes the value of {fails.take 3}"
  check (withCond > 100) s!"the random values have conditions: {withCond}"

/-! ## The reader on small terms -/

namespace DeriveReadTests

def elabE (stx : TermElabM Syntax) : TermElabM Expr := do
  let e ← Term.elabTerm (← stx) none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- The reader on the body of `fun d : MachineData => body`, with the start `d` and no load. -/
def readBody {α : Type} (f : ReadCtx → Expr → Except ReadError α) (e : Expr) : MetaM (Except ReadError α) :=
  lambdaTelescope e fun xs b => pure (f { start := xs[0]!.fvarId!, loads := #[] } b)

def isVal (r : Except ReadError Val) (v : Val) : Bool :=
  match r with | .ok x => x.show == v.show | .error _ => false

def isCond (r : Except ReadError Cond) (c : Cond) : Bool :=
  match r with | .ok x => x.show == c.show | .error _ => false

def isErr {α : Type} (r : Except ReadError α) (p : ReadError → Bool) : Bool :=
  match r with | .error e => p e | .ok _ => false

end DeriveReadTests

#eval show TermElabM Unit from do
  let rd (stx : TermElabM Syntax) := do readBody readVal (← elabE stx)
  -- registers, literals, the wrappers
  check (isVal (← rd `(fun d : MachineData => d.regs.rax + 8)) (.add (r .rax) (n 8))) "rax + 8"
  check (isVal (← rd `(fun d : MachineData => UInt64.ofBitVec (d.regs.rax.toBitVec - Width.W64.bytesv)))
    (.sub (r .rax) (n 8))) "the wrappers and bytesv"
  check (isVal (← rd `(fun d : MachineData => ({ toBitVec := d.regs.rbx.toBitVec * 4#64 } : UInt64)))
    (.mul (r .rbx) (n 4))) "the structure form and a BitVec literal"
  check (isVal (← rd `(fun _d : MachineData => (300 : BitVec 8))) (n 44)) "a literal of 8 bits is cut to 8 bits"
  check (isVal (← rd `(fun _d : MachineData => (300 : Width.type .W8))) (n 44)) "a literal of Width.type W8"
  check (isVal (← rd `(fun _d : MachineData => (0xFFFFFFFFFFFFFFFF : UInt64))) (n 0xFFFFFFFFFFFFFFFF)) "a UInt64 literal"
  check (isVal (← rd `(fun d : MachineData => d.regs.rax >>> 3)) (.shr (r .rax) 3)) "a UInt64 shift"
  check (isVal (← rd `(fun d : MachineData => d.regs.rax >>> 67)) (.shr (r .rax) 3)) "a UInt64 shift count modulo 64"
  check (isVal (← rd `(fun d : MachineData => d.regs.rax.toBitVec >>> 63)) (.shr (r .rax) 63)) "a BitVec shift"
  check (isVal (← rd `(fun d : MachineData => BitVec.setWidth 64 (BitVec.extractLsb' 0 32 d.regs.rcx.toBitVec)))
    (.zext32 (r .rcx))) "zext32"
  -- N5: the bit operations and the left shift
  check (isVal (← rd `(fun d : MachineData => d.regs.rax &&& d.regs.rbx)) (.and (r .rax) (r .rbx))) "and"
  check (isVal (← rd `(fun d : MachineData => d.regs.rax.toBitVec ||| 255#64)) (.or (r .rax) (n 255))) "or"
  check (isVal (← rd `(fun d : MachineData => d.regs.rax ^^^ d.regs.rbx)) (.xor (r .rax) (r .rbx))) "xor"
  check (isVal (← rd `(fun d : MachineData => ~~~d.regs.rax.toBitVec)) (.not (r .rax))) "not"
  check (isVal (← rd `(fun d : MachineData => -d.regs.rax.toBitVec)) (.neg (r .rax))) "neg"
  check (isVal (← rd `(fun d : MachineData => d.regs.rax.toBitVec <<< 16)) (.shl (r .rax) 16)) "shl"
  -- N6: the narrow forms, as zero extensions
  check (isVal (← rd `(fun d : MachineData => BitVec.setWidth 64 (BitVec.extractLsb' 0 16 d.regs.rcx.toBitVec)))
    (.zext .b16 (r .rcx))) "zext16"
  check (isVal (← rd `(fun d : MachineData => BitVec.setWidth 64 (BitVec.extractLsb' 0 8 d.regs.rcx.toBitVec)))
    (.zext .b8 (r .rcx))) "zext8"
  check (isVal (← rd `(fun d : MachineData => BitVec.extractLsb' 8 8 d.regs.rcx.toBitVec)) (.extract 8 8 (r .rcx) (by decide)))
    "an extraction from bit 8"
  check (isVal (← rd `(fun d : MachineData => BitVec.setWidth 8 d.regs.rcx.toBitVec)) (.zext .b8 (r .rcx)))
    "a truncation to 8 bits"
  check (isVal (← rd `(fun d : MachineData => BitVec.replaceLow d.regs.rax.toBitVec (BitVec.extractLsb' 0 8 d.regs.rdx.toBitVec)))
    (.replaceLow .b8 (r .rax) (.zext .b8 (r .rdx)))) "replaceLow of 8 bits"
  check (isVal (← rd `(fun d : MachineData => BitVec.replaceLow d.regs.rax.toBitVec (BitVec.extractLsb' 0 16 d.regs.rdx.toBitVec)))
    (.replaceLow .b16 (r .rax) (.zext .b16 (r .rdx)))) "replaceLow of 16 bits"
  check (isVal (← rd `(fun d : MachineData => BitVec.extractLsb' 0 8 d.regs.rax.toBitVec - 1#8))
    (.zext .b8 (.sub (.zext .b8 (r .rax)) (n 1)))) "an 8-bit subtraction has 8 bits"
  check (isVal (← rd `(fun d : MachineData => BitVec.extractLsb' 0 8 d.regs.rax.toBitVec &&& 15#8))
    (.and (.zext .b8 (r .rax)) (n 15))) "an 8-bit and"
  check (isVal (← rd `(fun d : MachineData => BitVec.extractLsb' 0 8 (BitVec.replaceLow d.regs.rax.toBitVec (BitVec.extractLsb' 0 8 d.regs.rdx.toBitVec))))
    (.zext .b8 (r .rdx))) "the low byte of a byte write is the byte"
  -- the `setcc` byte and `ite`
  check (isVal (← rd `(fun d : MachineData => BitVec.ofNat 8 (d.regs.rax.toBitVec - 5#64 == 0#64).toNat))
    (.setcc (.eq (r .rax) (n 5)))) "the setcc byte of sete"
  check (isVal (← rd `(fun d : MachineData => BitVec.ofNat 8 (!(d.regs.rax.toBitVec == 0#64)).toNat))
    (.setcc (.not (.eq (r .rax) (n 0))))) "the setcc byte of setne"
  check (isVal (← rd `(fun d : MachineData => if d.regs.rax = 0 then (1 : UInt64) else 2)) (.ite (.eq (r .rax) (n 0)) (n 1) (n 2)))
    "ite"
  check (isVal (← rd `(fun d : MachineData => if d.status.cf = true then d.regs.rdi.toBitVec else d.regs.rsi.toBitVec))
    (.ite (.flag .cf) (r .rdi) (r .rsi))) "the cmovb of a flag input"
  -- refused
  check (isErr (← rd `(fun d : MachineData => d.regs.rax / d.regs.rbx)) (· == .unsupported ``HDiv.hDiv)) "div is refused"
  check (isErr (← rd `(fun d : MachineData => BitVec.replaceLow d.regs.rax.toBitVec (BitVec.extractLsb' 0 32 d.regs.rdx.toBitVec)))
    (· == .unsupported ``BitVec.replaceLow)) "replaceLow of 32 bits is refused"
  check (isErr (← rd `(fun d : MachineData => BitVec.setWidth 128 d.regs.rcx.toBitVec)) (· == .unsupported ``BitVec.setWidth))
    "a width above 64 is refused"
  check (isErr (← rd `(fun d : MachineData => d.regs.rax.toBitVec >>> 64)) (· == .shift 64)) "a shift by 64 is refused"
  check (isErr (← rd `(fun d : MachineData => d.regs.rax.toBitVec <<< 64)) (· == .shift 64)) "a left shift by 64 is refused"
  check (isErr (← rd `(fun d : MachineData => d.regs.rax >>> d.regs.rcx)) (· == .unsupported ``HShiftRight.hShiftRight))
    "a shift by a register is refused"
  check (isErr (← rd `(fun d : MachineData => d.status.cf)) (· == .unsupported ``StatusFlags.cf)) "a flag is not a value"
  check (isErr (← rd `(fun d : MachineData => if d.regs.rax.toNat % 3 = 1 then (1 : UInt64) else 2))
    (· == .unsupported ``Eq)) "an ite of an unknown condition is refused"
  -- a free variable that is not the start and not a load
  let e ← elabE `(fun (_d e : MachineData) => e.regs.rax)
  let res ← lambdaTelescope e fun xs b => pure (readVal { start := xs[0]!.fvarId!, loads := #[] } b)
  check (isErr res fun | .freeVar _ => true | _ => false) "another state is a free variable"
  let e ← elabE `(fun (_d e : MachineData) => if e.status.cf = true then (1 : UInt64) else 2)
  let res ← lambdaTelescope e fun xs b => pure (readVal { start := xs[0]!.fvarId!, loads := #[] } b)
  check (isErr res fun | .freeVar _ => true | _ => false) "a flag of another state is a free variable"

/-! ## The conditions on small terms: one for each lemma of `Lift/Tactic/Cond.lean`, and the refused forms -/

#eval show TermElabM Unit from do
  let rc (stx : TermElabM Syntax) := do readBody readCond (← elabE stx)
  -- N8
  check (isCond (← rc `(fun d : MachineData => d.regs.rax.toBitVec - d.regs.rbx.toBitVec = 0#64)) (.eq (r .rax) (r .rbx)))
    "sub_zero_iff"
  check (isCond (← rc `(fun d : MachineData => d.regs.rax.toBitVec = 0#64)) (.eq (r .rax) (n 0))) "eq_zero_iff"
  check (isCond (← rc `(fun d : MachineData =>
      (((18446744073709551616 - d.regs.rsi.toNat : Nat) : Int) + (d.regs.rax.toNat : Int)) % 18446744073709551616 =
        (d.regs.rax.toNat : Int) - (d.regs.rsi.toNat : Int))) (.ule (r .rsi) (r .rax))) "nocarry_iff_le"
  check (isCond (← rc `(fun d : MachineData =>
      ((18446744073709541376 : Int) + (d.regs.rax.toBitVec.toNat : Int)) % 18446744073709551616 =
        (d.regs.rax.toBitVec.toNat : Int) - 10240)) (.ule (n 10240) (r .rax))) "nocarry_lit_iff_le: k is 2^64 - C"
  check (isCond (← rc `(fun d : MachineData =>
      ¬ (((18446744073709551616 - d.regs.rsi.toNat : Nat) : Int) + (d.regs.rax.toNat : Int)) % 18446744073709551616 =
        (d.regs.rax.toNat : Int) - (d.regs.rsi.toNat : Int))) (.not (.ule (r .rsi) (r .rax)))) "not_nocarry_iff_lt"
  check (isCond (← rc `(fun d : MachineData =>
      (((18446744073709551616 - d.regs.rcx.toNat : Nat) : Int) + (d.regs.rax.toNat : Int)) % 18446744073709551616 =
        (d.regs.rax.toNat : Int) - (d.regs.rcx.toNat : Int) ∧ ¬ d.regs.rax.toBitVec - d.regs.rcx.toBitVec = 0#64))
    (.ult (r .rcx) (r .rax))) "nocarry_and_ne_iff_lt"
  check (isCond (← rc `(fun d : MachineData =>
      ((18446744073709551609 : Int) + (d.regs.rsi.toNat : Int)) % 18446744073709551616 = (d.regs.rsi.toNat : Int) - 7 ∧
        ¬ d.regs.rsi.toBitVec - 7#64 = 0#64)) (.ult (n 7) (r .rsi))) "nocarry_lit_and_ne_iff_lt"
  check (isCond (← rc `(fun d : MachineData =>
      ¬ (((18446744073709551616 - d.regs.rsi.toNat : Nat) : Int) + (d.regs.r9.toNat : Int)) % 18446744073709551616 =
        (d.regs.r9.toNat : Int) - (d.regs.rsi.toNat : Int) ∨ d.regs.r9.toBitVec - d.regs.rsi.toBitVec = 0#64))
    (.ule (r .r9) (r .rsi))) "not_nocarry_or_zero_iff_le"
  -- N9
  check (isCond (← rc `(fun d : MachineData => 280375465082880#64 &&& d.regs.rsi.toBitVec = 0#64))
    (.eq (.and (r .rsi) (n 280375465082880)) (n 0))) "and_zero_iff"
  check (isCond (← rc `(fun d : MachineData => (d.regs.rax.toBitVec ^^^ d.regs.rsi.toBitVec) <<< 16 = 0#64))
    (.eq (.and (r .rax) (n 281474976710655)) (.and (r .rsi) (n 281474976710655)))) "shlxor_zero_iff_and"
  check (isCond (← rc `(fun d : MachineData => BitVec.extractLsb' 0 8 d.regs.rdx.toBitVec = 0#8))
    (.eq (.zext .b8 (r .rdx)) (n 0))) "extract8_zero_iff"
  check (isCond (← rc `(fun d : MachineData => BitVec.extractLsb' 0 16 d.regs.rax.toBitVec = 0#16))
    (.eq (.zext .b16 (r .rax)) (n 0))) "extract16_zero_iff"
  check (isCond (← rc `(fun d : MachineData => BitVec.extractLsb' 0 8 (d.regs.rsi.toBitVec >>> 32) = 0#8))
    (.eq (.zext .b8 (.shr (r .rsi) 32)) (n 0))) "extract8_shr32_zero_iff"
  check (isCond (← rc `(fun d : MachineData =>
      BitVec.extractLsb' 0 8 (d.regs.rbx.toBitVec.replaceLow (BitVec.ofNat 8 (d.regs.rax.toBitVec - d.regs.r10.toBitVec == 0#64).toNat)) =
        BitVec.extractLsb' 0 8 (d.regs.rbp.toBitVec.replaceLow (BitVec.ofNat 8 (!BitVec.extractLsb' 0 8 d.regs.rdx.toBitVec == 0#8).toNat))))
    (.iff (.eq (r .rax) (r .r10)) (.not (.eq (.zext .b8 (r .rdx)) (n 0))))) "setcc_xor_iff"
  -- N10
  check (isCond (← rc `(fun d : MachineData =>
      BitVec.extractLsb' 0 32 d.regs.rax.toBitVec - BitVec.extractLsb' 0 32 d.regs.rbx.toBitVec = 0#32))
    (.eq (.zext32 (r .rax)) (.zext32 (r .rbx)))) "sub32_zero_iff"
  check (isCond (← rc `(fun d : MachineData =>
      ((254 : Int) + (d.regs.rax.toBitVec.toNat : Int)) % 256 = (d.regs.rax.toBitVec.toNat : Int) % 256 - 2))
    (.ule (n 2) (.zext .b8 (r .rax)))) "nocarry8_lit_iff_le: k is 2^8 - C"
  -- NB: the borrow of a 32-bit sum (`cmpl $K` of the low 32 bits of `S`); the byte load is below
  let sum32 (c k : Nat) (s s' : String) : TermElabM (Except ReadError Cond) := do
    let src := s!"fun d : MachineData => (({c} : Int) + (({s} : Int) % 4294967296) % 18446744073709551616) % 4294967296 = ({s'} : Int) % 4294967296 - {k}"
    let stx ← match Parser.runParserCategory (← getEnv) `term src with
      | .ok stx => pure stx
      | .error e => throwError e
    readBody readCond (← elabE (pure stx))
  let sRdx := "(d.regs.rdx.toNat : Int)"
  let sDiff := "(((4294967296 - d.regs.rdi.toNat % 4294967296 : Nat) : Int) + ((d.regs.rdx.toNat : Int) + ((d.regs.rsi.toNat : Int) + 18446744073709551615)))"
  check (isCond (← sum32 4294967295 1 sDiff sDiff)
    (.ule (n 1) (.zext32 (.add (.neg (r .rdi)) (.add (r .rdx) (.add (r .rsi) (n 18446744073709551615)))))))
    "nocarry32_lit_iff_le: the sum of `l2Arith`"
  check (isCond (← sum32 4294967293 3 sRdx sRdx) (.ule (n 3) (.zext32 (r .rdx)))) "nocarry32_lit_iff_le: a register, K = 3"
  check (isCond (← sum32 4294967295 1 s!"({sRdx} + 5)" s!"({sRdx} + 5)") (.ule (n 1) (.zext32 (.add (r .rdx) (n 5)))))
    "nocarry32_lit_iff_le: a literal in the sum"
  check (isErr (← sum32 4294967294 1 sRdx sRdx) (· == .unsupported ``Int)) "nocarry32: C + K is not 2^32"
  check (isErr (← sum32 4294967295 1 sRdx sDiff) (· == .unsupported ``Int)) "nocarry32: the two sums differ"
  check (isCond (← rc `(fun d : MachineData => d.status.cf = true)) (.flag .cf)) "a flag input"
  check (isCond (← rc `(fun d : MachineData => d.status.zf = false)) (.not (.flag .zf))) "a flag input, not set"
  check (isCond (← rc `(fun d : MachineData => (d.status.cf && !d.status.zf) = true ↔ d.regs.rax ≤ 5))
    (.iff (.flag .cf) (.ule (r .rax) (n 5)))).not "a Bool and is not a ja form"
  check (isCond (← rc `(fun d : MachineData => d.regs.rax ≤ d.regs.rbx)) (.ule (r .rax) (r .rbx))) "≤ of UInt64"
  check (isCond (← rc `(fun d : MachineData => d.regs.rax < 5)) (.ult (r .rax) (n 5))) "< of UInt64"
  -- refused: an unknown condition form is an error
  let rcErr (stx : TermElabM Syntax) (h : Name) := do check (isErr (← rc stx) (· == .unsupported h)) s!"refused at {h}"
  rcErr `(fun d : MachineData => ((d.regs.rax.toNat : Int) + 1) % 7 = 3) ``Int
  rcErr `(fun d : MachineData =>
    ((18446744073709551614 : Int) + (d.regs.rax.toNat : Int)) % 18446744073709551616 = (d.regs.rax.toNat : Int) - 1) ``Int
  rcErr `(fun d : MachineData =>
    (((18446744073709551616 - d.regs.rsi.toNat : Nat) : Int) + (d.regs.rax.toNat : Int)) % 18446744073709551616 =
      (d.regs.rax.toNat : Int) - (d.regs.rbx.toNat : Int)) ``Int
  rcErr `(fun d : MachineData =>
    ((255 : Int) + (d.regs.rax.toBitVec.toNat : Int)) % 256 = (d.regs.rax.toBitVec.toNat : Int) % 256 - 2) ``Int
  -- READER, D1: two zero tests are read (`Skel/Test/DeriveReader.lean`); a zero test and another equation are refused
  rcErr `(fun d : MachineData => d.regs.rax = 0 ∧ d.regs.rbx = 1) ``And
  rcErr `(fun d : MachineData =>
    (((18446744073709551616 - d.regs.rcx.toNat : Nat) : Int) + (d.regs.rax.toNat : Int)) % 18446744073709551616 =
      (d.regs.rax.toNat : Int) - (d.regs.rcx.toNat : Int) ∧ ¬ d.regs.rax.toBitVec - d.regs.rbx.toBitVec = 0#64) ``And
  rcErr `(fun d : MachineData => d.regs.rax = 0 ∨ d.regs.rbx = 1) ``Or
  rcErr `(fun d : MachineData => d.regs.rax.toNat < 5) ``LT.lt
  rcErr `(fun d : MachineData => d.regs.rax.toNat ∣ 6) ``Dvd.dvd
  rcErr `(fun d : MachineData => d.regs.rax.toNat = 5) ``Eq
  -- L2-FLAGS: a conjunction of two flag inputs is the equation of their `setcc` bytes; with a compare it is refused
  check (isCond (← rc `(fun d : MachineData => (d.status.cf && !d.status.zf) = true))
    (.eq (.and (.setcc (.flag .cf)) (.setcc (.not (.flag .zf)))) (n 1))) "a conjunction of two flag inputs"
  check (isCond (← rc `(fun d : MachineData => (!d.status.cf && !d.status.zf) = true))
    (.eq (.and (.setcc (.not (.flag .cf))) (.setcc (.not (.flag .zf)))) (n 1))) "seta of two flag inputs"
  check (isCond (← rc `(fun d : MachineData => (d.status.cf || d.status.zf) = true))
    (.not (.eq (.or (.setcc (.flag .cf)) (.setcc (.flag .zf))) (n 0)))) "a disjunction of two flag inputs"
  rcErr `(fun d : MachineData => (d.status.cf && d.regs.rax == 0) = true) ``Bool.and

/-! ## The borrow of a byte load (NB)

The load value is a free variable of the walk: the reader gets it in `ReadCtx.loads`, here with the width of 8 bits. -/

namespace DeriveReadTests

/-- The reader on the body of `fun (v : BitVec 8) (d : MachineData) => body`: `v` is the load 0 of 8 bits. -/
def readLoad8 {α : Type} (f : ReadCtx → Expr → Except ReadError α) (e : Expr) : MetaM (Except ReadError α) :=
  lambdaTelescope e fun xs b => pure (f { start := xs[1]!.fvarId!, loads := #[(xs[0]!.fvarId!, .W8)] } b)

end DeriveReadTests

#eval show TermElabM Unit from do
  let rc (stx : TermElabM Syntax) := do readLoad8 readCond (← elabE stx)
  check (isCond (← rc `(fun (v : BitVec 8) (_d : MachineData) => ((255 : Int) + (v.toNat : Int)) % 256 = (v.toNat : Int) - 1))
    (.ule (n 1) (.load 0))) "nocarry8_load_lit_iff_le: K = 1"
  check (isCond (← rc `(fun (v : BitVec 8) (_d : MachineData) => ((254 : Int) + (v.toNat : Int)) % 256 = (v.toNat : Int) - 2))
    (.ule (n 2) (.load 0))) "nocarry8_load_lit_iff_le: K = 2"
  check (isCond (← rc `(fun (v : BitVec 8) (_d : MachineData) => ¬ ((255 : Int) + (v.toNat : Int)) % 256 = (v.toNat : Int) - 1))
    (.not (.ule (n 1) (.load 0)))) "the borrow is the negation"
  check (isErr (← rc `(fun (v : BitVec 8) (_d : MachineData) => ((255 : Int) + (v.toNat : Int)) % 256 = (v.toNat : Int) - 2))
    (· == .unsupported ``Int)) "nocarry8_load: C + K is not 256"
  check (isErr (← rc `(fun (v : BitVec 8) (_d : MachineData) => ((255 : Int) + (v.toNat : Int)) % 256 = (v.toNat : Int) % 256 - 1))
    (· == .unsupported ``Int)) "nocarry8_load: a load of 8 bits has no `% 256` on the right"
  -- the same value as a `Val`: the setcc byte of `sbb`
  let rv (stx : TermElabM Syntax) := do readLoad8 readVal (← elabE stx)
  check (isVal (← rv `(fun (v : BitVec 8) (_d : MachineData) =>
      BitVec.ofNat 8 (((255 : Int) + (v.toNat : Int)) % 256 != (v.toNat : Int) - 1).toNat))
    (.setcc (.not (.ule (n 1) (.load 0))))) "the setcc byte of the borrow"

/-! ## The addresses -/

#eval show TermElabM Unit from do
  let ra (stx : TermElabM Syntax) := do readBody readAddr (← elabE stx)
  check (isVal (← ra `(fun d : MachineData => d.regs.rax.toBitVec)) (r .rax)) "a base"
  check (isVal (← ra `(fun d : MachineData => 16#64 + d.regs.rdi.toBitVec)) (.add (r .rdi) (n 16))) "a base and a displacement"
  check (isVal (← ra `(fun d : MachineData => d.regs.rsp.toBitVec - 8#64 - Width.W64.bytesv))
    (.add (r .rsp) (n (2 ^ 64 - 16)))) "a base and a negative displacement"
  check (isVal (← ra `(fun d : MachineData => d.regs.rdx.toBitVec + d.regs.rcx.toBitVec))
    (.add (r .rdx) (.mul (r .rcx) (n 1)))) "a base and an index of scale 1"
  check (isVal (← ra `(fun d : MachineData => d.regs.rdi.toBitVec + d.regs.rsi.toBitVec * 8#64 + 72#64))
    (.add (.add (r .rdi) (.mul (r .rsi) (n 8))) (n 72))) "base + index * scale + displacement"
  check (isVal (← ra `(fun d : MachineData => d.regs.rsi.toBitVec * 8#64 + d.regs.rdi.toBitVec))
    (.add (r .rdi) (.mul (r .rsi) (n 8)))) "the scaled term is the index"
  check (isVal (← ra `(fun _d : MachineData => 4096#64)) (n 4096)) "a displacement alone"
  check (isVal (← ra `(fun d : MachineData => d.regs.rax.toBitVec * 12#64)) (.mul (r .rax) (n 12)))
    "an index of scale 12 alone"
  check (isVal (← ra `(fun d : MachineData => d.regs.rsi.toBitVec * 12#64 + d.regs.rdi.toBitVec + 4#64))
    (.add (.add (r .rdi) (.mul (r .rsi) (n 12))) (n 4))) "a base and an index of scale 12 (an imul folded in)"
  check (isVal (← ra `(fun d : MachineData => d.regs.rax.toBitVec * 2#64 + d.regs.rbx.toBitVec * 12#64))
    (.add (.mul (r .rax) (n 2)) (.mul (r .rbx) (n 12)))) "two terms without coefficient 1 are two indexes"
  check (isVal (← ra `(fun d : MachineData => d.regs.rax.toBitVec * 8#64 + d.regs.rbx.toBitVec * 8#64))
    (.add (.mul (r .rax) (n 8)) (.mul (r .rbx) (n 8)))) "two scaled terms are two indexes"
  check (isVal (← ra `(fun d : MachineData => d.regs.rax.toBitVec + d.regs.rbx.toBitVec + d.regs.rcx.toBitVec))
    (.add (.add (r .rax) (.mul (r .rbx) (n 1))) (.mul (r .rcx) (n 1)))) "three terms are a base and two indexes"
  check (isVal (← ra `(fun d : MachineData => d.regs.rbx.toBitVec * 4#64 + d.regs.rax.toBitVec * 8#64 + d.regs.rcx.toBitVec + 24#64))
    (.add (.add (.add (r .rcx) (.mul (r .rbx) (n 4))) (.mul (r .rax) (n 8))) (n 24))) "the base is the first term of coefficient 1"
  -- the scale of 12 is accepted for one index (above); a third term is a second index
  check (isVal (← ra `(fun d : MachineData => d.regs.rdi.toBitVec + d.regs.rsi.toBitVec * 12#64 + d.regs.rdx.toBitVec))
    (.add (.add (r .rdi) (.mul (r .rsi) (n 12))) (.mul (r .rdx) (n 1)))) "a base, an index of scale 12 and a third term are a base and two indexes"
  check (isVal (← ra `(fun d : MachineData => d.regs.rdi.toBitVec + d.regs.rsi.toBitVec * 12#64 + d.regs.rdx.toBitVec * 8#64 + 4#64))
    (.add (.add (.add (r .rdi) (.mul (r .rsi) (n 12))) (.mul (r .rdx) (n 8))) (n 4))) "three terms and a displacement are a base, two indexes and a displacement"
  check (isErr (← ra `(fun d : MachineData => d.regs.rax.toBitVec / 7#64)) (· == .unsupported ``HDiv.hDiv))
    "an address with a division is refused at the head"

/-! ## A walk: loads, the call, a branch -/

#eval show TermElabM Unit from do
  let walk (stx : TermElabM Syntax) : TermElabM Walk := do
    match ← walkTerm (← blockContext []) (← elabE stx) with
    | .ok w => pure w
    | .error e => throwError "walk error: {repr e}"
  -- two loads and a store: the loads are numbered 0 and 1, the store 0
  let w ← walk `(fun d : MachineData =>
    d.load (d.regs.rsp.toBitVec + 8#64) Width.W64 fun v s =>
      s.store (w := Width.W64) d.regs.rdi.toBitVec v fun s =>
        s.load (v + 16#64) Width.W64 fun u s =>
          Effects.done ⟨{ s with regs := { s.regs with rax := UInt64.ofBitVec u, rbx := UInt64.ofBitVec v + 1 } }, 110⟩)
  match readWalk 100 w with
  | .ok b =>
    check (match b.exit with | .goto 10 => true | _ => false) "goto 10 from the base 100"
    check (b.regs.map (·.1) == [.rax, .rbx]) "rax and rbx"
    check (isVal (.ok (regVal b.regs .rax)) (.load 1)) "rax is load 1"
    check (isVal (.ok (regVal b.regs .rbx)) (.add (.load 0) (n 1))) "rbx is load 0 + 1"
    match b.accesses with
    | [.load 0 a0 .W64, .store 0 a1 .W64 v1, .load 1 a2 .W64] =>
      check (isVal (.ok a0) (.add (r .rsp) (n 8))) "the address of load 0"
      check (isVal (.ok a1) (r .rdi)) "the address of store 0"
      check (isVal (.ok v1) (.load 0)) "the value of store 0"
      check (isVal (.ok a2) (.add (.load 0) (n 16))) "the address of load 1"
    | _ => throwError "the accesses: load 0, store 0, load 1"
  | .error e => throwError "read error {repr e}"
  -- a byte load is its zero extension: `setWidth 64 v` and the low byte of `v` are `load 0`
  let w ← walk `(fun d : MachineData =>
    d.load d.regs.rdi.toBitVec Width.W8 fun v s =>
      Effects.done ⟨{ s with regs := { s.regs with rax := UInt64.ofBitVec (BitVec.setWidth 64 (BitVec.extractLsb' 0 8 (BitVec.setWidth 64 v))) } }, 110⟩)
  match readWalk 100 w with
  | .ok b => check (isVal (.ok (regVal b.regs .rax)) (.load 0)) "a byte load zero-extended is load 0"
  | .error e => throwError "read error {repr e}"
  -- a call: the stored return address is `retAddr` of the offset of the continuation
  let w ← walk `(fun d : MachineData =>
    Effects.require_exec_access ⟨110, 115⟩ fun _ =>
      d.store (w := Width.W64) (d.regs.rsp.toBitVec - 8#64) (115#64 : BitVec 64) fun s =>
        Effects.done ⟨{ s with regs := { s.regs with rsp := s.regs.rsp - 8 } }, 300⟩)
  match readWalk 100 w with
  | .ok b =>
    check (match b.exit with | .call 300 15 => true | _ => false) "call 300, continuation 15"
    check (match b.accesses with | [.store 0 _ .W64 (.retAddr 15)] => true | _ => false) "the store of retAddr 15"
  | .error e => throwError "read error {repr e}"
  -- a branch: its condition and its targets
  let w ← walk `(fun d : MachineData =>
    Effects.done ⟨d, if d.regs.rax.toBitVec - d.regs.rbx.toBitVec = 0#64 then 107 else 109⟩)
  match readWalk 100 w with
  | .ok b =>
    check (match b.exit with | .branch c 7 9 => c.show == (Cond.eq (r .rax) (r .rbx)).show | _ => false)
      "branch on rax = rbx to 7, else 9"
  | .error e => throwError "read error {repr e}"
  -- a branch with an unknown condition is an error of the block
  let w ← walk `(fun d : MachineData => Effects.done ⟨d, if d.regs.rax.toNat % 3 = 1 then 107 else 109⟩)
  check (match readWalk 100 w with | .error (.unsupported h) => h == ``Eq | _ => false) "an unknown branch condition"
  -- a value with an unsupported head is an error of the block
  let w ← walk `(fun d : MachineData =>
    Effects.done ⟨{ d with regs := { d.regs with rax := d.regs.rax / d.regs.rbx } }, 110⟩)
  check (match readWalk 100 w with | .error (.unsupported h) => h == ``HDiv.hDiv | _ => false) "div is refused in a walk"
