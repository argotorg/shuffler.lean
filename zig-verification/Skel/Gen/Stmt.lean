import Skel.Gen.Types
import Skel.Gen.Frame
import Skel.Gen.Model
import Skel.Render

/-! The statements of the block lemmas and the proof text of `decompiles_l2` (`docs/one-way-lift-g1-plan-20261118.md`,
section 2.4, rules 6, 7 and 9; task G1-09). The forms are those of E1 and E5 (`/tmp/g1-plan/E1.lean`, `E5.lean`).

A block statement:

    theorem <block> : ∀ {policy : CpuPolicy} (hx : SysV.ExecRange policy <lo> <hi>) (d : MachineData)
        <each access: its value, then its hypothesis> {Q : MachineState → Prop} <the exit hypotheses>,
        Reaches <step> policy Q ⟨d, <pc>⟩ := by intros; lift_block

* A load `k` is `(v<k+1> : UInt64)` with `(hread<k+1> : readRam … .W64 = .ok v<k+1>.toBitVec)`. The return word of a block
  that returns is `(ra : Int64)` with `(hret : readRam …)`. A store `k` is `(m<k+1> : DataMem)` with
  `(hwrite<k+1> : writeRam …)`.
* A load of `w` bits below 64 (N13) is `(v<k+1> : BitVec w)` with `(hread<k+1> : readRam … .W<w> = .ok v<k+1>)`; its value
  is `BitVec.zeroExtend 64 v<k+1>` (`Val.load` of a narrow load is the zero extension, as the reader of N7 gives it). A
  store of `w` bits below 64 writes `BitVec.truncate w x` of its 64-bit value `x` (`storeText`).
* A register is `d.regs.<r>`. An exit hypothesis gives the state after the block (its field updates, then `dmem` when the
  block stores), and the PC of the exit: `<entry> + <offset>`, `ra` for a return, and for a call the entry PC of the
  callee (`calleePC`).
* A branch gives two hypotheses, `hyes : c → …` and `hno : ¬ c → …` (`a ≠ b` for `a = b`). A trap exit gives `c → False`.
* The field updates follow the first write of each register, with `rsp` last (E1, E5).

Errors and fallbacks (documented, so that a check fails and no text is accepted silently):
* `blockStatement` gives a `GenError` for a block with no statement: `unsupported` for a trap exit, a return whose last
  access is not a load of 64 bits, or a branch to a return or a call; `callee` for a call to a function with no interface.
  A trap block has no row (rule 10), so `rows` does not ask for its statement.
* `decompilesProof` gives a case for each block: a goto, a branch with two gotos, a return, and a trap block (its model step
  is `stuck`, so the case is `cases hn`), each after any number of loads and guarded stores through a register, of any
  width (a guarded store of `w` bytes has the guard `Clear` of `w` bytes).
  The invariant of the proof is `rep ∧ x.input = a ∧ At` (E1). When the state has memory or a state field is an input, it
  has `l = .entry → x = init a` (the entry state of the model is `init a`, which `At` does not say); when the state has
  memory it has the fact that the return word is unchanged in `x.mem`, which each store keeps by its guard.
  A block whose `At` has the conjunction form (a register that some paths write and others do not) has the case of the
  section "The conjunction form of `At`" (L2-GATE). In the memory form and in the conjunction form the hypotheses of the
  accesses are holes of `refine`.
* A block with a stack access or a call gets a case `fail "…"` (O2, O3). The entry block in a form with `init` unfolds
  `init` in `hn` (L2-GATE).
* The frame form (a stack room and no store through a register) has the proof of `frameProof` (G1-16): see its section.
  The entry block with an access in the memory form reads the input memory (`init`); the return
  word fact of a store chain from it is `Sites.readRet` (N13), and with no store it is `hkeep` (the memory of `init`). A
  function with no block, or a store through a register with no guard
  gets one `fail`: for the last, the model lets the store reach the return word, and `decompiles_l2` is false.

The lemmas are named by their blocks and are referred to by bare name in the proof. The statements must be placed in the
namespace of the proof (G1-10). -/

namespace Skel.Gen

/-! ## Names -/

/-- How a text names the registers at a block start: `reg r` is the text of the field of `r`; `entry` is the entry PC;
`loadU k` is the text of the value of load `k` as a `UInt64`, and `loadB k` as a `BitVec 64`; `flag f` is the text of
the flag `f` at the block start (a `Bool`). -/
structure Names where
  reg : Reg64 → String
  entry : String
  loadU : Nat → String
  loadB : Nat → String
  flag : Flag → String

/-- The name of the value of load `k` in a statement (`v1` for the first load). -/
private def valName (k : Nat) : String := s!"v{k + 1}"

/-- The name of the value of load `k` in the model (`v` for the first load, then `v1`, as `Model.lean` names it). -/
private def loadVar (k : Nat) : String := if k == 0 then "v" else s!"v{k}"

/-- The names of a statement of a block with the accesses `accs`: the fields of the machine data `d`. A load of 64 bits is a
`UInt64`; a load below 64 bits is a bit vector of its width, used with its zero extension. -/
private def stmtNames (t : Target) (accs : List Access) : Names :=
  let narrow (k : Nat) : Bool := loadWidthOf accs k != .W64
  ⟨fun r => s!"d.regs.{regLower r}", t.entryPC,
    fun k => if narrow k then s!"UInt64.ofBitVec (BitVec.zeroExtend 64 {valName k})" else valName k,
    fun k => if narrow k then s!"(BitVec.zeroExtend 64 {valName k})" else s!"{valName k}.toBitVec",
    fun f => s!"d.status.{f.name}"⟩

/-- The names of the proof of `decompiles_l2` for a block with the accesses `accs`: `x.input` for a register that no block
sets, `x` for a state field, and the variables of the model for a loaded value (a load below 64 bits with its zero
extension, as `Model.lean` writes it). A flag input is the state field `x.f` (as `Model.lean` names it). -/
private def proofNames (t : Target) (v : Vars) (accs : List Access) : Names :=
  let narrow (k : Nat) : Bool := loadWidthOf accs k != .W64
  ⟨fun r => if v.state.contains r then s!"x.{regLower r}" else s!"x.input.{regLower r}", t.entryPC,
    fun k => if narrow k then s!"(UInt64.ofBitVec (BitVec.zeroExtend 64 {loadVar k}))" else s!"(UInt64.ofBitVec {loadVar k})",
    fun k => if narrow k then s!"(BitVec.zeroExtend 64 {loadVar k})" else loadVar k, fun f => s!"x.{f.name}"⟩

/-- The name of the memory after store `k` (`m1` for the first store). -/
private def memName (k : Nat) : String := s!"m{k + 1}"

/-- The name of the hypothesis that load `k` reads its value. -/
private def readHyp (k : Nat) : String := s!"hread{k + 1}"

/-- The name of the hypothesis that store `k` writes its memory. -/
private def writeHyp (k : Nat) : String := s!"hwrite{k + 1}"

/-- The PC of the block at `off`: the entry PC, or the entry PC plus the offset (rule 7). -/
private def pcText (n : Names) (off : Nat) : String :=
  if off == 0 then n.entry else s!"{n.entry} + {off}"

/-- The entry PC of the callee `label` of the target `t`; `none` for a callee with no interface. -/
private def calleePC (t : Target) (label : String) : Option String :=
  (t.callees.find? (·.name == label)).map (·.entryPC)

/-! ## Values and conditions -/

mutual
/-- A 64-bit value, as a `UInt64`. -/
def valU (n : Names) : Val → Tm
  | .reg r => atom (n.reg r)
  | .lit k => atom (toString k)
  | .load k => atom (n.loadU k)
  | .retAddr off => atom s!"UInt64.ofBitVec (({n.entry} + {off}).toBitVec)"
  | .add a b => binop 65 "+" (valU n a) (valU n b)
  | .sub a b => binop 65 "-" (valU n a) (valU n b)
  | .mul a b => binop 70 "*" (valU n a) (valU n b)
  | .shr a k => (s!"{paren 75 (asU a (valU n a))} >>> ({k} : UInt64)", 75)
  | .zext32 a => zextU 32 (asU a (valU n a))
  | .and a b => binop 60 "&&&" (valU n a) (valU n b)
  | .or a b => binop 55 "|||" (valU n a) (valU n b)
  | .xor a b => binop 58 "^^^" (valU n a) (valU n b)
  | .not a => atom s!"(~~~{paren 1024 (asU a (valU n a))})"
  | .neg a => binop 65 "-" (atom "0") (valU n a)
  | .shl a k => (s!"{paren 75 (asU a (valU n a))} <<< ({k} : UInt64)", 75)
  | .extract lo len a _ => extractU lo len (asU a (valU n a))
  | .zext w a => zextU w.bits (asU a (valU n a))
  | .sext w a => atom s!"UInt64.ofBitVec ({(sextB w.bits (asB a (valB n a))).1})"
  | .replaceLow .b32 _ b => zextU 32 (asU b (valU n b))
  | .replaceLow w a b => replaceU w.bits (valU n a) (valU n b)
  | .setcc c => atom s!"(if {(condP n c).1} then 1 else 0)"
  | .ite c a b => atom s!"(if {(condP n c).1} then {(valU n a).1} else {(valU n b).1})"

/-- A bit vector of 64 bits, as a `BitVec 64` (the addresses and the stored values of the memory). -/
def valB (n : Names) : Val → Tm
  | .reg r => atom s!"{n.reg r}.toBitVec"
  | .lit k => atom (toString k)
  | .load k => atom (n.loadB k)
  | .retAddr off => atom s!"({n.entry} + {off}).toBitVec"
  | .add a b => binop 65 "+" (valB n a) (valB n b)
  | .sub a b => binop 65 "-" (valB n a) (valB n b)
  | .mul a b => binop 70 "*" (valB n a) (valB n b)
  | .shr a k => atom s!"BitVec.ushiftRight ({(asB a (valB n a)).1}) {k}"
  | .zext32 a => zextB 32 (asB a (valB n a))
  | .and a b => binop 60 "&&&" (valB n a) (valB n b)
  | .or a b => binop 55 "|||" (valB n a) (valB n b)
  | .xor a b => binop 58 "^^^" (valB n a) (valB n b)
  | .not a => atom s!"(~~~{paren 1024 (asB a (valB n a))})"
  | .neg a => binop 65 "-" (atom "0") (valB n a)
  | .shl a k => atom s!"BitVec.shiftLeft ({(asB a (valB n a)).1}) {k}"
  | .extract lo len a _ => atom s!"BitVec.zeroExtend 64 (BitVec.extractLsb' {lo} {len} ({(asB a (valB n a)).1}))"
  | .zext w a => zextB w.bits (asB a (valB n a))
  | .sext w a => sextB w.bits (asB a (valB n a))
  | .replaceLow .b32 _ b => zextB 32 (asB b (valB n b))
  | .replaceLow w a b => replaceU w.bits (valB n a) (valB n b)
  | .setcc c => atom s!"(if {(condP n c).1} then 1 else 0)"
  | .ite c a b => atom s!"(if {(condP n c).1} then {(valB n a).1} else {(valB n b).1})"

/-- A condition, as a proposition. -/
def condP (n : Names) : Cond → Tm
  | .eq a b => (s!"{paren 51 (both a b (valU n a))} = {paren 51 (valU n b)}", 50)
  | .ule a b => (s!"{paren 51 (both a b (valU n a))} ≤ {paren 51 (valU n b)}", 50)
  | .ult a b => (s!"{paren 51 (both a b (valU n a))} < {paren 51 (valU n b)}", 50)
  | .slt a b => atom s!"BitVec.slt ({(asB a (valB n a)).1}) ({(asB b (valB n b)).1})"
  | .slt32 a b =>
    atom s!"BitVec.slt (BitVec.truncate 32 ({(asB a (valB n a)).1})) (BitVec.truncate 32 ({(asB b (valB n b)).1}))"
  | .not c => atom s!"¬ ({(condP n c).1})"
  | .iff p q => atom s!"(({(condP n p).1}) ↔ ({(condP n q).1}))"
  | .flag f => (s!"{n.flag f} = true", 50)
end

/-- The negation of a condition: `a ≠ b` for `a = b`, the condition itself for `¬ c`, else `¬ c` (as E5 writes it). -/
private def negP (n : Names) : Cond → Tm
  | .eq a b => (s!"{paren 51 (both a b (valU n a))} ≠ {paren 51 (valU n b)}", 50)
  | .not c => condP n c
  | c => atom s!"¬ {(condP n c).1}"

mutual
/-- The registers that a value reads. -/
private def valRegs : Val → List Reg64
  | .reg r => [r]
  | .lit _ => []
  | .load _ => []
  | .retAddr _ => []
  | .add a b => valRegs a ++ valRegs b
  | .sub a b => valRegs a ++ valRegs b
  | .mul a b => valRegs a ++ valRegs b
  | .shr a _ => valRegs a
  | .zext32 a => valRegs a
  | .and a b | .or a b | .xor a b | .replaceLow _ a b => valRegs a ++ valRegs b
  | .not a | .neg a | .shl a _ | .extract _ _ a _ | .zext _ a | .sext _ a => valRegs a
  | .setcc c => condRegs c
  | .ite c a b => condRegs c ++ valRegs a ++ valRegs b

/-- The registers that a condition reads. -/
private def condRegs : Cond → List Reg64
  | .eq a b => valRegs a ++ valRegs b
  | .ule a b => valRegs a ++ valRegs b
  | .ult a b => valRegs a ++ valRegs b
  | .slt a b => valRegs a ++ valRegs b
  | .slt32 a b => valRegs a ++ valRegs b
  | .not c => condRegs c
  | .iff p q => condRegs p ++ condRegs q
  | .flag _ => []
end

/-! ## The statement of a block -/

/-- The field updates of a block: `rax := …`, in the order of the first write, with `rsp` last. -/
private def regUpdates (n : Names) (b : Block) : List String :=
  let field (p : Reg64 × Val) : String := s!"{regLower p.1} := {(valU n p.2).1}"
  (b.regs.filter (·.1 != .rsp)).map field ++ (b.regs.filter (·.1 == .rsp)).map field

/-- The state after a block, for an exit with the flag `f`. -/
private def stateText (n : Names) (b : Block) (mem : Option String) : String :=
  let regs := regUpdates n b
  let regsPart := if regs.isEmpty then [] else [s!"regs := \{ d.regs with {", ".intercalate regs} }"]
  let memPart := match mem with
    | some m => [s!"dmem := {m}"]
    | none => []
  "{ d with " ++ ", ".intercalate (regsPart ++ memPart ++ ["status := f"]) ++ " }"

/-- The value of the kept flag `g` at the exit of a block (L2-FLAGS), a `Bool`: the flag of the start when the block keeps
it, else `decide` of its condition. -/
def flagValText (n : Names) (g : Flag) : Cond → String
  | .flag g' => if g' == g then n.flag g else s!"decide ({(condP n (.flag g')).1})"
  | c => s!"decide ({(condP n c).1})"

/-- The hypotheses of the exits of a block, with the memory `mem` after the block when it stores. `none` when an exit
has no text: a goto is `(hQ : ∀ f : StatusFlags, Q ⟨state, pc⟩)`, a branch gives `(hyes : c → …)` and `(hno : ¬ c → …)`
(a trap side gives `c → False`), and a call gives its callee PC. A block with kept flags (`Block.flags`, L2-FLAGS) states
the value of each kept flag at a goto: `∀ f : StatusFlags, f.cf = decide (…) → … → Q ⟨state, pc⟩`. A block with no kept
flag has the exits for all flags. -/
private def exitHyps (t : Target) (n : Names) (b : Block) (mem : Option String) : Option (List String) :=
  let st := stateText n b mem
  let kept := String.join (b.flags.map fun (g, c) => s!"f.{g.name} = {flagValText n g c} → ")
  match b.term with
  | .exit .trap => none
  | .exit (.goto k) => some [s!"(hQ : ∀ f : StatusFlags, {kept}Q ⟨{st}, {pcText n k}⟩)"]
  | .exit .ret => some [s!"(hQ : ∀ f : StatusFlags, Q ⟨{st}, ra⟩)"]
  | .exit (.call f _) => (calleePC t f).map fun pc => [s!"(hQ : ∀ f : StatusFlags, Q ⟨{st}, {pc}⟩)"]
  | .branch c y no =>
    let side (name cond : String) (e : Exit) : Option String :=
      match e with
      | .goto k => some s!"({name} : {cond} → ∀ f : StatusFlags, {kept}Q ⟨{st}, {pcText n k}⟩)"
      | .trap => some s!"({name} : {cond} → False)"
      | _ => none
    match side "hyes" (condP n c).1 y, side "hno" (negP n c).1 no with
    | some a, some b' => some [a, b']
    | _, _ => none

/-- The binders of the accesses of a block in order, each access with its hypothesis, and the memory after them. The
memory before the first access is `mem`. A load that is the last access of a returning block is the return word
`ra`; `none` when that load is below 64 bits. A load below 64 bits is a bit vector of its width; a store below 64 bits
writes the low bits of its value (`storeText`). -/
private def accessBinders (n : Names) (ret : Bool) : List Access → String → Option (List String × String)
  | [], mem => some ([], mem)
  | .load k addr w :: rest, mem => do
    let a := paren 1024 (valB n addr)
    let own ←
      if ret && rest.isEmpty then
        if w == .W64 then some ["(ra : Int64)", s!"(hret : readRam policy {mem} {a} .W64 = .ok ra.toBitVec)"] else none
      else if w == .W64 then
        some [s!"({valName k} : UInt64)", s!"({readHyp k} : readRam policy {mem} {a} .W64 = .ok {valName k}.toBitVec)"]
      else
        some [s!"({valName k} : BitVec {w.bits})", s!"({readHyp k} : readRam policy {mem} {a} {widthText w} = .ok {valName k})"]
    let (bs, final) ← accessBinders n ret rest mem
    pure (own ++ bs, final)
  | .store k addr w v :: rest, mem => do
    let a := paren 1024 (valB n addr)
    let m := memName k
    let own := [s!"({m} : DataMem)", s!"({writeHyp k} : writeRam policy {mem} {a} {widthText w} {storeText w v (valB n v)} = .ok {m})"]
    let (bs, final) ← accessBinders n ret rest m
    pure (own ++ bs, final)

/-- Does a list of accesses have a store? -/
private def hasStore : List Access → Bool
  | [] => false
  | .store .. :: _ => true
  | .load .. :: rest => hasStore rest

/-- The statement of a block, or the error of a block with no statement (see the module comment). -/
private def statementOf (t : Target) (b : Block) : Except GenError String := do
  let n := stmtNames t b.accesses
  let ret := match b.term with
    | .exit .ret => true
    | _ => false
  if ret then
    match b.accesses.getLast? with
    | some (.load _ _ .W64) => pure ()
    | _ => throw (.unsupported b.offset "a return with no return word")
  match b.term with
  | .exit (.call f _) => if (calleePC t f).isNone then throw (.callee f)
  | _ => pure ()
  let some (accBs, final) := accessBinders n ret b.accesses "d.dmem"
    | throw (.unsupported b.offset "a return with no return word")
  let some hyps := exitHyps t n b (if hasStore b.accesses then some final else none)
    | throw (.unsupported b.offset "an exit with no statement: a trap, or a branch to a return or a call")
  pure ("theorem " ++ b.name.s ++ " : ∀ {policy : CpuPolicy} (hx : SysV.ExecRange policy " ++ t.lo ++ " " ++ t.hi ++
    ") " ++ " ".intercalate (["(d : MachineData)"] ++ accBs ++ ["{Q : MachineState → Prop}"] ++ hyps) ++
    ",\n    Reaches " ++ t.step ++ " policy Q ⟨d, " ++ pcText n b.offset ++ "⟩ := by intros; lift_block")

/-- The statement of the block lemma of `b` for the target `t`: `theorem <block> : ∀ … , Reaches … := by intros;
lift_block`. A block with no statement gives the error `GenError.unsupported` with its cause (a trap exit, a return with no
return word of 64 bits, a branch to a return or a call), or `GenError.callee` for a call to a callee with no
interface. The summary `_s` is not needed: a statement names the registers of the block. -/
def blockStatement (t : Target) (_s : Summary) (b : Block) : Except GenError String :=
  statementOf t b

/-! ## The proof of `decompiles_l2` -/

/-- The form of the proof: the state has memory (every store is guarded), and the invariant has `l = .entry → x = init a`
(the entry state is not constant: some state field is an input, or the state has memory). The form of E1 has neither. -/
private structure Form where
  mem : Bool
  needInit : Bool

private def formOf (v : Vars) : Form :=
  ⟨v.mem, v.mem || v.state.any (v.inputs.contains ·)⟩

/-- The hypothesis names `← h<r>` (rewrites of the rep equations) for the input registers of `regs` that are not state
fields. -/
private def inputRewrites (v : Vars) (regs : List Reg64) : List String :=
  (v.inputs.filter (fun r => !v.state.contains r && regs.contains r)).map fun r => s!"← h{regLower r}"

/-- The text of `n` spaces and then `l`. -/
private def at' (n : Nat) (l : String) : String := "".pushn ' ' n ++ l

/-- The hypothesis names of a store of the model: the guard, and the write. -/
private def guardHyp (n : Nat) : String := s!"hc{n + 1}"

private def writeHypP (n : Nat) : String := s!"hw{n + 1}"

/-- Does the block end with a return? -/
private def endsInRet (b : Block) : Bool :=
  match b.term with
  | .exit .ret => true
  | _ => false

/-- Does the block end with a call? -/
private def endsInCall (b : Block) : Bool :=
  match b.term with
  | .exit (.call _ _) => true
  | _ => false

/-- The accesses that the model has: all, except the load of the return word of a block that returns. -/
private def modelAccesses (b : Block) : List Access :=
  if endsInRet b then b.accesses.dropLast else b.accesses

/-- The stores among accesses. -/
private def storesOf (accs : List Access) : List Nat :=
  accs.filterMap fun
    | .store n .. => some n
    | .load .. => none

/-- Does the block keep a flag at its exit or read a kept flag at its start (L2-FLAGS)? The proof covers these blocks in
the frame form only. -/
private def hasKeptFlags (b : Block) : Bool := !b.flags.isEmpty || !(startFlags b).isEmpty

/-- Why the case of a block has no text, or `none` when it has one. -/
private def unsupported (f : Form) (b : Block) : Option String :=
  let isStack : Access → Bool
    | .load _ a _ => a.usesRsp
    | .store _ a _ _ => a.usesRsp
  let lastIsLoad := match b.accesses.getLast? with
    | some (.load _ _ .W64) => true
    | _ => false
  let isTrap : Exit → Bool
    | .trap => true
    | _ => false
  let trapSide := match b.term with
    | .branch _ y n => isTrap y || isTrap n
    | _ => false
  if hasKeptFlags b then some "a kept flag (L2-FLAGS: the frame form only)"
  else if endsInCall b then some "a call (O2)"
  else if (modelAccesses b).any isStack then some "a stack access (O3)"
  else if endsInRet b && !lastIsLoad then some "a return with no return word (O3)"
  else if trapSide then some "a trap side of a branch (O3)"
  else if (match b.term with | .exit .trap => !b.accesses.isEmpty | _ => false) then some "a trap block with accesses (O3)"
  else none

/-- The tactic that proves that a guarded store of the model does not meet the return word: the 8 bytes at the address
and the 8 bytes at `rsp` are disjoint, from the guard `hc<n>`. -/
private def disjointTac (n : Nat) : String :=
  s!"intro i hi l hl e; have hl8 : l < 8 := hl; apply {guardHyp n} i hi; unfold Private; rw [e, hsp]; bv_omega"

/-- The fact that the return word is unchanged after the stores of the block, from the fact `base` before it. -/
private def keepFrom (stores : List Nat) (base : String) : String :=
  stores.foldl (fun acc n => s!"Sites.readRam_of_writeRam {writeHypP n} (by {disjointTac n}) ({acc})") base

/-- The fact that the return word is unchanged after the stores of the block, from the fact `hkeep` before it, for the
return address `ra` (the names `r` and `hr`). In the entry block (`entry`) the memory is that of the machine: the fact
before the stores is `Sites.readRet`. -/
private def keepChain (entry : Bool) (stores : List Nat) (r hr : String) : String :=
  keepFrom stores (if entry then s!"Sites.readRet he {hr}" else s!"hkeep {r} {hr}")

/-- The rewrites `← h<r>` of the input registers among `regs`: in the entry block (`entry`) all inputs, as `init` copies the
inputs to the state fields; else the inputs that are not state fields. -/
private def regRewrites (v : Vars) (entry : Bool) (regs : List Reg64) : List String :=
  if entry then ((v.inputs.filter regs.contains).map fun r => s!"← h{regLower r}") else inputRewrites v regs

/-- The rewrite of the hypotheses of one access of the model, from the model terms to the machine terms. `fresh`: no store
of the block comes before the access, so it reads the memory at the block start; in the memory form that memory is the
input memory in the entry block (`hmem`), and the state memory in the others. -/
private def accessRewrites (v : Vars) (f : Form) (entry fresh : Bool) : Access → List String
  | .load k addr _ =>
    let memRw := if !f.mem || (entry && fresh) then ["hmem"] else []
    [s!"rw [{", ".intercalate (["hpol"] ++ memRw ++ regRewrites v entry (valRegs addr))}] at h{loadVar k}"]
  | .store n addr _ val =>
    let memRw := if f.mem && entry && fresh then ["hmem"] else []
    let addrRws := regRewrites v entry (valRegs addr)
    [s!"rw [{", ".intercalate (["hpol"] ++ memRw ++ regRewrites v entry (valRegs addr ++ valRegs val))}] at {writeHypP n}"] ++
      (if addrRws.isEmpty then [] else [s!"rw [{", ".intercalate addrRws}] at {guardHyp n}"])

/-- The rewrites of the accesses of a block in order (`accessRewrites`, with `fresh` until the first store). -/
private def accessesRewrites (v : Vars) (f : Form) (entry : Bool) (accs : List Access) : List String :=
  (accs.foldl (fun (acc : List String × Bool) a =>
    let fresh' := acc.2 && (match a with | .store .. => false | .load .. => true)
    (acc.1 ++ accessRewrites v f entry acc.2 a, fresh')) ([], true)).1

/-- The value of the load `k` of width `w` of the model as the binder of the block lemma: a `UInt64` for 64 bits, else the
bit vector of the width itself. -/
private def loadArg (k : Nat) (w : Width) : String :=
  if w == .W64 then s!"(UInt64.ofBitVec {loadVar k})" else loadVar k

/-- The arguments of the block lemma for one access of the model: the value and its hypothesis. -/
private def accessArgs : Access → List String
  | .load k _ w => [loadArg k w, s!"h{loadVar k}"]
  | .store n .. => [s!"m{n + 1}", writeHypP n]

/-- The nested cases of the accesses of the model, from the indent `ind`: a load or a write splits `hn` into the success
case, which goes on, and the failure case, which `cases hn` closes. A guarded store has the guard split first. -/
private def splitsOf (accs : List Access) (ind : Nat) (k : Nat → List String) : List String :=
  match accs with
  | [] => k ind
  | .load n .. :: rest =>
    [at' ind "split at hn", at' ind s!"· rename_i {loadVar n} h{loadVar n}"] ++ splitsOf rest (ind + 2) k ++
      [at' ind "· cases hn"]
  | .store n .. :: rest =>
    [at' ind "split at hn", at' ind s!"· rename_i {guardHyp n}", at' (ind + 2) "split at hn",
      at' (ind + 2) s!"· rename_i m{n + 1} {writeHypP n}"] ++ splitsOf rest (ind + 4) k ++
      [at' (ind + 2) "· cases hn", at' ind "· cases hn"]

/-- The invariant of the next block, from the proof `atP` of its `At` and the proof `keep` of the return word fact in the
memory form. -/
private def arriveWith (f : Form) (atP keep : String) : String :=
  if !f.needInit then s!"⟨hrep, rfl, {atP}⟩"
  else if !f.mem then s!"⟨hrep, rfl, {atP}, nofun⟩"
  else s!"⟨hrep, rfl, {atP}, nofun, {keep}⟩"

/-- The state that the block gives, as the invariant of the next block in the equality form: `⟨hrep, rfl, …⟩`. The `flag`
is the name of the flags, `eq` the proof of the state equation, and `keep` the proof of the return word fact in the memory
form. -/
private def arrive (f : Form) (flag eq keep : String) : String :=
  if !f.needInit then s!"⟨hrep, rfl, {flag}, {eq}⟩" else arriveWith f s!"⟨{flag}, {eq}⟩" keep

/-! ### The conjunction form of `At` (L2-GATE)

A block whose `At` has the conjunction form (a register that some paths write and others do not, and no call) starts from
free machine data `d` with the facts of `atItems`: `hpc`, `hx<r>` (`d.regs.r = x.r`), `hk<r>` (`d.regs.r = s₀.data.regs.r`),
`hrsp`, `hdm`. The facts of the model are rewritten to the terms of `d`: a state field `x.r` by `← hx<r>`, an input
`x.input.r` by `← h<r>, ← hk<r>`, the memory by `← hdm`. An arrival at a block in the conjunction form proves each conjunct:
the `pc` by `rfl`, a register of `s₀` by `hk<r>` (or `rfl` when the machine data is that of `s₀`), `rsp` by `hrsp`, and a
register of the state and the memory by `simp only` with the facts that take the terms of the model to those of the
machine (`simpSet`). A goto from a block in the conjunction form to a block in the equality form gets `fail`. A return from
a block in the conjunction form proves the exit with `hrsp` and `hk<r>` of the callee-saved registers. -/

/-- The kind of the block that a case proves: the entry, a block in the equality form, or a block in the conjunction form,
each with its flow. -/
private inductive Src where
  | entry
  | eq (fb : Flow)
  | conj (fb : Flow)

/-- The fact of the register `r` in the flow `fb`. -/
private def factOf (fb : Flow) (r : Reg64) : RegFact := (fb.regs.lookup r).getD ⟨false, false⟩

/-- The rewrites of a model fact that reads the registers `regs` to the terms of the machine data `d` of a block in the
conjunction form; `none` when a register has no fact. -/
private def conjRws (v : Vars) (fb : Flow) (regs : List Reg64) : Option (List String) :=
  ((regs.eraseDups.filter (· != .rsp)).mapM fun r =>
    if v.state.contains r then (if (factOf fb r).x then some [s!"← hx{regLower r}"] else none)
    else if v.inputs.contains r && (factOf fb r).s0 then some [s!"← h{regLower r}", s!"← hk{regLower r}"]
    else none).map List.flatten

/-- The facts that take the terms of the model to those of the machine, for `simp only`: for the entry, `init`, the inputs
and the memory; for a block in the equality form, the inputs that are not state fields; for a block in the conjunction
form, `← hx<r>` of the state fields, `← h<r>, ← hk<r>` of the other inputs, and `← hdm`. The facts of `At` have the left
side `{ data := d, pc := … }.data…`, which `simp only` does not find in the goal; their right sides are model terms. -/
private def simpSet (v : Vars) (f : Form) : Src → List String
  | .entry => (if f.needInit then ["init"] else []) ++ v.inputs.map (fun r => s!"← h{regLower r}") ++
      (if f.mem then ["hmem"] else [])
  | .eq _ => (v.inputs.filter (!v.state.contains ·)).map fun r => s!"← h{regLower r}"
  | .conj fb => ((regOrder.filter (· != .rsp)).flatMap fun r =>
      let rf := factOf fb r
      if v.state.contains r then (if rf.x then [s!"← hx{regLower r}"] else [])
      else if rf.s0 && v.inputs.contains r then [s!"← h{regLower r}", s!"← hk{regLower r}"]
      else []) ++ ["← hdm"]

/-- The proof of an equation of the machine and the model by `rfl` or `simp only` with the facts `H`. -/
private def simpPf (H : List String) : String :=
  if H.isEmpty then "rfl" else s!"(by first | rfl | simp only [{", ".intercalate H}])"

/-- The proof of an equation of the machine and the model by `simp only` with the facts `H`, then `rfl`. The rewrites come
before `rfl`: after `simp only [e] at hn` a side can be a shift where the other side has a register, and `rfl` on it unfolds
the operations and uses up the heartbeats (L2-CALLBLK, `keepWildcardSlots` o44). -/
private def simpFirst (H : List String) : String :=
  if H.isEmpty then "rfl" else s!"(by first | (simp only [{", ".intercalate H}]; done) | rfl)"

/-- Check a record field with computed values as parameters first. The direct
proof remains available for a changed field whose relation needs those values. -/
private def stateFieldPf (proof : String) : String :=
  s!"(by first | (sim_state => exact {proof}) | exact {proof})"

/-- The proof of a conjunct of `At` of a block in the conjunction form at the exit of the block `b`; `none` when the text
has no proof of it. -/
private def conjItemPf (v : Vars) (b : Block) (src : Src) (H : List String) : AtItem → Option String
  | .pc => some "rfl"
  | .regX _ => some (simpPf H)
  | .regS r =>
    if (writesOf b).contains r then none
    else match src with
      | .entry => some "rfl"
      | .eq fb => if v.state.contains r && (factOf fb r).x then none else some "rfl"
      | .conj fb => if (factOf fb r).s0 then some s!"hk{regLower r}" else none
  | .rsp => match src with
    | .conj _ => some "hrsp"
    | _ => some "rfl"
  | .dmem => some (simpPf H)
  | _ => none

/-- The rewrites of the facts of the accesses of a block in the conjunction form, to the terms of `d`: a fact before the
first store reads `x.mem` (`← hdm`), or the input memory when the state has no memory (`hmem, ← hdm`). -/
private def conjAccessRewrites (v : Vars) (f : Form) (fb : Flow) (accs : List Access) : Option (List String) :=
  (accs.foldlM (m := Option) (init := (([] : List String), true)) fun (acc : List String × Bool) (a : Access) =>
    let (lines, fresh) := acc
    let mem := if !f.mem then ["hmem", "← hdm"] else if fresh then ["← hdm"] else []
    match a with
    | .load k addr _ => do
      let rs ← conjRws v fb (valRegs addr)
      pure (lines ++ [s!"rw [{", ".intercalate (["hpol"] ++ mem ++ rs)}] at h{loadVar k}"], fresh)
    | .store n addr _ val => do
      let rs ← conjRws v fb (valRegs addr ++ valRegs val)
      let g ← conjRws v fb (valRegs addr)
      pure (lines ++ [s!"rw [{", ".intercalate (["hpol"] ++ mem ++ rs)}] at {writeHypP n}"] ++
        (if g.isEmpty then [] else [s!"rw [{", ".intercalate g}] at {guardHyp n}"]), false)).map (·.1)

/-- The case of `b` in `cases l with`, with the flows `fl` of the blocks. A block that the text does not cover gets a
`fail` case. -/
private def armText (t : Target) (v : Vars) (f : Form) (fl : List (Nat × Flow)) (b : Block) : List String :=
  let name := b.name.s
  let head := s!"  | {name} =>"
  let failArm (why : String) := [head, s!"    fail \"decompiles_l2: the case of this block is not generated: {why}\""]
  match unsupported f b with
  | some why => failArm why
  | none =>
  match b.term with
  | .exit .trap => [head, "    simp only [blocks] at hn", "    cases hn"]
  | term =>
  match fl.lookup b.offset with
  | none => failArm "no path reaches the block"
  | some fb =>
    let isEntry := b.offset == 0
    let src : Src := if isEntry then .entry else if atConj fb then .conj fb else .eq fb
    let conj := match src with | .conj _ => true | _ => false
    -- the entry in a form with `init`: `hn` has `init` of the input, which the text unfolds
    let entryInit := isEntry && f.needInit
    let xn := if entryInit then
        { proofNames t v b.accesses with
          reg := fun r => if v.state.contains r then (if v.inputs.contains r then s!"x.input.{regLower r}" else "(0 : UInt64)")
            else s!"x.input.{regLower r}" }
      else proofNames t v b.accesses
    let accs := modelAccesses b
    let stores := storesOf accs
    let dArg := if isEntry || conj then "d" else "_"
    let single := match term with | .exit _ => true | _ => false
    let fl' := if isEntry && single then "f" else "f'"
    let accArgs := (accs.flatMap accessArgs) ++ (if endsInRet b then ["ra", "?_"] else [])
    -- the equation of the state after the block: the entry block with a non-constant state reads the input
    let blockRws := inputRewrites v (b.regs.flatMap fun p => valRegs p.2)
    let entryRws :=
      if entryInit then
        ["init"] ++ (v.inputs.filter v.state.contains).map (fun r => s!"← h{regLower r}") ++
          (if f.mem then ["hmem"] else [])
      else []
    let allRws := entryRws ++ blockRws
    let eq := if allRws.isEmpty then "rfl" else s!"by simp only [{", ".intercalate allRws}]"
    -- the entry block in the memory form reads the input memory (`init`), so its return word fact is `Sites.readRet`
    let entryMem := isEntry && f.mem && !accs.isEmpty
    -- with no store the memory of the next state is that of `hkeep` (the entry: `init`, after `rw [hent rfl]`)
    let keepArr :=
      if stores.isEmpty then "hkeep"
      else if conj then s!"fun r' hr' => {keepFrom stores "(by rw [hdm]; exact hkeep r' hr')"}"
      else s!"fun r' hr' => {keepChain entryMem stores "r'" "hr'"}"
    let H := simpSet v f src
    -- the invariant at the target `tgt`: the equality form (not from a block in the conjunction form), or the conjunction form
    -- `extra`: the fact of a branch condition `a = b` when `hn` has `b` in place of `a` in a register update
    let arrAt (extra : List String) (tgt : Nat) : Option String := do
      let g ← fl.lookup tgt
      if atConj g then
        let pfs ← (atItems v f.mem false g).mapM fun item =>
          (conjItemPf v b src (H ++ extra) item).map stateFieldPf
        pure (arriveWith f s!"⟨{", ".intercalate pfs}⟩" keepArr)
      else if conj then none
      else
        let eq' := if extra.isEmpty then eq else s!"by first | rfl | simp only [{", ".intercalate (allRws ++ extra)}]"
        pure (arrive f fl' eq' keepArr)
    let itemNames := (atItems v f.mem false fb).map AtItem.name
    let pre :=
      if isEntry then
        ["    cases hat"] ++ (if f.needInit then [s!"    rw [hent rfl] at hn{if f.mem then " hkeep" else ""}"] else [])
      else if conj then
        ["    obtain ⟨d, pc⟩ := s", s!"    obtain ⟨{", ".intercalate itemNames}⟩ := hat",
          s!"    obtain rfl : pc = {t.entryPC} + {b.offset} := hpc"]
      else ["    obtain ⟨f, rfl⟩ := hat"]
    let blocksSimp := if entryInit then "blocks, init" else "blocks"
    let top :=
      if accs.isEmpty then
        match term with
        | .branch .. => [s!"    simp only [{blocksSimp}] at hn"]
        | .exit _ => [s!"    simp only [{blocksSimp}, Res.ok.injEq] at hn", "    subst hn"]
      else [s!"    simp only [{blocksSimp}] at hn"]
    let rwsOpt : Option (List String) :=
      match src with
      | .conj fb => conjAccessRewrites v f fb accs
      | _ => some (accessesRewrites v f entryInit accs)
    -- the rewrites of the goal of a branch condition, from the terms of the model to those of the machine
    let condRws (c : Cond) : Option (List String) :=
      match src with
      | .conj fb => conjRws v fb (condRegs c)
      | .entry => some (regRewrites v entryInit (condRegs c))
      | .eq _ => some (inputRewrites v (condRegs c))
    let inner (ind : Nat) : Option (List String) := do
      let sub := if accs.isEmpty then [] else match term with
        | .branch .. => []
        | .exit _ => [at' ind "simp only [Res.ok.injEq] at hn", at' ind "subst hn"]
      let dp := if isEntry then [at' ind "obtain ⟨d, pc⟩ := s₀", at' ind s!"obtain rfl : pc = {t.entryPC} := he.pc"] else []
      let rws := (← rwsOpt).map (at' ind)
      -- the hypotheses of the accesses come after the goal fixes the machine data: they are goals of `refine` (a fact of
      -- `x.mem` as an argument next to `_` makes `isDefEq` time out); the form with no memory and no conjunction passes them
      let holes : List String := accs.flatMap fun
        | .load k _ w => [loadArg k w, "?_"]
        | .store n .. => [s!"m{n + 1}", "?_"]
      let hypGoals := (accs.map fun a => at' ind s!"· exact {(accessArgs a).getLast!}")
      let byHoles := f.mem || conj
      let (argsG, goalsG) := if byHoles then (holes, hypGoals) else (accs.flatMap accessArgs, [])
      let fin : List String ←
        match term with
        | .exit (.goto k) => do
          let arr ← arrAt [] k
          if byHoles then
            pure ([at' ind (" ".intercalate (["refine", name, "hx", dArg] ++ argsG ++ [s!"(fun {fl'} => {arr})"]))] ++ goalsG)
          else
            pure [at' ind (" ".intercalate (["exact", name, "hx", dArg] ++ accArgs ++ ["fun", fl', "=>", arr]))]
        | .exit .ret => do
          let bullet := if accs.isEmpty then "" else "· "
          if conj then
            -- the callee-saved registers keep the value of `s₀` (`hk<r>`); `post`: the exit, then `rax` and the memory
            -- (the memory form), or the memory and `rax`, each by `simpPf`
            let abis ← calleeSaved.mapM fun r =>
              if (writesOf b).contains r || !(factOf fb r).s0 then none else some s!"hk{regLower r}"
            let post := s!"fun _ => ⟨⟨hra, (by rw [hrsp]), {", ".intercalate abis}⟩, {simpPf H}, {simpPf H}⟩"
            let retTac := if f.mem then s!"rw [hrsp]; exact {keepFrom stores "(by rw [hdm]; exact hkeep ra hra)"}"
              else "rw [hrsp, hdm]; exact Sites.readRet he hra"
            pure ([at' ind (" ".intercalate (["refine", name, "hx", dArg] ++ holes ++ ["ra", "?_", post]))] ++ hypGoals ++
              [at' ind s!"{bullet}{retTac}"])
          else
            let proof := if f.mem then keepChain entryMem stores "ra" "hra" else "Sites.readRet he hra"
            -- `rax` reads the input registers of the call (`x.input`), the block the registers of the machine state
            let raxRws := allRws ++ (regRewrites v entryMem (valRegs (endVal b .rax))).filter (!allRws.contains ·)
            let raxEq := if raxRws.isEmpty then "rfl" else s!"(by first | rfl | simp only [{", ".intercalate raxRws}])"
            -- `post`: the exit, then `rax` and the memory (the memory form), or the memory and `rax`
            let post := if f.mem then s!"fun _ => ⟨⟨hra, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, {raxEq}, rfl⟩"
              else s!"fun _ => ⟨⟨hra, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, {raxEq}⟩"
            pure ([at' ind (" ".intercalate (["refine", name, "hx", dArg] ++ holes ++ ["ra", "?_", post]))] ++ hypGoals ++
              [at' ind s!"{bullet}exact {proof}"])
        | .branch c (.goto y) (.goto n) => do
          -- `simp only [e]` at `hn` puts `b` in place of `a` in the updates of `a = b`: the arrival rewrites the
          -- machine side with the fact (`e`, or `h` of the machine terms in the conjunction form)
          let inUpdate := match c with
            | .eq a _ => let at_ := (valU xn a).1; b.regs.any fun p => ((valU xn p.2).1.splitOn at_).length > 1
            | _ => false
          let extra := if inUpdate then [if conj then "h" else "e"] else []
          let ay ← arrAt extra y
          let an ← arrAt [] n
          let rws' ← condRws c
          let by' := if rws'.isEmpty then "exact h" else s!"rw [{", ".intercalate rws'}]; exact h"
          pure ([at' ind (" ".intercalate (["refine", name, "hx", dArg] ++ argsG ++
              [s!"(fun h {fl'} => ?_)", s!"(fun h {fl'} => ?_)"]))] ++ goalsG ++ [
            at' ind s!"· have e : {(condP xn c).1} := by {by'}",
            at' (ind + 2) "simp only [e, ↓reduceIte, Res.ok.injEq] at hn", at' (ind + 2) "subst hn",
            at' (ind + 2) s!"exact {ay}",
            at' ind s!"· have e : {(negP xn c).1} := by {by'}",
            at' (ind + 2) "simp only [e, ↓reduceIte, Res.ok.injEq] at hn", at' (ind + 2) "subst hn",
            at' (ind + 2) s!"exact {an}"])
        | _ => none
      pure (sub ++ dp ++ rws ++ fin)
    match inner 0 with
    | none => failArm "an exit or a fact that the proof does not cover"
    | some _ => [head] ++ pre ++ top ++ splitsOf accs 4 fun ind => (inner ind).getD []

/-- The first line of a `fail` for the whole proof. -/
private def failAll (why : String) : String := s!"  fail \"decompiles_l2: {why}\""

/-- The names of the conjuncts of `rep` for the stack arguments (ARGS8): `hstk0 …`, after the registers. -/
private def stackHyps (s : Summary) : List String := (List.range (stackArgCount s.frame s.blocks)).map fun k => s!"h{stkName k}"

/-- The names of the conjuncts of `rep` after the input registers: `hsp` for `a.sp = rsp`, `hroom` for the stack room. -/
private def repConjNames (fr : FrameText) : List String :=
  (fr.repConjs "a").map fun c => if c.startsWith "SysV.StackRoom" then "hroom" else "hsp"

/-! ## The proof of a function with a call or a stack access (G1-12)

The memory form with a stack room. The invariant is that of the memory form (`rep`, `x.input = a`, `At`, the entry state, the
return word in `x.mem`). A case has these parts, in this order: the data of the block from `At` (the equality form gives
`rfl`; the conjunction form, after a call, gives the facts as hypotheses `hpc`, `hx<r>`, `hk<r>`, `hrsp`, `hdm`, `hsl<k>`);
the splits of the accesses of the model; the rewrite of each model fact to the terms of the machine; one `refine` of the block
lemma with a hole for the hypothesis of each access; and a proof for each hole and each exit. A block outside the forms
below gets a case with `fail`: a block with a stack access below 64 bits, a stack access at or above the return word, a
`goto` or a call from a conjunction-form block, a change of `rsp` at a `goto`, or a trap side of a branch. -/

/-- Does the function use the stack by `rsp` or call? -/
private def needsStack (s : Summary) : Bool :=
  s.blocks.any fun b => endsInCall b || (modelAccesses b).any fun
    | .load _ a _ => a.usesRsp
    | .store _ a _ _ => a.usesRsp

/-- The stores of the model in a block: the number, and whether the store is through a register (the store is guarded). -/
private def storeInfo (b : Block) : List (Nat × Bool) :=
  (modelAccesses b).filterMap fun
    | .store n a _ _ => some (n, !a.usesRsp)
    | .load .. => none

/-- The proof that a fact about a word is kept by the stores `stores`, in order, from the fact `start`. -/
private def chainThrough (stores : List (Nat × Bool)) (start : String) : String :=
  stores.foldl (fun acc (n, heap) =>
    s!"Sites.readRam_of_writeRam (w' := .W64) {writeHypP n} (by {if heap then disjointTac n else "intro i hi l hl e; have hi8 : i < 8 := hi; have hl8 : l < 8 := hl; bv_omega"}) ({acc})")
    start

/-- The depth of a store to the stack, in bytes. -/
private def storeDepth (d0 : Nat) : Access → Option Nat
  | .store _ a _ _ => if a.usesRsp then (depthOf d0 a).bind fun k => if 0 < k then some k.toNat else none else none
  | .load .. => none

/-- The proof that the address of a stack access is the address `sp - k` of its depth `k` (`depthOf`). The address of a
hypothesis is `rsp` of the block with constants added and subtracted, in any nesting (`sp - 8 - 8`, `sp - 32 + 8 + 8`); the
facts of the model state and the permits of `StackRoom` have one constant (`sp - 16`). A saved register is found by its
depth, so the proof does not read the form of the address. -/
private def addrEq : String := "by bv_omega"

/-- The two facts of the proof of a stack word that take an equation of addresses: `hrr` moves a read to an equal address, and
`hrw` is `readRam_writeRam` for a read at an address that is equal to the address of the write. -/
private def addrFacts : List String :=
  [ "  have hrr : ∀ {m : DataMem} {a b v : BitVec 64}, a = b → readRam policy m a .W64 = .ok v → readRam policy m b .W64 = .ok v := by",
    "    intro m a b v h; subst h; exact id",
    "  have hrw : ∀ {m m' : DataMem} {a b v : BitVec 64}, a = b → writeRam policy m a .W64 v = .ok m' →",
    "      policy.permits (.read b .W64) = true → readRam policy m' b .W64 = .ok v := by",
    "    intro m m' a b v h hw hr; subst h",
    "    have e : m' = Mem.storeInt m a 8 v.toInt := by",
    "      unfold writeRam at hw",
    "      split at hw",
    "      · split at hw",
    "        · exact (Except.ok.inj hw).symm",
    "        · cases hw",
    "      · cases hw",
    "    rw [e]",
    "    simp [readRam, hr, Width.bytes, Width.bits, Mem.loadInt_storeInt_64, BitVec.ofInt_ofBytes_toBytes_64]" ]

/-- The permit of a read of the room word at the depth `k`. -/
private def permitK (k : Nat) : String := s!"(hroom {k} (by decide) (by decide) (by decide)).2.1"

/-- The names of the hypotheses of the callee `post` for a callee-saved register. -/
private def abiName : Reg64 → String
  | .rbx => "hbx'" | .rbp => "hbp'" | .r12 => "h12'" | .r13 => "h13'" | .r14 => "h14'" | .r15 => "h15'" | _ => "h?'"

/-- The text of the closer of an equation of two `UInt64` numbers that differ in a constant offset. -/
private def u64Closer : String :=
  "apply UInt64.toBitVec_inj.mp; simp [UInt64.toBitVec_add, UInt64.toBitVec_sub] <;> bv_omega"

/-- The rewrites of a model fact that reads the registers `regs`, to the terms of the machine: the registers that are not
state fields are inputs (`← h<r>`), and, in the entry block, the state fields that are inputs; in the conjunction form the
rewrites of `conjRws` (`← hx<r>`, or `← h<r>, ← hk<r>`; `blockReads` refuses a register with no fact first). -/
private def regRw (v : Vars) (isEntry conj : Bool) (fb : Flow) (regs : List Reg64) : List String :=
  if conj then (conjRws v fb regs).getD [] else
  (regs.eraseDups.filter (· != .rsp)).filterMap fun r =>
    if !v.state.contains r then (if v.inputs.contains r then some s!"← h{regLower r}" else none)
    else if isEntry then (if v.inputs.contains r then some s!"← h{regLower r}" else none)
    else none

/-- The registers whose model values the block proof needs: live output expressions, accesses, branch and kept-flag
conditions, callee arguments, and live model fields that the block does not write. -/
private def blockReads (v : Vars) (b : Block) (c : Option Callee) (needed : List Reg64) : List Reg64 :=
  let accRegs : Access → List Reg64
    | .load _ a _ => valRegs a
    | .store _ a _ v => valRegs a ++ valRegs v
  let condR := match b.term with
    | .branch c _ _ => condRegs c
    | .exit _ => []
  let args := match b.term, c with
    | .exit (.call _ _), some c => c.inputs.flatMap fun r => valRegs (endVal b r)
    | _, _ => []
  (b.regs.filter (needed.contains ·.1)).flatMap (valRegs ·.2) ++
    b.accesses.flatMap accRegs ++ condR ++ args ++ b.flags.flatMap (condRegs ·.2) ++
    needed.filter (fun r => !(b.regs.map (·.1)).contains r && (v.state.contains r || v.inputs.contains r))

/-- The proof of the stack word of `(k, r)` at the exit of a block, from the facts at its start (the names `hsl<k>`) and its
stores. `none` when the block stores to the word something that is not the entry value of `r` at a canonical address, or when
there is no fact. `ee` is the proof that the field of `r` is its entry value, for a push of the field. -/
private def slotProof (b : Block) (d0 : Nat) (fb : Flow) (ee : Reg64 → Option String) (k : Nat) (r : Reg64) :
    Option String :=
  let stores : List (Nat × Val × Val) := (modelAccesses b).filterMap fun a =>
    match a with
    | .store n addr _ val => if storeDepth d0 a == some k then some (n, addr, val) else none
    | .load .. => none
  let last := stores.getLast?
  match last with
  | some (n, _, .reg r') =>
    if r' == r then
      let base := s!"hrw ({addrEq}) {writeHypP n} {permitK k}"
      let after := (storeInfo b).filter (·.1 > n)
      match ee r with
      | some "" => some (chainThrough after base)
      | some h => some (chainThrough after s!"(by have h := {base}; rw [{h}] at h; exact h)")
      | none => none
    else none
  | some _ => none
  | none => if fb.slots.contains (k, r) then some (chainThrough (storeInfo b) s!"hsl{k}") else none

/-- The proof that the source register value equals its entry value.
The equality form uses a model field; the conjunction form uses the machine register. -/
private def eeProof (isEntry : Bool) (fb : Flow) (r : Reg64) : Option String :=
  if isEntry then some "" else
  let fact := (fb.regs.lookup r).getD ⟨false, false⟩
  if atConj fb then
    if fact.s0 then some s!"hk{regLower r}" else none
  else if fact.s0 && fact.x then some s!"hee{regLower r}"
  else none

/-- The proof of a conjunct of `At` at the label that follows a goto, in the equality form. -/
private def gotoItem (b : Block) (d0 : Nat) (fb : Flow) (isEntry : Bool) : AtItem → Option String
  | .entryEq r => if isEntry then some s!"h{regLower r}.symm" else (eeProof false fb r).map fun h => h
  | .slot k r => (slotProof b d0 fb (eeProof isEntry fb) k r).map fun p => s!"(by rw [hpol, hsp]; exact {p})"
  | _ => none

/-- The cases of the splits of the accesses of the model, from the indent `ind`: a load, a write to the stack and a write
through a register (with its guard) split `hn` into the success case, which goes on, and the failure cases. -/
private def splitsOfS (accs : List Access) (ind : Nat) (k : Nat → List String) : List String :=
  match accs with
  | [] => k ind
  | .load n .. :: rest =>
    [at' ind "split at hn", at' ind s!"· rename_i {loadVar n} h{loadVar n}"] ++ splitsOfS rest (ind + 2) k ++
      [at' ind "· cases hn"]
  | .store n addr .. :: rest =>
    if addr.usesRsp then
      [at' ind "split at hn", at' ind s!"· rename_i m{n + 1} {writeHypP n}"] ++ splitsOfS rest (ind + 2) k ++
        [at' ind "· cases hn"]
    else
      [at' ind "split at hn", at' ind s!"· rename_i {guardHyp n}", at' (ind + 2) "split at hn",
        at' (ind + 2) s!"· rename_i m{n + 1} {writeHypP n}"] ++ splitsOfS rest (ind + 4) k ++
        [at' (ind + 2) "· cases hn", at' ind "· cases hn"]

/-- The callee of the call of the block `b`, from the interfaces of `t` (MULTI-CALLEE: each call block has its callee). -/
private def blockCallee (t : Target) (b : Block) : Option Callee :=
  (exitsOfTerm b.term).findSome? fun
    | .call f _ => t.callees.find? (·.name == f)
    | _ => none

/-- The case of a block in the proof of this section. -/
private def armStack (t : Target) (s : Summary) (fl : List (Nat × Flow)) (b : Block)
    (needed : List Reg64) : List String :=
  let callee := blockCallee t b
  let v := s.vars
  let name := b.name.s
  let head := s!"  | {name} =>"
  let failArm (why : String) := [head, s!"    fail \"decompiles_l2: the case of this block is not generated: {why}\""]
  match b.term with
  | .exit .trap =>
    if b.accesses.isEmpty then [head, "    simp only [blocks] at hn", "    cases hn"]
    else failArm "a trap block with accesses"
  | term =>
  match fl.lookup b.offset with
  | none => failArm "no path reaches the block"
  | some fb =>
  let d0 := (s.frame.delta.lookup b.offset).getD 0
  let isEntry := b.offset == 0
  let conj := !isEntry && atConj fb
  let items := atItems v true false fb
  let flagNames := (startFlags b).map fun f => s!"hf{f.name}"
  let flagBinders := String.join (b.flags.map fun (f, _) => s!" hq{f.name}")
  let accs := modelAccesses b
  let stores := storeInfo b
  let xn := if isEntry then
      { proofNames t v b.accesses with
        reg := fun r => if v.state.contains r then (if v.inputs.contains r then s!"x.input.{regLower r}" else "(0 : UInt64)")
          else s!"x.input.{regLower r}" }
    else proofNames t v b.accesses
  let pcT := if isEntry then t.entryPC else s!"{t.entryPC} + {b.offset}"
  let lastIsLoad := match b.accesses.getLast? with
    | some (.load _ _ .W64) => true
    | _ => false
  -- a stack access is of 8 bytes (`frameFacts` refuses others); an access below 64 bits is through a register
  let w64 := b.accesses.all fun
    | .load _ a w => w == .W64 || !a.usesRsp
    | .store _ a w _ => w == .W64 || !a.usesRsp
  let badStack := accs.any fun a => match a with
    | a@(.load _ addr _) => addr.usesRsp && (stackArg d0 a).isNone &&
        ((depthOf d0 addr).map (fun k => decide (k ≤ 0))).getD true
    | .store _ addr _ _ => addr.usesRsp && ((depthOf d0 addr).map (fun k => decide (k ≤ 0))).getD true
  let rspChanged := b.regs.any (·.1 == .rsp)
  let gotos : List Nat := match term with
    | .exit (.goto k) => [k]
    | .branch _ y n => (match y with | .goto k => [k] | _ => []) ++ (match n with | .goto k => [k] | _ => [])
    | _ => []
  -- a goto target in the equality form (its `At` is the state of `s₀` with the fields of the model)
  let eqTarget := gotos.any fun k => (fl.lookup k).any (!atConj ·)
  let trapSide := match term with
    | .branch _ y n => (match y with | .goto _ => false | _ => true) || (match n with | .goto _ => false | _ => true)
    | _ => false
  let why : Option String :=
    if !w64 then some "a stack access below 64 bits"
    else if badStack then some "a stack access at or above the return word"
    else if trapSide then some "a trap side of a branch"
    else if endsInRet b && !lastIsLoad then some "a return with no return word"
    else if conj && (conjRws v fb (blockReads v b callee needed)).isNone then
      some "a read of a register with no fact after a call (a caller-saved register that the callee can change)"
    else if conj && eqTarget then some "a goto from a block in the conjunction form to a block in the equality form"
    else none
  match why with
  | some w => failArm w
  | none =>
  -- the data of the block from `At`
  let itemNames := items.map AtItem.name ++ flagNames
  let pre : List String :=
    if isEntry then ["    cases hat", "    rw [hent rfl] at hn hkeep hmapped"]
    else if conj then
      ["    obtain ⟨d, pc⟩ := s", s!"    obtain ⟨{", ".intercalate itemNames}⟩ := hat",
        s!"    obtain rfl : pc = {pcT} := hpc"]
    else [s!"    obtain ⟨f, rfl{String.join (itemNames.map (", " ++ ·))}⟩ := hat"]
  let slotPrep : List String := items.filterMap fun
    | .slot k _ => some s!"    rw [{if conj then "hpol, hsp, ← hdm" else "hpol, hsp"}] at hsl{k}"
    | _ => none
  let kpPrep : List String :=
    if endsInRet b then ["    have kp := hkeep ra hra"] ++ (if isEntry then ["    simp only [init] at kp", "    rw [hmem] at kp"] else if conj then ["    rw [← hdm] at kp"] else []) else []
  let top := [s!"    simp only [blocks{if isEntry then ", init" else ""}] at hn"]
  -- the rewrites of the facts of the accesses
  let rwLines (ind : Nat) : List String :=
    (accs.foldl (fun (acc : List String × Bool) a =>
      let (lines, fresh) := acc
      match a with
      | .load k addr _ =>
        let mem := if fresh then (if isEntry then ["hmem"] else if conj then ["← hdm"] else []) else []
        let rs := ["hpol"] ++ mem ++ (if addr.usesRsp then ["hsp"] else []) ++ regRw v isEntry conj fb (valRegs addr)
        (lines ++ [at' ind s!"rw [{", ".intercalate rs}] at h{loadVar k}"], fresh)
      | .store n addr _ val =>
        let mem := if fresh then (if isEntry then ["hmem"] else if conj then ["← hdm"] else []) else []
        let regs := regRw v isEntry conj fb (valRegs addr ++ valRegs val)
        let rs := ["hpol"] ++ mem ++ (if addr.usesRsp then ["hsp"] else []) ++ regs
        let g := regRw v isEntry conj fb (valRegs addr)
        let gl := if addr.usesRsp || g.isEmpty then [] else [at' ind s!"rw [{", ".intercalate g}] at {guardHyp n}"]
        (lines ++ [at' ind s!"rw [{", ".intercalate rs}] at {writeHypP n}"] ++ gl, false)) ([], true)).1
  let dArg := if isEntry || conj then "d" else "_"
  -- the holes of the accesses, and their proofs
  let holes : List String := accs.flatMap fun
    | .load k _ w => [loadArg k w, "?_"]
    | .store n .. => [s!"m{n + 1}", "?_"]
  -- `rspRw`: the stack addresses of the facts are of `s₀` and the goal has `rsp` of the machine data (`hrsp`)
  let holeProofs (ind : Nat) (rspRw : Bool := conj) : List String := accs.map fun a =>
    match a with
    | .load k addr _ =>
      at' ind s!"· {if rspRw && addr.usesRsp then "rw [hrsp]; " else ""}exact h{loadVar k}"
    | .store n addr _ _ =>
      at' ind s!"· {if rspRw && addr.usesRsp then "rw [hrsp]; " else ""}exact {writeHypP n}"
  let src : Src := if isEntry then .entry else if conj then .conj fb else .eq fb
  let H := simpSet v ⟨true, true⟩ src ++ flagNames.map ("← " ++ ·)
  let flagsAt (tgt : Nat) (extra : List String) : Option (List String) :=
    let needed := ((s.blocks.find? (·.offset == tgt)).map startFlags).getD []
    needed.mapM fun g => do
      let (_, c) ← b.flags.find? (·.1 == g)
      match c with
      | .flag g' => if g' == g then pure s!"(hq{g.name}.trans hf{g.name})" else none
      | _ => pure s!"(hq{g.name}.trans (by first | rfl | (simp only [{", ".intercalate (H ++ extra)}]; done)))"
  -- the proof of an item of `At` after a goto (equality form)
  let gotoAt (tgt : Nat) (flag : String) (extra : List String) : Option String := do
    let g ← fl.lookup tgt
    guard (!atConj g)
    let tItems := atItems v true false g
    let proofs ← tItems.mapM (gotoItem b d0 fb isEntry)
    let flags ← flagsAt tgt extra
    let eq := s!"(by first | (simp only [{", ".intercalate H}]; done) | (simp only [{", ".intercalate (H ++ extra)}] <;> first | rfl | (congr 3 <;> ({u64Closer}))))"
    pure s!"⟨{", ".intercalate ([flag, eq] ++ proofs ++ flags)}⟩"
  -- the return word fact at the block start, about the memory of the first store of the block: the input memory at the
  -- entry (`init`, `hmem`), the machine memory `d.dmem` in the conjunction form (`hdm`)
  let keep0 :=
    if isEntry then "(by have hk := hkeep r' hr'; simp only [init] at hk; rw [hmem] at hk; exact hk)"
    else if conj then "(by rw [hdm]; exact hkeep r' hr')"
    else "hkeep r' hr'"
  let keepArr := if stores.isEmpty then "hkeep" else s!"fun r' hr' => {chainThrough stores keep0}"
  let map0 := if isEntry then "(by simpa only [init, hmem] using hmapped)"
    else if conj then "(by rw [hdm]; exact hmapped)" else "hmapped"
  let mapMachine := stores.foldl (fun p (n, _) => s!"SysV.MappedMemory.trans ({p}) (SysV.MappedMemory.writeRam {writeHypP n})") map0
  let mapArr := if stores.isEmpty then "hmapped" else mapMachine
  -- the proof of a conjunct of `At` of a target in the conjunction form (L2-CALLBLK): `rsp` from the block start (`hrsp`
  -- after a call) and its change; a stack word by the last store of the block to it (`slotProof`, L2-STACK2)
  let conjItem (extra : List String) : AtItem → Option String
    | .pc => some "rfl"
    | .regX _ | .dmem => some (simpFirst (H ++ extra))
    | .regS r =>
      if (writesOf b).contains r then none
      else match src with
        | .entry => some "rfl"
        | .eq _ => if v.state.contains r && (factOf fb r).x then eeProof false fb r else some "rfl"
        | .conj _ => if (factOf fb r).s0 then some s!"hk{regLower r}" else none
    | .rsp =>
      if rspChanged then some (if conj then s!"(by rw [hrsp] <;> ({u64Closer}))" else s!"(by {u64Closer})")
      else some (if conj then "hrsp" else "rfl")
    | .slot k r => (slotProof b d0 fb (eeProof isEntry fb) k r).map fun p =>
        s!"(by rw [hpol, hsp]; first | exact {p} | (rw [← hdm]; exact {p}))"
    | .entryEq _ => none
  let arrive (tgt : Nat) (flag : String) (extra : List String := []) : Option String := do
    let g ← fl.lookup tgt
    if atConj g then
      let pfs ← (atItems v true false g).mapM fun item =>
        (conjItem extra item).map stateFieldPf
      let flags ← flagsAt tgt extra
      pure s!"⟨hrep, rfl, ⟨{", ".intercalate (pfs ++ flags)}⟩, nofun, {keepArr}, {mapArr}⟩"
    else
      let at_ ← gotoAt tgt flag extra
      pure s!"⟨hrep, rfl, {at_}, nofun, {keepArr}, {mapArr}⟩"
  let dp : List String :=
    if isEntry then ["obtain ⟨d, pc⟩ := s₀", s!"obtain rfl : pc = {t.entryPC} := he.pc"] else []
  -- the exit
  let fin (ind : Nat) : Option (List String) :=
    match term with
    | .exit (.goto tgt) => do
      let a ← arrive tgt "f'"
      pure ([at' ind (s!"refine {name} hx {dArg} {" ".intercalate holes} (fun f'{flagBinders} => {a})")] ++ holeProofs ind)
    | .branch c (.goto y) (.goto n) => do
      -- Each arrival can use the corresponding machine condition when it proves a register update.
      let ay ← arrive y "f'" ["h"]
      let an ← arrive n "f'" ["h"]
      let regRws ← if conj then conjRws v fb (condRegs c) else some (regRw v isEntry false fb (condRegs c))
      let rws' := regRws ++ flagNames.map ("← " ++ ·)
      let by' := if rws'.isEmpty then "exact h" else s!"rw [{", ".intercalate rws'}]; exact h"
      let side (positive : Bool) (cond a : String) : List String :=
        let condition := if positive then "if_pos e" else match c with
          | .not _ => "if_neg (not_not_intro e)"
          | _ => "if_neg e"
        [at' ind s!"· have e : {cond} := by {by'}", at' (ind + 2) s!"rw [{condition}] at hn",
          at' (ind + 2) "simp only [Res.ok.injEq] at hn",
          at' (ind + 2) "subst hn", at' (ind + 2) s!"exact {a}"]
      pure ([at' ind (s!"refine {name} hx {dArg} {" ".intercalate holes} (fun h f'{flagBinders} => ?_) (fun h f'{flagBinders} => ?_)")] ++
        holeProofs ind ++ side true (condP xn c).1 ay ++ side false (negP xn c).1 an)
    | .exit .ret => do
      -- the callee-saved registers
      let abi (r : Reg64) : Option String :=
        let e := (b.regs.find? (·.1 == r)).map (·.2)
        let rf := (fb.regs.lookup r).getD ⟨false, false⟩
        match e with
        | none =>
          if isEntry then some "rfl"
          else if conj then (if rf.s0 then some s!"hk{regLower r}" else none)
          else if rf.s0 && rf.x && v.state.contains r then some s!"hee{regLower r}"
          else if rf.s0 then some "rfl"
          else none
        | some (.load k) =>
          let acc := accs.takeWhile fun a => match a with | .load k' .. => k' != k | _ => true
          let found := accs.find? fun a => match a with | .load k' .. => k' == k | _ => false
          match found with
          | some (.load _ addr _) =>
            match depthOf d0 addr with
            | some kk =>
              if 0 < kk then do
                let savedEq (r' : Reg64) : Option String :=
                  if isEntry then some "" else
                  let f := factOf fb r'
                  if !f.s0 then none else
                  if conj then some s!"hk{regLower r'}"
                  else if f.x && v.state.contains r' then some s!"hee{regLower r'}" else some ""
                let beforeLoad := { b with accesses := acc, term := .exit (.goto b.offset) }
                let hs ← slotProof beforeLoad d0 fb savedEq kk.toNat r
                let data0 := if isEntry then "d" else "s₀.data"
                some s!"(by have hs : readRam policy _ ({data0}.regs.rsp.toBitVec - {kk}) .W64 = .ok {data0}.regs.{regLower r}.toBitVec := {hs}; have hvr := Except.ok.inj ((hrr ({addrEq}) h{loadVar k}).symm.trans hs); rw [hvr])"
              else none
            | none => none
          | _ => none
        | some _ => none
      let rspPf := if conj then s!"(by rw [hrsp] <;> ({u64Closer}))" else s!"(by {u64Closer})"
      let abis ← [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15].mapM abi
      -- `rax` and the memory: a fact of `At`, or after a call a term of the machine data (`simp only` with the facts `H`)
      let eqPf := s!"(by first | (simp only [{", ".intercalate H}]; done) | rfl | assumption)"
      let post := s!"fun _ => ⟨⟨hra, {", ".intercalate (rspPf :: abis)}⟩, {eqPf}, {eqPf}, {mapMachine}⟩"
      let retPf :=
        let chain := chainThrough stores "kp"
        s!"{if conj then "rw [hrsp]; " else ""}exact hrr (by first | bv_omega | (simp [UInt64.toBitVec_sub, UInt64.toBitVec_add] <;> bv_omega)) ({chain})"
      pure ([at' ind (s!"refine {name} hx {dArg} {" ".intercalate holes} ra ?_ ({post})")] ++ holeProofs ind ++
        [at' ind s!"· {retPf}"])
    | .exit (.call f cont) => do
      let c ← callee
      let _ ← if c.name == f then some () else none
      let tgtF ← fl.lookup cont
      let cdepth := (s.frame.delta.lookup cont).getD 0
      let nBytes := cdepth + 8
      let lastStore ← (accs.filterMap fun a => match a with
        | .store n _ _ (.retAddr off) => some (n, off)
        | _ => none).getLast?
      let rspEnd := match b.regs.find? (·.1 == .rsp) with
        | some (_, e) => e
        | none => .reg .rsp
      -- after a call (the conjunction form) the `rsp` of the block start is that of the machine data (`hrsp`)
      let rspBase := if conj then "d.regs.rsp" else if d0 == 0 then "s₀.data.regs.rsp" else s!"(s₀.data.regs.rsp - {d0})"
      let rspNames : Names := ⟨fun r => if r == .rsp then rspBase else s!"s₀.data.regs.{regLower r}", t.entryPC,
        fun _ => "0", fun _ => "0", fun f => s!"s₀.data.status.{f.name}"⟩
      -- in the entry block `s₀` is `⟨d, pc⟩` after `obtain` (PIL-CALL: a call from the entry block)
      let s0d (x : String) : String := if isEntry then x.replace "s₀.data." "d." else x
      let rspExpr := s0d (valU rspNames rspEnd).1
      -- an argument that is an input register of the caller: its `rep` fact `h<r>` (PIL-CALL: `put` takes `rdi` of the input)
      -- the return word of the caller in its entry memory: in the entry block `hkeep` is of `(init a).mem`
      -- after a call (the conjunction form) an argument is a term of the machine data: `simpPf` of the facts of `At`
      let argEqs := c.inputs.map fun _ => simpFirst H
      let stackEqs ← (List.range c.stackArgs).mapM fun k => do
        let depth := nBytes - 8 * (k + 1)
        let (n, _) ← (accs.filterMap fun a => match a with
          | .store n addr .W64 _ => if depthOf d0 addr == some (Int.ofNat depth) then some (n, addr) else none
          | _ => none).getLast?
        let after := stores.filter (·.1 > n)
        let read := chainThrough after s!"(hrw ({addrEq}) {writeHypP n} {permitK depth})"
        pure s!"(by simp only [{", ".intercalate (H ++ ["hsp", "UInt64.toBitVec_add", "UInt64.toBitVec_sub"])}]; exact hrr (by simp [UInt64.toBitVec_add, UInt64.toBitVec_sub] <;> bv_omega) ({read}))"
      -- a callee with memory (PIL-CALL): its `rep` has `sp`, its `post` is `Exit`, `rax`, the memory, then `Kept` of the
      -- bytes of the caller from the `rsp` of the callee (`hkept`); a word of the caller is read again through `Kept.readRam`
      let kept (k : Nat) (p : String) : String :=
        if c.mem then s!"(Kept.readRam hkept (k := {nBytes - k}) (by decide) (by simp only [hsp]; bv_omega) ({p}))" else p
      let tItems := atItems v true false tgtF
      let itemPf (i : AtItem) : Option String :=
        match i with
        | .pc => some s!"Option.some.inj (hpc.symm.trans (retOf {writeHypP lastStore.1}))"
        | .regX r =>
          if r == .rax then some "hz"
          else if calleeSaved.contains r then
            -- after a call (the conjunction form) the register at the call is a term of the machine data (`simpPf`)
            if conj then some s!"({abiName r}.trans {simpFirst H})" else
            -- the entry block writes an input register to `r` (PIL-CALL: `rbx := rdi` before the call)
            match endVal b r with
            | .reg r' => if isEntry && v.inputs.contains r' then some s!"({abiName r}.trans h{regLower r'})"
                else some (abiName r)
            | _ => some (abiName r)
          else none
        | .regS r =>
          -- a state field that holds its entry value: the machine register is the field, which `hee<r>` equates to `s₀`
          if !calleeSaved.contains r then none
          else if conj then
            if (factOf fb r).s0 && !(writesOf b).contains r then some s!"({abiName r}.trans hk{regLower r})" else none
          else if !v.state.contains r then some (abiName r)
          else match eeProof isEntry fb r with
            | some "" => some (abiName r)
            | some h => some s!"({abiName r}.trans {h})"
            | none => none
        | .rsp => some s!"(by rw [hsp'{if conj then ", hrsp" else ""}] <;> ({u64Closer}))"
        | .dmem => some "hmem'"
        | .slot k r => (slotProof b d0 fb (eeProof isEntry fb) k r).map fun p => s!"(by rw [hpol, hsp]; exact {kept k p})"
        | .entryEq _ => none
      let proofs ← tItems.mapM itemPf
      let spEq := if c.mem then [s!"(by rw [hsp{if conj then ", hrsp" else ""}]; first | rfl | bv_omega | (simp [UInt64.toBitVec_sub, UInt64.toBitVec_add] <;> bv_omega))"] else []
      let roomPf := if c.room == 0 then [] else
        [s!"(by intro k hk8 hkn hd; have e : ({rspExpr}).toBitVec - BitVec.ofNat 64 k = s₀.data.regs.rsp.toBitVec - BitVec.ofNat 64 ({nBytes} + k) := (by {if conj then "rw [hrsp]; " else ""}simp [UInt64.toBitVec_sub, UInt64.toBitVec_add]; bv_omega); rw [e]; have h := hroom ({nBytes} + k) (by omega) (by omega) (Nat.dvd_add (by decide) hd); exact ⟨h.1, h.2.1, ({mapArr}) _ _ h.2.2⟩)"]
      let rep := s!"⟨hpol, (by first | rfl | trivial), ⟨rfl, hx, ?_, {t.entryPC} + {lastStore.2}, ?_⟩{String.join ((argEqs ++ stackEqs ++ spEq ++ roomPf).map (", " ++ ·))}⟩"
      let postPat := if c.mem then "⟨⟨⟨hpc, hsp', hbx', hbp', h12', h13', h14', h15'⟩, hz, hmem', hmap'⟩, hkept⟩"
        else "⟨⟨hpc, hsp', hbx', hbp', h12', h13', h14', h15'⟩, hmem', hz⟩"
      let mapAfter := if c.mem then s!"(by change SysV.MappedMemory s₀.data.dmem z.2; rw [← hmem']; exact SysV.MappedMemory.trans ({mapMachine}) hmap')" else mapArr
      let permit := s!"(hroom {nBytes} (by decide) (by decide) (by decide)).2.1"
      -- after a call (the conjunction form) the stack addresses of the facts are put in terms of the `rsp` of the machine
      -- data (`hsd`), so that the write of the return word is at the `rsp` of the callee (`retAddr_writeRam`)
      let s0sp := if d0 == 0 then "s₀.data.regs.rsp.toBitVec" else s!"s₀.data.regs.rsp.toBitVec - {d0}"
      let stackFacts := accs.filterMap fun a => match a with
        | .load k addr _ => if addr.usesRsp then some s!"h{loadVar k}" else none
        | .store n addr _ _ => if addr.usesRsp then some (writeHypP n) else none
      let hsd := if conj then
          [at' ind s!"have hsd : {s0sp} = d.regs.rsp.toBitVec := by rw [hrsp]; first | rfl | simp [UInt64.toBitVec_sub]"] ++
            stackFacts.map fun h => at' ind s!"rw [hsd] at {h}"
        else []
      pure (hsd ++ [at' ind (s0d s!"refine {name} hx {dArg} {" ".intercalate holes} (fun f' => ⟨{rep}, ?_⟩)")] ++ holeProofs ind false ++
        [at' ind (s0d s!"· have e : ({rspExpr}).toBitVec = s₀.data.regs.rsp.toBitVec - BitVec.ofNat 64 {nBytes} := by"),
          at' (ind + 4) s!"{if conj then "rw [hrsp]; " else ""}first | bv_omega | (simp [UInt64.toBitVec_sub, UInt64.toBitVec_add] <;> bv_omega)",
          at' (ind + 2) s!"show policy.permits (.read ({rspExpr}).toBitVec .W64) = true",
          at' (ind + 2) "rw [e]",
          at' (ind + 2) s!"exact {permit}",
          at' ind s!"· exact retOf {writeHypP lastStore.1}",
          at' ind s!"· rintro z u {postPat}",
          at' (ind + 2) (s0d s!"exact ⟨hrep, rfl, ⟨{", ".intercalate proofs}⟩, nofun, fun r' hr' => {kept 0 (chainThrough stores keep0)}, {mapAfter}⟩")])
    | _ => none
  let inner (ind : Nat) : List String :=
    let sub := match term with
      | .branch .. => []
      | _ => [at' ind "simp only [Res.ok.injEq] at hn", at' ind "subst hn"]
    let dpl := dp.map (at' ind)
    match fin ind with
    | some fl' => sub ++ dpl ++ rwLines ind ++ fl'
    | none => [at' ind "fail \"decompiles_l2: the case of this block is not generated: an exit or a fact that the proof does not cover\""]
  [head] ++ pre ++ slotPrep ++ kpPrep ++ top ++ splitsOfS accs 4 inner

/-- The return address of a call: the write of the return address at `rsp` of the callee state `t` that gives its memory.
The lemma is stated in the proof, so that the check file needs no module of the spike (`Lift.Spike.Sites.Stack` has the
same lemma, `retAddr_writeRam`, and imports `Lift.Spike.L1`, whose names clash with those of other units). -/
private def retOfLines : List String :=
  [ "  have retOf : ∀ {m : DataMem} {t : MachineState} {ra : Int64},",
    "      writeRam policy m t.data.regs.rsp.toBitVec .W64 ra.toBitVec = .ok t.data.dmem → SysV.retAddr t = some ra := by",
    "    intro m t ra h",
    "    have e : t.data.dmem = Mem.storeInt m t.data.regs.rsp.toBitVec 8 ra.toBitVec.toInt := by",
    "      unfold writeRam at h",
    "      split at h",
    "      · split at h",
    "        · exact (Except.ok.inj h).symm",
    "        · cases h",
    "      · cases h",
    "    unfold SysV.retAddr",
    "    rw [e]",
    "    simp only [Mem.loadInt_storeInt_64, Option.map_some, BitVec.ofInt_ofBytes_toBytes_64, BitVec.ofInt_toInt,",
    "      Int64.ofBitVec_toBitVec]" ]

/-- The invariant of the memory form with a guard (the `at_` of `Decompiles.ofBlocks`), at the indent 4. -/
private def stackInv : List String :=
  [ "    (fun policy a s₀ l x s => l2.rep policy a s₀ ∧ x.input = a ∧ At s₀ l x s ∧ (l = .entry → x = init a) ∧",
    "      (∀ ra, SysV.retAddr s₀ = some ra → readRam policy x.mem s₀.data.regs.rsp.toBitVec .W64 = .ok ra.toBitVec) ∧",
    "      SysV.MappedMemory s₀.data.dmem x.mem)" ]

/-- The proof that the entry state holds the invariant of `stackInv`. -/
private def stackStart : String :=
  "(fun _ _ _ h => ⟨h, rfl, rfl, fun _ => rfl, fun ra hra => by simp only [init]; rw [h.2.1]; exact Sites.readRet h.2.2.1 hra, by simp only [init]; rw [h.2.1]; exact SysV.MappedMemory.refl _⟩)"

/-- The pattern of the invariant of `stackInv`. -/
private def stackPat : String := "⟨hrep, rfl, hat, hent, hkeep, hmapped⟩"

/-- The parts of the proof of a function in the memory form with a guard: the callee arguments of `Decompiles.ofBlocks`,
the lines after the `rintro` of a case (the facts of `rep`, the return word, the run, the facts of the addresses and of the
return word of a call), and for each block its name and its case lines (`armStack`, from the indent 4). Else the reason of
the `fail`. -/
private def stackParts (t : Target) (s : Summary) (fr : FrameText) :
    Except String (String × List String × List (String × List String)) :=
  let called := calledOf s.blocks
  let fl := flows s
  let live := liveOutputs s.blocks t.callees
  let hyps := ", ".intercalate (["hpol", "hmem", "he"] ++ s.vars.inputs.map (fun r => s!"h{regLower r}") ++ stackHyps s ++
    repConjNames fr)
  let pre := [ s!"  have ⟨{hyps}⟩ := hrep", "  obtain ⟨ra, hra⟩ := he.ret", "  have hx := he.exec" ] ++ addrFacts ++
    (if called.isEmpty then [] else retOfLines)
  match called.find? (fun f => !t.callees.any (·.name == f)) with
  | some f => .error s!"the call to {f} has no callee interface in the target"
  | none => .ok (decompCalleeArgs t s, pre, s.blocks.map fun b => (b.name.s, (armStack t s fl b ((live.lookup b.offset).getD regOrder)).drop 1))

/-- The proof of a function with a call or a stack access, in the memory form with a guard. -/
private def stackProof (t : Target) (s : Summary) (fr : FrameText) : String :=
  match stackParts t s fr with
  | .error why => failAll why
  | .ok (calleeArgs, pre, arms) =>
    let head := [ s!"  refine Decompiles.ofBlocks blocks {calleeArgs} .entry init"] ++ stackInv ++ [
      s!"    (fun _ _ h => h) {stackStart} ?_",
      s!"  rintro policy a s₀ l x s {stackPat} n hn"] ++ pre ++ ["  cases l with"]
    "\n".intercalate (head ++ arms.flatMap fun (name, lines) => s!"  | {name} =>" :: lines)

/-- The name of the lemma of the case of the block `name` (`stackSplit`). -/
def caseLemma (name : String) : String := s!"decompiles_l2_{name}"

/-- The proof of `stackProof` with one lemma for each case, so that each case has its own heartbeats (MULTI-CALLEE3): the
helpers (`Skel.Proof`) are the invariant `decompiles_l2_inv` and the lemma `decompiles_l2_<block>` of each block, which takes
the block lemma as a hypothesis when the block has a row (`rowTy` gives its statement), and states the `block` premise of
`Decompiles.ofBlocks` at the label of the block. The theorem applies `Decompiles.ofBlocks` and gives each case its lemma,
after `cases n`: the `match` of the lemma and that of `Decompiles.ofBlocks` are two matchers, which the elaborator does not
unfold on a variable (the toy `two`: type mismatch), and which reduce on each constructor.
A case lemma has the lines of the case in `stackProof`, after the lines of the block start. `none` when `stackProof` is a
`fail`. -/
private def stackSplit (t : Target) (s : Summary) (fr : FrameText) (rowTy : String → Option String) : Option String :=
  match stackParts t s fr with
  | .error _ => none
  | .ok (calleeArgs, pre, arms) =>
    let inv := "decompiles_l2_inv"
    let fam := decompCalleeFam t s
    let invDef := ["abbrev decompiles_l2_inv : CpuPolicy → In2 → MachineState → Lbl → St In2 DataMem → MachineState → Prop :="] ++
      stackInv.map fun l => String.ofList (l.toList.drop 2)
    let lemma (name : String) (lines : List String) : String :=
      let hyp := match rowTy name with
        | some ty => s!" ({name} : {ty})"
        | none => ""
      "\n".intercalate ([
        s!"theorem {caseLemma name}{hyp} : ∀ (policy : CpuPolicy) (a : In2) (s₀ : MachineState) (x : St In2 DataMem)",
        s!"    (s : MachineState), {inv} policy a s₀ .{name} x s → ∀ (n : {nextTypeText t s true}),",
        s!"    blocks.step .{name} x = .ok n → Reaches {t.step} policy (fun t => match n with",
        s!"      | .goto l' x' => {inv} policy a s₀ l' x' t",
        "      | .ret r => l2.post a r s₀ t",
        s!"      | .call f y k => ({fam} f).rep policy y t ∧",
        s!"          ∀ z u, ({fam} f).post y z t u → {inv} policy a s₀ (k z).1 (k z).2 u) s := by",
        s!"  rintro policy a s₀ x s {stackPat} n hn"] ++ pre ++ lines.map fun l => String.ofList (l.toList.drop 2))
    let helpers := "\n\n".intercalate ("\n".intercalate invDef :: arms.map fun (name, lines) => lemma name lines)
    let main := [ "by", s!"  refine Decompiles.ofBlocks blocks {calleeArgs} .entry init {inv}",
      s!"    (fun _ _ h => h) {stackStart} ?_",
      "  intro policy a s₀ l x s h n hn",
      "  cases l with" ] ++ arms.map fun (name, _) =>
        let arg := if (rowTy name).isSome then s!" {name}" else ""
        s!"  | {name} => have H := {caseLemma name}{arg} policy a s₀ x s h n hn; cases n <;> exact H"
    some (Proof.text { helpers := helpers, proof := "\n".intercalate main })


/-! ## The proof of a function in the frame form (G1-16, O3)

The frame form: all stores are stack stores, and the stack room is not 0 (pushes, `sub rsp`, the return word of a call).
The memory is not in the state: `At` of a block but the entry has the conjunction form with `Frame policy s₀ u.data.dmem`
(the saved registers at their words, the bytes outside the room, the words of the room mapped). The invariant is `rep`,
`x.input = a`, `At`, and `l = .entry → x = init a`. A case has these parts:

* the data of the block: `cases hat` at the entry; else `obtain ⟨d, pc⟩ := s`, `dsimp only [At] at hat` and the names of
  the conjuncts (`hpc`, `hx<r>`, `hk<r>`, `hrsp`, then the names of `Frame`);
* the step of the model: `simp only [blocks, …] at hn`; a block whose model is `stuck` (a stack load that is not a load of
  8 bytes of a slot) is closed there;
* one `refine'` of the block lemma with a hole `?b<off>_h<k>` for the hypothesis of each access, and the exit;
* `any_goals frame_call`, which closes the memory holes (the writes and reads of the stack, the room and the frame), and a
  closer for the register equations that are left: `rfl`, or `simp only` with the facts of the block start.

A call (`frame_call` at the return, section 7 of `docs/research/outer-mem-experiment-20261118.md`): the callee `rep` is the
policy, `Entry` (with the return address of the store of the call), the arguments, and the room of a callee with a room;
the callee `post` is `Exit`, then `t.data.dmem = s.data.dmem` (`hm`, a callee with room 0) or `Outside` and `Mapped`
(`out'`, `mp'`, a callee with a room), then `rax`. A return: `Exit` (the callee-saved registers from their words or from
the block start), `Outside`, `Mapped`, `rax`. A branch: one side for each exit, and `split at hn` on the condition of the
model.

A load through a register (PIL-HEAP) reads the input memory of `rep`, `SysV.Hidden s <room>`: the entry memory with the room
unmapped. `split at hn` gives the read of the model, and `SysV.Hidden.readRam` gives the read of the machine memory, which is
the entry memory outside the room (`Outside`, a hole that `frame_call` closes).

A stack argument (ARGS8): a load of the word `k` above the return word has a hole that `frame_call` closes from the conjunct
`hstk<k>` of `rep` (the bytes outside the room keep their entry value). A call passes each stack argument of the callee with
`Lift.Tactic.Frame.readRam_arg ?s<k> ?e<k>`: `frame_call` reads the word in the memory at the call (`?s<k>`), and the closer
proves that its value is the value of the model (`?e<k>`).

A block outside these forms gets a case with `fail`: a stack load at or above the return word that is not a stack
argument, a store of fewer than 8 bytes
in a block whose model goes on, a store to the word of a saved register after the entry block, a trap side of a branch, a
return with no return word, and a call to a callee with no interface or a callee with memory. -/

/-- The name of a hole of the block at `off`. -/
private def holeOf (off : Nat) (what : String) : String := s!"?b{off}_{what}"

/-- Is the model of a block `stuck` in the frame form? A stack load of 8 bytes at a positive depth reads the latest store of
the block to its word (`pushedVal`, a push and its pop in one block) or else the entry value of the register of a slot
(`entrySlots`); any other stack load is `stuck`. The rule is that of `accessAt` of `Model.lean`. -/
private def frameStuck (v : Vars) (slots : List (Int × Reg64)) (d0 : Nat) (b : Block) : Bool :=
  let accs := modelAccesses b
  (List.range accs.length).any fun i =>
    match accs[i]? with
    | some (.load _ addr w) =>
      addr.usesRsp && match depthOf d0 addr with
        | some k =>
          let pushed := (pushedVal ⟨v, "", [], d0⟩ (accs.take i) k).isSome
          0 < k && !(w == .W64 && (pushed || slots.any (·.1 == k)))
        | none => true
    | _ => false

/-- Is the access a load through a register (a heap load)? -/
private def isHeapLoad : Access → Bool
  | .load _ a _ => !a.usesRsp
  | .store .. => false

/-- Why the case of a block in the frame form has no text, or `none`. `slots` are the slots of the frame. -/
private def frameWhy (t : Target) (t' : Vars) (slots : List (Int × Reg64)) (d0 : Nat) (b : Block) : Option String :=
  let accs := modelAccesses b
  let highLoad := accs.any fun
    | acc@(.load _ a _) => a.usesRsp && (stackArg d0 acc).isNone &&
      ((depthOf d0 a).map (fun k => decide (k ≤ 0))).getD true
    | .store .. => false
  let narrowStore := accs.any fun | .store _ _ w _ => w != .W64 | .load .. => false
  let slotStore := b.offset != 0 && accs.any fun
    | .store _ a _ _ => a.usesRsp && ((depthOf d0 a).map fun k => slots.any (·.1 == k)).getD false
    | .load .. => false
  let isGoto : Exit → Bool | .goto _ => true | _ => false
  let lastIsLoad := match b.accesses.getLast? with
    | some (.load _ _ .W64) => true
    | _ => false
  if highLoad then some "a stack load at or above the return word in the frame form"
  else if frameStuck t' slots d0 b then none
  else if narrowStore then some "a stack store of fewer than 8 bytes in the frame form"
  else if slotStore then some "a store to the word of a saved register after the entry block"
  else match b.term with
    | .branch _ y n => if isGoto y && isGoto n then none else some "a trap side of a branch"
    | .exit .ret => if lastIsLoad then none else some "a return with no return word"
    | .exit (.call f _) =>
      match t.callees.find? (·.name == f) with
      | none => some s!"the call to {f} has no callee interface in the target"
      | some c => if c.mem then some s!"the callee {f} has a memory in its result" else none
    | _ => none

/-- The rewrites of the closer of a register equation, from the facts of the block start: at the entry the equations of
`rep` (`h<r>`, the input registers); else for each register its `x` fact (`hx<r>`) or its `s₀` fact (`hk<r>`, then `h<r>`
for an input). -/
private def frameSet (v : Vars) (isEntry : Bool) (fb : Flow) : List String :=
  if isEntry then v.inputs.map fun r => s!"h{regLower r}"
  else flowRegs'.flatMap fun r =>
    let rf := (fb.regs.lookup r).getD ⟨false, false⟩
    if rf.x && v.state.contains r then [s!"hx{regLower r}"]
    else if rf.s0 then [s!"hk{regLower r}"] ++ (if v.inputs.contains r then [s!"h{regLower r}"] else [])
    else []
where flowRegs' : List Reg64 := regOrder.filter (· != .rsp)

/-- The closer of the register equations that the memory tactics leave: the rewrites `set`, `rfl`, and for `rsp` the
arithmetic of `UInt64` (with `hrsp` after the entry). The `rsp` of a `refine'` is a hole too: a `by` in the term of a
`refine'` runs before the memory tactics give the values of its holes. The rewrites come before `rfl`: `rfl` on an equation
of two shifts or `xor`s of different registers unfolds the operations and uses up the heartbeats (PIL-HEAP,
`shallowestCopyPosition` o12). -/
private def frameCloser (isEntry : Bool) (set : List String) : String :=
  let l := ", ".intercalate set
  let l' := ", ".intercalate (set ++ ["UInt64.ofBitVec_toBitVec"])
  s!"all_goals first | (simp only [{l}]; done) | (simp only [{l'}]; done) | rfl | " ++
    s!"(apply UInt64.toBitVec_inj.mp; simp [{if isEntry then "" else "hrsp, "}UInt64.toBitVec_add, UInt64.toBitVec_sub] <;> bv_omega)"

/-- The proof of `rsp = s₀.rsp - k` (or `+ 8`) after the rewrite `pre`, from the fact `hrsp` of a block after the entry. -/
private def rspCloser (isEntry : Bool) (pre : String) : String :=
  s!"(by {pre}apply UInt64.toBitVec_inj.mp; simp [{if isEntry then "" else "hrsp, "}UInt64.toBitVec_add, UInt64.toBitVec_sub] <;> bv_omega)"

/-- The holes of the accesses of the block lemma, in order: a value and its hypothesis; the return word of a block that
returns is `ra`. A load through a register (PIL-HEAP) has the value of the model and the read of `SysV.Hidden.readRam` from
the read of the model (`hv<k>`): the input memory of `rep` is the memory of the entry with the room unmapped, so a read that
succeeds in it meets no byte of the room. The address and the bytes outside the room (`?b<off>_a<k>`, `?b<off>_o<k>`) are
holes. -/
private def accessHoles (b : Block) : List String :=
  let n := b.accesses.length
  (List.range n).flatMap fun k =>
    if endsInRet b && k + 1 == n then ["ra", holeOf b.offset s!"h{k + 1}"]
    else match b.accesses[k]? with
      | some (.load j a w) =>
        if a.usesRsp then ["_", holeOf b.offset s!"h{k + 1}"]
        else [loadArg j w,
          s!"(SysV.Hidden.readRam hmem hpol h{loadVar j} {holeOf b.offset s!"a{k + 1}"} {holeOf b.offset s!"o{k + 1}"})"]
      | _ => ["_", holeOf b.offset s!"h{k + 1}"]

/-- The lines `ls` of a block case after the split of each load through a register of the model (PIL-HEAP), in the order of
the model: `split at hn` gives the read `hv<k>` and its value `v<k>`; the failed read is `cases hn`. The lines of the case
are at 4 spaces; each split adds 2. -/
private def heapSplits (b : Block) (ls : List String) : List String :=
  let loads := (modelAccesses b).filterMap fun
    | .load j a _ => if a.usesRsp then none else some j
    | .store .. => none
  let rec go : List Nat → Nat → List String
    | [], ind => [at' ind "try simp only [Res.ok.injEq] at hn"] ++ ls.map ("".pushn ' ' (ind - 4) ++ ·)
    | j :: rest, ind =>
      [at' ind "split at hn", at' ind s!"· rename_i {loadVar j} h{loadVar j}"] ++ go rest (ind + 2) ++ [at' ind "· cases hn"]
  if loads.isEmpty then ls else go loads 4

/-- The conjuncts of `At` at the start of the block `tgt` (the conjunction form), as proofs: `pc` and `rsp` by the texts
given, a register by a hole of the closer (after the callee fact `abi r` when it is given), and a hole for each conjunct
of `Frame`. -/
private def targetItems (v : Vars) (fr : FrameText) (off : Nat) (side : String) (g : Flow) (pc rsp : String)
    (reg : AtItem → Option String) (flagPfs : List String := []) : List String :=
  let items := atItems v false true g
  let regs := (items.zip (List.range items.length)).map fun (i, k) =>
    match i with
    | .pc => pc
    | .rsp => rsp
    | it => (reg it).getD (holeOf off s!"{side}i{k}")
  regs ++ flagPfs ++ (List.range fr.frameIntro.length).map fun k => holeOf off s!"{side}f{k}"

/-- The name of the fact `s.data.status.g = x.g` of `At` at a block start (L2-FLAGS). -/
private def startFlagHyp (g : Flag) : String := s!"hf{g.name}"

/-- The name of the fact `f.g = …` of a kept flag of an exit of the block lemma (L2-FLAGS). -/
private def exitFlagHyp (g : Flag) : String := s!"hq{g.name}"

/-- The binders of the kept flags of an exit of the block lemma `b`, after `f` (L2-FLAGS). -/
private def exitFlagBinders (b : Block) : String := String.join (b.flags.map fun (g, _) => " " ++ exitFlagHyp g)

/-- The proofs of the flag facts of `At` of the block `tgt` at a goto of the block `b` (L2-FLAGS): the fact of the exit,
then the fact of the start of `b` for a flag that `b` keeps, or the closer `set` for a flag that `b` sets. `none` when `b`
does not keep a flag that `tgt` reads. -/
private def flagArrivals (s : Summary) (b : Block) (set : List String) (tgt : Nat) : Option (List String) :=
  let tflags := ((s.blocks.find? (·.offset == tgt)).map startFlags).getD []
  tflags.mapM fun g => do
    let (_, c) ← b.flags.find? (·.1 == g)
    match c with
    | .flag g' => if g' == g then pure s!"({exitFlagHyp g}.trans {startFlagHyp g})" else none
    | _ => pure s!"({exitFlagHyp g}.trans (by first | rfl | (simp only [{", ".intercalate set}]; done)))"

/-- The case of a block in the frame form. -/
private def armFrame (t : Target) (s : Summary) (fr : FrameText) (fl : List (Nat × Flow)) (b : Block) : List String :=
  let v := s.vars
  let name := b.name.s
  let off := b.offset
  let head := s!"  | {name} =>"
  let failArm (why : String) := [head, s!"    fail \"decompiles_l2: the case of this block is not generated: {why}\""]
  let slots := entrySlots s
  let d0 := (s.frame.delta.lookup off).getD 0
  let isEntry := off == 0
  match fl.lookup off with
  | none => [head, "    exact (hat : False).elim"]
  | some fb =>
  let pre : List String :=
    if isEntry then ["    cases hat", "    rw [hent rfl] at hn"]
    else
      let names := (atItems v false true fb).map AtItem.name ++ (startFlags b).map startFlagHyp ++ fr.frameIntro
      ["    obtain ⟨d, pc⟩ := s", "    dsimp only [At] at hat", s!"    obtain ⟨{", ".intercalate names}⟩ := hat",
        s!"    obtain rfl : pc = {t.entryPC} + {off} := hpc"]
  let top := [s!"    simp only [blocks{if isEntry then ", init" else ""}, Res.ok.injEq] at hn"]
  let stuckEnd := ["    all_goals cases hn"]
  match b.term with
  | .exit .trap => [head] ++ pre ++ [s!"    simp only [blocks] at hn"] ++ stuckEnd
  | term =>
  if frameStuck v slots d0 b then [head] ++ pre ++ [s!"    simp only [blocks{if isEntry then ", init" else ""}] at hn"] ++ stuckEnd
  else
  match frameWhy t v slots d0 b with
  | some why => failArm why
  | none =>
  let dp : List String :=
    if isEntry then
      ["    obtain ⟨d, pc⟩ := s₀", s!"    obtain rfl : pc = {t.entryPC} := he.pc"] ++
        (if v.inputs.isEmpty then [] else [s!"    try dsimp only at {" ".intercalate (v.inputs.map fun r => s!"h{regLower r}")}"])
    else []
  -- the facts of the block start: the registers, and the kept flags that the block reads (L2-FLAGS)
  let set := frameSet v isEntry fb ++ (startFlags b).map startFlagHyp
  let closer := "    " ++ frameCloser isEntry set
  let holes := " ".intercalate (accessHoles b)
  let qs := exitFlagBinders b
  let arrive (side : String) (tgt : Nat) : Option String := do
    let g ← fl.lookup tgt
    let flagPfs ← flagArrivals s b set tgt
    let items := targetItems v fr off side g "rfl" (holeOf off s!"{side}rsp") (fun
      | .regS r => if isEntry then some "rfl" else
          if ((fb.regs.lookup r).map (·.s0)).getD false && !(b.regs.any (·.1 == r)) then some s!"hk{regLower r}" else none
      | _ => none) flagPfs
    pure s!"⟨hrep, rfl, ⟨{", ".intercalate items}⟩, nofun⟩"
  let body : Option (List String) :=
    match term with
    | .exit (.goto tgt) => do
      let a ← arrive "" tgt
      pure (top ++ ["    subst hn"] ++ dp ++
        [s!"    refine' {name} hx d {holes} fun f{qs} => {a}", "    any_goals frame_call", closer])
    | .branch _ (.goto y) (.goto n) => do
      let ay ← arrive "y" y
      let an ← arrive "n" n
      let simpa := s!"simpa only [{", ".intercalate set}] using"
      -- the side of the exit `goes`: the case of the condition that goes on, and the case that the condition refutes. The
      -- cases are those of the outer `if` of `hn` (`ite_cases`): `split` takes the first `if` that it finds, which is an
      -- `if` inside the condition when the condition has one (PIL-HEAP, `closestCopy` o156)
      let side (tag : String) (a : String) (first : Bool) : List String :=
        let go := ["        subst hn", s!"        refine {a}", "        any_goals frame_call", "    " ++ closer]
        let refute := [s!"        first | (exfalso; apply hc; {simpa} h) | (exfalso; apply h; {simpa} hc)"]
        [s!"    case {(holeOf off tag).drop 1} =>", "      rcases SysV.ite_cases hn with ⟨hc, hn⟩ | ⟨hc, hn⟩", "      · skip"] ++
          (if first then go else refute) ++ ["      · skip"] ++ (if first then refute else go)
      pure (top ++ dp ++
        [s!"    refine' {name} hx d {holes} (fun h f{qs} => {holeOf off "y"}) (fun h f{qs} => {holeOf off "n"})"] ++
          -- a block with no access has no memory hole (the entry of `l2zFlags`): `any_goals frame_call` fails there
          (if b.accesses.isEmpty then [] else ["    any_goals frame_call"]) ++ side "y" ay true ++ side "n" an false ++
          [closer])
    | .exit .ret => do
      let abi (r : Reg64) : Option String :=
        match (b.regs.find? (·.1 == r)).map (·.2) with
        | none => if isEntry then some "rfl" else
            if ((fb.regs.lookup r).map (·.s0)).getD false then some s!"hk{regLower r}" else none
        | some (.load k) =>
          let found := b.accesses.find? fun a => match a with | .load k' .. => k' == k | _ => false
          let prior := b.accesses.takeWhile fun a => match a with | .load k' .. => k' != k | _ => true
          match found with
          | some (.load _ addr .W64) =>
            -- the last store of the block to the word before the pop gives the value (L2-STACK2), as in the model
            match (depthOf d0 addr).bind (pushedVal ⟨v, "", [], d0⟩ prior) with
            | some (.reg r') =>
              -- a pop of the word that the block pushed from `r` (L2-FLAGS: the pushes of LBB16_3 of `l2zFlags`)
              if r' != r then none else if isEntry then some "rfl"
              else if ((fb.regs.lookup r).map (·.s0)).getD false then some s!"hk{regLower r}" else none
            | some _ => none
            | none =>
              -- a pop of the word of the slot of `r`: the value of the load is the entry value
              if ((depthOf d0 addr).map fun kk => slots.contains (kk, r)).getD false then some "rfl" else none
          | _ => none
        | some _ => none
      let abis ← [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15].mapM abi
      let rsp := holeOf off "rsp"
      pure (top ++ ["    subst hn"] ++ dp ++ ["    have hret := Sites.readRet he hra",
        s!"    refine' {name} hx d {holes} fun f => ⟨⟨hra, {", ".intercalate (rsp :: abis)}⟩, {holeOf off "out"}, {holeOf off "map"}, {holeOf off "rax"}⟩",
        "    any_goals frame_call", closer])
    | .exit (.call f cont) => do
      let c ← t.callees.find? (·.name == f)
      let g ← fl.lookup cont
      let k ← (b.accesses.zip (List.range b.accesses.length)).findSome? fun (a, k) =>
        match a with
        | .store _ _ _ (.retAddr _) => some k
        | _ => none
      let retOff := (b.accesses.findSome? fun a => match a with
        | .store _ _ _ (.retAddr o) => some o
        | _ => none).getD cont
      let args := (List.range c.inputs.length).map fun i => holeOf off s!"a{i}"
      -- a stack argument: the read of its word (`?s<k>`, `frame_call`) and the value (`?e<k>`, the closer) (ARGS8)
      let stack := (List.range c.stackArgs).map fun k =>
        s!"(Lift.Tactic.Frame.readRam_arg {holeOf off s!"s{k}"} {holeOf off s!"e{k}"})"
      let args := args ++ stack
      let room := if c.room == 0 then [] else [holeOf off "room"]
      let rep := s!"⟨hpol, (by first | rfl | trivial), ⟨rfl, hx, {holeOf off "perm"}, {t.entryPC} + {retOff}, hret⟩{String.join ((args ++ room).map (", " ++ ·))}⟩"
      let memPat := if c.room == 0 then "hm" else "out', mp'"
      let abiName' : Reg64 → String
        | .rbx => "hbx'" | .rbp => "hbp'" | .r12 => "h12'" | .r13 => "h13'" | .r14 => "h14'" | .r15 => "h15'" | _ => "h?'"
      let items := targetItems v fr off "p" g "hpc.symm" (rspCloser isEntry "rw [hsp']; ") fun i =>
        match i with
        | .regX .rax => some "hz"
        | .regX r => if calleeSaved.contains r then some s!"({abiName' r}.trans {holeOf off s!"x{regLower r}"})" else none
        | .regS r =>
          if !calleeSaved.contains r then none
          else if isEntry then some (abiName' r)
          else if ((fb.regs.lookup r).map (·.s0)).getD false && !(b.regs.any (·.1 == r)) then
            some s!"({abiName' r}.trans hk{regLower r})"
          else none
        | _ => none
      let memLine := if c.room == 0 then ["      any_goals (rw [hm]; frame_call)"] else ["      any_goals frame_call"]
      pure (top ++ ["    subst hn"] ++ dp ++
        [s!"    refine' {name} hx d {holes} fun f =>",
          s!"      have hret := retOf {holeOf off s!"h{k + 1}"}",
          s!"      ⟨{rep}, {holeOf off "post"}⟩",
          "    any_goals frame_call",
          s!"    case {(holeOf off "post").drop 1} =>",
          s!"      rintro z u ⟨⟨hpc, hsp', hbx', hbp', h12', h13', h14', h15'⟩, {memPat}, hz⟩",
          "      rw [hret, Option.some.injEq] at hpc",
          s!"      refine ⟨hrep, rfl, ⟨{", ".intercalate items}⟩, nofun⟩"] ++ memLine ++ ["  " ++ closer, closer])
    | _ => none
  match body with
  | some lines => [head] ++ pre ++ top ++ heapSplits b (lines.drop top.length)
  | none => failArm "an exit or a fact that the proof does not cover"


/-- The proof of a function in the frame form (see the section). -/
private def frameProof (t : Target) (s : Summary) (fr : FrameText) : String :=
  let called := calledOf s.blocks
  let callName := called.head?
  let fl := flows s
  let memName := ["hmem"]
  let hyps := ", ".intercalate (["hpol"] ++ memName ++ ["he"] ++ s.vars.inputs.map (fun r => s!"h{regLower r}") ++ stackHyps s ++
    repConjNames fr)
  let body (calleeArgs : String) : String :=
    let head := [ s!"  refine Decompiles.ofBlocks blocks {calleeArgs} .entry init",
      "    (fun policy a s₀ l x s => l2.rep policy a s₀ ∧ x.input = a ∧ At policy s₀ l x s ∧ (l = .entry → x = init a))",
      "    (fun _ _ h => h) (fun _ _ _ h => ⟨h, rfl, rfl, fun _ => rfl⟩) ?_",
      "  rintro policy a s₀ l x s ⟨hrep, rfl, hat, hent⟩ n hn",
      s!"  have ⟨{hyps}⟩ := hrep",
      "  obtain ⟨ra, hra⟩ := he.ret",
      "  have hx := he.exec" ] ++ (if callName.isSome then retOfLines else []) ++ [
      "  cases l with" ]
    "\n".intercalate (head ++ s.blocks.flatMap (armFrame t s fr fl))
  match called.find? fun f => !t.callees.any (·.name == f) with
  | some f => failAll s!"the call to {f} has no callee interface in the target"
  | none => body (decompCalleeArgs t s)

/-- The tactic block of `decompiles_l2` for the target `t`, the summary `s` and the frame text `fr`. Its lines start at
two spaces. The proof names the lemmas of the blocks by their names. The frame form has the proof of `frameProof` (G1-16).
A function with a call or a stack access and no store through a register outside the frame form, a state with memory and
no guard, or no block gives one `fail` (the second is a model that lets a store reach the return word, for which
`decompiles_l2` is false). -/
def decompilesProof (t : Target) (s : Summary) (fr : FrameText) : String :=
  if s.blocks.isEmpty then failAll "a function with no block has no case text"
  else if fr.frameDef.isSome then frameProof t s fr
  else if s.vars.mem && fr.guardDefs.isSome then stackProof t s fr
  else if needsStack s then
    failAll "a call or a stack access in a function with no store through a register: the memory form with a guard is the only form generated"
  else if s.vars.mem && fr.guardDefs.isNone then
    failAll "a store through a register with no guard: the model lets the store reach the return word (room 0 has no guard)"
  else
    let f := formOf s.vars
    let inv := (if f.needInit then " ∧ (l = .entry → x = init a)" else "") ++
      (if f.mem then " ∧ (∀ ra, SysV.retAddr s₀ = some ra → readRam policy x.mem s₀.data.regs.rsp.toBitVec .W64 = .ok ra.toBitVec)" else "")
    let start := (if f.needInit then ", fun _ => rfl" else "") ++
      (if f.mem then ", fun ra hra => by simp only [init]; rw [h.2.1]; exact Sites.readRet h.2.2.1 hra" else "")
    let pat := (if f.needInit then ", hent" else "") ++ (if f.mem then ", hkeep" else "")
    let hyps := ", ".intercalate (["hpol", "hmem", "he"] ++
      s.vars.inputs.map (fun r => s!"h{regLower r}") ++ stackHyps s ++ repConjNames fr)
    let head := [ "  refine Decompiles.ofBlocks blocks noCallee (fun f => f.elim) .entry init",
      s!"    (fun policy a s₀ l x s => l2.rep policy a s₀ ∧ x.input = a ∧ At s₀ l x s{inv})",
      s!"    (fun _ _ h => h) (fun _ _ _ h => ⟨h, rfl, rfl{start}⟩) ?_",
      s!"  rintro policy a s₀ l x s ⟨hrep, rfl, hat{pat}⟩ n hn",
      s!"  have ⟨{hyps}⟩ := hrep",
      "  obtain ⟨ra, hra⟩ := he.ret",
      "  have hx := he.exec",
      "  cases l with" ]
    "\n".intercalate (head ++ s.blocks.flatMap (armText t s.vars f (flows s)))

/-- The theorem `name binders : stmt` with the proof text `det`, after the helpers of `det` (`Skel.Proof`). -/
def detTheorem (name binders stmt det : String) : String :=
  let p := Proof.ofText det
  let thm := s!"theorem {name}{if binders.isEmpty then "" else " " ++ binders} : {stmt} := {p.proof}"
  if p.helpers.isEmpty then thm else p.helpers ++ "\n\n" ++ thm

/-- The `det` text of `decompiles_l2`: in the memory form with a guard the proof with one lemma for each case (`stackSplit`;
`rowTy` gives the statement of the row of a block), else `by`, a line break and `decompilesProof`. -/
def decompilesDet (t : Target) (s : Summary) (fr : FrameText) (rowTy : String → Option String) : String :=
  let split := if s.blocks.isEmpty || fr.frameDef.isSome || !(s.vars.mem && fr.guardDefs.isSome) then none
    else stackSplit t s fr rowTy
  split.getD s!"by\n{decompilesProof t s fr}"

end Skel.Gen
