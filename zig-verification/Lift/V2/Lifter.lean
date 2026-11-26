module

/-
The lifter, version 2: a Kraken `Program` (one function) becomes a block machine in Lean text
(see `Lift.V2.Machine`). Deterministic, no search, and no Lean elaboration: the functions here are
plain code, so that a program can run the lifter over many functions.

* Each label starts a block `B : St → Option (Next Lbl)`. A block is a chain of `let`s that ends in
  a jump (`.go`, `.goF` with the flags), a return, a tail call or a fault.
* A `jcc` is an `if`; a `jmp` and a fall-through are jumps; a `call g` calls the lifted `g`.
* The flags are local to a block. A block gets the flags as a parameter only when it reads flags
  that a predecessor set (`liveIn`); a flag computation that nobody reads is not generated.
* The instruction table is by operand kind and width (`liftOp`). It is not trusted: the generated
  proof (`Lift.V2.Layer1`) checks each block against the `@[spec]` theorems of Kraken, and the
  differential test (`Lift.V2.Diff`) against Kraken's executor.
-/
public import Kraken.X64.Syntax
public import Kraken.X64.Parser
public import Lift.V2.Machine

@[expose] public section

namespace Lift.V2

/-- A failure of the lifter. `cat` groups the failures: `instr` (an instruction the table does not
have), `sse`, `indirect-call`, `indirect-jump`, `exception-call`, `symbol` (the address of a symbol),
`flags` (flags that the table cannot give), `struct` (the shape of the code), `parse`. -/
structure LErr where
  cat : String
  detail : String
  deriving Repr, Inhabited

/-! ### Commands -/

/-- Commands of a lifted block. -/
inductive Cmd where
  /-- `let v := e` -/
  | bind (v e : String)
  /-- `let st := { st with r := e }` -/
  | set (r : Reg64) (e : String)
  /-- `let v ← ldN st.m addr` -/
  | ld (n : Nat) (addr v : String)
  /-- `let m ← stN st.m addr val`, then `let st := { st with m := m }` -/
  | store (n : Nat) (addr val m : String)
  /-- `let fl := e`; `reads`: `e` uses the old `fl`. -/
  | flag (e : String) (reads : Bool)
  /-- The flags of the instruction are not in the table; an error if somebody reads them. -/
  | flagBad (msg : String)
  | call (target : Label)
  | tail (target : Label)
  | ite (cc : String) (t e : List Cmd)
  | jump (lbl : Label)
  | ret
  | fault
  /-- `if c then failure` -/
  | guard (c : String)
  deriving Inhabited, Repr

def regName : Reg64 → String
  | .rax => "rax" | .rbx => "rbx" | .rcx => "rcx" | .rdx => "rdx"
  | .rsi => "rsi" | .rdi => "rdi" | .rsp => "rsp" | .rbp => "rbp"
  | .r8 => "r8" | .r9 => "r9" | .r10 => "r10" | .r11 => "r11"
  | .r12 => "r12" | .r13 => "r13" | .r14 => "r14" | .r15 => "r15"

def ccName : CondCode → String
  | .o => "o" | .no => "no" | .c => "c" | .nc => "nc" | .z => "z" | .nz => "nz"
  | .be => "be" | .a => "a" | .s => "s" | .ns => "ns" | .p => "p" | .np => "np"
  | .l => "l" | .ge => "ge" | .le => "le" | .g => "g"

/-! ### Expressions

An expression is its text and how tightly it binds: an atom (`st.rax`, `0#64`, `v0`), an
application (`st.rax.setWidth 32`) or an infix term (`a + b`). -/

structure E where
  s : String
  p : Nat

def E.atom (s : String) : E := ⟨s, 2⟩
def E.app (s : String) : E := ⟨s, 1⟩
def E.inf (s : String) : E := ⟨s, 0⟩
/-- As a function argument or the receiver of a method. -/
def E.arg (e : E) : String := if e.p ≥ 2 then e.s else s!"({e.s})"
/-- As an operand of an infix operator. -/
def E.opnd (e : E) : String := if e.p ≥ 1 then e.s else s!"({e.s})"
/-- `e.f` (a literal needs parentheses as a receiver) -/
def E.meth (e : E) (f : String) : E :=
  E.app (if e.s.contains '#' && e.p ≥ 2 then s!"({e.s}).{f}" else s!"{e.arg}.{f}")

/-- The zero extension to 64 bits; a literal is extended at once. -/
def E.zext64 (e : E) : E :=
  match e.s.splitOn "#" with
  | [n, _] => if n.all Char.isDigit && e.p ≥ 2 then E.atom s!"{n}#64" else e.meth "setWidth 64"
  | _ => e.meth "setWidth 64"
/-- `f e` -/
def E.fn (f : String) (args : List E) : E := E.app (" ".intercalate (f :: args.map (·.arg)))
/-- `a op b` -/
def E.bin (a : E) (op : String) (b : E) : E := E.inf s!"{a.opnd} {op} {b.opnd}"

/-- The literal `n#w`. -/
def E.lit (n : Nat) (w : Nat) : E := E.atom s!"{n}#{w}"

/-! ### Generator state -/

structure Gen where
  counts : List (String × Nat) := []
  callees : List Label := []
  /-- The symbols whose address the code uses. -/
  labels : List Label := []

abbrev GenM := StateT Gen (Except LErr)

def fail {α : Type} (cat detail : String) : GenM α := throw ⟨cat, detail⟩

/-- A fresh variable `<pfx><n>`; the numbers are per prefix. -/
def fresh (pfx : String) : GenM String := do
  let g ← get
  let n := (g.counts.lookup pfx).getD 0
  set { g with counts := (pfx, n + 1) :: g.counts.filter (·.1 != pfx) }
  return s!"{pfx}{n}"

def noteLabel (l : Label) : GenM Unit :=
  modify fun g => if g.labels.contains l then g else { g with labels := g.labels ++ [l] }

def noteCallee (l : Label) : GenM Unit :=
  modify fun g => if g.callees.contains l then g else { g with callees := g.callees ++ [l] }

/-! ### Operands -/

/-- The value of a register of width `w`. -/
def regExpr {w : Width} (r : Reg w) : E :=
  match r with
  | .low b w' => if w' == .W64 then E.atom s!"st.{regName b}" else E.app s!"st.{regName b}.setWidth {w'.bits}"
  | .ah => E.app "(st.rax >>> 8).setWidth 8"
  | .bh => E.app "(st.rbx >>> 8).setWidth 8"
  | .ch => E.app "(st.rcx >>> 8).setWidth 8"
  | .dh => E.app "(st.rdx >>> 8).setWidth 8"

/-- The command that writes `v` to the register `r`, with the rules of x86-64: a 32-bit write clears
the upper half, a narrower write keeps the other bits. -/
def regWrite {w : Width} (r : Reg w) (v : E) : Cmd :=
  match r with
  | .low b w' =>
    match w' with
    | .W64 => .set b v.s
    | .W32 => .set b v.zext64.s
    | .W16 | .W8 => .set b s!"st.{regName b}.replaceLow {v.arg}"
  | .ah => .set .rax s!"st.rax.replaceLow ({v.arg} ++ st.rax.setWidth 8)"
  | .bh => .set .rbx s!"st.rbx.replaceLow ({v.arg} ++ st.rbx.setWidth 8)"
  | .ch => .set .rcx s!"st.rcx.replaceLow ({v.arg} ++ st.rcx.setWidth 8)"
  | .dh => .set .rdx s!"st.rdx.replaceLow ({v.arg} ++ st.rdx.setWidth 8)"

/-- The register that a register of any width is part of, as a 64-bit read. -/
def regBase {w : Width} (r : Reg w) : Reg64 := Reg.base r

def ldName (n : Nat) : String := match n with | 8 => "ld64" | 4 => "ld32" | 2 => "ld16" | _ => "ld8"
def stName (n : Nat) : String := match n with | 8 => "st64" | 4 => "st32" | 2 => "st16" | _ => "st8"

def dispE (d : Int64) : E :=
  let i := d.toInt
  if i ≥ 0 then E.lit i.toNat 64 else E.app s!"BitVec.ofInt 64 ({i})"

/-- A constant expression of the instruction: the address of a symbol is `lbl "sym"`. `rip`: the
expression is relative to the end of the instruction, which the symbol addressing of the code
model makes the symbol itself. -/
partial def constE (c : ConstExpr) : GenM E :=
  match c with
  | .int64 d => return dispE d
  | .label l => do noteLabel l; return E.app s!"lbl \"{l}\""
  | .add a b => do return (← constE a).bin "+" (← constE b)
  | .sub a b => do return (← constE a).bin "-" (← constE b)
  | _ => fail "symbol" "position-dependent constant"

/-- The address `base + idx * scale + disp`, in the state `st`. -/
def addrE (a : AddrExpr) : GenM E := do
  let mut parts : List E := []
  let mut rip := false
  match a.base with
  | some (.reg b) => parts := parts ++ [E.atom s!"st.{regName b}"]
  | some .rip => rip := true
  | none => pure ()
  match a.idx with
  | some ⟨r, sc⟩ =>
    parts := parts ++ [if sc.bytes == 1 then E.atom s!"st.{regName r}" else E.app s!"st.{regName r} * {sc.bytes}#64"]
  | none => pure ()
  match a.disp with
  | .int64 d =>
    if rip then fail "symbol" "rip-relative address without a symbol"
    if d.toInt != 0 || parts.isEmpty then parts := parts ++ [dispE d]
  | .sub x .after_current_instruction =>
    unless rip do fail "symbol" "relative address without rip"
    parts := parts ++ [← constE x]
  | .add (.sub x .after_current_instruction) k =>
    unless rip do fail "symbol" "relative address without rip"
    parts := parts ++ [← constE x, ← constE k]
  | c =>
    if rip then fail "symbol" "rip-relative address of another form"
    parts := parts ++ [← constE c]
  match parts with
  | [e] => return e
  | e :: rest => return E.inf (rest.foldl (fun acc x => acc ++ " + " ++ x.opnd) e.opnd)
  | [] => return E.lit 0 64

/-- The value of an immediate at width `w`. -/
def immE (w : Width) (c : ConstExpr) : GenM E :=
  match c with
  | .int64 i => return E.lit (i.toInt % (2 ^ w.bits : Nat)).toNat w.bits
  | c => do
    let e ← constE c
    return if w == .W64 then e else e.meth s!"setWidth {w.bits}"

/-- Reads a register or memory operand: the commands and the value (type `BitVec w.bits`). -/
def readRM {w : Width} (o : RegOrMem w) (pfx : String := "v") : GenM (List Cmd × E) := do
  match o with
  | .reg r => return ([], regExpr r)
  | .mem a =>
    let ad ← addrE a
    let v ← fresh pfx
    return ([.ld w.bytes ad.arg v], E.atom v)

def readOp {w : Width} (o : Operand w) (pfx : String := "v") : GenM (List Cmd × E) := do
  match o with
  | .regOrMem rm => readRM rm pfx
  | .imm c => return ([], ← immE w c)

/-- Writes `v` to a register or memory operand. -/
def writeRM {w : Width} (d : RegOrMem w) (v : E) : GenM (List Cmd) := do
  match d with
  | .reg r => return [regWrite r v]
  | .mem a =>
    let ad ← addrE a
    let m ← fresh "m"
    return [.store w.bytes ad.arg v.arg m]

/-- `if cc then a else b` -/
def condE (cc : CondCode) (a b : E) : E :=
  E.inf s!"if CondCode.{ccName cc}.interp fl then {a.s} else {b.s}"

/-- A value bound to a fresh variable. -/
def bindE (e : E) : GenM (List Cmd × E) := do
  let t ← fresh "t"
  return ([.bind t e.s], E.atom t)

/-- The count of a shift: a number (of the operand width mask) for an immediate, an expression for
`%cl`. -/
def shiftCount (w : Width) (c : ShiftCountExpr) : GenM E := do
  let mask := if w == .W64 then 63 else 31
  match c with
  | .cl => return E.inf s!"st.rcx.toNat &&& {mask}"
  | .imm8 (.int64 i) => return E.atom s!"{(i.toInt % 256).toNat &&& mask}"
  | .imm8 _ => fail "symbol" "shift count with a symbol"

/-- A name of the operation for the error messages. -/
def opName {w : Width} (op : Operation w) : String :=
  ((toString (repr op)).splitOn " ").headD "?" |>.replace "Lift.V2." "" |>.replace "Operation." ""

/-- The commands of an operation. `asz` is the address size of the instruction. -/
def liftOp {w : Width} (op : Operation w) : GenM (List Cmd) := do
  let bits := w.bits
  let zero := E.lit 0 bits
  let one := E.lit 1 bits
  -- `dst := dst op src` with flags
  let binop (dst : Dst w) (src : Operand w) (val : E → E → E) (fl : Option (E → E → E → Cmd)) :
      GenM (List Cmd) := do
    let (c1, b) ← readRM dst
    let (c2, a) ← readOp src "w"
    let (c3, t) ← bindE (val b a)
    let flc := match fl with | some f => [f b a t] | none => []
    let c4 ← writeRM dst t
    return c1 ++ c2 ++ c3 ++ flc ++ c4
  match op with
  | .mov dst src =>
    let (c1, a) ← readOp src
    return c1 ++ (← writeRM dst a)
  | @Operation.movzx _ w' dst src =>
    let (c1, a) ← readRM src
    let a64 := a.zext64
    let c2 ← match dst with
      | .reg r => if w == .W64 || w == .W32 then pure [Cmd.set (Reg.base r) a64.s]
                  else writeRM dst (a.meth s!"setWidth {bits}")
      | _ => writeRM dst (a.meth s!"setWidth {bits}")
    return c1 ++ c2
  | @Operation.movsx _ w' dst src =>
    let (c1, a) ← readRM src
    let ext := a.meth s!"signExtend {bits}"
    let c2 ← match dst with
      | .reg r => if w == .W32 then pure [Cmd.set (Reg.base r) (ext.meth "setWidth 64").s]
                  else writeRM dst ext
      | _ => writeRM dst ext
    return c1 ++ c2
  | .push src =>
    unless w == .W64 do fail "instr" "push of a narrow operand"
    let (c1, a) ← readOp src
    let (c2, t) ← bindE a
    let m ← fresh "m"
    return c1 ++ (if a.p ≥ 2 && c1.isEmpty then [Cmd.bind (t.s) a.s] else c2) ++
      [.store 8 "(st.rsp - 8#64)" t.s m, .set .rsp "st.rsp - 8#64"]
  | .pop dst =>
    unless w == .W64 do fail "instr" "pop of a narrow operand"
    let v ← fresh "v"
    return [.ld 8 "st.rsp" v, .set .rsp "st.rsp + 8#64"] ++ (← writeRM dst (E.atom v))
  | .setcc cc dst =>
    writeRM dst (condE cc one zero)
  | .cmovcc cc dst src =>
    let (c1, a) ← readRM src
    return c1 ++ [regWrite dst (condE cc a (regExpr dst))]
  | .lea dst src =>
    let a ← addrE src
    return [regWrite dst (if bits == 64 then a else a.meth s!"setWidth {bits}")]
  | .add dst src =>
    -- Kraken's order: `src + dst`
    binop dst src (fun b a => a.bin "+" b)
      (some fun b a _ => .flag (E.fn "StatusFlags.ofAdd" [a, b]).s false)
  | .sub dst src =>
    binop dst src (fun b a => b.bin "-" a)
      (some fun b a _ => .flag (E.fn "StatusFlags.ofSub" [b, a]).s false)
  | .and dst src =>
    binop dst src (fun b a => b.bin "&&&" a)
      (some fun _ _ t => .flag s!"StatusFlags.ofLogic {t.arg} false" false)
  | .or dst src =>
    binop dst src (fun b a => b.bin "|||" a)
      (some fun _ _ t => .flag s!"StatusFlags.ofLogic {t.arg} false" false)
  | .xor dst src =>
    binop dst src (fun b a => b.bin "^^^" a)
      (some fun _ _ t => .flag s!"StatusFlags.ofLogic {t.arg} false" false)
  | .adc dst src =>
    binop dst src (fun b a => (a.bin "+" b).bin "+" (E.atom s!"(if fl.cf then {one.s} else {zero.s})"))
      (some fun b a _ => .flag (E.fn "Fl.adc" [a, b, E.atom "fl.cf"]).s true)
  | .sbb dst src =>
    binop dst src (fun b a => (b.bin "-" a).bin "-" (E.atom s!"(if fl.cf then {one.s} else {zero.s})"))
      (some fun b a _ => .flag (E.fn "Fl.sbb" [b, a, E.atom "fl.cf"]).s true)
  | .inc dst =>
    let (c1, b) ← readRM dst
    let (c3, t) ← bindE (b.bin "+" one)
    return c1 ++ c3 ++ [.flag (E.fn "Fl.inc" [b, E.atom "fl.cf"]).s true] ++ (← writeRM dst t)
  | .dec dst =>
    let (c1, b) ← readRM dst
    let (c3, t) ← bindE (b.bin "-" one)
    return c1 ++ c3 ++ [.flag (E.fn "Fl.dec" [b, E.atom "fl.cf"]).s true] ++ (← writeRM dst t)
  | .neg dst =>
    let (c1, b) ← readRM dst
    let (c3, t) ← bindE (E.inf s!"-{b.opnd}")
    return c1 ++ c3 ++ [.flag (E.fn "Fl.neg" [b]).s false] ++ (← writeRM dst t)
  | .not dst =>
    let (c1, b) ← readRM dst
    return c1 ++ (← writeRM dst (E.inf s!"~~~{b.opnd}"))
  | .cmp a b =>
    let (c1, x) ← readRM a
    let (c2, y) ← readOp b "w"
    return c1 ++ c2 ++ [.flag (E.fn "StatusFlags.ofSub" [x, y]).s false]
  | .test a b =>
    let (c1, x) ← readRM a
    let (c2, y) ← readOp b "w"
    return c1 ++ c2 ++ [.flag s!"StatusFlags.ofLogic {(x.bin "&&&" y).arg} false" false]
  | .shl dst c | .shr dst c | .sar dst c | .rol dst c | .ror dst c =>
    let (c1, b) ← readRM dst
    let n ← shiftCount w c
    let v : E := match op with
      | .shl .. => b.bin "<<<" n
      | .shr .. => b.bin ">>>" n
      | .sar .. => b.meth s!"sshiftRight {n.arg}"
      | .rol .. => b.meth s!"rotateLeft {n.arg}"
      | _ => b.meth s!"rotateRight {n.arg}"
    return c1 ++ [.flagBad s!"flags of {opName op}"] ++ (← writeRM dst v)
  | .imul dst s1 s2 =>
    let (c1, a) ← readRM s1
    let (c2, b) ← readOp s2 "w"
    let d : Dst w := match dst with | some d => d | none => s1
    return c1 ++ c2 ++ [.flagBad "flags of imul"] ++ (← writeRM d (a.bin "*" b))
  | .mul src | .imul1 src | .div src | .idiv src =>
    unless w == .W64 || w == .W32 do fail "instr" s!"{opName op} of a narrow operand"
    let (c1, d) ← readRM src
    let ra : E := E.atom "st.rax"
    let rd : E := E.atom "st.rdx"
    let ra' := if w == .W64 then ra else ra.meth s!"setWidth {bits}"
    let rd' := if w == .W64 then rd else rd.meth s!"setWidth {bits}"
    let wide := bits * 2
    let wr (r : Reg64) (v : E) : Cmd := regWrite (Reg.low r w) v
    match op with
    | .mul _ | .imul1 _ =>
      let ext := match op with | .mul _ => "setWidth" | _ => "signExtend"
      let (c2, p) ← bindE ((ra'.meth s!"{ext} {wide}").bin "*" (d.meth s!"{ext} {wide}"))
      return c1 ++ c2 ++ [.flagBad "flags of mul"] ++
        [wr .rax (p.meth s!"setWidth {bits}"), wr .rdx ((p.bin ">>>" (E.atom s!"{bits}")).meth s!"setWidth {bits}")]
    | .div _ =>
      let (c2, n) ← bindE (E.inf s!"{rd'.s} ++ {ra'.s}")
      return c1 ++ c2 ++
        [.guard s!"{d.s} == 0#{bits} || {n.arg}.toNat / {d.arg}.toNat ≥ {2 ^ bits}",
         .flagBad "flags of div",
         wr .rax (E.app s!"BitVec.ofNat {bits} ({n.arg}.toNat / {d.arg}.toNat)"),
         wr .rdx (E.app s!"BitVec.ofNat {bits} ({n.arg}.toNat % {d.arg}.toNat)")]
    | _ =>
      let (c2, n) ← bindE (E.inf s!"{rd'.s} ++ {ra'.s}")
      return c1 ++ c2 ++
        [.guard s!"{d.arg}.toInt == 0 || {n.arg}.toInt.tdiv {d.arg}.toInt < -{2 ^ (bits - 1)} || {n.arg}.toInt.tdiv {d.arg}.toInt ≥ {2 ^ (bits - 1)}",
         .flagBad "flags of idiv",
         wr .rax (E.app s!"BitVec.ofInt {bits} ({n.arg}.toInt.tdiv {d.arg}.toInt)"),
         wr .rdx (E.app s!"BitVec.ofInt {bits} ({n.arg}.toInt.tmod {d.arg}.toInt)")]
  | .cwtd => return [regWrite (Reg.low .rdx .W16) (E.inf "if st.rax.setWidth 16 |>.msb then -1#16 else 0#16")]
  | .cltd => return [regWrite (Reg.low .rdx .W32) (E.inf "if (st.rax.setWidth 32).msb then -1#32 else 0#32")]
  | .cqto => return [regWrite (Reg.low .rdx .W64) (E.inf "if st.rax.msb then -1#64 else 0#64")]
  | .cbtw => return [regWrite (Reg.low .rax .W16) (E.app "(st.rax.setWidth 8).signExtend 16")]
  | .cwtl => return [regWrite (Reg.low .rax .W32) (E.app "(st.rax.setWidth 16).signExtend 32")]
  | .cltq => return [regWrite (Reg.low .rax .W64) (E.app "(st.rax.setWidth 32).signExtend 64")]
  | .leave =>
    let v ← fresh "v"
    return [.ld 8 "st.rbp" v, .set .rsp "st.rbp + 8#64", .set .rbp v]
  | .nop _ | .nopalign _ _ | .prefetcht0 _ => return []
  | .ud2 => return [.fault]
  | .bswap dst =>
    if w == .W32 || w == .W64 then
      return [regWrite dst (E.fn s!"bswap{bits}" [regExpr dst])]
    else fail "instr" "bswap"
  | .call _ | .jcc .. | .jmp _ | .ret => fail "struct" "a control transfer in the middle of straight code"
  | _ => fail "instr" (opName op)

/-- The target label of a direct `call` or `jmp`. -/
def relLabel? : RelRegOrMem → Option Label
  | .rel (.sub (.label l) .after_current_instruction) => some l
  | .rel (.label l) => some l
  | _ => none

/-- Names of the C++ runtime that raise, catch or unwind an exception. -/
def isExceptionName (l : Label) : Bool :=
  ["__cxa_throw", "__cxa_rethrow", "__cxa_begin_catch", "__cxa_end_catch", "__cxa_allocate_exception",
   "__cxa_free_exception", "_Unwind_Resume", "__gxx_personality_v0", "__cxa_call_unexpected",
   "_ZSt9terminatev", "__cxa_bad_cast", "__cxa_bad_typeid", "__cxa_throw_bad_array_new_length",
   "_ZSt17__throw_bad_allocv", "_ZSt20__throw_length_errorPKc", "_ZSt19__throw_logic_errorPKc",
   "_ZSt24__throw_out_of_range_fmtPKcz", "_ZSt20__throw_out_of_rangePKc",
   "_ZSt25__throw_bad_function_callv", "_ZSt16__throw_bad_castv", "_ZSt28__throw_bad_array_new_lengthv"
  ].any (fun n => l == n || l.startsWith "__cxa_" || l.startsWith "_Unwind_")
    || (l.startsWith "_ZSt" && (l.splitOn "__throw").length > 1)

/-- The commands of one instruction that is not a branch. -/
def liftInstr (i : Instr) : GenM (List Cmd) := do
  match i with
  | .regular asz _ op =>
    unless asz == .W64 do fail "instr" "address size other than 64 bits"
    match op with
    | .call t =>
      match relLabel? t with
      | some l =>
        if isExceptionName l then fail "exception-call" l
        noteCallee l
        return [.call l]
      | none => fail "indirect-call" "call through a register or memory"
    | _ => liftOp op
  | .avx .. => fail "sse" "vector or floating-point instruction"

/-! ### Flags

A flag command is dead when no later command reads the flags. -/

/-- The identifiers of an expression text. -/
def tokens (s : String) : List String :=
  (s.split fun c => !(c.isAlphanum || c == '_' || c == '.' || c == '\'')).toList.map (·.copy) |>.filter (· != "")

def mentionsFl (s : String) : Bool := (tokens s).any fun t => t == "fl" || t.startsWith "fl."

def Cmd.readsFl : Cmd → Bool
  | .bind _ e | .set _ e => mentionsFl e
  | .ld _ a _ => mentionsFl a
  | .store _ a v _ => mentionsFl a || mentionsFl v
  | .flag _ r => r
  | .guard c => mentionsFl c
  | .ite .. => true
  | _ => false

/-- Are the flags live at the start of the commands `cs`? `live l` tells it for the start of the
block `l`. The error is a read of flags that a call or a flag command without semantics leaves. -/
def liveBefore (live : Label → Bool) : List Cmd → Except LErr Bool
  | [] => pure false
  | c :: rest => do
    match c with
    | .jump l => pure (live l)
    | .ret | .tail _ | .fault => pure false
    | .ite .. => pure true
    | .call l =>
      if (← liveBefore live rest) then throw ⟨"flags", s!"flags read after the call of {l}"⟩
      else pure false
    | .flag _ r => do
      if (← liveBefore live rest) then pure r else liveBefore live rest
    | .flagBad msg => do
      if (← liveBefore live rest) then throw ⟨"flags", msg⟩ else liveBefore live rest
    | _ => do
      let r ← liveBefore live rest
      pure (r || c.readsFl)

/-- Removes the dead flag commands (and the flags without semantics, which must be dead). -/
partial def prune (live : Label → Bool) : List Cmd → Except LErr (List Cmd)
  | [] => pure []
  | c :: rest => do
    match c with
    | .ite cc t e =>
      pure [.ite cc (← prune live t) (← prune live e)]
    | .flag _ _ | .flagBad _ =>
      if (← liveBefore live rest) then
        match c with
        | .flagBad msg => throw ⟨"flags", msg⟩
        | _ => pure (c :: (← prune live rest))
      else prune live rest
    | _ => pure (c :: (← prune live rest))

/-- Is the variable `v` mentioned by the command? -/
def Cmd.mentions (v : String) : Cmd → Nat :=
  -- `v.setWidth 64` mentions `v`
  let count (e : String) : Nat := ((tokens e).filter fun t => t == v || t.startsWith (v ++ ".")).length
  fun
  | .bind _ e | .set _ e => count e
  | .ld _ a _ => count a
  | .store _ a x _ => count a + count x
  | .flag e _ => count e
  | .guard c => count c
  | _ => 0

/-- Replaces the token `v` in a text by `e`. -/
def substTok (v e : String) (s : String) : String :=
  -- `v.f` (a method of `v`) becomes `e.f`; a literal needs parentheses as a receiver
  let sub (tok : String) : String :=
    if tok == v then e
    else if tok.startsWith (v ++ ".") then (if e.contains '#' && !e.startsWith "(" then s!"({e})" else e) ++ (tok.drop v.length).toString
    else tok
  let rec go (cs : List Char) (cur : String) (acc : String) : String :=
    match cs with
    | [] => acc ++ sub cur
    | c :: r =>
      if c.isAlphanum || c == '_' || c == '.' || c == '\'' then go r (cur.push c) acc
      else go r "" (acc ++ sub cur ++ c.toString)
  go s.toList "" ""

def Cmd.subst (v e : String) : Cmd → Cmd
  | .bind x s => .bind x (substTok v e s)
  | .set r s => .set r (substTok v e s)
  | .ld n a x => .ld n (substTok v e a) x
  | .store n a x m => .store n (substTok v e a) (substTok v e x) m
  | .flag s r => .flag (substTok v e s) r
  | .guard c => .guard (substTok v e c)
  | c => c

/-- Inlines the variable bound by `bind` into the next command when it is the only use. -/
partial def inlineBinds : List Cmd → List Cmd
  | [] => []
  | .ite cc t e :: rest => .ite cc (inlineBinds t) (inlineBinds e) :: inlineBinds rest
  | .bind v e :: next :: rest =>
    let uses := (next :: rest).foldl (fun n c => n + c.mentions v) 0
    let atomic := !(e.contains ' ')
    if uses == 1 && next.mentions v == 1 && !(match next with | .ite .. | .call _ | .jump _ => true | _ => false) then
      let e' := if atomic then e else s!"({e})"
      inlineBinds (next.subst v e' :: rest)
    else .bind v e :: inlineBinds (next :: rest)
  | c :: rest => c :: inlineBinds rest

/-- One instruction in the tests: its commands with the dead flags removed. -/
def liftInstrCmds (i : Instr) (flagsLive : Bool) : Except LErr (List Cmd) := do
  let (cs, _) ← (liftInstr i).run {}
  prune (fun _ => flagsLive) (cs ++ [Cmd.jump "?"])
    |>.map fun cs => cs.dropLast

/-! ### Printing -/

def ind (n : Nat) : String := "".pushn ' ' n

/-- The lines of a command; `names` gives the Lean function of a callee, `lbl` a label's
constructor and whether the flags go with the jump. -/
partial def printCmd (names : Label → String) (lbl : Label → String × Bool) (hasFl : Bool) :
    Cmd → List String
  | .bind v e => [s!"let {v} := {e}"]
  | .set r e => [s!"let st := \{ st with {regName r} := {e} }"]
  | .ld n a v => [s!"let {v} ← {ldName n} st.m {a}"]
  | .store n a v m => [s!"let {m} ← {stName n} st.m {a} {v}", s!"let st := \{ st with m := {m} }"]
  | .flag e _ => [s!"let fl := {e}"]
  | .flagBad msg => [s!"-- flags: {msg}"]
  | .call l => [s!"let st ← call {names l} n st"]
  | .tail l => [s!"let st ← {names l} n st", "return .ret st"]
  | .ite cc t e =>
    [s!"if CondCode.{cc}.interp fl then"] ++ (t.flatMap (printCmd names lbl hasFl)).map (ind 2 ++ ·) ++
    ["else"] ++ (e.flatMap (printCmd names lbl hasFl)).map (ind 2 ++ ·)
  | .jump l =>
    let (c, f) := lbl l
    [if f then s!"return .goF {c} st fl" else s!"return .go {c} st"]
  | .ret => ["let st ← st.leave", "return .ret st"]
  | .fault => ["failure"]
  | .guard c => [s!"if {c} then failure"]

/-! ### Blocks -/

structure LBlock where
  label : Label
  /-- The Lean name of the block and the constructor of `Lbl`. -/
  name : String
  cmds : List Cmd
  /-- The block reads flags that a predecessor sets. -/
  liveIn : Bool := false

def jmpLabel? : Instr → Option Label
  | .regular _ _ (.jmp t) => relLabel? t
  | _ => none

def isIndirectJmp : Instr → Bool
  | .regular _ _ (.jmp t) => (relLabel? t).isNone
  | _ => false

/-- The commands of the instructions of a block. `next` is the label after the block; `own` the
labels of the function. -/
partial def liftBody (own : List Label) (next : Option Label) (is : List Instr) : GenM (List Cmd) := do
  match is with
  | [] =>
    match next with
    | some l => return [.jump l]
    | none => fail "struct" "the code falls off its end"
  | i :: rest =>
    match i with
    | .regular _ _ .ret => return [.ret]
    | .regular _ _ (.jcc cc l) =>
      unless own.contains l do fail "struct" s!"conditional jump out of the function ({l})"
      return [.ite (ccName cc) [.jump l] (← liftBody own next rest)]
    | .regular _ _ (.jmp t) =>
      match relLabel? t with
      | some l =>
        if own.contains l then return [.jump l]
        else if isExceptionName l then fail "exception-call" l
        else
          noteCallee l
          return [.tail l]
      | none => fail "indirect-jump" "jump through a register or memory"
    | _ =>
      let cs ← liftInstr i
      -- after a fault, or after a call at the end of the code (a function that does not return),
      -- nothing runs
      let isCall := match i with | .regular _ _ (.call _) => true | _ => false
      if (cs.getLast?.map fun | .fault => true | _ => false).getD false then return cs
      else if isCall && rest.isEmpty && next.isNone then return cs ++ [.fault]
      else return cs ++ (← liftBody own next rest)

def blockNameOf (entry l : Label) : String :=
  if l == entry then "entry"
  else
    let s := (if l.startsWith "." then l.drop 1 |>.copy else l).map fun c =>
      if c.isAlphanum || c == '_' then c else '_'
    if ["entry", "step", "fn", "Lbl", "St", "run"].contains s then s ++ "_" else s

/-- The blocks of a program: label and instructions. -/
def splitBlocks (p : Program) : Except LErr (List (Label × List Instr)) := do
  let mut blocks : Array (Label × Array Instr) := #[]
  for d in p do
    match d with
    | .label l => blocks := blocks.push (l, #[])
    | .instr i =>
      if blocks.isEmpty then throw ⟨"struct", "the code starts with no label"⟩
      blocks := blocks.modify (blocks.size - 1) fun (l, is) => (l, is.push i)
    | .byteArray _ => throw ⟨"struct", "data in the code"⟩
  return blocks.toList.map fun (l, is) => (l, is.toList)

structure LFn where
  /-- The label of the first block: the symbol of the function. -/
  entry : Label
  blocks : List LBlock
  callees : List Label
  /-- The symbols whose address the code uses (the function needs `Labels`). -/
  labels : List Label := []
  deriving Inhabited

/-- Does any block of the function call or tail call? -/
partial def Cmd.hasCall : Cmd → Bool
  | .call _ | .tail _ => true
  | .ite _ t e => t.any Cmd.hasCall || e.any Cmd.hasCall
  | _ => false

/-- Lifts a program (one function) to blocks with the flags resolved. -/
def liftFn (p : Program) : Except LErr LFn := do
  let blocks ← splitBlocks p
  let some (en, _) := blocks.head? | throw ⟨"struct", "empty program"⟩
  let own := blocks.map (·.1)
  let nexts := (own.drop 1).map some ++ [none]
  let mut gen : Gen := {}
  let mut raw : List (Label × List Cmd) := []
  for ((l, is), next) in blocks.zip nexts do
    match (liftBody own next is).run gen with
    | .ok (c, g) => gen := g; raw := raw ++ [(l, c)]
    | .error e => throw ⟨e.cat, s!"{e.detail} (block {l})"⟩
  -- Which blocks read flags that come from outside: a fixpoint from "no block does".
  let mut liveIn : List (Label × Bool) := own.map (·, false)
  let lookup (li : List (Label × Bool)) (l : Label) : Bool := (li.lookup l).getD false
  for _ in [0:own.length + 2] do
    let mut changed := false
    let mut next : List (Label × Bool) := []
    for (l, cs) in raw do
      -- liveness of the unpruned commands: a flag command is a definition
      let b ← liveBefore (lookup liveIn) cs
      next := next ++ [(l, b)]
      if b != lookup liveIn l then changed := true
    liveIn := next
    if !changed then break
  if lookup liveIn en then throw ⟨"flags", "the function reads flags that its caller sets"⟩
  let mut out : List LBlock := []
  for (l, cs) in raw do
    let cs' ← prune (lookup liveIn) cs
    out := out ++ [{ label := l, name := blockNameOf en l, cmds := inlineBinds cs', liveIn := lookup liveIn l }]
  return { entry := en, blocks := out, callees := gen.callees, labels := gen.labels }

/-! ### The Lean text of a lifted function -/

/-- The text of a lifted function in the namespace `ns`; `names l` is the Lean name of the lifted
function of the label `l`. Commands, in order: the labels, the blocks, `step`, `fn`. -/
def printFn (ns : String) (names : Label → String) (f : LFn) : List String := Id.run do
  let nameOf (l : Label) : String := ((f.blocks.find? (·.label == l)).map (·.name)).getD l
  let flOf (l : Label) : Bool := ((f.blocks.find? (·.label == l)).map (·.liveIn)).getD false
  let lbl (l : Label) : String × Bool := (s!"Lbl.{nameOf l}", flOf l)
  let mut cmds : List String := [s!"namespace {ns}"]
  if !f.labels.isEmpty then cmds := cmds ++ ["variable [Labels]"]
  cmds := cmds ++ [s!"inductive Lbl where\n" ++ "".intercalate (f.blocks.map fun b => s!"  | {b.name}\n") ++
    "  deriving DecidableEq"]
  for b in f.blocks do
    let hasCall := b.cmds.any Cmd.hasCall
    let params := (if hasCall then "(n : Nat) " else "") ++ "(st : St)" ++ (if b.liveIn then " (fl : StatusFlags)" else "")
    let body := (b.cmds.flatMap (printCmd names lbl b.liveIn)).map (ind 2 ++ ·)
    cmds := cmds ++ [s!"def {b.name} {params} : Option (Next Lbl) := do\n" ++ "\n".intercalate body]
  let arms := f.blocks.map fun b =>
    let hasCall := b.cmds.any Cmd.hasCall
    let args := (if hasCall then "n " else "") ++ "st" ++ (if b.liveIn then " fl" else "")
    s!"  | .{b.name}, st, {if b.liveIn then "fl" else "_"} => {b.name} {args}"
  cmds := cmds ++ [s!"def step (n : Nat) : Lbl → St → StatusFlags → Option (Next Lbl)\n" ++ "\n".intercalate arms]
  cmds := cmds ++ [s!"def fn (n : Nat) (st : St) : Option St := run step n .entry st flags0"]
  cmds := cmds ++ [s!"end {ns}"]
  return cmds

/-- The commands of one instruction as lines: for the tests of the table. -/
def liftInstrText (insn : String) (flagsLive : Bool := true) : Except LErr (List String) := do
  match Kraken.X64.Parser.parse insn with
  | .error e => throw ⟨"parse", e⟩
  | .ok [.instr i] =>
    let cs ← liftInstrCmds i flagsLive
    return cs.flatMap (printCmd id (fun l => (l, false)) false)
  | .ok _ => throw ⟨"parse", "not one instruction"⟩

end Lift.V2
