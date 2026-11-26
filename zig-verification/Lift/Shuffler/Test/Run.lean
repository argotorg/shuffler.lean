module

public import Lift.Shuffler.L1
public import Lift.Shuffler.Statement
public import Lift.Shuffler.Test.Planner
public import Lift.Toys.Test.Run
public import Kraken.X64.PrintATT
public import Lean.Data.Json
meta import Lift.Shuffler.L1
meta import Lift.Shuffler.Statement
meta import Lift.Shuffler.Test.Planner
meta import Lift.Toys.Test.Run
meta import Kraken.X64.PrintATT
meta import Lean.Data.Json

@[expose] public section

/-! Run test of the exact L1 of the full shuffler (`Lift/Shuffler/L1.lean`) against native results.

The vectors are those of the native runs of `solidity_shuffler_shuffle` (`Lift/Shuffler/Test/data/native-*.jsonl`,
made by `tools/shuffler-harness`): the input (source, target, spill bytes, reach, `spilling_allowed`) and the
output (status, spill bytes after the call, and after Done the stack, the trace and the sources). Each vector
becomes a machine start state with the System V convention: `rdi` is the record `Shuffle` (96 bytes), the
return address and the marks of the callee-saved registers as in `Lift/Level3/Test/Run.lean`. The memory
is mapped for the stack (512 bytes below `rsp`), the record, the source, the target, the spill buffer and the
workspace (357,672 bytes, zero): an access outside them is a fault. The state runs under `L1.step`
(`Lift.Shuffler.L1`, with its dispatch indexed: `step`) with the runner step `handle` of the toy tests until the PC is the return address.
The run must return with `rsp` and the marks restored, `eax` equal to the native status, the spill buffer equal
to the native one, the record fields at offsets 0 to 63, the source and the target as before, and after Done the
pointers of the record in the workspace, `trace_size`, and the stack, the trace (bytes 0, 1 and 4 to 11 of each
12-byte operation) and the sources equal to the native ones. -/

namespace Lift.Shuffler.Test.Run

open Lift.P2.Total Lift.Shuffler Lift.Shuffler.Statement
open Lift.Shuffler.Test.Planner (Vec)
open Lift.Toys.Test.Run (handle Stop index stepWith)

/-! ### Layout and start state -/

def rsp0 : BitVec 64 := 0x7ff00008
def ra0 : BitVec 64 := 0x200000
/-- Bytes of stack below `rsp0` that are mapped (filled with 0xCD); the room of `shuffle` is 416. -/
def stackRoom : Nat := 512

def selfA : BitVec 64 := 0x10000
def srcA : BitVec 64 := 0x20000
def tgtA : BitVec 64 := 0x30000
def spillsA : BitVec 64 := 0x40000
def wsA : BitVec 64 := 0x100000

/-- The entry PC and the first address after the code. -/
def entryPC : Int64 := Code.code.startAddr
def endPC : Int64 := entryPC + Int64.ofNat (Code.code.sizeBefore Code.code.program.length)

/-- The 8 bytes of `x`, least significant first. -/
def le64 (x : Nat) : List UInt8 := (List.range 8).map fun i => UInt8.ofNat (x >>> (8 * i))

def leWords (l : List Nat) : List UInt8 := l.flatMap le64

/-- The stack and the workspace; the same for each vector. -/
def baseMem : DataMem :=
  let m : DataMem := (∅ : DataMem).storeBytes (rsp0 - BitVec.ofNat 64 stackRoom) (List.replicate stackRoom 0xCD)
  m.storeBytes wsA (List.replicate workspaceSize 0)

/-- The padding of the flag word: not initialised by the caller; any value. -/
def flagsOf (allowed : Bool) : Nat := 0xDEADBEEFCAFE00 ||| (if allowed then 1 else 0)

/-- The words of the record before the call: offsets 0 to 63, and 4 words of junk for the outputs. -/
def recordIn (v : Vec) : List Nat :=
  [srcA.toNat, v.source.length, tgtA.toNat, v.target.length, spillsA.toNat, wsA.toNat, v.reach, flagsOf v.allowed,
    0xABABABABABABABAB, 0xABABABABABABABAB, 0xABABABABABABABAB, 0xABABABABABABABAB]

def memOf (v : Vec) : DataMem :=
  let m := baseMem.storeBytes rsp0 (le64 ra0.toNat)
  let m := m.storeBytes selfA (leWords (recordIn v))
  let m := m.storeBytes srcA (leWords v.source)
  let m := m.storeBytes tgtA (leWords v.target)
  m.storeBytes spillsA (v.spills.map UInt8.ofNat)

/-- The marks of the callee-saved registers `rbx rbp r12 r13 r14 r15`. -/
def marks : List UInt64 :=
  [0x1111111111111111, 0x2222222222222222, 0x3333333333333333, 0x4444444444444444,
   0x5555555555555555, 0x6666666666666666]

def calleeSaved (r : Reg64s) : List UInt64 := [r.rbx, r.rbp, r.r12, r.r13, r.r14, r.r15]

def startOf (v : Vec) : MachineState :=
  ⟨{ regs := { rax := 0xAAAAAAAAAAAAAAAA, rdi := UInt64.ofBitVec selfA, rsi := 0x5151515151515151,
               rdx := 0x5252525252525252, rcx := 0x5353535353535353, r8 := 0x5454545454545454,
               r9 := 0x5555555555555555, rsp := UInt64.ofBitVec rsp0, rbx := 0x1111111111111111,
               rbp := 0x2222222222222222, r12 := 0x3333333333333333, r13 := 0x4444444444444444,
               r14 := 0x5555555555555555, r15 := 0x6666666666666666 },
     dmem := memOf v }, entryPC⟩

/-! ### Run -/

/-- The index of the sites of `L1.table`: a constant, built once. -/
def idx : Std.HashMap Nat (MachineData → Effects) := index L1.table

/-- `L1.step` with the PC dispatch by the index (`stepWith_index`: the same effects for each state). -/
def step (s : MachineState) : Effects := stepWith idx s

/-- Execution inside the code; each read and write is allowed (an unmapped one is a fault). -/
def pol : CpuPolicy := ⟨fun
  | .execute a b => decide (entryPC ≤ a ∧ b ≤ endPC)
  | _ => true⟩

/-- At most `n` steps of `step` from `s`, to the PC `ra`; with the set of the PCs of the executed
instructions and the number of steps. -/
def drive (step : MachineState → Effects) (ra : Int64) :
    Nat → Nat → MachineState → Std.HashSet Nat → Stop × Std.HashSet Nat × Nat
  | 0, k, _, seen => (.fuel, seen, k)
  | n + 1, k, s, seen =>
    if s.pc == ra then (.ret s, seen, k)
    else
      let pc := s.pc
      match handle pol (step s) with
      | some t => drive step ra n (k + 1) t (seen.insert pc.toBitVec.toNat)
      | none => (.fault pc, seen, k)

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- The first byte where `got` and `want` differ. -/
def firstDiff (got want : List UInt8) : String :=
  match (got.zip want).zipIdx.find? (fun p => p.1.1 != p.1.2) with
  | some ((g, w), i) => s!"byte {i}: expected {w}, got {g}"
  | none => s!"length: expected {want.length}, got {got.length}"

/-- The bytes at `a` are `want`; else what differs. -/
def checkBytes (what : String) (m : DataMem) (a : BitVec 64) (want : List UInt8) : Option String :=
  match m.loadBytes a want.length with
  | none => some s!"{what} unreadable"
  | some bs => if bs == want then none else some s!"{what} at {hex a.toNat}: {firstDiff bs want}"

/-- The word at `a`. -/
def word (m : DataMem) (a : BitVec 64) : Option Nat :=
  (m.loadBytes a 8).map fun bs => bs.foldr (fun b acc => acc * 256 + b.toNat) 0

/-- The checks of the output of Done: the pointers are in the workspace, `trace_size`, the stack, the trace
and the sources. -/
def checkDone (v : Vec) (m : DataMem) : Option String :=
  match word m (selfA + 64), word m (selfA + 72), word m (selfA + 80), word m (selfA + 88) with
  | some st, some tr, some n, some so =>
    let inWs (p len : Nat) := wsA.toNat ≤ p && p + len ≤ wsA.toNat + workspaceSize
    let ops := v.trace
    if n != ops.length then some s!"trace_size: expected {ops.length}, got {n}"
    else if !inWs st (8 * v.stack.length) then some s!"stack pointer {hex st} outside the workspace"
    else if !inWs tr (12 * ops.length) then some s!"trace pointer {hex tr} outside the workspace"
    else if !inWs so (8 * v.sources.length) then some s!"sources pointer {hex so} outside the workspace"
    else
      (checkBytes "stack" m (BitVec.ofNat 64 st) (leWords v.stack)).orElse fun _ =>
      (checkBytes "sources" m (BitVec.ofNat 64 so) (leWords (v.sources.map fun s => s.getD (2 ^ 64 - 1)))).orElse
        fun _ =>
      (ops.zipIdx.findSome? fun ((k, d, w), i) =>
        let a := BitVec.ofNat 64 (tr + 12 * i)
        (checkBytes s!"op {i} kind and depth" m a [UInt8.ofNat k, UInt8.ofNat d]).orElse fun _ =>
          checkBytes s!"op {i} slot" m (a + 4) (le64 w))
  | _, _, _, _ => some "the output words of the record are unreadable"

/-- `none` if the run returned as the native run did; else what differs. -/
def check (v : Vec) (fuel : Nat) : Stop → Option String
  | .fault pc => some s!"fault at {hex pc.toBitVec.toNat}"
  | .fuel => some s!"no return in {fuel} steps"
  | .ret s =>
    let m := s.data.dmem
    if s.data.regs.rsp != UInt64.ofBitVec (rsp0 + 8) then
      some s!"rsp at the return: expected {hex (rsp0 + 8).toNat}, got {hex s.data.regs.rsp.toNat}"
    else if calleeSaved s.data.regs != marks then
      some s!"callee-saved registers (rbx rbp r12-r15): {(calleeSaved s.data.regs).map (hex ·.toNat)}"
    else if s.data.regs.rax.toNat % 2 ^ 32 != v.status then
      some s!"status in eax: expected {v.status}, got {hex (s.data.regs.rax.toNat % 2 ^ 32)}"
    else
      (checkBytes "spills" m spillsA (v.spillsAfter.map UInt8.ofNat)).orElse fun _ =>
      (checkBytes "record input" m selfA (leWords (recordIn v |>.take 8))).orElse fun _ =>
      (checkBytes "source" m srcA (leWords v.source)).orElse fun _ =>
      (checkBytes "target" m tgtA (leWords v.target)).orElse fun _ =>
        if v.status == 0 then checkDone v m else none

/-- Run `v` under `step`: the mismatch (if any), the PCs that the run executed and the steps. -/
def runVec (step : MachineState → Effects) (fuel : Nat) (v : Vec) : Option String × Std.HashSet Nat × Nat :=
  let (stop, seen, k) := drive step (Int64.ofBitVec ra0) fuel 0 (startOf v) {}
  (check v fuel stop, seen, k)

/-! ### Vectors -/

open Lean in
/-- The vectors of a file of `Lift/Shuffler/Test/data` (the first line is the header). -/
def loadFile (file : String) : IO (List Vec) := do
  let mut out := []
  for l in (← IO.FS.readFile s!"Lift/Shuffler/Test/data/{file}").splitOn "\n" do
    if l.isEmpty then continue
    let j ← IO.ofExcept (Json.parse l)
    if (j.getObjValAs? Bool "header").toOption == some true then continue
    out := (← IO.ofExcept (Vec.ofJson j)) :: out
  return out.reverse

def files : List String :=
  ["native-random.jsonl", "native-boundary.jsonl", "native-status2.jsonl", "native-big.jsonl"]

/-- The size of a vector: the larger of the source and the target. -/
def vsize (v : Vec) : Nat := max v.source.length v.target.length

/-- The sizes of the vectors that the report counts. -/
def sizeClasses : List (Nat × Nat) := [(0, 0), (1, 1), (2, 2), (3, 8), (9, 16), (17, 32), (33, 48), (49, 64), (65, 100000)]

/-! ### Report -/

/-- The address and text of each instruction of the code. -/
def sites : List (Nat × String) :=
  (Code.code.program.foldl (fun (acc : Nat × List (Nat × String)) sd =>
      match sd.directive with
      | .instr i => (acc.1 + sd.size, (acc.1, Kraken.X64.ATT.instr i) :: acc.2)
      | _ => (acc.1 + sd.size, acc.2)) (entryPC.toBitVec.toNat, [])).2.reverse

#guard sites.length == 2087

/-- The run of each vector of `vecs`, one line each; the coverage and the totals; an error if a vector differs. -/
def report (fuel : Nat) (vecs : List Vec) : IO Unit := do
  let mut seen : Std.HashSet Nat := {}
  let mut failed : List String := []
  let mut passed := 0
  let mut totalMs := 0
  let mut maxMs := 0
  let mut maxSteps := 0
  let mut statuses : List (Nat × Nat) := []
  for v in vecs do
    let t0 ← IO.monoMsNow
    let (msg, s, k) := runVec step fuel v
    let r := msg.isNone
    let t1 ← IO.monoMsNow
    let ms := t1 - t0
    totalMs := totalMs + ms
    maxMs := max maxMs ms
    maxSteps := max maxSteps k
    IO.println s!"{v.id}: size {vsize v}, status {v.status}, allowed {v.allowed}, {k} steps, {ms} ms: {msg.getD "ok"}"
    if r then
      passed := passed + 1
      seen := s.fold (·.insert ·) seen
      statuses := (v.status, 1) :: statuses
    else failed := v.id :: failed
  let run := sites.filter fun p => seen.contains p.1
  let mnemonics := (sites.map (Prod.snd · |>.splitOn " " |>.headD "")).eraseDups
  let ran := (run.map (Prod.snd · |>.splitOn " " |>.headD "")).eraseDups
  IO.println s!"total: {vecs.length} vectors, {passed} pass, {failed.length} fail; \
    status 0: {(vecs.filter (·.status == 0)).length}, 1: {(vecs.filter (·.status == 1)).length}, \
    2: {(vecs.filter (·.status == 2)).length}; spilling allowed: {(vecs.filter (·.allowed)).length}, \
    not allowed: {(vecs.filter (!·.allowed)).length}"
  IO.println s!"time: {totalMs} ms in all, at most {maxMs} ms for one vector, at most {maxSteps} steps"
  for (lo, hi) in sizeClasses do
    IO.println s!"size {lo}..{hi}: {(vecs.filter fun v => lo ≤ vsize v && vsize v ≤ hi).length} vectors"
  IO.println s!"coverage: {run.length} of {sites.length} instructions executed by at least one passing vector; \
    mnemonics {ran.length} of {mnemonics.length}"
  unless failed.isEmpty do
    throw (IO.userError s!"{failed.length} vectors differ from the native result: {failed}")

def fuel : Nat := 5000000

/-- The largest size that the test runs. The interpreter takes about 20 to 40 us for a step (SH-MEM: it was
about 0.9 ms). The steps grow with the size: 93,000 for size 32 (4 s), 1.4 to 2.3 million for size 48 (70 to 100 s),
3.9 million for a size 64 vector (97 s), and a size 1,024 vector does not return in 5 million steps (100 s). So
the build runs the sizes up to 32; the larger ones need a compiled executable. -/
def maxSize : Nat := 32

/-- The size classes of the selection (inclusive bounds). -/
def sizeClass (v : Vec) : Nat × Nat :=
  match sizeClasses.find? fun (lo, hi) => lo ≤ vsize v && vsize v ≤ hi with
  | some c => c
  | none => (0, 0)

/-- At most `k` vectors for each (size class, status, spilling allowed), the first ones of `vecs`. -/
def select (k : Nat) (vecs : List Vec) : List Vec :=
  let key (v : Vec) := (sizeClass v, v.status, v.allowed)
  let keys := (vecs.map key).eraseDups
  keys.flatMap fun c => ((vecs.filter (key · == c)).take k)

/-! ### The test detects a difference

Each change of the expected result of a vector must be reported: the status, a spill byte, a stack word, a
source offset, the kind of an operation, the slot word of an operation. A vector that has a record input larger
than its memory faults. -/

def mutations (v : Vec) : List (String × Vec) :=
  [("status", { v with status := (v.status + 1) % 3 }),
   ("spill byte", { v with spillsAfter := v.spillsAfter.mapIdx fun i b => if i == 0 then b ^^^ 1 else b }),
   ("stack word", { v with stack := v.stack.mapIdx fun i w => if i == 0 then w ^^^ 1 else w }),
   ("sources", { v with sources := v.sources.mapIdx fun i s => if i == 0 then some ((s.getD 0) ^^^ 1) else s }),
   ("op kind", { v with trace := v.trace.mapIdx fun i (k, d, w) => if i == 0 then (k ^^^ 1, d, w) else (k, d, w) }),
   ("op depth", { v with trace := v.trace.mapIdx fun i (k, d, w) => if i == 0 then (k, d ^^^ 1, w) else (k, d, w) }),
   ("op slot", { v with trace := v.trace.mapIdx fun i (k, d, w) => if i == 0 then (k, d, w ^^^ 1) else (k, d, w) })]

/-- The mutations that the check accepts although the vector has the part that the mutation changes. -/
def undetected (fuel : Nat) (v : Vec) : List String :=
  (mutations v).filterMap fun (name, w) =>
    let has := match name with
      | "spill byte" => !v.spillsAfter.isEmpty
      | "stack word" => !v.stack.isEmpty
      | "sources" => !v.sources.isEmpty
      | "status" => true
      | _ => !v.trace.isEmpty
    if has && (runVec step fuel w).1.isNone then some name else none

/-- A source pointer outside the mapped memory faults at the first read of the source. -/
def faults (fuel : Nat) (v : Vec) : Bool :=
  let (stop, _, _) := drive step (Int64.ofBitVec ra0) fuel 0
    { startOf v with data := { (startOf v).data with
        dmem := (startOf v).data.dmem.storeBytes selfA (leWords [0x900000]) } } {}
  match stop with | .fault _ => true | _ => false

#eval show IO Unit from do
  let vs := (← files.mapM loadFile).flatten
  let sel := select 2 (vs.filter (vsize · ≤ maxSize))
  report fuel sel
  unless sel.length ≥ 30 do throw (IO.userError "fewer than 30 vectors")
  -- the negative tests on one vector of each status
  for st in [0, 1, 2] do
    match sel.find? (·.status == st) with
    | none => throw (IO.userError s!"no vector of status {st}")
    | some v =>
      let bad := undetected fuel v
      IO.println s!"mutations of {v.id} (status {st}): undetected {bad}"
      unless bad.isEmpty do throw (IO.userError s!"{v.id}: the check accepts a changed result: {bad}")
  match sel.find? (fun v => v.status == 0 && !v.trace.isEmpty) with
  | none => throw (IO.userError "no Done vector with a trace")
  | some v =>
    let bad := undetected fuel v
    IO.println s!"mutations of {v.id} (Done, trace {v.trace.length}): undetected {bad}"
    unless bad.isEmpty do throw (IO.userError s!"{v.id}: the check accepts a changed result: {bad}")
    unless faults fuel v do throw (IO.userError "a read outside the memory does not fault")
    IO.println "a source pointer outside the memory: fault"

end Lift.Shuffler.Test.Run
