module

-- The reference semantics are taken from https://www.felixcloutier.com/x86/,
-- which itself is just extracted from https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html

import Kraken.Attribute
public import Kraken.Float32Fma
public import Kraken.Layout
public import Kraken.Mem
meta import Kraken.Mem
public import Kraken.X64.Syntax
meta import Kraken.X64.Syntax
public import Lean.ToExpr
meta import Lean.Elab.Deriving.ToExpr

@[expose] public section

-- injective coercions only
attribute [-instance] BitVec.instNatCast
attribute [-instance] BitVec.instIntCast
instance : Coe Bool Nat where coe := Bool.toNat

namespace BitVec
def unsigned {w} (x : BitVec w) : Int := x.toNat
def signed {w} (x : BitVec w) : Int := x.toInt
@[kstep] def take {w} (x : BitVec w) (n : Nat) : BitVec n := x.extractLsb' 0 n
@[kstep] def drop {w} (x : BitVec w) (n : Nat) : BitVec (w - n) := x.extractLsb' n (w-n)
end BitVec
attribute [kstep]
  BitVec.extractLsb'
  BitVec.ofInt_add
  BitVec.ofInt_toInt
  BitVec.signed
  BitVec.truncate
def BitVec.replaceLow {w n} (old : BitVec w) (new : BitVec n) : BitVec w :=
  (BitVec.append (old.drop n) new).setWidth _

namespace Reg
@[kstep] def base {w} (r : Reg w) : Reg64 := match r with
  | .low r _ => r
  | .ah => .rax | .bh => .rbx | .ch => .rcx | .dh => .rdx

@[kstep] def offset {w} (r : Reg w) : Nat := match r with
  | .low _ _ => 0
  | .ah | .bh | .ch | .dh => 8
end Reg

namespace AvxReg
def base {w} (r : AvxReg w) : RegMm := match r with
  | .xmm r => r
  | .ymm r => r
  | .zmm r => r
end AvxReg

structure Reg64s where
  rax : UInt64 := 0
  rbx : UInt64 := 0
  rcx : UInt64 := 0
  rdx : UInt64 := 0
  rsi : UInt64 := 0
  rdi : UInt64 := 0
  rsp : UInt64 := 0
  rbp : UInt64 := 0
  r8  : UInt64 := 0
  r9  : UInt64 := 0
  r10 : UInt64 := 0
  r11 : UInt64 := 0
  r12 : UInt64 := 0
  r13 : UInt64 := 0
  r14 : UInt64 := 0
  r15 : UInt64 := 0
  deriving Repr, BEq, DecidableEq, Hashable, Hashable, Lean.ToExpr

/-- The register file's own width is the literal 64: stating it as `BitVec 64`
makes every consumer store the literal as the width index, the one spelling
`grind`'s congruence and `bv_decide` read syntactically. `Width.W64.type` is
definitionally the same type; an index spelled through it depends on which
reduction path the elaborator took (`Width.W64.bits`, a stranded `bits` match,
or `64`), and syntactically distinct spellings of one index split atoms. -/
@[kstep] def Reg64s.get64 (s : Reg64s) (r : Reg64) : BitVec 64 := UInt64.toBitVec (match r with
  | .rax => s.rax | .rbx => s.rbx | .rcx => s.rcx | .rdx => s.rdx
  | .rsi => s.rsi | .rdi => s.rdi | .rsp => s.rsp | .rbp => s.rbp
  | .r8  => s.r8  | .r9  => s.r9  | .r10 => s.r10 | .r11 => s.r11
  | .r12 => s.r12 | .r13 => s.r13 | .r14 => s.r14 | .r15 => s.r15)

@[kstep] def Reg64s.set64 (regs : Reg64s) (r : Reg64) (v : BitVec 64) : Reg64s :=
  let  v := UInt64.ofBitVec v
  match r with
  | .rax => { regs with rax := v } | .rbx => { regs with rbx := v }
  | .rcx => { regs with rcx := v } | .rdx => { regs with rdx := v }
  | .rsi => { regs with rsi := v } | .rdi => { regs with rdi := v }
  | .rsp => { regs with rsp := v } | .rbp => { regs with rbp := v }
  | .r8  => { regs with r8  := v } | .r9  => { regs with r9  := v }
  | .r10 => { regs with r10 := v } | .r11 => { regs with r11 := v }
  | .r12 => { regs with r12 := v } | .r13 => { regs with r13 := v }
  | .r14 => { regs with r14 := v } | .r15 => { regs with r15 := v }

@[kstep] def Reg64s.get (s : Reg64s) {w} (r : Reg w) : w.type :=
  ((s.get64 r.base).drop r.offset).take w.bits
  -- BitVec because it may be signed or unsigned depending on context

@[kstep] def Reg64s.set (s : Reg64s) {w} (r : Reg w) (v : w.type) : Reg64s := match r with
  | .low r .W64 => s.set64 r v
  | .low r .W32 => s.set64 r (v.zeroExtend _)
  | .low r w => s.set64 r ((s.get64 r).replaceLow v)
  | .ah | .bh | .ch | .dh => let old := s.get64 r.base;
    s.set64 r.base (old.replaceLow (BitVec.append v (s.get (.low r.base .W8))))

def ZmmValue : Type := BitVec 512
  deriving Repr, BEq, DecidableEq, Hashable, Hashable, Lean.ToExpr

def zmmZero : ZmmValue := 0#512

structure RegZmms where
  zmm0  : ZmmValue := zmmZero
  zmm1  : ZmmValue := zmmZero
  zmm2  : ZmmValue := zmmZero
  zmm3  : ZmmValue := zmmZero
  zmm4  : ZmmValue := zmmZero
  zmm5  : ZmmValue := zmmZero
  zmm6  : ZmmValue := zmmZero
  zmm7  : ZmmValue := zmmZero
  zmm8  : ZmmValue := zmmZero
  zmm9  : ZmmValue := zmmZero
  zmm10 : ZmmValue := zmmZero
  zmm11 : ZmmValue := zmmZero
  zmm12 : ZmmValue := zmmZero
  zmm13 : ZmmValue := zmmZero
  zmm14 : ZmmValue := zmmZero
  zmm15 : ZmmValue := zmmZero
  zmm16 : ZmmValue := zmmZero
  zmm17 : ZmmValue := zmmZero
  zmm18 : ZmmValue := zmmZero
  zmm19 : ZmmValue := zmmZero
  zmm20 : ZmmValue := zmmZero
  zmm21 : ZmmValue := zmmZero
  zmm22 : ZmmValue := zmmZero
  zmm23 : ZmmValue := zmmZero
  zmm24 : ZmmValue := zmmZero
  zmm25 : ZmmValue := zmmZero
  zmm26 : ZmmValue := zmmZero
  zmm27 : ZmmValue := zmmZero
  zmm28 : ZmmValue := zmmZero
  zmm29 : ZmmValue := zmmZero
  zmm30 : ZmmValue := zmmZero
  zmm31 : ZmmValue := zmmZero
  deriving Repr, BEq, DecidableEq, Hashable, Hashable, Lean.ToExpr

def RegZmms.get512 (s : RegZmms) (r : RegMm) : AvxWidth.W512.type := (match r with
  | .mm0  => s.zmm0  | .mm1  => s.zmm1  | .mm2  => s.zmm2  | .mm3  => s.zmm3
  | .mm4  => s.zmm4  | .mm5  => s.zmm5  | .mm6  => s.zmm6  | .mm7  => s.zmm7
  | .mm8  => s.zmm8  | .mm9  => s.zmm9  | .mm10 => s.zmm10 | .mm11 => s.zmm11
  | .mm12 => s.zmm12 | .mm13 => s.zmm13 | .mm14 => s.zmm14 | .mm15 => s.zmm15
  | .mm16 => s.zmm16 | .mm17 => s.zmm17 | .mm18 => s.zmm18 | .mm19 => s.zmm19
  | .mm20 => s.zmm20 | .mm21 => s.zmm21 | .mm22 => s.zmm22 | .mm23 => s.zmm23
  | .mm24 => s.zmm24 | .mm25 => s.zmm25 | .mm26 => s.zmm26 | .mm27 => s.zmm27
  | .mm28 => s.zmm28 | .mm29 => s.zmm29 | .mm30 => s.zmm30 | .mm31 => s.zmm31)

def RegZmms.set512 (regs : RegZmms) (r : RegMm) (v : AvxWidth.W512.type) : RegZmms :=
  match r with
  | .mm0  => { regs with zmm0  := v } | .mm1  => { regs with zmm1  := v }
  | .mm2  => { regs with zmm2  := v } | .mm3  => { regs with zmm3  := v }
  | .mm4  => { regs with zmm4  := v } | .mm5  => { regs with zmm5  := v }
  | .mm6  => { regs with zmm6  := v } | .mm7  => { regs with zmm7  := v }
  | .mm8  => { regs with zmm8  := v } | .mm9  => { regs with zmm9  := v }
  | .mm10 => { regs with zmm10 := v } | .mm11 => { regs with zmm11 := v }
  | .mm12 => { regs with zmm12 := v } | .mm13 => { regs with zmm13 := v }
  | .mm14 => { regs with zmm14 := v } | .mm15 => { regs with zmm15 := v }
  | .mm16 => { regs with zmm16 := v } | .mm17 => { regs with zmm17 := v }
  | .mm18 => { regs with zmm18 := v } | .mm19 => { regs with zmm19 := v }
  | .mm20 => { regs with zmm20 := v } | .mm21 => { regs with zmm21 := v }
  | .mm22 => { regs with zmm22 := v } | .mm23 => { regs with zmm23 := v }
  | .mm24 => { regs with zmm24 := v } | .mm25 => { regs with zmm25 := v }
  | .mm26 => { regs with zmm26 := v } | .mm27 => { regs with zmm27 := v }
  | .mm28 => { regs with zmm28 := v } | .mm29 => { regs with zmm29 := v }
  | .mm30 => { regs with zmm30 := v } | .mm31 => { regs with zmm31 := v }

def RegZmms.get (s : RegZmms) {w} (r : AvxReg w) : w.type :=
  (s.get512 r.base).take w.bits

def RegZmms.set (s : RegZmms) {w} (r : AvxReg w) (v : w.type) : RegZmms := match r with
  | .zmm r => s.set512 r v
  | .ymm r => s.set512 r (v.zeroExtend _)
  | .xmm r => s.set512 r (v.zeroExtend _)

def RegZmms.setLegacy (s : RegZmms) {w} (r : AvxReg w) (v : w.type) : RegZmms := match r with
  | .zmm r => s.set512 r v  -- impossible
  | .ymm r => s.set512 r ((s.get512 r).replaceLow v)  -- impossible
  | .xmm r => s.set512 r ((s.get512 r).replaceLow v)

def RegZmms.zeroUpper (s : RegZmms) : RegZmms :=
  let z (v : ZmmValue) : ZmmValue := (BitVec.setWidth 128 v).setWidth 512
  { s with
    zmm0 := z s.zmm0, zmm1 := z s.zmm1, zmm2 := z s.zmm2, zmm3 := z s.zmm3,
    zmm4 := z s.zmm4, zmm5 := z s.zmm5, zmm6 := z s.zmm6, zmm7 := z s.zmm7,
    zmm8 := z s.zmm8, zmm9 := z s.zmm9, zmm10 := z s.zmm10, zmm11 := z s.zmm11,
    zmm12 := z s.zmm12, zmm13 := z s.zmm13, zmm14 := z s.zmm14, zmm15 := z s.zmm15 }

@[kstep]
def BitVec.toAddressSize [address_size: AddressSize] (w: BitVec 64): BitVec address_size.address_size.bits :=
  w.take address_size.address_size.bits

-- TODO: consider adding a `split` helper to switch representations between
-- u128, 4xu32, etc.
def BitVec.packedBinOp {w : Nat} (c : Nat) (op : BitVec c → BitVec c → BitVec c) (a b : BitVec w) : BitVec w :=
  if _ : c = 0 ∨ w < c then
    a -- Fallback/Base case (w = 0 or invalid chunk size)
  else
    -- Extract the lowest chunk
    let a_low := a.take c
    let b_low := b.take c
    let res_low := op a_low b_low

    -- Recursively process the remaining high bits
    let a_high := a.drop c
    let b_high := b.drop c
    let res_high := BitVec.packedBinOp c op a_high b_high

    -- Recombine: res_high is the high part, res_low is the low part
    (BitVec.append res_high res_low).setWidth _
termination_by w
decreasing_by omega

def BitVec.toFloat32 (v : BitVec 32) : Float32 :=
  Float32.ofBits (UInt32.ofBitVec v)

def Float32.toBitVec (f : Float32) : BitVec 32 :=
  UInt32.toBitVec (Float32.toBits f)

/-- An SSE single-precision operation on one lane: a NaN operand propagates (quieted, the first
operand winning), and an invalid operation gives the default NaN ("QNaN floating-point
indefinite"). In binary32, `0x400000` is bit 22, the most significant fraction bit, which makes a
NaN quiet; `0xffc00000` (sign set, exponent all ones, fraction `100…0`) is the default NaN.
Lean's `Float32` can't express this: its logical model has a single NaN (all NaNs are equal), so
every NaN result reads back as `0x7fc00000`. -/
def sseBinOp (op : Float32 → Float32 → Float32) (a b : BitVec 32) : BitVec 32 :=
  if a.toFloat32.isNaN then a ||| 0x400000#32
  else if b.toFloat32.isNaN then b ||| 0x400000#32
  else let r := op a.toFloat32 b.toFloat32; if r.isNaN then 0xffc00000#32 else r.toBitVec

def sseTernOp (op : Float32 → Float32 → Float32 → Float32) (a b c : BitVec 32) : BitVec 32 :=
  if a.toFloat32.isNaN then a ||| 0x400000#32
  else if b.toFloat32.isNaN then b ||| 0x400000#32
  else if c.toFloat32.isNaN then c ||| 0x400000#32
  else let r := op a.toFloat32 b.toFloat32 c.toFloat32
    if r.isNaN then 0xffc00000#32 else r.toBitVec

def BitVec.packedTernOp {w : Nat} (c : Nat) (op : BitVec c → BitVec c → BitVec c → BitVec c)
    (a b d : BitVec w) : BitVec w :=
  if _ : c = 0 ∨ w < c then
    a
  else
    let res_low := op (a.take c) (b.take c) (d.take c)
    let res_high := BitVec.packedTernOp c op (a.drop c) (b.drop c) (d.drop c)
    (BitVec.append res_high res_low).setWidth _
termination_by w
decreasing_by omega

def BitVec.shufps128 (imm : UInt8) (a b : BitVec 128) : BitVec 128 :=
  let pick (x : BitVec 128) (k : Nat) : BitVec 32 :=
    x.extractLsb' (32 * ((imm.toNat >>> k) % 4)) 32
  pick b 6 ++ pick b 4 ++ pick a 2 ++ pick a 0

structure StatusFlags where
  cf : Bool
  pf : Bool
  af : Bool
  zf : Bool
  sf : Bool
  of : Bool
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

abbrev DataMem := Mem 64
instance : Repr DataMem where reprPrec _ _ := "<opaque memory>"

@[grind =, vcgen_simp] theorem Mem.loadInt_storeInt_8 (m : DataMem) (a : BitVec 64) (v : Int) :
    (m.storeInt a 1 v).loadInt a 1 = some (Int.ofBytes (Int.toBytes 1 v)) :=
  Mem.loadInt_storeInt m a 1 v (by decide)

@[vcgen_simp] theorem BitVec.ofInt_ofBytes_toBytes_8 (v : Int) :
    BitVec.ofInt 8 (Int.ofBytes (Int.toBytes 1 v)) = BitVec.ofInt 8 v :=
  BitVec.ofInt_ofBytes_toBytes 8 1 rfl v

@[grind =, vcgen_simp] theorem Mem.loadInt_storeInt_16 (m : DataMem) (a : BitVec 64) (v : Int) :
    (m.storeInt a 2 v).loadInt a 2 = some (Int.ofBytes (Int.toBytes 2 v)) :=
  Mem.loadInt_storeInt m a 2 v (by decide)

@[vcgen_simp] theorem BitVec.ofInt_ofBytes_toBytes_16 (v : Int) :
    BitVec.ofInt 16 (Int.ofBytes (Int.toBytes 2 v)) = BitVec.ofInt 16 v :=
  BitVec.ofInt_ofBytes_toBytes 16 2 rfl v

@[grind =, vcgen_simp] theorem Mem.loadInt_storeInt_32 (m : DataMem) (a : BitVec 64) (v : Int) :
    (m.storeInt a 4 v).loadInt a 4 = some (Int.ofBytes (Int.toBytes 4 v)) :=
  Mem.loadInt_storeInt m a 4 v (by decide)

@[vcgen_simp] theorem BitVec.ofInt_ofBytes_toBytes_32 (v : Int) :
    BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 v)) = BitVec.ofInt 32 v :=
  BitVec.ofInt_ofBytes_toBytes 32 4 rfl v

@[grind =, vcgen_simp] theorem Mem.loadInt_storeInt_64 (m : DataMem) (a : BitVec 64) (v : Int) :
    (m.storeInt a 8 v).loadInt a 8 = some (Int.ofBytes (Int.toBytes 8 v)) :=
  Mem.loadInt_storeInt m a 8 v (by decide)

@[vcgen_simp] theorem BitVec.ofInt_ofBytes_toBytes_64 (v : Int) :
    BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 v)) = BitVec.ofInt 64 v :=
  BitVec.ofInt_ofBytes_toBytes 64 8 rfl v

grind_pattern BitVec.ofInt_ofBytes_toBytes_8 => Option.get! (some (Int.ofBytes (Int.toBytes 1 v)))
grind_pattern BitVec.ofInt_ofBytes_toBytes_16 => Option.get! (some (Int.ofBytes (Int.toBytes 2 v)))
grind_pattern BitVec.ofInt_ofBytes_toBytes_32 => Option.get! (some (Int.ofBytes (Int.toBytes 4 v)))
grind_pattern BitVec.ofInt_ofBytes_toBytes_64 => Option.get! (some (Int.ofBytes (Int.toBytes 8 v)))

structure MachineData where -- does not include code or program position
  regs : Reg64s := {}
  zmms : RegZmms := {}
  status : StatusFlags := .mk false false false false false false
  dmem : DataMem := ∅
  deriving Repr, BEq, DecidableEq

-- We only allow nondeterministic choices for a fixed set of types.
class inductive NondetSupportingType : Type -> Type
  | bitvec (w : Width) : NondetSupportingType w.type
  | avx_bitvec (aw : AvxWidth) : NondetSupportingType aw.type
  | bool : NondetSupportingType Bool
  | statusFlags : NondetSupportingType StatusFlags

def NondetSupportingType.from_hash {α} [t : NondetSupportingType α] (h : UInt64) : α :=
  match t with
  | .bool => h % 2 != 0
  | .statusFlags => let h := h.toBitVec; (.mk h[0] h[1] h[2] h[3] h[4] h[5])
  | .bitvec w => h.toBitVec.setWidth w.bits
  | .avx_bitvec w => h.toBitVec.setWidth w.bits

instance (w : Width) : NondetSupportingType w.type := .bitvec w
instance (w : AvxWidth) : NondetSupportingType w.type := .avx_bitvec w
instance : NondetSupportingType Bool := .bool
instance : NondetSupportingType StatusFlags := .statusFlags

structure MachineState where
  data : MachineData
  pc : Int64

/-- A processor exception that an instruction raises. -/
inductive Fault
  | invalidOpcode  -- #UD
  | divideError    -- #DE
  deriving Repr, BEq, DecidableEq

instance : ToString Fault where
  toString | .invalidOpcode => "#UD" | .divideError => "#DE"

inductive Effects
  | done (a : MachineState)
  | unimplemented (msg : String)
  | gp_unaligned (addr : BitVec 64) (w : Nat)
  | fault (f : Fault)
  -- loads and stores *outside* the data memory, eg. MMIO, might still affect the data memory:
  -- for instance, MMIO reads/writes at certain device register addresses might change what
  -- data memory the process logically owns vs what memory is owned by devices
  | nonmem_load (dmem : DataMem) (addr : BitVec 64) (w : Width) (ret : w.type → DataMem → Effects)
  | nonmem_store (dmem : DataMem) (addr : BitVec 64) {w : Width} (v : w.type) (ret: DataMem → Effects)
  | undefined {α : Type} [NondetSupportingType α] (ret : α → Effects)
  | require_read_access (addr : BitVec 64) (w : Width) (ok : Unit → Effects)
  | require_write_access (addr : BitVec 64) (w : Width) (ok : Unit → Effects)
  | require_exec_access (p: Std.Rco Int64) (ok : Unit → Effects)
export Effects (unimplemented nonmem_load nonmem_store undefined require_read_access require_write_access require_exec_access)

-- the unused `Std.Rco Int64` argument and the unmodified `MachineData` return
-- value are present for uniformity with RegOrMem.interp
@[kstep] def Reg.interp {w} (r : Reg w) (s : MachineData) (_ : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) : Effects :=
  ret (s.regs.get r) s

-- Since MMIO can cause devices to do arbitrary actions, a load might actually
-- *modify* memory. For instance:
-- A TEST instruction might load a flag from an MMIO address and bitwise-and it with
-- an immediate, and if the result is non-zero, it might mean that some device has
-- finished processing a buffer and therefore now passes ownership of that buffer
-- to the CPU.
-- Note that `ret` takes a whole `MachineData` instead of only `DataMem`, which
-- provides a bit more flexibility than we need: MachineData.load might change
-- dmem, but will not change the registers or status flags.
-- But this superfluous flexibility helps us simplify the state-threading:
-- Instead of writing `fun v dmem => ... { s with dmem } ...` everywhere, we
-- can just write `fun v s => ...` and the new `s` will shadow the old `s`.
def MachineData.load
  (s : MachineData) (addr : BitVec 64) (w : Width)
  (ret : w.type → MachineData → Effects): Effects :=
  require_read_access addr w (fun _unit =>
    match Mem.loadInt s.dmem addr w.bytes with
    | .some i => ret (.ofInt _ i) s
    | .none => nonmem_load s.dmem addr w (fun v dmem => ret v { s with dmem }))

-- Alternatively, we could define this in terms of BitVecs without %:
-- (addr &&& BitVec.ofNat 64 (bytes - 1)) == 0#64
def isAligned (bytes : Nat) (addr : BitVec 64) : Bool :=
  addr.toNat % bytes == 0

-- Legacy SSE instructions are generally stricter about alignment requirements,
-- while AVX (VEX-encoded) instructions can mostly deal with unaligned
-- addresses (https://discourse.llvm.org/t/memory-alignment-model-on-avx-avx2-and-avx-512-targets/34705).
-- For this reason we default checkAlign to false.
def MachineData.loadAvx
  (s : MachineData) (addr : BitVec 64) (w : AvxWidth)
  (ret : w.type → MachineData → Effects) (checkAlign : Bool := false) : Effects :=
  if checkAlign && !(isAligned w.bytes addr) then
    .gp_unaligned addr w.bytes
  else
    require_read_access addr .W64 (fun _unit =>
  match Mem.loadInt s.dmem addr w.bytes with
      | .some i => ret (.ofInt _ i) s
      | .none => unimplemented "AVX nonmem load not supported")

def MachineData.store (s : MachineData) (addr : BitVec 64) {w : Width} (v : w.type) (ret: MachineData → Effects) : Effects :=
  require_write_access addr w (fun _unit =>
    match Mem.loadInt s.dmem addr w.bytes with
    | .some _ =>
        ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }
    | .none => nonmem_store s.dmem addr v (fun dmem' => ret { s with dmem := dmem' }))

def MachineData.storeAvx (s : MachineData) (addr : BitVec 64) {w : AvxWidth} (v : w.type) (ret: MachineData → Effects) (checkAlign : Bool := false) : Effects :=
  if checkAlign && !(isAligned w.bytes addr) then
    .gp_unaligned addr w.bytes
  else
    require_write_access addr .W64 (fun _unit =>
  match Mem.loadInt s.dmem addr w.bytes with
      | .some _ =>
          ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }
      | .none => unimplemented "AVX nonmem store not supported")

class Labels where label : Label → Int64
export Labels (label)

@[kstep] def ConstExpr.interp [Labels] : ConstExpr → Std.Rco _root_.Int64 → _root_.Int64
  | .label l, _ => Labels.label l
  | .int64 i, _ => i
  | .before_current_instruction, r => r.lower
  | .after_current_instruction, r => r.upper
  | .add e1 e2, p => e1.interp p + e2.interp p
  | .sub e1 e2, p => e1.interp p - e2.interp p

@[kstep] def AddrExpr.interp [Labels] [address_size : AddressSize] (a : AddrExpr) (s : Reg64s) (p : Std.Rco Int64) :=
  let base := match a.base with
              | .some (.reg r) => (s.get64 r).toAddressSize.signed
              | .some .rip => p.upper.toInt
              | .none => 0
  let idx := match a.idx with
             | .some ⟨r, c⟩ => (s.get64 r).toAddressSize.signed * c.bytes
             | .none => 0
  BitVec.ofInt address_size.address_size.bits (base + idx + (a.disp.interp p).toInt)

@[kstep] def RegOrMem.interp {w} [Labels] [AddressSize]
  (o : RegOrMem w) (s : MachineData) (p : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) :=
match o with
  | .reg r => ret (s.regs.get r) s
  | .mem a => s.load ((a.interp s.regs p).zeroExtend _) w ret

def AvxRegOrMem.interp {w} [Labels] [AddressSize]
  (o : AvxRegOrMem w) (s : MachineData) (p : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) (checkAlign : Bool := false) :=
match o with
  | .avx r => ret (s.zmms.get r) s
  | .mem a => s.loadAvx ((a.interp s.regs p).zeroExtend _) w ret checkAlign

/-- The scalar single operand: the low 32 bits of an xmm register, or a 32-bit load. -/
def AvxRegOrMem.interpLow32 [Labels] [AddressSize]
  (o : AvxRegOrMem .W128) (s : MachineData) (p : Std.Rco Int64)
  (ret : BitVec 32 → MachineData → Effects) : Effects :=
match o with
  | .avx r => ret ((s.zmms.get r).setWidth 32) s
  | .mem a => s.load ((a.interp s.regs p).zeroExtend _) .W32 ret

/-- The scalar double operand: the low 64 bits of an xmm register, or a 64-bit load. -/
def AvxRegOrMem.interpLow64 [Labels] [AddressSize]
  (o : AvxRegOrMem .W128) (s : MachineData) (p : Std.Rco Int64)
  (ret : BitVec 64 → MachineData → Effects) : Effects :=
match o with
  | .avx r => ret ((s.zmms.get r).setWidth 64) s
  | .mem a => s.load ((a.interp s.regs p).zeroExtend _) .W64 ret

@[kstep]
def MachineData.setReg (s : MachineData) {w} (r : Reg w) (v : w.type) : MachineData :=
  { s with regs := s.regs.set r v }

def MachineData.setAvxReg (s : MachineData) {w : AvxWidth} (r : AvxReg w) (v : w.type) : MachineData :=
  { s with zmms := s.zmms.set r v }

def MachineData.setAvxLegacyReg (s : MachineData) {w : AvxWidth} (r : AvxReg w) (v : w.type) : MachineData :=
  { s with zmms := s.zmms.setLegacy r v }

@[kstep]
def MachineData.set {w} [Labels] [AddressSize] (s : MachineData) (d : Dst w) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects) : Effects :=
  match d with
  | .reg r => ret (s.setReg r v)
  | .mem a => s.store ((a.interp s.regs p).zeroExtend _) v ret

def MachineData.setAvx {aw} [Labels] [AddressSize] (s : MachineData) (d : AvxDst aw) (v : aw.type) (p : Std.Rco Int64) (ret : MachineData → Effects) (checkAlign : Bool := false) : Effects :=
match d with
  | .avx r => ret (s.setAvxReg r v)
  | .mem a => s.storeAvx ((a.interp s.regs p).zeroExtend _) v ret checkAlign

def MachineData.setAvxLegacy {w} [Labels] [AddressSize] (s : MachineData) (d : AvxDst w) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects) (checkAlign : Bool := false) : Effects :=
match d with
  | .avx r => ret (s.setAvxLegacyReg r v)
  | .mem a => s.storeAvx ((a.interp s.regs p).zeroExtend _) v ret checkAlign

@[kstep] def Operand.interp {w} [Labels] [AddressSize]
  (o : Operand w) (s : MachineData) (p : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) :=
  match o with
  | regOrMem rm => rm.interp s p ret
  | .imm v => ret ((v.interp p).toBitVec.truncate _) s
  -- we rely on assemblers erroring out on too-large immediates in uniform ops

def AvxOperand.interp {aw} [Labels] [AddressSize]
  (o : AvxOperand aw) (s : MachineData) (p : Std.Rco Int64)
  (ret : aw.type → MachineData → Effects) (checkAlign : Bool := false) :=
match o with
  | regOrMem rm => rm.interp s p ret checkAlign

@[kstep]
def CondCode.interp (cc : CondCode) (s : StatusFlags) : Bool := match cc with
  | .o  => s.of | .no => !s.of
  | .c  => s.cf | .nc => !s.cf
  | .z  => s.zf | .nz => !s.zf
  | .be => s.cf || s.zf | .a  => !s.cf && !s.zf
  | .s  => s.sf | .ns => !s.sf
  | .p  => s.pf | .np => !s.pf
  | .l  => s.sf != s.of | .ge => s.sf == s.of
  | .le => (s.sf != s.of) || s.zf | .g  => !s.zf && (s.sf == s.of)

@[kstep] def ShiftCountExpr.interp [Labels] (c : ShiftCountExpr) (s : MachineData) (p : Std.Rco Int64) := match c with
  | .cl => s.regs.rcx.toBitVec.take 8
  | .imm8 v => (v.interp p).toBitVec.take _
@[kstep] def ShiftCountExpr.interpMasked [Labels] (c : ShiftCountExpr) (s : MachineData) (p : Std.Rco Int64) (w : Width) : Nat :=
  (c.interp s p).toNat &&& match w with | .W64 => 0x3f | _ => 0x1f -- "masked to 5 bits (or 6 bits with a 64-bit operand)"

def RelRegOrMem.interp [Labels] [AddressSize]
  (o : RelRegOrMem) (s : MachineData) (p : Std.Rco Int64)
  (ret : BitVec 64 → MachineData → Effects) :=
  match o with
  | .rel c => ret (p.upper + c.interp p).toBitVec s
  | .reg r => ret (s.regs.get r) s
  | .mem a => s.load ((a.interp s.regs p).zeroExtend _) .W64 ret

structure StatusFlags.from_result.Remaining where
  cf : Bool
  af : Bool
  of : Bool
  deriving Repr, BEq, DecidableEq

-- TEMPORARY: definitions stolen from Lean 4.28's standard library, but with a
-- different name so that this file builds with both 4.27 and 4.28
namespace BitVec
def cpopNatRec_ {w} (x : BitVec w) (pos acc : Nat) : Nat :=
  match pos with
  | 0 => acc
  | n + 1 => x.cpopNatRec_ n (acc + (x.getLsbD n).toNat)

def cpop_ {w} (x : BitVec w) : BitVec w := BitVec.ofNat w (cpopNatRec_ x w 0)
end BitVec

/-- The index of the highest set bit of `v`, or 0 if there is none. -/
def BitVec.highestSetBit {w} (v : BitVec w) : Nat :=
  (List.range w).foldl (fun a i => if v.getLsbD i then i else a) 0

def RegOrMem.isMem {w} : RegOrMem w → Bool
  | .mem _ => true
  | .reg _ => false

/-- `btc` with a register bit offset and a memory destination addresses a bit string that
extends past the destination. -/
def btcBitString {w} : Dst w → Operand w → Bool
  | .mem _, .regOrMem _ => true
  | _, _ => false

/-- The index of the lowest set bit of `v`, or 0 if there is none. -/
def BitVec.lowestSetBit {w} (v : BitVec w) : Nat :=
  (List.range w).foldr (fun i a => if v.getLsbD i then i else a) 0

@[kstep] def StatusFlags.from_result {w} (result : BitVec w) (f : from_result.Remaining) : StatusFlags :=
  { pf := (result.take 8).cpop_ % 2 == BitVec.zero _
    zf := result == BitVec.zero _
    sf := result.msb, cf := f.cf, af := f.af, of := f.of }



set_option maxHeartbeats 1000000
@[kstep] def Operation.interp [Labels] [address_size : AddressSize]
  {w} (i : Operation w) (p : Std.Rco Int64) (s : MachineData)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  match (generalizing := false) (motive := Operation w → Effects) i with
  | .mov dst src => src.interp s p (fun val s => s.set dst val p next)
  | .movsx dst src => src.interp s p (fun val s => s.set dst (val.signExtend _) p next)
  | .movzx dst src => src.interp s p (fun val s => s.set dst (val.zeroExtend _) p next)
  | .push src =>
    src.interp s p (fun v s =>
    let rsp := s.regs.get64 .rsp - w.bytesv
    -- The store precedes the rsp commit, so a faulting push leaves rsp at its
    -- original value, as a restartable fault requires.
    s.store rsp v (fun s => next { s with regs := s.regs.set64 .rsp rsp }))
  | .pop dst =>
    let rsp := s.regs.get64 .rsp
    s.load rsp w (fun val s =>
    let s := { s with regs := s.regs.set64 .rsp (rsp + w.bytesv) }
    s.set dst val p next)
  | .setcc cc dst =>
    s.set dst (cc.interp s.status) p next
  | .cmovcc cc dst src =>
    src.interp s p (fun src s =>
    let v := if cc.interp s.status then src else s.regs.get dst
    next (s.setReg dst v))
-- Arithmetic
  | .lea dst src => next (s.setReg dst ((src.interp s.regs p).zeroExtend _))
  | .add dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let v := a + b
    let status := .from_result v {
      cf := v.unsigned != a.unsigned + b.unsigned
      af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
      of := v.signed != a.signed + b.signed }
    { s with status }.set dst v p next))
  | .adc dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let c := s.status.cf
    let v := a + b + c
    let status := .from_result v {
      cf := v.unsigned != a.unsigned + b.unsigned + c
      af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned + c,
      of := v.signed != a.signed + b.signed + c }
    { s with status }.set dst v p next))
  | .adcx dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let v := a + b + s.status.cf
    let cf := v.unsigned != a.unsigned + b.unsigned + s.status.cf
    next { s with regs := s.regs.set dst v, status := { s.status with cf := cf }}))
  | .adox dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let v := a + b + s.status.of
    let of := v.unsigned != a.unsigned + b.unsigned + s.status.of
    next { s with regs := s.regs.set dst v, status := { s.status with of := of }}))
  | .inc dst =>
    dst.interp s p (fun a s =>
    let v := a + 1
    let status := .from_result v {
      cf := s.status.cf
      af := (v.take 4).unsigned != (a.take 4).unsigned + 1,
      of := v.signed != a.signed + 1 }
    { s with status }.set dst v p next)
  | .dec dst =>
    dst.interp s p (fun a s =>
    let v := a - 1
    let status := .from_result v {
      cf := s.status.cf
      af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
      of := v.signed != a.signed - 1 }
    { s with status }.set dst v p next)
  | .neg dst =>
    dst.interp s p (fun b s =>
    let v := -b
    let status := .from_result v {
      cf := b != 0
      af := (b.take 4) != 0,
      of := v.signed != - b.signed }
    { s with status }.set dst v p next)
  | .sub dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let v := b - a
    let status := .from_result v {
      cf := v.unsigned != b.unsigned - a.unsigned
      af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
      of := v.signed != b.signed - a.signed }
    { s with status }.set dst v p next))
  | .sbb dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let c := s.status.cf
    let v := b - a - c
    let status := .from_result v {
      cf := v.unsigned != b.unsigned - a.unsigned - c
      af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - c,
      of := v.signed != b.signed - a.signed - c }
    { s with status }.set dst v p next))
  | .cmp a b =>
    a.interp s p (fun a s =>
    b.interp s p (fun b s =>
    let v := a - b
    let status := .from_result v {
      cf := v.unsigned != a.unsigned - b.unsigned
      af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
      of := v.signed != a.signed - b.signed }
    next { s with status }))
  -- lock is valid only with a memory destination.
  | .xadd lock dst src =>
    if lock && !dst.isMem then .fault .invalidOpcode else
    dst.interp s p (fun a s =>
    let b := s.regs.get src
    let v := a + b
    let status : StatusFlags := .from_result v {
      cf := v.unsigned != a.unsigned + b.unsigned
      af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
      of := v.signed != a.signed + b.signed }
    -- src gets the old destination, then the destination the sum: with one register as both,
    -- the sum stays.
    { s with status }.set dst v p (fun s => next (if dst = RegOrMem.reg src then s else s.setReg src a)))
  | .cmpxchg lock dst src =>
    if lock && !dst.isMem then .fault .invalidOpcode else
    dst.interp s p (fun d s =>
    let a := s.regs.get (Reg.low .rax w)
    let v := a - d
    let status : StatusFlags := .from_result v {
      cf := v.unsigned != a.unsigned - d.unsigned
      af := (v.take 4).unsigned != (a.take 4).unsigned - (d.take 4).unsigned,
      of := v.signed != a.signed - d.signed }
    let s := { s with status }
    if a = d then s.set dst (s.regs.get src) p next
    -- On a failed comparison the processor writes a memory destination back with its own value.
    -- For a register destination the SDM writes it back too, which zeroes the upper half of a
    -- 32-bit register; AMD Zen 5 keeps the register. Both are allowed.
    else if dst.isMem then s.set dst d p (fun s => next (s.setReg (Reg.low .rax w) d))
    else undefined (fun (writeBack : Bool) =>
      if writeBack then s.set dst d p (fun s => next (s.setReg (Reg.low .rax w) d))
      else next (s.setReg (Reg.low .rax w) d)))
  | .mul src =>
    let a := s.regs.get (Reg.low .rax w)
    src.interp s p (fun b s =>
    let v := a * b
    let vn := a.unsigned * b.unsigned
    let s := if w == .W8
      then s.setReg (.low .rax .W16) (.ofInt _ vn)
      else (s.setReg (.low .rax w) v).setReg (.low .rdx w) (.ofInt _ (vn >>> w.bits))
    undefined (λ sf => undefined (λ zf => undefined (λ af => undefined (λ pf =>
    next { s with status := { cf := v.unsigned != vn, pf, af, zf, sf, of := v.unsigned != vn }})))))
  | .mulx r_hi r_lo src1 =>
    src1.interp s p (fun a s =>
    let b := s.regs.get (.low .rdx w)
    let v := a.unsigned * b.unsigned
    let s := s.setReg r_lo (.ofInt _ v) -- if r_hi = r_li, hi is written:
    let s := s.setReg r_hi (.ofInt _ (v >>> w.bits))
    next s)
  -- imul1 and imul collectively describe variants of the same
  -- syntax level `imul` instruction, where imul1 is the 1-operand case
  | .imul1 src =>
    let a := s.regs.get (Reg.low .rax w)
    src.interp s p (fun b s =>
    let v := a.toInt * b.toInt
    let s := if w == .W8 then
      s.setReg (.low .rax .W16) (BitVec.ofInt 16 v)
    else
      let result := BitVec.ofInt (w.bits * 2) v
      let low := result.take w.bits
      let high := (result.drop w.bits).setWidth _
      (s.setReg (.low .rax w) low).setReg (.low .rdx w) high
    undefined (λ sf => undefined (λ zf => undefined (λ af => undefined (λ pf =>
    let low := BitVec.ofInt w.bits v
    let cf := v != low.toInt
    next { s with status := { cf := cf, pf, af, zf, sf, of := cf }})))))
  | .imul dst src1 src2 =>
    src1.interp s p (fun a s =>
    src2.interp s p (fun b s =>
    let v := a * b
    s.set (match (generalizing := false) (motive := Option (RegOrMem w) → RegOrMem w)
             dst with | .some dst => dst | _ => src1) v p (fun s =>
    let cf := v.signed != a.signed * b.signed
    undefined (λ sf => undefined (λ zf => undefined (λ af => undefined (λ pf =>
    next { s with status := { cf := cf, pf, af, zf, sf, of := cf }})))))))
-- Bitwise
  | .div src =>
    src.interp s p (fun d s =>
    let n := if w == .W8 then (s.regs.get (Reg.low .rax .W16)).toNat
      else (s.regs.get (Reg.low .rdx w) ++ s.regs.get (Reg.low .rax w)).toNat
    if d.toNat = 0 ∨ n / d.toNat ≥ 2 ^ w.bits then .fault .divideError else
    let s := if w == .W8
      then (s.setReg (Reg.low .rax .W8) (.ofNat _ (n / d.toNat))).setReg Reg.ah (.ofNat _ (n % d.toNat))
      else (s.setReg (Reg.low .rax w) (.ofNat _ (n / d.toNat))).setReg (Reg.low .rdx w) (.ofNat _ (n % d.toNat))
    undefined (fun status => next { s with status }))
  | .idiv src =>
    src.interp s p (fun d s =>
    let n := if w == .W8 then (s.regs.get (Reg.low .rax .W16)).toInt
      else (s.regs.get (Reg.low .rdx w) ++ s.regs.get (Reg.low .rax w)).toInt
    -- The quotient is truncated toward zero; the remainder has the sign of the dividend.
    let q := n.tdiv d.toInt
    let r := n.tmod d.toInt
    if d.toInt = 0 ∨ q < -2 ^ (w.bits - 1) ∨ q ≥ 2 ^ (w.bits - 1) then .fault .divideError else
    let s := if w == .W8
      then (s.setReg (Reg.low .rax .W8) (.ofInt _ q)).setReg Reg.ah (.ofInt _ r)
      else (s.setReg (Reg.low .rax w) (.ofInt _ q)).setReg (Reg.low .rdx w) (.ofInt _ r)
    undefined (fun status => next { s with status }))
  | .cwtd => next (s.setReg (Reg.low .rdx .W16) (if (s.regs.get (Reg.low .rax .W16)).msb then -1 else 0))
  | .cltd => next (s.setReg (Reg.low .rdx .W32) (if (s.regs.get (Reg.low .rax .W32)).msb then -1 else 0))
  | .cqto => next (s.setReg (Reg.low .rdx .W64) (if (s.regs.get (Reg.low .rax .W64)).msb then -1 else 0))
  | .cbtw => next (s.setReg (Reg.low .rax .W16) ((s.regs.get (Reg.low .rax .W8)).signExtend 16))
  | .cwtl => next (s.setReg (Reg.low .rax .W32) ((s.regs.get (Reg.low .rax .W16)).signExtend 32))
  | .cltq => next (s.setReg (Reg.low .rax .W64) ((s.regs.get (Reg.low .rax .W32)).signExtend 64))
  | .test a b =>
    a.interp s p (fun a s =>
    b.interp s p (fun b s =>
    let v := a &&& b
    undefined (fun af =>
    let status := .from_result v { cf := false, af, of := false}
    next { s with status})))
  | .and dst src | .or dst src | .xor dst src =>
    dst.interp s p (fun a s =>
    src.interp s p (fun b s =>
    let v := match i with | .and _ _ => a &&& b | .or _ _ => a ||| b | _ => a ^^^ b
    undefined (fun af =>
    let status := .from_result v { cf := false, of := false, af }
    { s with status }.set dst v p next)))
  | .not dst =>
    dst.interp s p (fun a s =>
    let v := ~~~a
    s.set dst v p next)
  | .shl dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    -- A zero count leaves flags unchanged but still writes dst, zero-extending 32-bit registers.
    if count == 0 then s.set dst a p next else
    let v := a <<< count
    undefined (λ af =>
    (λ setcf => if count < w.bits then setcf (a <<< (count-1)).msb else undefined setcf) (λ cf =>
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := .from_result v { s.status with cf, af, of } }.set dst v p next))))
  | .shr dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then s.set dst a p next else
    let v := a.ushiftRight count
    undefined (λ af =>
    (λ setcf => if count < w.bits then setcf (a.getLsbD (count-1)) else undefined setcf) (λ cf =>
    (λ setof => if count == 1 then setof a.msb else undefined setof) (λ of =>
    { s with status := .from_result v { s.status with cf, af, of } }.set dst v p next))))
  | .sar dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then s.set dst a p next else
    let v := a.sshiftRight count
    let cf := (a.sshiftRight (count-1)).getLsbD 0
    undefined (λ af =>
    (λ setof => if count == 1 then setof false else undefined setof) (λ of =>
    { s with status := .from_result v { s.status with cf, af, of } }.set dst v p next)))
  | .shrd dst src count =>
    dst.interp s p (fun a s =>
    src.interp s p (fun b s =>
    let count := count.interpMasked s p w
    if count == 0 then s.set dst a p next else
    let v := (((b.append a) >>> count).take w.bits).setWidth _
    (λ setstatus => if count > w.bits then undefined setstatus else
      let cf := a.getLsbD (count-1)
      undefined (λ af =>
      (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
      setstatus (.from_result v { cf, af, of})))) (λ status =>
    -- The result is undefined if the count exceeds the operand size (only possible for 16 bits).
    (λ setv => if count > w.bits then undefined setv else setv v) (λ v =>
    { s with status }.set dst v p next))))
  | .shld dst src count =>
    dst.interp s p (fun a s =>
    src.interp s p (fun b s =>
    let count := count.interpMasked s p w
    if count == 0 then s.set dst a p next else
    let v := (((a.append b) <<< count).drop w.bits).setWidth _
    (λ setstatus => if count > w.bits then undefined setstatus else
      let cf := (a <<< (count-1)).msb
      undefined (λ af =>
      (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
      setstatus (.from_result v { cf, af, of})))) (λ status =>
    (λ setv => if count > w.bits then undefined setv else setv v) (λ v =>
    { s with status }.set dst v p next))))
  | .rol dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then s.set dst a p next else
    let v := a.rotateLeft count
    let cf := v.getLsbD 0
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  | .ror dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then s.set dst a p next else
    let v := a.rotateRight count
    let cf := v.msb
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  | .rcr dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then s.set dst a p next else
    let t := (BitVec.ofBool s.status.cf ++ a).rotateRight count
    let (cf, v) := (t.msb, t.take w.bits)
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  | .rcl dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then s.set dst a p next else
    let t := (BitVec.ofBool s.status.cf ++ a).rotateLeft count
    let (cf, v) := (t.msb, t.take w.bits)
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  -- For a zero source the destination is undefined, and processors keep it, upper bits
  -- included; so all 64 bits of the register are undefined.
  | .bsr dst src =>
    src.interp s p (fun v s =>
    undefined (fun (status : StatusFlags) =>
    if v = 0 then
      @undefined _ (.bitvec .W64) (fun r =>
        next { s with regs := s.regs.set64 dst.base r, status := { status with zf := true } })
    else
      next { s.setReg dst (.ofNat _ v.highestSetBit) with status := { status with zf := false } }))
  -- tzcnt and bsf set different flags, and tzcnt gives the width for a zero source.
  | .repBsf dst src =>
    src.interp s p (fun v s =>
    undefined (fun (status : StatusFlags) =>
    if v = 0 then
      @undefined _ (.bitvec .W64) (fun r => next { s with regs := s.regs.set64 dst.base r, status })
    else
      next { s.setReg dst (.ofNat _ v.lowestSetBit) with status }))
  | .btc dst bit =>
    if btcBitString dst bit then unimplemented "btc with a register bit offset into memory" else
    bit.interp s p (fun b s =>
    dst.interp s p (fun a s =>
    let i := b.toNat % w.bits
    undefined (fun of => undefined (fun sf => undefined (fun af => undefined (fun pf =>
    { s with status := { s.status with cf := a.getLsbD i, of, sf, af, pf } }.set dst
      (a ^^^ BitVec.ofNat w.bits (2 ^ i)) p next))))))
  | .bswap dst =>
    let a := s.regs.get dst
    match (generalizing := false) (motive := Width → Effects) w with
    | .W32 =>
      let v := a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.drop 24
      next (s.setReg dst (v.setWidth _))
    | .W64 =>
      let v := a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8
            ++ a.extractLsb' 32 8 ++ a.extractLsb' 40 8 ++ a.extractLsb' 48 8 ++ a.drop 56
      next (s.setReg dst (v.setWidth _))
    | _ => undefined (fun v => next (s.setReg dst v))
  | .jcc cc l =>
    if cc.interp s.status
    then jmp (label l) s
    else next s
  | .jmp tgt =>
    tgt.interp s p (fun a s =>
    jmp (.ofBitVec a) s)
  | .call tgt =>
    tgt.interp s p (fun a s =>
    let rsp := s.regs.get64 .rsp - Width.W64.bytesv
    { s with regs := s.regs.set64 .rsp rsp }.store rsp (w:=.W64) p.upper.toBitVec (jmp (.ofBitVec a)))
  | .ret =>
    let rsp := s.regs.get64 .rsp
    s.load rsp .W64 (fun ra s =>
    jmp (.ofBitVec ra) { s with regs := s.regs.set64 .rsp (rsp + 8) })
  | .leave =>
    -- The load precedes the register commit, so a faulting leave changes nothing.
    let rbp := s.regs.get64 .rbp
    s.load rbp .W64 (fun v s =>
    next { s with regs := (s.regs.set64 .rsp (rbp + 8)).set64 .rbp v })
  | nop _ | nopalign _ _ => next s
  | ud2 => .fault .invalidOpcode
  | prefetcht0 _ => next s

-- AVX Operations Interpreter
/-- A binary64 bit pattern in Lean's logical float model. The model has a single NaN. -/
def BitVec.toFloatModel (v : BitVec 64) : Float.Model := Float.Model.ofBits (UInt64.ofBitVec v)

def Float.Model.toBitVec64 (f : Float.Model) : BitVec 64 := f.toBits.toBitVec

/-- An SSE double-precision operation on one lane, computed in Lean's logical float model (not
the compiled `Float`, so the hardware tests check the model): a NaN operand propagates (quieted,
the first operand winning), and an invalid operation gives the default NaN
0xfff8000000000000 (sign set, exponent all ones, fraction `100…0`). -/
def sseBinOp64 (op : Float.Model → Float.Model → Float.Model) (a b : BitVec 64) : BitVec 64 :=
  if a.toFloatModel.isNaN then a ||| 0x0008000000000000#64
  else if b.toFloatModel.isNaN then b ||| 0x0008000000000000#64
  else let r := op a.toFloatModel b.toFloatModel
    if r.isNaN then 0xfff8000000000000#64 else r.toBitVec64

/-- A binary32 bit pattern in Lean's logical float model. -/
def BitVec.toFloat32Model (v : BitVec 32) : Float32.Model := Float32.Model.ofBits (UInt32.ofBitVec v)

def Float32.Model.toBitVec32 (f : Float32.Model) : BitVec 32 := f.toBits.toBitVec

/-- `sseBinOp64` for binary32, in the logical model: the default NaN is 0xffc00000. -/
def sseBinOp32 (op : Float32.Model → Float32.Model → Float32.Model) (a b : BitVec 32) : BitVec 32 :=
  if a.toFloat32Model.isNaN then a ||| 0x400000#32
  else if b.toFloat32Model.isNaN then b ||| 0x400000#32
  else let r := op a.toFloat32Model b.toFloat32Model
    if r.isNaN then 0xffc00000#32 else r.toBitVec32

/-- The flags of an SSE compare from an IEEE ordering (`none` is unordered). -/
def compareFlags (c : Option Ordering) : StatusFlags :=
  let (zf, pf, cf) := match c with
    | none => (true, true, true)
    | some .gt => (false, false, false)
    | some .lt => (false, false, true)
    | some .eq => (true, false, false)
  { zf, pf, cf, of := false, sf := false, af := false }

/-- An SSE compare predicate (the low three bits of the cmpss and cmpsd immediate) on an IEEE
ordering. -/
def cmpPredicate (pred : UInt8) (c : Option Ordering) : Bool :=
  match pred.toNat % 8, c with
  | 0, some .eq => true
  | 1, some .lt => true
  | 2, some .lt | 2, some .eq => true
  | 3, none => true
  | 4, some .lt | 4, some .gt | 4, none => true
  | 5, some .eq | 5, some .gt | 5, none => true
  | 6, some .gt | 6, none => true
  | 7, some _ => true
  | _, _ => false

/-- cvttss2si: `f` truncated toward zero as an `n`-bit signed integer; NaN, infinity or a result
out of range gives the integer indefinite value -2^(n-1). -/
def cvttToInt (n : Nat) (f : Float32.Model) : Int :=
  let z := f.unpack.toInt 0 0
  if f.isNaN || f.isInf || z < -2 ^ (n - 1) || z ≥ 2 ^ (n - 1) then -2 ^ (n - 1) else z

/-- The most significant bit of each byte of `v`; byte `i` gives bit `i` (`pmovmskb`). -/
def BitVec.byteMsbMask (v : BitVec 128) : BitVec 16 :=
  (List.range 16).foldl (fun m i => m ||| (BitVec.ofBool (v.getLsbD (8 * i + 7))).zeroExtend 16 <<< i) 0#16

/-- `pshufd`: doubleword `i` of the result is doubleword `imm[2i+1:2i]` of `v`. -/
def BitVec.pshufd (imm : UInt8) (v : BitVec 128) : BitVec 128 :=
  let lane (i : Nat) : BitVec 32 := v.extractLsb' (32 * ((imm.toNat >>> (2 * i)) % 4)) 32
  lane 3 ++ lane 2 ++ lane 1 ++ lane 0

def AvxOperation.interp [Labels] [address_size : AddressSize]
  {w} (i : AvxOperation w) (p : Std.Rco Int64) (s : MachineData)
  (next : MachineData → Effects) : Effects :=
match i with
  | .movups dst src | .movdqu dst src | .movupd dst src => src.interp s p (fun val s => s.setAvxLegacy dst val p next)
  | .vmovups dst src => src.interp s p (fun val s => s.setAvx dst val p next)
  | .movaps dst src | .movdqa dst src | .movapd dst src =>
    src.interp s p (checkAlign := true)
      (fun val s => s.setAvxLegacy dst val p (checkAlign := true) next)
  -- TODO: MXCSR
  | .subps dst src =>
    src.interp s p (checkAlign := true) (fun a s =>
    dst.interp s p (fun b s =>
      s.setAvxLegacy dst (BitVec.packedBinOp 32 (sseBinOp (· - ·)) b a) p next))
  | .addps dst src =>
    src.interp s p (checkAlign := true) (fun a s =>
    dst.interp s p (fun b s =>
      s.setAvxLegacy dst (BitVec.packedBinOp 32 (sseBinOp (· + ·)) b a) p next))
  | .vmovaps dst src =>
    src.interp s p (checkAlign := true)
      (fun val s => s.setAvx dst val p (checkAlign := true) next)
  | .vxorps dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (s.zmms.get src1 ^^^ b)))
  | .vaddps dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 32 (sseBinOp (· + ·)) (s.zmms.get src1) b)))
  | .vmulps dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 32 (sseBinOp (· * ·)) (s.zmms.get src1) b)))
  -- dst = src1 * src2 + dst. A NaN result is the first NaN in the order multiplicand (src1),
  -- multiplier (src2), addend (dst): Intel SDM Vol. 1, Table 14-17.
  | .vfmadd231ps dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst
        (BitVec.packedTernOp 32 (sseTernOp Kraken.Float32.fma) (s.zmms.get src1) b (s.zmms.get dst))))
  | .vshufps dst src1 src2 imm =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 128 (BitVec.shufps128 imm) (s.zmms.get src1) b)))
  | .vextractf128 dst src imm =>
    next (s.setAvxReg dst ((s.zmms.get src).extractLsb' (128 * (imm.toNat % 2)) 128))
  | .vmovhlps dst src1 src2 =>
    next (s.setAvxReg dst
      ((s.zmms.get src1).extractLsb' 64 64 ++ (s.zmms.get src2).extractLsb' 64 64))
  | .vmovss dst src1 src2 =>
    next (s.setAvxReg dst
      ((s.zmms.get src1).extractLsb' 32 96 ++ (s.zmms.get src2).extractLsb' 0 32))
  | .vaddss dst src1 src2 =>
    let a := s.zmms.get src1
    let b := s.zmms.get src2
    next (s.setAvxReg dst
      (a.extractLsb' 32 96 ++ sseBinOp (· + ·) (a.extractLsb' 0 32) (b.extractLsb' 0 32)))
  | .vzeroupper => next { s with zmms := s.zmms.zeroUpper }
  -- A legacy SSE memory operand must be 16-byte aligned.
  | .pxor dst src =>
    src.interp s p (checkAlign := true) (fun b s =>
      next (s.setAvxLegacyReg dst (s.zmms.get dst ^^^ b)))
  | .pcmpeqb dst src =>
    src.interp s p (checkAlign := true) (fun b s =>
      next (s.setAvxLegacyReg dst
        (BitVec.packedBinOp 8 (fun x y => if x = y then BitVec.allOnes 8 else 0) (s.zmms.get dst) b)))
  | .pshufd dst src imm =>
    src.interp s p (checkAlign := true) (fun v s =>
      next (s.setAvxLegacyReg dst (BitVec.pshufd imm v)))
  | .pmovmskb dst src =>
    next (s.setReg dst ((BitVec.byteMsbMask (s.zmms.get src)).zeroExtend _))
  -- The bits of the xmm register above the operand are zeroed; the bits above 128 are kept.
  | .movdIn dst src =>
    src.interp s p (fun v s => next (s.setAvxLegacyReg dst (v.zeroExtend 128)))
  | .movdOut dst src =>
    s.set dst ((s.zmms.get src).setWidth _) p next
  | .addsd dst src | .subsd dst src | .mulsd dst src | .divsd dst src =>
    src.interpLow64 s p (fun b s =>
    let d := s.zmms.get dst
    let op : Float.Model → Float.Model → Float.Model := match i with
      | .addsd .. => (· + ·) | .subsd .. => (· - ·) | .mulsd .. => (· * ·) | _ => (· / ·)
    next (s.setAvxLegacyReg dst (d.extractLsb' 64 64 ++ sseBinOp64 op (d.setWidth 64) b)))
  | .ucomisd a b | .comisd a b =>
    b.interpLow64 s p (fun y s =>
    next { s with status := compareFlags (((s.zmms.get a).setWidth 64).toFloatModel.compare y.toFloatModel) })
  | .cmpsd dst src pred =>
    src.interpLow64 s p (fun y s =>
    let d := s.zmms.get dst
    let c := (d.setWidth 64).toFloatModel.compare y.toFloatModel
    next (s.setAvxLegacyReg dst
      (d.extractLsb' 64 64 ++ if cmpPredicate pred c then BitVec.allOnes 64 else 0#64)))
  | .addss dst src | .subss dst src | .mulss dst src | .divss dst src =>
    src.interpLow32 s p (fun b s =>
    let d := s.zmms.get dst
    let op : Float32.Model → Float32.Model → Float32.Model := match i with
      | .addss .. => (· + ·) | .subss .. => (· - ·) | .mulss .. => (· * ·) | _ => (· / ·)
    next (s.setAvxLegacyReg dst (d.extractLsb' 32 96 ++ sseBinOp32 op (d.setWidth 32) b)))
  | .ucomiss a b | .comiss a b =>
    b.interpLow32 s p (fun y s =>
    next { s with status :=
      compareFlags (((s.zmms.get a).setWidth 32).toFloat32Model.compare y.toFloat32Model) })
  | .cmpss dst src pred =>
    src.interpLow32 s p (fun y s =>
    let d := s.zmms.get dst
    let c := (d.setWidth 32).toFloat32Model.compare y.toFloat32Model
    next (s.setAvxLegacyReg dst
      (d.extractLsb' 32 96 ++ if cmpPredicate pred c then BitVec.allOnes 32 else 0#32)))
  | .movssRR dst src =>
    next (s.setAvxLegacyReg dst ((s.zmms.get dst).extractLsb' 32 96 ++ (s.zmms.get src).setWidth 32))
  | .movssLoad dst a =>
    s.load ((a.interp s.regs p).zeroExtend _) .W32 (fun v s =>
    next (s.setAvxLegacyReg dst (v.zeroExtend 128)))
  | .movssStore a src =>
    s.store ((a.interp s.regs p).zeroExtend _) (w := .W32) ((s.zmms.get src).setWidth 32) next
  | .cvtsi2ss dst src =>
    src.interp s p (fun v s =>
    next (s.setAvxLegacyReg dst
      ((s.zmms.get dst).extractLsb' 32 96 ++ (Float32.Model.ofInt v.toInt).toBitVec32)))
  | .cvttss2si (rw := rw) dst src =>
    src.interpLow32 s p (fun v s =>
    next (s.setReg dst (.ofInt _ (cvttToInt rw.bits v.toFloat32Model))))
  | .andps dst src | .andnps dst src | .orps dst src | .xorps dst src | .xorpd dst src =>
    src.interp s p (checkAlign := true) (fun b s =>
    let d := s.zmms.get dst
    let v := match i with
      | .andps .. => d &&& b | .andnps .. => ~~~d &&& b | .orps .. => d ||| b | _ => d ^^^ b
    next (s.setAvxLegacyReg dst v))
  | .movsdRR dst src =>
    next (s.setAvxLegacyReg dst ((s.zmms.get dst).extractLsb' 64 64 ++ (s.zmms.get src).setWidth 64))
  | .movsdLoad dst a =>
    s.load ((a.interp s.regs p).zeroExtend _) .W64 (fun v s =>
    next (s.setAvxLegacyReg dst (v.zeroExtend 128)))
  | .movsdStore a src =>
    s.store ((a.interp s.regs p).zeroExtend _) (w := .W64) ((s.zmms.get src).setWidth 64) next
  | .cvtsi2sd dst src =>
    src.interp s p (fun v s =>
    next (s.setAvxLegacyReg dst
      ((s.zmms.get dst).extractLsb' 64 64 ++ (Float.Model.ofInt v.toInt).toBitVec64)))

@[kstep]
def Instr.interp [Labels]
  (i : Instr) (s : MachineData) (p : Std.Rco Int64)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  require_exec_access p (fun _unit =>
    match i with
      | .regular addr_sz op_sz op =>
          Operation.interp (w := op_sz) (address_size := .mk addr_sz) op p s next jmp
      | .avx addr_sz op_sz op =>
          AvxOperation.interp (w := op_sz) (address_size := .mk addr_sz) op p s next
  )

@[kstep] def Directive.interp [Labels]
  (d : Directive) (s : MachineData) (p : Std.Rco Int64)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  match d with
  | .label _ => next s
  | .instr i => i.interp s p next jmp
  | .byteArray _ => .unimplemented s!"Unimplemented: execution reached data block at {p.1}"

def Directives.interp [Labels]
  (ds : List (Kraken.Sized Directive)) (s : MachineData) (pc : Int64)
  (ret : Int64 → MachineData → Effects) (jmp : Int64 → MachineData → Effects := ret) : Effects :=
  match ds with
  | [] => ret pc s
  | {directive, size := sz} :: ds =>
    directive.interp s (.mk pc (pc+.ofNat sz)) (jmp:=jmp) (next := (fun s =>
    interp ds s (pc+.ofNat sz) ret jmp))

abbrev Layout := Kraken.Layout Directive

@[reducible]
def Executable.labels (e : Executable) : Labels :=
  { label l := (e.withAddresses.findSome?
      (fun {directive, addr, ..} => if directive = .label l then .some addr else .none)).getD (-1) }

def Executable.directivesFromLabel (e : Executable) (l : Label) : List (Kraken.Sized Directive) :=
  e.program.dropWhile (·.directive != .label l)

def Executable.step (e : Executable) (s : MachineState) (ret : MachineState → Effects) : Effects :=
  let := Executable.labels e
  Directives.interp (e.directivesAtAddress s.pc) s.data s.pc (fun pc s => ret ⟨s, pc⟩)

def Executable.straightline (e : Executable) (s : MachineState) (ret : MachineState → Effects) : Effects :=
  let := Executable.labels e
  Directives.interp (e.directivesFromAddress s.pc) s.data s.pc (fun pc s => ret ⟨s, pc⟩)

-- -- Concrete evaluators for expedient testing

partial def Executable.eval (e : Executable) (s : MachineState) (until_ : MachineState → Bool) : Except String (MachineState) :=
  if until_ s then .ok s else handleEffects (Executable.straightline e s .done)
where
  handleEffects es :=
    match es with
    | .done s => eval e s until_
    | .unimplemented msg => .error msg
    | .gp_unaligned addr w => .error s!"#GP: Memory op at {repr addr} did not have mandatory alignment of {w}"
    | .fault f => .error (toString f)
    | .require_read_access _ _ ok => handleEffects (ok ())
    | .require_write_access _ _ ok => handleEffects (ok ())
    | .require_exec_access _ ok => handleEffects (ok ())
    | .nonmem_load _ addr _ _ => .error s!"Load at unmapped address {repr addr}"
    | .nonmem_store _ addr _ _ => .error s!"Store at unmapped address {repr addr}"
    | @Effects.undefined _ t cont => handleEffects (cont (t.from_hash (hash s.1.regs)))

def Directive.fakeSize (hashOfProgram : UInt64) (d : Directive) : Nat :=
  match d with
  | .label _ => 0
  | .instr (.regular _ _ (.nop sz)) => sz -- may be zero
  | .instr i => (1 + hash (hashOfProgram, i) % 15).toNat
  | .byteArray bs => bs.size

def Program.fakeLayout (prog : Program) : Executable :=
  let : Inhabited Directive := .mk (.byteArray (.mk #[]))
  let h := hash prog;
  let layout : Layout := { start := h.toInt64<<<16, size i := prog[i]!.fakeSize h }
  layout prog

abbrev eval [layout : Layout] (prog : Program) := Executable.eval (layout prog)

/-- info: Except.ok 42 -/
#guard_msgs in
#eval
  let exe := Program.fakeLayout [
    .label "main",
    .instr (.regular .W64 .W64 (.lea (.low .rax .W64) (.mk .none .none (.int64 41)))),
    .instr (.regular .W64 .W64 (.inc (.reg (.low .rax .W64)))),
    .instr (.regular .W64 .W64 .ret) ]
  let start := (Executable.labels exe).label "main"
  let data : MachineData := { dmem := Mem.storeInt {} 0x100 8 0x1337, regs := {rsp := 0x100} }
  (Executable.eval exe {data, pc := start} (fun st => st.pc = 0x1337)).bind (fun s => .ok s.1.regs.rax)
