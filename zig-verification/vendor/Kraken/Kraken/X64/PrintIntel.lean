module

public import Kraken.X64.Syntax

public section
/-!
# IntelPrinter
This file prints Kraken-supported x64 assembly in Intel syntax.
This is different from Parser.lean which expects AT&T syntax.
-/

instance : ToString Reg64 where
  toString r := match r with
  | .rax => "rax" | .rbx => "rbx" | .rcx => "rcx" | .rdx => "rdx"
  | .rsi => "rsi" | .rdi => "rdi" | .rsp => "rsp" | .rbp => "rbp"
  | .r8  => "r8"  | .r9  => "r9"  | .r10 => "r10" | .r11 => "r11"
  | .r12 => "r12" | .r13 => "r13" | .r14 => "r14" | .r15 => "r15"

instance : ToString RegMm where
  toString r := match r with
  | .mm0  => "mm0"  | .mm1  => "mm1"  | .mm2  => "mm2"  | .mm3  => "mm3"
  | .mm4  => "mm4"  | .mm5  => "mm5"  | .mm6  => "mm6"  | .mm7  => "mm7"
  | .mm8  => "mm8"  | .mm9  => "mm9"  | .mm10 => "mm10" | .mm11 => "mm11"
  | .mm12 => "mm12" | .mm13 => "mm13" | .mm14 => "mm14" | .mm15 => "mm15"
  | .mm16 => "mm16" | .mm17 => "mm17" | .mm18 => "mm18" | .mm19 => "mm19"
  | .mm20 => "mm20" | .mm21 => "mm21" | .mm22 => "mm22" | .mm23 => "mm23"
  | .mm24 => "mm24" | .mm25 => "mm25" | .mm26 => "mm26" | .mm27 => "mm27"
  | .mm28 => "mm28" | .mm29 => "mm29" | .mm30 => "mm30" | .mm31 => "mm31"

def Reg.toStr {w} (r : Reg w) : String := match w, r with
  | .W64, .low r _ => toString r
  | .W32, .low r _ => match r with
    | .rax => "eax" | .rbx => "ebx" | .rcx => "ecx" | .rdx => "edx"
    | .rsi => "esi" | .rdi => "edi" | .rsp => "esp" | .rbp => "ebp"
    | .r8  => "r8d" | .r9  => "r9d" | .r10 => "r10d" | .r11 => "r11d"
    | .r12 => "r12d"| .r13 => "r13d"| .r14 => "r14d"| .r15 => "r15d"
  | .W16, .low r _ => match r with
    | .rax => "ax" | .rbx => "bx" | .rcx => "cx" | .rdx => "dx"
    | .rsi => "si" | .rdi => "di" | .rsp => "sp" | .rbp => "bp"
    | .r8  => "r8w" | .r9  => "r9w" | .r10 => "r10w" | .r11 => "r11w"
    | .r12 => "r12w"| .r13 => "r13w"| .r14 => "r14w"| .r15 => "r15w"
  | .W8, .low r _ => match r with
    | .rax => "al" | .rbx => "bl" | .rcx => "cl" | .rdx => "dl"
    | .rsi => "sil" | .rdi => "dil" | .rsp => "spl" | .rbp => "bpl"
    | .r8  => "r8b" | .r9  => "r9b" | .r10 => "r10b" | .r11 => "r11b"
    | .r12 => "r12b"| .r13 => "r13b"| .r14 => "r14b"| .r15 => "r15b"
  | .W8, .ah => "ah" | .W8, .bh => "bh" | .W8, .ch => "ch" | .W8, .dh => "dh"

instance {w} : ToString (Reg w) where toString := Reg.toStr

instance {w} : ToString (AvxReg w) where
  toString r := match r with
  | .xmm r => "x" ++ toString r
  | .ymm r => "y" ++ toString r
  | .zmm r => "z" ++ toString r

def RegOrRip.toStr (b : RegOrRip) (addr_w : Width := .W64) : String := match b with
  | .reg r => toString (Reg.low r addr_w)
  | .rip => "rip"
instance : ToString RegOrRip where toString b := b.toStr

def ConstExpr.toStr : ConstExpr → String
  | .label l => l
  | .int64 i => s!"{i}"
  | .before_current_instruction => "."
  | .after_current_instruction => "."
  | .add e1 e2 => s!"({e1.toStr} + {e2.toStr})"
  | .sub e1 e2 => s!"({e1.toStr} - {e2.toStr})"
instance : ToString ConstExpr where toString := ConstExpr.toStr

def AddrExpr.toStr (a : AddrExpr) (addr_w : Width := .W64) : String :=
  let dispStr := match a.base, a.disp with
    -- Unwrap RIP-relative displacements back to just the label for printing
    -- (like RelRegOrMem.toStr below)
    | .some .rip, .sub e .after_current_instruction => toString e
    | _, _ => toString a.disp
  "[" ++ "+".intercalate (
    (match a.base with | .some b => [b.toStr addr_w] | _ => [])
    ++ (match a.idx with | .some ⟨r, s⟩ => [s!"{Reg.low r addr_w}*{s.bytes}"] | _ => [])
    ++ [dispStr]
  ) ++ "]"

def RegOrMem.toStr {w} (rm : RegOrMem w) (addr_w : Width := .W64) : String := match rm with
  | .reg r => ToString.toString r
  | .mem a => match w with
    | .W64 => "QWORD PTR " ++ a.toStr addr_w
    | .W32 => "DWORD PTR " ++ a.toStr addr_w
    | .W16 => "WORD PTR " ++ a.toStr addr_w
    | .W8 => "BYTE PTR " ++ a.toStr addr_w
instance {w} : ToString (RegOrMem w) where toString rm := rm.toStr

def AvxRegOrMem.toStr {w} (rm : AvxRegOrMem w) (addr_w : Width := .W64) : String := match rm with
  | .avx r => ToString.toString r
  | .mem a => match w with
    | .W512 => "ZMMWORD PTR " ++ a.toStr addr_w
    | .W256 => "YMMWORD PTR " ++ a.toStr addr_w
    | .W128 => "XMMWORD PTR " ++ a.toStr addr_w
instance {w} : ToString (AvxRegOrMem w) where toString rm := rm.toStr

def Operand.toStr {w} (op : Operand w) (addr_w : Width := .W64) : String := match op with
  | .regOrMem rm => rm.toStr addr_w
  | .imm (.int64 i) => toString i
  -- In Intel syntax a bare symbol is a memory operand; its address needs OFFSET
  | .imm v => s!"OFFSET {v}"
instance {w} : ToString (Operand w) where toString op := op.toStr

def AvxOperand.toStr {w} (op : AvxOperand w) (addr_w : Width := .W64) : String := match op with
  | .regOrMem rm => rm.toStr addr_w
instance {w} : ToString (AvxOperand w) where toString op := op.toStr

def RelRegOrMem.toStr (rel : RelRegOrMem) (addr_w : Width := .W64) : String := match rel with
  | .rel (.sub e .after_current_instruction) => toString e
  | .rel c => toString c
  | .reg r => toString r
  | .mem a => "QWORD PTR " ++ a.toStr addr_w
instance : ToString RelRegOrMem where toString rel := rel.toStr

instance : ToString CondCode where toString
  | .o => "o" | .no => "no" | .c => "b" | .nc => "ae" | .z => "e" | .nz => "ne" | .be => "be" | .a => "a"
  | .s => "s" | .ns => "ns" | .p => "p" | .np => "np" | .l => "l" | .ge => "ge" | .le => "le" | .g => "g"

instance : ToString ShiftCountExpr where toString
  | .cl => "cl"
  | .imm8 v => ToString.toString v

def Operation.toStr {w} (op : Operation w) (addr_w : Width := .W64) : String := match op with
  | .mov dst src => s!"mov {dst.toStr addr_w}, {src.toStr addr_w}"
  | @Operation.movsx _ w' dst src =>
    -- Intel spells the 32-to-64-bit form `movsxd` (opcode 63 /r, AT&T `movslq`).
    let m := if w == .W64 && w' == .W32 then "movsxd" else "movsx"
    s!"{m} {dst.toStr addr_w}, {src.toStr addr_w}"
  | .movzx dst src => s!"movzx {dst.toStr addr_w}, {src.toStr addr_w}"
  | .push src => s!"push {src.toStr addr_w}"
  | .pop dst => s!"pop {dst.toStr addr_w}"
  | .setcc cc dst => s!"set{cc} {dst.toStr addr_w}"
  | .cmovcc cc dst src => s!"cmov{cc} {dst}, {src.toStr addr_w}"
  | .lea dst src => s!"lea {dst}, {src.toStr addr_w}"
  | .add dst src => s!"add {dst.toStr addr_w}, {src.toStr addr_w}"
  | .adc dst src => s!"adc {dst.toStr addr_w}, {src.toStr addr_w}"
  | .adcx dst src => s!"adcx {dst}, {src.toStr addr_w}"
  | .adox dst src => s!"adox {dst}, {src.toStr addr_w}"
  | .inc dst => s!"inc {dst.toStr addr_w}"
  | .dec dst => s!"dec {dst.toStr addr_w}"
  | .neg dst => s!"neg {dst.toStr addr_w}"
  | .sub dst src => s!"sub {dst.toStr addr_w}, {src.toStr addr_w}"
  | .sbb dst src => s!"sbb {dst.toStr addr_w}, {src.toStr addr_w}"
  | .cmp a b => s!"cmp {a.toStr addr_w}, {b.toStr addr_w}"
  | .xadd l dst src => s!"{if l then "lock " else ""}xadd {dst.toStr addr_w}, {src}"
  | .cmpxchg l dst src => s!"{if l then "lock " else ""}cmpxchg {dst.toStr addr_w}, {src}"
  | .mul src => s!"mul {src.toStr addr_w}"
  | .mulx hi lo src => s!"mulx {hi}, {lo}, {src.toStr addr_w}"
  | .imul none src1 src2 => s!"imul {src1.toStr addr_w}, {src2.toStr addr_w}"
  | .imul (some dst) src1 src2 => s!"imul {dst.toStr addr_w}, {src1.toStr addr_w}, {src2.toStr addr_w}"
  | .imul1 src => s!"imul {src.toStr addr_w}"
  | .div src => s!"div {src.toStr addr_w}"
  | .idiv src => s!"idiv {src.toStr addr_w}"
  | .cwtd => "cwd" | .cltd => "cdq" | .cqto => "cqo"
  | .cbtw => "cbw" | .cwtl => "cwde" | .cltq => "cdqe"
  | .test a b => s!"test {a.toStr addr_w}, {b.toStr addr_w}"
  | .and dst src => s!"and {dst.toStr addr_w}, {src.toStr addr_w}"
  | .not dst => s!"not {dst.toStr addr_w}"
  | .or dst src => s!"or {dst.toStr addr_w}, {src.toStr addr_w}"
  | .xor dst src => s!"xor {dst.toStr addr_w}, {src.toStr addr_w}"
  | .shl dst cnt => s!"shl {dst.toStr addr_w}, {cnt}"
  | .shr dst cnt => s!"shr {dst.toStr addr_w}, {cnt}"
  | .sar dst cnt => s!"sar {dst.toStr addr_w}, {cnt}"
  | .shld dst src cnt => s!"shld {dst.toStr addr_w}, {src}, {cnt}"
  | .shrd dst src cnt => s!"shrd {dst.toStr addr_w}, {src}, {cnt}"
  | .rol dst cnt => s!"rol {dst.toStr addr_w}, {cnt}"
  | .ror dst cnt => s!"ror {dst.toStr addr_w}, {cnt}"
  | .rcl dst cnt => s!"rcl {dst.toStr addr_w}, {cnt}"
  | .rcr dst cnt => s!"rcr {dst.toStr addr_w}, {cnt}"
  | .bswap dst => s!"bswap {dst}"
  | .bsr dst src => s!"bsr {dst}, {src.toStr addr_w}"
  | .repBsf dst src => s!"rep bsf {dst}, {src.toStr addr_w}"
  | .btc dst bit => s!"btc {dst.toStr addr_w}, {bit.toStr addr_w}"
  | .jcc cc l => s!"j{cc} {l}"
  | .jmp tgt => s!"jmp {tgt.toStr addr_w}"
  | .call tgt => s!"call {tgt.toStr addr_w}"
  | .ret => "ret"
  | .nop n => s!".nops {n}"
  | .nopalign a none => s!".align {a}"
  | .nopalign a (some p) => s!".align {a}, {p}"
  | .ud2 => "ud2"
  | .prefetcht0 a => s!"prefetcht0 BYTE PTR {a.toStr addr_w}"
  | .leave => "leave"
instance {w} : ToString (Operation w) where toString op := op.toStr

/-- A scalar single operand: an xmm register or a 32-bit memory operand. -/
def AvxRegOrMem.toStr32 (rm : AvxRegOrMem .W128) (addr_w : Width := .W64) : String := match rm with
  | .avx r => ToString.toString r
  | .mem a => "DWORD PTR " ++ a.toStr addr_w

/-- A scalar double operand: an xmm register or a 64-bit memory operand. -/
def AvxRegOrMem.toStr64 (rm : AvxRegOrMem .W128) (addr_w : Width := .W64) : String := match rm with
  | .avx r => ToString.toString r
  | .mem a => "QWORD PTR " ++ a.toStr addr_w

def AvxOperation.toStr {w} (op : AvxOperation w) (addr_w : Width := .W64) : String := match op with
  | .movups dst src => s!"movups {dst.toStr addr_w}, {src.toStr addr_w}"
  | .vmovups dst src => s!"vmovups {dst.toStr addr_w}, {src.toStr addr_w}"
  | .movaps dst src => s!"movaps {dst.toStr addr_w}, {src.toStr addr_w}"
  | .movdqa dst src => s!"movdqa {dst.toStr addr_w}, {src.toStr addr_w}"
  | .movdqu dst src => s!"movdqu {dst.toStr addr_w}, {src.toStr addr_w}"
  | .movapd dst src => s!"movapd {dst.toStr addr_w}, {src.toStr addr_w}"
  | .movupd dst src => s!"movupd {dst.toStr addr_w}, {src.toStr addr_w}"
  | .subps dst src => s!"subps {dst.toStr addr_w}, {src.toStr addr_w}"
  | .addps dst src => s!"addps {dst.toStr addr_w}, {src.toStr addr_w}"
  | .vmovaps dst src => s!"vmovaps {dst.toStr addr_w}, {src.toStr addr_w}"
  | .vxorps dst src1 src2 => s!"vxorps {dst}, {src1}, {src2.toStr addr_w}"
  | .vaddps dst src1 src2 => s!"vaddps {dst}, {src1}, {src2.toStr addr_w}"
  | .vmulps dst src1 src2 => s!"vmulps {dst}, {src1}, {src2.toStr addr_w}"
  | .vfmadd231ps dst src1 src2 => s!"vfmadd231ps {dst}, {src1}, {src2.toStr addr_w}"
  | .vshufps dst src1 src2 imm => s!"vshufps {dst}, {src1}, {src2.toStr addr_w}, {imm}"
  | .vextractf128 dst src imm => s!"vextractf128 {dst}, {src}, {imm}"
  | .vmovhlps dst src1 src2 => s!"vmovhlps {dst}, {src1}, {src2}"
  | .vmovss dst src1 src2 => s!"vmovss {dst}, {src1}, {src2}"
  | .vaddss dst src1 src2 => s!"vaddss {dst}, {src1}, {src2}"
  | .vzeroupper => "vzeroupper"
  | .pxor dst src => s!"pxor {dst}, {src.toStr addr_w}"
  | .pcmpeqb dst src => s!"pcmpeqb {dst}, {src.toStr addr_w}"
  | .pshufd dst src imm => s!"pshufd {dst}, {src.toStr addr_w}, {imm}"
  | .pmovmskb dst src => s!"pmovmskb {dst}, {src}"
  | .movdIn (rw := rw) dst src => s!"mov{if rw == .W64 then "q" else "d"} {dst}, {src.toStr addr_w}"
  | .movdOut (rw := rw) dst src => s!"mov{if rw == .W64 then "q" else "d"} {dst.toStr addr_w}, {src}"
  | .addsd dst src => s!"addsd {dst}, {src.toStr64 addr_w}"
  | .subsd dst src => s!"subsd {dst}, {src.toStr64 addr_w}"
  | .mulsd dst src => s!"mulsd {dst}, {src.toStr64 addr_w}"
  | .divsd dst src => s!"divsd {dst}, {src.toStr64 addr_w}"
  | .ucomisd a b => s!"ucomisd {a}, {b.toStr64 addr_w}"
  | .comisd a b => s!"comisd {a}, {b.toStr64 addr_w}"
  | .cmpsd dst src pred => s!"cmpsd {dst}, {src.toStr64 addr_w}, {pred}"
  | .addss dst src => s!"addss {dst}, {src.toStr32 addr_w}"
  | .subss dst src => s!"subss {dst}, {src.toStr32 addr_w}"
  | .mulss dst src => s!"mulss {dst}, {src.toStr32 addr_w}"
  | .divss dst src => s!"divss {dst}, {src.toStr32 addr_w}"
  | .ucomiss a b => s!"ucomiss {a}, {b.toStr32 addr_w}"
  | .comiss a b => s!"comiss {a}, {b.toStr32 addr_w}"
  | .cmpss dst src pred => s!"cmpss {dst}, {src.toStr32 addr_w}, {pred}"
  | .movssRR dst src => s!"movss {dst}, {src}"
  | .movssLoad dst a => s!"movss {dst}, DWORD PTR {a.toStr addr_w}"
  | .movssStore a src => s!"movss DWORD PTR {a.toStr addr_w}, {src}"
  | .cvtsi2ss dst src => s!"cvtsi2ss {dst}, {src.toStr addr_w}"
  | .cvttss2si dst src => s!"cvttss2si {dst}, {src.toStr32 addr_w}"
  | .andps dst src => s!"andps {dst}, {src.toStr addr_w}"
  | .andnps dst src => s!"andnps {dst}, {src.toStr addr_w}"
  | .orps dst src => s!"orps {dst}, {src.toStr addr_w}"
  | .xorps dst src => s!"xorps {dst}, {src.toStr addr_w}"
  | .xorpd dst src => s!"xorpd {dst}, {src.toStr addr_w}"
  | .movsdRR dst src => s!"movsd {dst}, {src}"
  | .movsdLoad dst a => s!"movsd {dst}, QWORD PTR {a.toStr addr_w}"
  | .movsdStore a src => s!"movsd QWORD PTR {a.toStr addr_w}, {src}"
  | .cvtsi2sd dst src => s!"cvtsi2sd {dst}, {src.toStr addr_w}"
instance {w} : ToString (Operation w) where toString op := op.toStr

instance : ToString Instr where
  toString i := match i with
  | .regular a _ o => o.toStr a
  | .avx a _ o => o.toStr a

instance : ToString Directive where
  toString
  | .instr i => ToString.toString i
  | .label l => s!"{l}:"
  | .byteArray bs => ".byte "++", ".intercalate (bs.toList.map (fun b => s!"{b}"))
