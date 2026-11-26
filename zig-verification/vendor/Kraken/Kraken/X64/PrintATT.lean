module

public import Kraken.X64.PrintIntel

public section
/-!
# AT&T printer
Prints Kraken x64 syntax in the AT&T dialect accepted by `Kraken.X64.Parser.parse`.
The intended property is `parse (toATT p) = .ok p` for every program `p` that `parse`
can produce (see `PrintATTTests.lean`). Values outside the parser's image (e.g. memory
operands without a base register, or `ConstExpr` arithmetic) are still printed, but
won't round-trip.

Mnemonics carry a width suffix whenever the operands may not determine the width
(immediates, memory), and are unsuffixed when a register operand always does.
-/
namespace Kraken.X64.ATT

def suffix : Width → String | .W8 => "b" | .W16 => "w" | .W32 => "l" | .W64 => "q"

def reg {w} (r : Reg w) : String := "%" ++ r.toStr

def avxReg {w} (r : AvxReg w) : String := "%" ++ toString r

def const : ConstExpr → String
  | .label l => l
  | .int64 i => toString i
  | .add a b => s!"{const a}+{const b}"
  | .sub a b => s!"{const a}-{const b}"
  | e => toString e

def addr (aw : Width) (a : AddrExpr) : String :=
  let disp := match a.base, a.disp with
    | some .rip, .sub e .after_current_instruction => const e
    | _, .int64 0 => ""
    | _, d => const d
  let base := match a.base with
    | some (.reg r) => reg (.low r aw)
    | some .rip => "%rip"
    | none => ""
  let idx := match a.idx with
    | some ⟨r, s⟩ => s!",{reg (.low r aw)},{s.bytes}"
    | none => ""
  -- Without registers, the displacement alone is an absolute address.
  if a.base.isNone && a.idx.isNone then const a.disp else s!"{disp}({base}{idx})"

def rm {w} (aw : Width) : RegOrMem w → String
  | .reg r => reg r
  | .mem a => addr aw a

def avxRm {w} (aw : Width) : AvxRegOrMem w → String
  | .avx r => avxReg r
  | .mem a => addr aw a

def operand {w} (aw : Width) : Operand w → String
  | .regOrMem x => rm aw x
  | .imm e => "$" ++ const e

def count : ShiftCountExpr → String
  | .cl => "%cl"
  | .imm8 e => "$" ++ const e

def target (aw : Width) : RelRegOrMem → String
  | .rel (.sub e .after_current_instruction) => const e
  | .rel e => const e
  | .reg r => "*" ++ reg r
  | .mem a => "*" ++ addr aw a

def operation {w} (aw : Width) (op : Operation w) : String :=
  let s := suffix w
  let one (mn a : String) := s!"{mn}{s} {a}"
  let two (mn a b : String) := s!"{mn}{s} {a}, {b}"
  match op with
  | .mov d x => two "mov" (operand aw x) (rm aw d)
  -- A memory source needs the suffixed form (`movsbl`, `movzwq`, `movslq`, ...) for its width.
  | .movsx (w' := w') d x@(.mem _) => s!"movs{suffix w'}{s} {rm aw x}, {rm aw d}"
  | .movzx (w' := w') d x@(.mem _) => s!"movz{suffix w'}{s} {rm aw x}, {rm aw d}"
  | .movsx d x => s!"movsx {rm aw x}, {rm aw d}"
  | .movzx d x => s!"movzx {rm aw x}, {rm aw d}"
  | .push x => one "push" (operand aw x)
  | .pop d => one "pop" (rm aw d)
  | .setcc cc d => s!"set{cc} {rm aw d}"
  | .cmovcc cc d x => s!"cmov{cc} {rm aw x}, {reg d}"
  | .lea d a => s!"lea {addr aw a}, {reg d}"
  | .add d x => two "add" (operand aw x) (rm aw d)
  | .adc d x => two "adc" (operand aw x) (rm aw d)
  | .adcx d x => s!"adcx {rm aw x}, {reg d}"
  | .adox d x => s!"adox {rm aw x}, {reg d}"
  | .inc d => one "inc" (rm aw d)
  | .dec d => one "dec" (rm aw d)
  | .neg d => one "neg" (rm aw d)
  | .sub d x => two "sub" (operand aw x) (rm aw d)
  | .sbb d x => two "sbb" (operand aw x) (rm aw d)
  | .cmp a b => two "cmp" (operand aw b) (rm aw a)
  | .xadd l d x => (if l then "lock " else "") ++ two "xadd" (reg x) (rm aw d)
  | .cmpxchg l d x => (if l then "lock " else "") ++ two "cmpxchg" (reg x) (rm aw d)
  | .mul x => one "mul" (rm aw x)
  | .mulx hi lo x => s!"mulx {rm aw x}, {reg lo}, {reg hi}"
  | .imul1 x => one "imul" (rm aw x)
  | .imul none a b => two "imul" (operand aw b) (rm aw a)
  | .imul (some d) a b => s!"imul{s} {operand aw b}, {rm aw a}, {rm aw d}"
  | .div x => one "div" (rm aw x)
  | .idiv x => one "idiv" (rm aw x)
  | .cwtd => "cwtd" | .cltd => "cltd" | .cqto => "cqto"
  | .cbtw => "cbtw" | .cwtl => "cwtl" | .cltq => "cltq"
  | .test a b => two "test" (operand aw b) (rm aw a)
  | .and d x => two "and" (operand aw x) (rm aw d)
  | .not d => one "not" (rm aw d)
  | .or d x => two "or" (operand aw x) (rm aw d)
  | .xor d x => two "xor" (operand aw x) (rm aw d)
  | .shl d c => two "shl" (count c) (rm aw d)
  | .shr d c => two "shr" (count c) (rm aw d)
  | .sar d c => two "sar" (count c) (rm aw d)
  | .shld d x c => s!"shld {count c}, {reg x}, {rm aw d}"
  | .shrd d x c => s!"shrd {count c}, {reg x}, {rm aw d}"
  | .rol d c => two "rol" (count c) (rm aw d)
  | .ror d c => two "ror" (count c) (rm aw d)
  | .rcl d c => two "rcl" (count c) (rm aw d)
  | .rcr d c => two "rcr" (count c) (rm aw d)
  | .bswap d => s!"bswap {reg d}"
  | .bsr d x => s!"bsr{s} {rm aw x}, {reg d}"
  | .repBsf d x => s!"rep bsf{s} {rm aw x}, {reg d}"
  | .btc d x => two "btc" (operand aw x) (rm aw d)
  | .jcc cc l => s!"j{cc} {l}"
  | .jmp t => s!"jmp {target aw t}"
  | .call t => s!"call {target aw t}"
  | .ret => "ret"
  | .leave => "leave"
  | .nop 1 => "nop"
  | .nop n => s!"nop {n}"
  | .nopalign a none => s!".align {a}"
  | .nopalign a (some p) => s!".align {a}, {p}"
  | .ud2 => "ud2"
  | .prefetcht0 a => s!"prefetcht0 {addr aw a}"

def avxOperation {w} (aw : Width) (op : AvxOperation w) : String :=
  let two (mn : String) {w} (d x : AvxRegOrMem w) := s!"{mn} {avxRm aw x}, {avxRm aw d}"
  let three (mn : String) {w} (d a : AvxReg w) (b : AvxRegOrMem w) :=
    s!"{mn} {avxRm aw b}, {avxReg a}, {avxReg d}"
  match op with
  | .movups d x => two "movups" d x
  | .vmovups d x => two "vmovups" d x
  | .movaps d x => two "movaps" d x
  | .movdqa d x => two "movdqa" d x
  | .movdqu d x => two "movdqu" d x
  | .movapd d x => two "movapd" d x
  | .movupd d x => two "movupd" d x
  | .subps d x => two "subps" d x
  | .addps d x => two "addps" d x
  | .vmovaps d x => two "vmovaps" d x
  | .vxorps d a b => three "vxorps" d a b
  | .vaddps d a b => three "vaddps" d a b
  | .vmulps d a b => three "vmulps" d a b
  | .vfmadd231ps d a b => three "vfmadd231ps" d a b
  | .vshufps d a b i => s!"vshufps ${i}, {avxRm aw b}, {avxReg a}, {avxReg d}"
  | .vextractf128 d x i => s!"vextractf128 ${i}, {avxReg x}, {avxReg d}"
  | .vmovhlps d a b => s!"vmovhlps {avxReg b}, {avxReg a}, {avxReg d}"
  | .vmovss d a b => s!"vmovss {avxReg b}, {avxReg a}, {avxReg d}"
  | .vaddss d a b => s!"vaddss {avxReg b}, {avxReg a}, {avxReg d}"
  | .vzeroupper => "vzeroupper"
  | .pxor d x => s!"pxor {avxRm aw x}, {avxReg d}"
  | .pcmpeqb d x => s!"pcmpeqb {avxRm aw x}, {avxReg d}"
  | .pshufd d x i => s!"pshufd ${i}, {avxRm aw x}, {avxReg d}"
  | .pmovmskb d x => s!"pmovmskb {avxReg x}, {reg d}"
  | .movdIn (rw := rw) d x => s!"mov{if rw == .W64 then "q" else "d"} {rm aw x}, {avxReg d}"
  | .movdOut (rw := rw) d x => s!"mov{if rw == .W64 then "q" else "d"} {avxReg x}, {rm aw d}"
  | .addsd d x => s!"addsd {avxRm aw x}, {avxReg d}"
  | .subsd d x => s!"subsd {avxRm aw x}, {avxReg d}"
  | .mulsd d x => s!"mulsd {avxRm aw x}, {avxReg d}"
  | .divsd d x => s!"divsd {avxRm aw x}, {avxReg d}"
  | .ucomisd a b => s!"ucomisd {avxRm aw b}, {avxReg a}"
  | .comisd a b => s!"comisd {avxRm aw b}, {avxReg a}"
  | .cmpsd d x pred => s!"cmpsd ${pred}, {avxRm aw x}, {avxReg d}"
  | .addss d x => s!"addss {avxRm aw x}, {avxReg d}"
  | .subss d x => s!"subss {avxRm aw x}, {avxReg d}"
  | .mulss d x => s!"mulss {avxRm aw x}, {avxReg d}"
  | .divss d x => s!"divss {avxRm aw x}, {avxReg d}"
  | .ucomiss a b => s!"ucomiss {avxRm aw b}, {avxReg a}"
  | .comiss a b => s!"comiss {avxRm aw b}, {avxReg a}"
  | .cmpss d x pred => s!"cmpss ${pred}, {avxRm aw x}, {avxReg d}"
  | .movssRR d x => s!"movss {avxReg x}, {avxReg d}"
  | .movssLoad d a => s!"movss {addr aw a}, {avxReg d}"
  | .movssStore a x => s!"movss {avxReg x}, {addr aw a}"
  | .cvtsi2ss (rw := rw) d x => s!"cvtsi2ss{suffix rw} {rm aw x}, {avxReg d}"
  | .cvttss2si (rw := rw) d x => s!"cvttss2si{suffix rw} {avxRm aw x}, {reg d}"
  | .andps d x => s!"andps {avxRm aw x}, {avxReg d}"
  | .andnps d x => s!"andnps {avxRm aw x}, {avxReg d}"
  | .orps d x => s!"orps {avxRm aw x}, {avxReg d}"
  | .xorps d x => s!"xorps {avxRm aw x}, {avxReg d}"
  | .xorpd d x => s!"xorpd {avxRm aw x}, {avxReg d}"
  | .movsdRR d x => s!"movsd {avxReg x}, {avxReg d}"
  | .movsdLoad d a => s!"movsd {addr aw a}, {avxReg d}"
  | .movsdStore a x => s!"movsd {avxReg x}, {addr aw a}"
  | .cvtsi2sd (rw := rw) d x => s!"cvtsi2sd{suffix rw} {rm aw x}, {avxReg d}"

def instr : Instr → String
  | .regular aw _ op => operation aw op
  | .avx aw _ op => avxOperation aw op

def directive : Directive → String
  | .instr i => instr i
  | .label l => s!"{l}:"
  | d@(.byteArray _) => toString d

end Kraken.X64.ATT

/-- Print a program in AT&T syntax, one directive per line. -/
def Kraken.X64.toATT (p : Program) : String :=
  "\n".intercalate (p.map ATT.directive)
