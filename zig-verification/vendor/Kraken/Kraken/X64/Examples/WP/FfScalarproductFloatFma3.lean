module

public import Kraken.StateCfg
public import Kraken.SeparationMem
import Kraken.FunSpec
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace State.FfScalarproductFloatFma3

def scalarproduct_fma3_prog : Program := parse("
ff_scalarproduct_float_fma3:
    xor %r8,%r8
    vxorps %ymm0,%ymm0,%ymm0
    shl $0x2,%edx
    mov %rdx,%rcx
    cmp $0x20,%rcx
    jl .l16
    cmp $0x40,%rcx
    jl .l32
    vxorps %ymm1,%ymm1,%ymm1
    cmp $0x80,%rcx
    jl .l64
    and $0xffffffffffffff80,%rcx
    vxorps %ymm2,%ymm2,%ymm2
    vxorps %ymm3,%ymm3,%ymm3
.loop128:
    vmovups (%rdi,%r8,1),%ymm4
    vmovups 0x20(%rdi,%r8,1),%ymm5
    vmovups 0x40(%rdi,%r8,1),%ymm6
    vmovups 0x60(%rdi,%r8,1),%ymm7
    vfmadd231ps (%rsi,%r8,1),%ymm4,%ymm0
    vfmadd231ps 0x20(%rsi,%r8,1),%ymm5,%ymm1
    vfmadd231ps 0x40(%rsi,%r8,1),%ymm6,%ymm2
    vfmadd231ps 0x60(%rsi,%r8,1),%ymm7,%ymm3
    sub $0xffffffffffffff80,%r8
    cmp %rcx,%r8
    jl .loop128
    vaddps %ymm2,%ymm0,%ymm0
    vaddps %ymm3,%ymm1,%ymm1
    mov %rdx,%rcx
    and $0x7f,%rcx
    cmp $0x40,%rcx
    jge .l64
    vaddps %ymm1,%ymm0,%ymm0
    cmp $0x20,%rcx
    jge .l32
    vextractf128 $0x1,%ymm0,%xmm2
    vaddps %xmm2,%xmm0,%xmm0
    cmp $0x10,%rcx
    jge .l16
    vmovhlps %xmm0,%xmm1,%xmm1
    vaddps %xmm1,%xmm0,%xmm0
    vmovss %xmm0,%xmm1,%xmm1
    vshufps $0x1,%xmm0,%xmm0,%xmm0
    vaddss %xmm1,%xmm0,%xmm0
    vzeroupper
    jmp done
.l64:
    and $0xffffffffffffffc0,%rcx
    add %r8,%rcx
.loop64:
    vmovups (%rdi,%r8,1),%ymm4
    vmovups 0x20(%rdi,%r8,1),%ymm5
    vfmadd231ps (%rsi,%r8,1),%ymm4,%ymm0
    vfmadd231ps 0x20(%rsi,%r8,1),%ymm5,%ymm1
    add $0x40,%r8
    cmp %rcx,%r8
    jl .loop64
    vaddps %ymm1,%ymm0,%ymm0
    mov %rdx,%rcx
    and $0x3f,%rcx
    cmp $0x20,%rcx
    jge .l32
    vextractf128 $0x1,%ymm0,%xmm2
    vaddps %xmm2,%xmm0,%xmm0
    cmp $0x10,%rcx
    jge .l16
    vmovhlps %xmm0,%xmm1,%xmm1
    vaddps %xmm1,%xmm0,%xmm0
    vmovss %xmm0,%xmm1,%xmm1
    vshufps $0x1,%xmm0,%xmm0,%xmm0
    vaddss %xmm1,%xmm0,%xmm0
    vzeroupper
    jmp done
.l32:
    and $0xffffffffffffffe0,%rcx
    add %r8,%rcx
.loop32:
    vmovups (%rdi,%r8,1),%ymm4
    vfmadd231ps (%rsi,%r8,1),%ymm4,%ymm0
    add $0x20,%r8
    cmp %rcx,%r8
    jl .loop32
    vextractf128 $0x1,%ymm0,%xmm2
    vaddps %xmm2,%xmm0,%xmm0
    mov %rdx,%rcx
    and $0x1f,%rcx
    cmp $0x10,%rcx
    jge .l16
    vmovhlps %xmm0,%xmm1,%xmm1
    vaddps %xmm1,%xmm0,%xmm0
    vmovss %xmm0,%xmm1,%xmm1
    vshufps $0x1,%xmm0,%xmm0,%xmm0
    vaddss %xmm1,%xmm0,%xmm0
    vzeroupper
    jmp done
.l16:
    and $0xfffffffffffffff0,%rcx
    add %r8,%rcx
.loop16:
    vmovaps (%rdi,%r8,1),%xmm1
    vmulps (%rsi,%r8,1),%xmm1,%xmm1
    vaddps %xmm1,%xmm0,%xmm0
    add $0x10,%r8
    cmp %rcx,%r8
    jl .loop16
    vmovhlps %xmm0,%xmm1,%xmm1
    vaddps %xmm1,%xmm0,%xmm0
    vmovss %xmm0,%xmm1,%xmm1
    vshufps $0x1,%xmm0,%xmm0,%xmm0
    vaddss %xmm1,%xmm0,%xmm0
    vzeroupper
done:
    nop
")

def scalarproduct_fma3 : Program := scalarproduct_fma3_prog ++ parse("
    ret
")

theorem scalarproduct_fma3_spec [Host] [FunDecls] (s : MachineData) (len : Nat)
    (h_len_reg : (s.regs.get64 .rdx).take 32 = BitVec.ofNat 32 len)
    (h_len_mod : len % 4 = 0) (h_len_pos : 0 < len) (h_len_bound : len * 4 < 2 ^ 32)
    (h_v1_aligned : isAligned 16 (s.regs.get64 .rdi) = true)
    (R₁ R₂ : DataMem → Prop)
    (h_v1 : s.dmem =⋆ Mem.Blocks [(s.regs.get64 .rdi, len * 4)] ⋆ R₁)
    (h_v2 : s.dmem =⋆ Mem.Blocks [(s.regs.get64 .rsi, len * 4)] ⋆ R₂) :
    WP.wp scalarproduct_fma3_prog (fun _ s' => s'.dmem = s.dmem) (fun _ _ => False) s := by
  vcgen [scalarproduct_fma3_prog]
    invariants
    · fun l s' =>
        match l with
        | "ff_scalarproduct_float_fma3" => s' = s
        | ".loop128" => s'.regs.get64 .rdi = s.regs.get64 .rdi ∧ s'.regs.get64 .rsi = s.regs.get64 .rsi
            ∧ (s'.regs.get64 .rdx).toNat = len * 4 ∧ s'.dmem = s.dmem ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp
            ∧ (s'.regs.get64 .rcx).toNat % 128 = 0 ∧ (s'.regs.get64 .rcx).toNat ≤ len * 4 ∧ len * 4 < (s'.regs.get64 .rcx).toNat + 128 ∧ (s'.regs.get64 .r8).toNat % 128 = 0 ∧ (s'.regs.get64 .r8).toNat < (s'.regs.get64 .rcx).toNat
        | ".l64" => s'.regs.get64 .rdi = s.regs.get64 .rdi ∧ s'.regs.get64 .rsi = s.regs.get64 .rsi
            ∧ (s'.regs.get64 .rdx).toNat = len * 4 ∧ s'.dmem = s.dmem ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp
            ∧ (s'.regs.get64 .rcx).toNat + (s'.regs.get64 .r8).toNat = len * 4 ∧ 64 ≤ (s'.regs.get64 .rcx).toNat ∧ (s'.regs.get64 .rcx).toNat < 128 ∧ (s'.regs.get64 .r8).toNat % 128 = 0
        | ".loop64" => s'.regs.get64 .rdi = s.regs.get64 .rdi ∧ s'.regs.get64 .rsi = s.regs.get64 .rsi
            ∧ (s'.regs.get64 .rdx).toNat = len * 4 ∧ s'.dmem = s.dmem ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp
            ∧ (s'.regs.get64 .rcx).toNat = (s'.regs.get64 .r8).toNat + 64 ∧ (s'.regs.get64 .r8).toNat + 64 ≤ len * 4 ∧ len * 4 < (s'.regs.get64 .r8).toNat + 128 ∧ (s'.regs.get64 .r8).toNat % 64 = 0
        | ".l32" => s'.regs.get64 .rdi = s.regs.get64 .rdi ∧ s'.regs.get64 .rsi = s.regs.get64 .rsi
            ∧ (s'.regs.get64 .rdx).toNat = len * 4 ∧ s'.dmem = s.dmem ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp
            ∧ (s'.regs.get64 .rcx).toNat + (s'.regs.get64 .r8).toNat = len * 4 ∧ 32 ≤ (s'.regs.get64 .rcx).toNat ∧ (s'.regs.get64 .rcx).toNat < 64 ∧ (s'.regs.get64 .r8).toNat % 64 = 0
        | ".loop32" => s'.regs.get64 .rdi = s.regs.get64 .rdi ∧ s'.regs.get64 .rsi = s.regs.get64 .rsi
            ∧ (s'.regs.get64 .rdx).toNat = len * 4 ∧ s'.dmem = s.dmem ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp
            ∧ (s'.regs.get64 .rcx).toNat = (s'.regs.get64 .r8).toNat + 32 ∧ (s'.regs.get64 .r8).toNat + 32 ≤ len * 4 ∧ len * 4 < (s'.regs.get64 .r8).toNat + 64 ∧ (s'.regs.get64 .r8).toNat % 32 = 0
        | ".l16" => s'.regs.get64 .rdi = s.regs.get64 .rdi ∧ s'.regs.get64 .rsi = s.regs.get64 .rsi
            ∧ (s'.regs.get64 .rdx).toNat = len * 4 ∧ s'.dmem = s.dmem ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp
            ∧ (s'.regs.get64 .rcx).toNat + (s'.regs.get64 .r8).toNat = len * 4 ∧ 16 ≤ (s'.regs.get64 .rcx).toNat ∧ (s'.regs.get64 .rcx).toNat < 32 ∧ (s'.regs.get64 .r8).toNat % 32 = 0
        | ".loop16" => s'.regs.get64 .rdi = s.regs.get64 .rdi ∧ s'.regs.get64 .rsi = s.regs.get64 .rsi
            ∧ (s'.regs.get64 .rdx).toNat = len * 4 ∧ s'.dmem = s.dmem ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp
            ∧ (s'.regs.get64 .rcx).toNat = (s'.regs.get64 .r8).toNat + 16 ∧ (s'.regs.get64 .r8).toNat + 16 ≤ len * 4 ∧ len * 4 < (s'.regs.get64 .r8).toNat + 32 ∧ (s'.regs.get64 .r8).toNat % 16 = 0
        | "done" => s'.dmem = s.dmem ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp
        | _ => False
    · fun l s' => match l with
        | "ff_scalarproduct_float_fma3" => 2 ^ 64
        | ".loop128" => (s'.regs.get64 .rcx).toNat - (s'.regs.get64 .r8).toNat
        | _ => 0
    with kfinish

funspec scalarproduct_fma3_funspec "ff_scalarproduct_float_fma3" [Host] [FunDecls]
    [Embeds scalarproduct_fma3]
    (hf : FunDecls.at (label "ff_scalarproduct_float_fma3") = some ⟨scalarproduct_fma3⟩)
    (len : Nat) at s
    requires s.regs.rdx.toBitVec.take 32 = BitVec.ofNat 32 len
      ∧ len % 4 = 0 ∧ 0 < len ∧ len * 4 < 2 ^ 32 ∧ isAligned 16 s.regs.rdi.toBitVec = true
      ∧ Mem.Mapped [(s.regs.rsp.toBitVec - 8#64, 8), (s.regs.rdi.toBitVec, len * 4),
          (s.regs.rsi.toBitVec, len * 4)] s.dmem
    ensures s' => True
    autoframes calling_conv SysV preserves rax rsi rdi r9 r10 r11 := by
  vcgen [scalarproduct_fma3]
    invariants
    · fun {s₀} l s' => match l with
        | "ff_scalarproduct_float_fma3" => s' = s₀
        | ".loop128" => s'.regs.rdx.toNat = len * 4 ∧ s'.dmem = s₀.dmem ∧ Frame.Regs s s'
            ∧ s'.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64
            ∧ s'.regs.rcx.toNat % 128 = 0 ∧ s'.regs.rcx.toNat ≤ len * 4 ∧ len * 4 < s'.regs.rcx.toNat + 128 ∧ s'.regs.r8.toNat % 128 = 0 ∧ s'.regs.r8.toNat < s'.regs.rcx.toNat
        | ".l64" => s'.regs.rdx.toNat = len * 4 ∧ s'.dmem = s₀.dmem ∧ Frame.Regs s s'
            ∧ s'.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64
            ∧ s'.regs.rcx.toNat + s'.regs.r8.toNat = len * 4 ∧ 64 ≤ s'.regs.rcx.toNat ∧ s'.regs.rcx.toNat < 128 ∧ s'.regs.r8.toNat % 128 = 0
        | ".loop64" => s'.regs.rdx.toNat = len * 4 ∧ s'.dmem = s₀.dmem ∧ Frame.Regs s s'
            ∧ s'.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64
            ∧ s'.regs.rcx.toNat = s'.regs.r8.toNat + 64 ∧ s'.regs.r8.toNat + 64 ≤ len * 4 ∧ len * 4 < s'.regs.r8.toNat + 128 ∧ s'.regs.r8.toNat % 64 = 0
        | ".l32" => s'.regs.rdx.toNat = len * 4 ∧ s'.dmem = s₀.dmem ∧ Frame.Regs s s'
            ∧ s'.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64
            ∧ s'.regs.rcx.toNat + s'.regs.r8.toNat = len * 4 ∧ 32 ≤ s'.regs.rcx.toNat ∧ s'.regs.rcx.toNat < 64 ∧ s'.regs.r8.toNat % 64 = 0
        | ".loop32" => s'.regs.rdx.toNat = len * 4 ∧ s'.dmem = s₀.dmem ∧ Frame.Regs s s'
            ∧ s'.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64
            ∧ s'.regs.rcx.toNat = s'.regs.r8.toNat + 32 ∧ s'.regs.r8.toNat + 32 ≤ len * 4 ∧ len * 4 < s'.regs.r8.toNat + 64 ∧ s'.regs.r8.toNat % 32 = 0
        | ".l16" => s'.regs.rdx.toNat = len * 4 ∧ s'.dmem = s₀.dmem ∧ Frame.Regs s s'
            ∧ s'.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64
            ∧ s'.regs.rcx.toNat + s'.regs.r8.toNat = len * 4 ∧ 16 ≤ s'.regs.rcx.toNat ∧ s'.regs.rcx.toNat < 32 ∧ s'.regs.r8.toNat % 32 = 0
        | ".loop16" => s'.regs.rdx.toNat = len * 4 ∧ s'.dmem = s₀.dmem ∧ Frame.Regs s s'
            ∧ s'.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64
            ∧ s'.regs.rcx.toNat = s'.regs.r8.toNat + 16 ∧ s'.regs.r8.toNat + 16 ≤ len * 4 ∧ len * 4 < s'.regs.r8.toNat + 32 ∧ s'.regs.r8.toNat % 16 = 0
        | "done" => s'.dmem = s₀.dmem ∧ Frame.Regs s s' ∧ s'.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64
        | _ => False
    · fun l s' => match l with
        | "ff_scalarproduct_float_fma3" => 2 ^ 64
        | ".loop128" => s'.regs.rcx.toNat - s'.regs.r8.toNat
        | _ => 0
    simp [scalarproduct_fma3_prog] with kfinish

end State.FfScalarproductFloatFma3
