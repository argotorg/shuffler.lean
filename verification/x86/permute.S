/* SPDX-License-Identifier: GPL-3.0-or-later */
/* SysV x86-64: n=EDI, data=RSI, permutation=RDX, target=RCX,
 * used=R8, trace=R9, output=[entry RSP+8].
 * Save five registers in 40 bytes. RBP is untouched. There are no calls.
 * All indexes are written as 32-bit registers before use in an address.
 * Conditional branches use only ZF or SF. Signed range tests operate on
 * bounded nonnegative integers after the explicit high-bit checks.
 */
.intel_syntax noprefix
.text
.globl permute
.type permute, @function
permute:
.Lentry:
    mov r10, qword ptr [rsp + 8]
    push rbx
    push r12
    push r13
    push r14
    push r15
    mov dword ptr [r10], 0
    mov dword ptr [r10 + 4], 0
    mov dword ptr [r10 + 8], 0

    /* Split the unsigned size check so signed subtraction cannot overflow. */
    cmp edi, 0
    jns .Lsize_nonnegative
    jmp .Lreturn_invalid
.Lsize_nonnegative:
    cmp edi, 1025
    jns .Lsize_invalid
.Lif_end:
    cmp edi, 0
    jne .Lif_end10_preheader
    jmp .Lreturn_done
.Lsize_invalid:
    jmp .Lreturn_invalid

.Lif_end10_preheader:
    xor eax, eax
.Lif_end10:
    mov dword ptr [r8 + rax * 4], 0
    add eax, 1
    cmp eax, edi
    jne .Lif_end10

.Lif_end17_preheader:
    xor eax, eax
.Lif_end17:
    mov r11d, dword ptr [rdx + rax * 4]
    cmp r11d, 0
    jns .Ldestination_nonnegative
    jmp .Lreturn_invalid
.Ldestination_nonnegative:
    cmp r11d, edi
    jns .Lvalidation_invalid
.Lif_end23:
    mov ebx, dword ptr [r8 + r11 * 4]
    cmp ebx, 0
    jne .Lvalidation_invalid
.Lif_end29:
    mov dword ptr [r8 + r11 * 4], 1
    mov ebx, dword ptr [rsi + rax * 4]
    mov dword ptr [rcx + r11 * 4], ebx
    add eax, 1
    cmp eax, edi
    jne .Lif_end17
    jmp .Lif_end43_preheader
.Lvalidation_invalid:
    jmp .Lreturn_invalid

.Lif_end43_preheader:
    xor eax, eax
.Lif_end43:
    mov r11d, dword ptr [rsi + rax * 4]
    mov ebx, dword ptr [rcx + rax * 4]
    cmp r11d, ebx
    mov ebx, 0
    jne .Lif_end57
.Lif_then49:
    mov dword ptr [rdx + rax * 4], eax
    mov ebx, 1
.Lif_end57:
    mov dword ptr [r8 + rax * 4], ebx
    add eax, 1
    cmp eax, edi
    jne .Lif_end43

.Lif_end65_preheader:
    xor eax, eax
.Lif_end65:
    mov r11d, dword ptr [rsi + rax * 4]
    mov ebx, dword ptr [rcx + rax * 4]
    cmp r11d, ebx
    jne .Lsearch_preheader
    jmp .Lif_end103
.Lsearch_preheader:
    xor r13d, r13d
.Lif_end77:
    mov ebx, dword ptr [r8 + r13 * 4]
    cmp ebx, 0
    jne .Lif_end91
.Lif_then81:
    mov ebx, dword ptr [rcx + r13 * 4]
    cmp r11d, ebx
    jne .Lif_end91
    jmp .Lwhile_end93
.Lif_end91:
    add r13d, 1
    cmp r13d, edi
    jne .Lif_end77
.Lwhile_end93:
    cmp r13d, edi
    jne .Lif_end97
    jmp .Lreturn_invalid
.Lif_end97:
    mov dword ptr [rdx + rax * 4], r13d
    mov dword ptr [r8 + r13 * 4], 1
.Lif_end103:
    add eax, 1
    cmp eax, edi
    jne .Lif_end65

.Lwhile_end105:
    mov r12d, edi
    sub r12d, 1
    mov r15d, edi
    add r15d, edi
.Lwhile_cond106:
    mov r13d, dword ptr [rdx + r12 * 4]
    cmp r13d, r12d
    jne .Lif_end133
.Lwhile_cond112:
    cmp r13d, 0
    jne .Lif_end117
    jmp .Lwhile_end125
.Lif_end117:
    sub r13d, 1
    mov ebx, dword ptr [rdx + r13 * 4]
    cmp ebx, r13d
    jne .Lwhile_end125
    cmp r13d, 0
    jne .Lif_end117
.Lwhile_end125:
    mov ebx, dword ptr [rdx + r13 * 4]
    cmp ebx, r13d
    jne .Lif_end133
    jmp .Lreturn_done

.Lif_end133:
    mov eax, dword ptr [rsi + r13 * 4]
    mov ebx, dword ptr [rsi + r12 * 4]
    cmp eax, ebx
    jne .Lif_then139
    jmp .Lif_end169
.Lif_then139:
    mov r14d, r12d
    sub r14d, r13d
    cmp r14d, 17
    jns .Lif_then142
.Lif_end147:
    mov r11d, dword ptr [r10]
    cmp r11d, r15d
    jns .Lcapacity_invalid
.Lif_end153:
    mov dword ptr [rsi + r13 * 4], ebx
    mov dword ptr [rsi + r12 * 4], eax
    mov dword ptr [r9 + r11 * 4], r14d
    add r11d, 1
    mov dword ptr [r10], r11d
    jmp .Lif_end169
.Lif_then142:
    mov dword ptr [r10 + 4], r13d
    sub r14d, 16
    mov dword ptr [r10 + 8], r14d
    mov eax, 1
    jmp .Lcleanup
.Lcapacity_invalid:
    jmp .Lreturn_invalid

.Lif_end169:
    mov eax, dword ptr [rdx + r13 * 4]
    mov ebx, dword ptr [rdx + r12 * 4]
    mov dword ptr [rdx + r13 * 4], ebx
    mov dword ptr [rdx + r12 * 4], eax
    jmp .Lwhile_cond106

.Lreturn_done:
    xor eax, eax
    jmp .Lcleanup
.Lreturn_invalid:
    mov eax, 2
.Lcleanup:
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbx
    ret
.size permute, .-permute
.section .note.GNU-stack,"",@progbits
