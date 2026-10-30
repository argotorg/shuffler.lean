	.file	"build_bottom_up.cpp"
	.text
	.align 2
	.type	_ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot, @function
_ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot:
	movq	%rsi, %rdx
	shrq	$32, %rdx
	movl	$0, %eax
	testb	%dl, %dl
	jne	.LB1
	movq	%rsi, %rdx
	shrq	$40, %rdx
	testb	%dl, %dl
	je	.LB1
	movl	%esi, %esi
	movq	16(%rdi), %rax
	cmpb	$0, (%rax,%rsi)
	setne	%al
.LB1:
	ret
	.size	_ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot, .-_ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot
	.align 2
	.type	_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot, @function
_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot:
	movq	32(%rdi), %rax
	.p2align 5
.LB6:
	testq	%rax, %rax
	je	.LB10
	subq	$1, %rax
	movq	24(%rdi), %rdx
	movq	%rsi, %rcx
	xorq	(%rdx,%rax,8), %rcx
	movq	%rcx, %rdx
	salq	$16, %rdx
	jne	.LB6
	ret
.LB10:
	movq	$-1, %rax
.LB7:
	ret
	.size	_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot, .-_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission4pushE9StackSlot11StackOffset, @function
_ZN12_GLOBAL__N_18Emission4pushE9StackSlot11StackOffset:
	movq	%rdi, %rax
	movq	%rsi, %rcx
	movq	%rdx, %rdi
	movq	%rsi, %r9
	shrq	$32, %r9
	movq	%rsi, %r8
	shrq	$40, %r8
	movq	24(%rax), %rsi
	movq	32(%rax), %rdx
	leaq	1(%rdx), %r10
	movq	%r10, 32(%rax)
	movq	%rcx, (%rsi,%rdx,8)
	movq	48(%rax), %rdx
	leaq	1(%rdx), %rsi
	movq	%rsi, 48(%rax)
	leaq	(%rdx,%rdx,2), %rdx
	salq	$2, %rdx
	addq	40(%rax), %rdx
	testb	%r8b, %r8b
	setne	%sil
	testb	%r9b, %r9b
	sete	%r10b
	andl	%r10d, %esi
	addl	$3, %esi
	movb	%sil, (%rdx)
	movb	$0, 1(%rdx)
	movl	%ecx, 4(%rdx)
	movb	%r9b, 8(%rdx)
	movb	%r8b, 9(%rdx)
	movl	$2, %edx
	cmpq	$-1, 8248(%rax,%rdi,8)
	jne	.LB11
	movq	32(%rax), %rcx
	leaq	-1(%rcx), %rdx
	movq	%rdi, 56(%rax,%rdx,8)
	movq	%rdx, 8248(%rax,%rdi,8)
	movl	$0, %edx
.LB11:
	movl	%edx, %eax
	ret
	.size	_ZN12_GLOBAL__N_18Emission4pushE9StackSlot11StackOffset, .-_ZN12_GLOBAL__N_18Emission4pushE9StackSlot11StackOffset
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission3dupE11StackOffsetS1_, @function
_ZN12_GLOBAL__N_18Emission3dupE11StackOffsetS1_:
	movq	%rdi, %rax
	movq	%rdx, %rcx
	movq	24(%rdi), %rdi
	movl	$2, %edx
	cmpb	$3, 4(%rdi,%rsi,8)
	je	.LB14
	movq	32(%rax), %rdi
	subq	%rsi, %rdi
	movq	48(%rax), %rdx
	leaq	1(%rdx), %r8
	movq	%r8, 48(%rax)
	leaq	(%rdx,%rdx,2), %rdx
	salq	$2, %rdx
	addq	40(%rax), %rdx
	movb	$1, (%rdx)
	movb	%dil, 1(%rdx)
	movl	$0, 4(%rdx)
	movb	$1, 8(%rdx)
	movb	$5, 9(%rdx)
	movq	24(%rax), %rdx
	movq	32(%rax), %rdi
	movq	(%rdx,%rsi,8), %rsi
	movq	%rsi, (%rdx,%rdi,8)
	movq	32(%rax), %rsi
	leaq	1(%rsi), %rdx
	movq	%rdx, 32(%rax)
	movl	$2, %edx
	cmpq	$-1, 8248(%rax,%rcx,8)
	jne	.LB14
	movq	%rcx, 56(%rax,%rsi,8)
	movq	%rsi, 8248(%rax,%rcx,8)
	movl	$0, %edx
.LB14:
	movl	%edx, %eax
	ret
	.size	_ZN12_GLOBAL__N_18Emission3dupE11StackOffsetS1_, .-_ZN12_GLOBAL__N_18Emission3dupE11StackOffsetS1_
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission7produceE11StackOffset, @function
_ZN12_GLOBAL__N_18Emission7produceE11StackOffset:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$8, %rsp
	movq	%rdi, %rbx
	movq	%rsi, %r12
	leaq	0(,%rsi,8), %r14
	movq	%r14, %rdx
	addq	(%rdi), %rdx
	movzbl	5(%rdx), %r15d
	movzbl	4(%rdx), %r13d
	movzbl	%r15b, %eax
	salq	$40, %rax
	movabsq	$-280375465082881, %rbp
	andq	(%rdx), %rbp
	orq	%rax, %rbp
	movq	%rbp, %rsi
	call	_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot
	movq	%rax, (%rsp)
	cmpb	$1, %r13b
	je	.LB33
	movq	(%rsp), %rax
	cmpq	$-1, %rax
	je	.LB21
	notq	%rax
	addq	32(%rbx), %rax
	cmpq	$15, %rax
	jbe	.LB22
.LB21:
	cmpb	$2, %r13b
	je	.LB23
	testb	%r15b, %r15b
	jne	.LB34
.LB23:
	movq	%r12, %rdx
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission4pushE9StackSlot11StackOffset
.LB20:
	testb	%al, %al
	jne	.LB18
	movq	32(%rbx), %rcx
	leaq	-1(%rcx), %rdx
	cmpq	%rdx, 8248(%rbx,%r14)
	jne	.LB29
	subq	$1, 16440(%rbx)
.LB18:
	addq	$8, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB33:
	movq	%r12, %rdx
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission4pushE9StackSlot11StackOffset
	jmp	.LB20
.LB22:
	movq	%r12, %rdx
	movq	(%rsp), %rsi
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission3dupE11StackOffsetS1_
	jmp	.LB20
.LB34:
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	call	_ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot
	testb	%al, %al
	jne	.LB23
	movl	$2, %eax
	cmpq	$-1, (%rsp)
	je	.LB18
	movq	$-16, %rdx
	movq	(%rsp), %rcx
	subq	%rcx, %rdx
	movl	$2, %eax
	addq	32(%rbx), %rdx
	je	.LB18
	movq	%rcx, 16448(%rbx)
	movq	%rdx, 16456(%rbx)
	movl	$1, %eax
	jmp	.LB18
.LB29:
	movl	$2, %eax
	jmp	.LB18
	.size	_ZN12_GLOBAL__N_18Emission7produceE11StackOffset, .-_ZN12_GLOBAL__N_18Emission7produceE11StackOffset
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset, @function
_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset:
	movq	%rdi, %rax
	movq	%rsi, %rdx
	movq	32(%rdi), %rsi
	movl	$2, %ecx
	cmpq	%rsi, %rdx
	jnb	.LB35
	leaq	0(,%rdx,8), %rdi
	cmpq	56(%rax,%rdx,8), %rdx
	je	.LB35
	movq	%rsi, %rcx
	subq	%rdx, %rcx
	leaq	-2(%rcx), %r8
	movl	$2, %ecx
	cmpq	$15, %r8
	ja	.LB35
	movq	24(%rax), %r8
	leaq	(%r8,%rdi), %rcx
	movl	(%rcx), %r10d
	movzbl	4(%rcx), %r9d
	movzbl	5(%rcx), %edi
	movq	-8(%r8,%rsi,8), %rsi
	movq	%rsi, (%rcx)
	movq	32(%rax), %rsi
	movq	24(%rax), %rcx
	leaq	-8(%rcx,%rsi,8), %rcx
	movl	%r10d, (%rcx)
	movb	%r9b, 4(%rcx)
	movb	%dil, 5(%rcx)
	movq	%rdx, %rsi
	notq	%rsi
	addq	32(%rax), %rsi
	movq	48(%rax), %rcx
	leaq	1(%rcx), %rdi
	movq	%rdi, 48(%rax)
	leaq	(%rcx,%rcx,2), %rcx
	salq	$2, %rcx
	addq	40(%rax), %rcx
	movb	$0, (%rcx)
	movb	%sil, 1(%rcx)
	movl	$0, 4(%rcx)
	movb	$1, 8(%rcx)
	movb	$5, 9(%rcx)
	movq	32(%rax), %rdi
	leaq	-1(%rdi), %rcx
	movq	56(%rax,%rdx,8), %rsi
	movq	56(%rax,%rcx,8), %rdi
	movq	%rdi, 56(%rax,%rdx,8)
	movq	%rsi, 56(%rax,%rcx,8)
	movq	56(%rax,%rdx,8), %rsi
	cmpq	$-1, %rsi
	je	.LB37
	movq	%rdx, 8248(%rax,%rsi,8)
.LB37:
	movq	56(%rax,%rcx,8), %rdx
	cmpq	$-1, %rdx
	je	.LB38
	movq	%rcx, 8248(%rax,%rdx,8)
.LB38:
	movl	$0, %ecx
.LB35:
	movl	%ecx, %eax
	ret
	.size	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset, .-_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset, @function
_ZN12_GLOBAL__N_18Emission8generateE11StackOffset:
	movl	$2, %eax
	cmpq	8(%rdi), %rsi
	jnb	.LB49
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movq	%rsi, %rbx
	call	_ZN12_GLOBAL__N_18Emission7produceE11StackOffset
	testb	%al, %al
	jne	.LB42
	movq	32(%rbp), %rdx
	leaq	1(%rbx), %rcx
	cmpq	%rdx, %rcx
	jnb	.LB42
	cmpq	%rbx, 56(%rbp,%rbx,8)
	je	.LB42
	movq	24(%rbp), %rdi
	leaq	-1(%rdx), %rsi
	movq	(%rdi,%rsi,8), %rcx
	xorq	(%rdi,%rbx,8), %rcx
	salq	$16, %rcx
	je	.LB52
	subq	%rbx, %rdx
	subq	$1, %rdx
	cmpq	$16, %rdx
	jbe	.LB53
.LB42:
	popq	%rbx
	popq	%rbp
	ret
.LB52:
	movq	56(%rbp,%rbx,8), %rdx
	movq	56(%rbp,%rsi,8), %rcx
	movq	%rcx, 56(%rbp,%rbx,8)
	movq	%rdx, 56(%rbp,%rsi,8)
	movq	56(%rbp,%rbx,8), %rdx
	cmpq	$-1, %rdx
	je	.LB45
	movq	%rbx, 8248(%rbp,%rdx,8)
.LB45:
	movq	56(%rbp,%rsi,8), %rdx
	cmpq	$-1, %rdx
	je	.LB42
	movq	%rsi, 8248(%rbp,%rdx,8)
	jmp	.LB42
.LB53:
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	jmp	.LB42
.LB49:
	ret
	.size	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset, .-_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE, @function
_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE:
	movq	32(%rdi), %rdx
	movl	$0, %eax
	testq	%rdx, %rdx
	je	.LB92
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$8216, %rsp
	movq	%rdi, %r13
	movq	%rsi, %r14
	leaq	16(%rsp), %rax
	leaq	(%rax,%rdx,8), %rdx
	.p2align 4
.LB56:
	movq	$-1, (%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB56
	movq	$8, (%rsp)
	movl	$1, %r15d
	movl	$0, %ebx
	leaq	16(%rsp), %rbp
	jmp	.LB69
	.p2align 5
.LB60:
	addq	$8, %rax
	cmpq	%rax, (%rsp)
	je	.LB95
.LB58:
	movq	8(%rsp), %rdi
	movq	%r12, %rdx
	xorq	(%rdi,%rax), %rdx
	salq	$16, %rdx
	jne	.LB60
	movq	(%r14,%rax), %rdx
	movq	%rbx, 16(%rsp,%rdx,8)
	jmp	.LB60
.LB95:
	movl	$0, %ecx
	movl	$0, %eax
	jmp	.LB68
.LB62:
	movq	32(%r13), %rsi
	cmpq	%rsi, %rax
	jb	.LB66
.LB63:
	movl	$2, %eax
.LB54:
	addq	$8216, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
	.p2align 4
.LB64:
	addq	$1, %rax
	cmpq	%rax, %rsi
	je	.LB63
.LB66:
	cmpq	0(%rbp,%rax,8), %rbx
	jne	.LB64
	movq	%r12, %rdx
	xorq	(%rdi,%rax,8), %rdx
	salq	$16, %rdx
	je	.LB64
	cmpq	%rsi, %rax
	jnb	.LB63
	movq	%rax, (%r14,%rcx,8)
	addq	$1, %rax
.LB61:
	addq	$1, %rcx
	cmpq	%rcx, %r15
	je	.LB59
.LB68:
	movq	24(%r13), %rdi
	movq	%r12, %rdx
	xorq	(%rdi,%rcx,8), %rdx
	salq	$16, %rdx
	jne	.LB61
	cmpq	0(%rbp,%rcx,8), %rbx
	jne	.LB62
	movq	%rcx, (%r14,%rcx,8)
	jmp	.LB61
.LB59:
	movq	32(%r13), %rcx
	addq	$1, %rbx
	addq	$1, %r15
	addq	$8, (%rsp)
	cmpq	%rcx, %rbx
	jnb	.LB96
.LB69:
	movq	24(%r13), %rax
	movq	%rax, 8(%rsp)
	movq	(%rax,%rbx,8), %r12
	movq	%r12, %rsi
	movq	%r13, %rdi
	call	_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot
	cmpq	%rbx, %rax
	jne	.LB59
	movl	$0, %eax
	jmp	.LB58
.LB96:
	leaq	-1(%rcx), %rsi
	jmp	.LB82
.LB84:
	movq	%rsi, %rdx
.LB70:
	testq	%rdx, %rdx
	je	.LB97
	leaq	-1(%rdx), %rax
	cmpq	(%r14,%rax,8), %rax
	jne	.LB72
	movq	%rax, %rdx
	jmp	.LB70
.LB97:
	movl	$0, %eax
	jmp	.LB54
.LB72:
	cmpq	%rcx, %rdx
	jne	.LB71
	movl	$0, %eax
	jmp	.LB54
.LB98:
	movq	56(%r13,%rax,8), %rdx
	movq	56(%r13,%rsi,8), %rdi
	movq	%rdi, 56(%r13,%rax,8)
	movq	%rdx, 56(%r13,%rsi,8)
	movq	56(%r13,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB76
	movq	%rax, 8248(%r13,%rdx,8)
.LB76:
	movq	56(%r13,%rsi,8), %rdx
	cmpq	$-1, %rdx
	je	.LB78
	movq	%rsi, 8248(%r13,%rdx,8)
.LB78:
	movq	(%r14,%rax,8), %rdx
	movq	(%r14,%rsi,8), %rdi
	movq	%rdi, (%r14,%rax,8)
	movq	%rdx, (%r14,%rsi,8)
.LB82:
	movq	(%r14,%rsi,8), %rax
	cmpq	%rsi, %rax
	je	.LB84
.LB71:
	movq	24(%r13), %rdx
	movq	32(%r13), %rdi
	leaq	-8(%rdx,%rdi,8), %r9
	leaq	(%rdx,%rax,8), %r8
	movq	(%r8), %rdx
	xorq	(%r9), %rdx
	salq	$16, %rdx
	je	.LB98
	subq	%rax, %rdi
	leaq	-1(%rdi), %rdx
	cmpq	$16, %rdx
	ja	.LB99
	movl	(%r8), %r11d
	movzbl	4(%r8), %r10d
	movzbl	5(%r8), %edi
	movq	(%r9), %rdx
	movq	%rdx, (%r8)
	movq	32(%r13), %r8
	movq	24(%r13), %rdx
	leaq	-8(%rdx,%r8,8), %rdx
	movl	%r11d, (%rdx)
	movb	%r10b, 4(%rdx)
	movb	%dil, 5(%rdx)
	movq	%rax, %rdi
	notq	%rdi
	addq	32(%r13), %rdi
	movq	48(%r13), %rdx
	leaq	1(%rdx), %r8
	movq	%r8, 48(%r13)
	leaq	(%rdx,%rdx,2), %rdx
	salq	$2, %rdx
	addq	40(%r13), %rdx
	movb	$0, (%rdx)
	movb	%dil, 1(%rdx)
	movl	$0, 4(%rdx)
	movb	$1, 8(%rdx)
	movb	$5, 9(%rdx)
	movq	56(%r13,%rax,8), %rdx
	movq	56(%r13,%rsi,8), %rdi
	movq	%rdi, 56(%r13,%rax,8)
	movq	%rdx, 56(%r13,%rsi,8)
	movq	56(%r13,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB80
	movq	%rax, 8248(%r13,%rdx,8)
.LB80:
	movq	56(%r13,%rsi,8), %rdx
	cmpq	$-1, %rdx
	je	.LB78
	movq	%rsi, 8248(%r13,%rdx,8)
	jmp	.LB78
.LB99:
	movq	%rax, 16448(%r13)
	subq	$17, %rdi
	movq	%rdi, 16456(%r13)
	movl	$1, %eax
	jmp	.LB54
.LB92:
	ret
	.size	_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE, .-_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv, @function
_ZN12_GLOBAL__N_18Emission13buildBottomUpEv:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$8216, %rsp
	movq	%rdi, %r12
	movq	8(%rdi), %r13
	testq	%r13, %r13
	je	.LB101
	movl	$0, %r14d
	jmp	.LB139
.LB104:
	movl	$2, %eax
	cmpq	%r13, %r15
	jne	.LB100
.LB109:
	movq	56(%r12,%rdx,8), %rax
	cmpq	$-1, %rax
	je	.LB108
	movq	%rax, 16(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rdx, %r13
	jne	.LB109
	leaq	16(%rsp), %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE
	jmp	.LB100
.LB108:
	movl	$2, %eax
	jmp	.LB100
.LB161:
	movq	%rax, 16448(%r12)
	subq	$16, %rcx
	movq	%rcx, 16456(%r12)
	movl	$1, %eax
	jmp	.LB100
	.p2align 5
.LB115:
	addq	$1, %rbx
	cmpq	%r13, %rbx
	je	.LB160
.LB105:
	cmpq	$-1, 8248(%r12,%rbx,8)
	jne	.LB115
	movq	(%r12), %rax
	leaq	(%rax,%rbx,8), %rax
	movq	(%rax), %rbp
	movzbl	4(%rax), %edx
	cmpb	$1, %dl
	je	.LB115
	movzbl	5(%rax), %ecx
	movzbl	%dl, %eax
	salq	$32, %rax
	movabsq	$-1095216660481, %rsi
	andq	%rsi, %rbp
	orq	%rax, %rbp
	testb	%cl, %cl
	je	.LB115
	cmpb	$2, %dl
	je	.LB115
	movzbl	%cl, %ecx
	salq	$40, %rcx
	movabsq	$-280375465082881, %rax
	andq	%rax, %rbp
	orq	%rcx, %rbp
	movq	%rbp, %rsi
	movq	%r12, %rdi
	call	_ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot
	testb	%al, %al
	jne	.LB115
	movq	%rbp, %rsi
	movq	%r12, %rdi
	call	_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot
	cmpq	$-1, %rax
	je	.LB115
	movq	%r15, %rcx
	subq	%rax, %rcx
	leaq	-1(%rcx), %rdx
	cmpq	$15, %rdx
	ja	.LB161
	cmpq	%r14, %rax
	sete	%al
	cmpq	$15, %rdx
	setne	%dl
	orb	%dl, %al
	jne	.LB115
	movq	8(%rsp), %rax
	cmpq	$-1, %rax
	cmove	%rbx, %rax
	movq	%rax, 8(%rsp)
	jmp	.LB115
.LB160:
	movq	8(%rsp), %rdi
	cmpq	$-1, %rdi
	sete	%al
	cmpq	%r14, %rdi
	je	.LB106
	testb	%al, %al
	je	.LB162
.LB106:
	cmpq	%r13, %r15
	setb	%cl
	cmpq	%r15, %r14
	setb	%dl
	testb	%dl, %cl
	je	.LB117
	testb	%al, %al
	jne	.LB163
.LB117:
	leaq	0(,%r14,8), %rbx
	movq	8248(%r12,%rbx), %rdx
	cmpq	$-1, %rdx
	je	.LB121
	cmpq	%r14, %rdx
	jb	.LB164
	movq	24(%r12), %rcx
	movq	(%rcx,%rdx,8), %rsi
	movq	%rsi, %rdi
	xorq	(%rcx,%r14,8), %rdi
	movq	%r14, %rax
	salq	$16, %rdi
	jne	.LB165
.LB129:
	movq	%rax, %rsi
	movq	56(%r12,%rax,8), %rcx
	movq	56(%r12,%rdx,8), %rdi
	movq	%rdi, 56(%r12,%rax,8)
	movq	%rcx, 56(%r12,%rdx,8)
	movq	56(%r12,%rax,8), %rcx
	cmpq	$-1, %rcx
	je	.LB130
	movq	%rax, 8248(%r12,%rcx,8)
.LB130:
	movq	56(%r12,%rdx,8), %rcx
	cmpq	$-1, %rcx
	je	.LB131
	movq	%rdx, 8248(%r12,%rcx,8)
.LB131:
	cmpq	%rax, %r14
	je	.LB146
	leaq	-1(%r15), %rdx
	cmpq	%rax, %rdx
	je	.LB132
	subq	%rax, %r15
	leaq	-1(%r15), %rdx
	cmpq	$16, %rdx
	ja	.LB166
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	testb	%al, %al
	jne	.LB100
.LB132:
	movq	32(%r12), %rax
	cmpq	%rax, %r14
	jnb	.LB148
	cmpq	%r14, 56(%r12,%rbx)
	jne	.LB134
	movl	$2, %eax
.LB100:
	addq	$8216, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB162:
	movq	%r15, %rax
	subq	%r14, %rax
	cmpq	$15, %rax
	ja	.LB117
	movq	8(%rsp), %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
	testb	%al, %al
	jne	.LB100
	subq	$1, %r14
	jmp	.LB137
.LB163:
	cmpq	$-1, 8248(%r12,%r15,8)
	jne	.LB117
	movq	%r15, %rax
	subq	%r14, %rax
	cmpq	$15, %rax
	ja	.LB117
	movq	%r15, %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
	testb	%al, %al
	jne	.LB100
	subq	$1, %r14
	jmp	.LB137
.LB121:
	movq	%r14, %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
	testb	%al, %al
	jne	.LB100
	movq	32(%r12), %rax
	cmpq	%rax, %r14
	jnb	.LB147
	cmpq	%r14, 56(%r12,%rbx)
	je	.LB137
.LB134:
	leaq	-1(%rax), %rdx
	cmpq	%r14, %rdx
	je	.LB137
	subq	%r14, %rax
	leaq	-1(%rax), %rdx
	cmpq	$16, %rdx
	ja	.LB167
	movq	%r14, %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	testb	%al, %al
	je	.LB137
	jmp	.LB100
.LB165:
	leaq	-1(%r15), %rax
	cmpq	%rax, %rdx
	jb	.LB128
	movq	%rdx, %rax
	jmp	.LB129
	.p2align 5
.LB126:
	subq	$1, %rax
	cmpq	%rax, %rdx
	jnb	.LB168
.LB128:
	movq	%rsi, %rdi
	xorq	(%rcx,%rax,8), %rdi
	salq	$16, %rdi
	jne	.LB126
	cmpq	%rax, 56(%r12,%rax,8)
	je	.LB126
	xorq	(%rcx,%rax,8), %rsi
	salq	$16, %rsi
	je	.LB129
	movl	$2, %eax
	jmp	.LB100
.LB168:
	movq	%rdx, %rax
	jmp	.LB129
.LB166:
	movq	%rax, 16448(%r12)
	subq	$17, %r15
	movq	%r15, 16456(%r12)
	movl	$1, %eax
	jmp	.LB100
.LB167:
	movq	%r14, 16448(%r12)
	subq	$17, %rax
	movq	%rax, 16456(%r12)
	movl	$1, %eax
	jmp	.LB100
.LB146:
	movq	%rax, %r14
.LB137:
	addq	$1, %r14
	movq	8(%r12), %r13
	cmpq	%r13, %r14
	jnb	.LB101
.LB139:
	movq	32(%r12), %r15
	cmpq	%r15, %r14
	jnb	.LB102
	cmpq	%r14, 56(%r12,%r14,8)
	je	.LB137
.LB102:
	movq	16440(%r12), %rdx
	testq	%rdx, %rdx
	je	.LB104
	movq	%r14, %rbx
	movq	$-1, 8(%rsp)
	movl	$1, %eax
	cmpq	%r13, %r14
	jb	.LB105
	jmp	.LB106
.LB164:
	movl	$2, %eax
	jmp	.LB100
.LB147:
	movl	$2, %eax
	jmp	.LB100
.LB148:
	movl	$2, %eax
	jmp	.LB100
.LB101:
	cmpq	%r13, 32(%r12)
	setne	%al
	addl	%eax, %eax
	jmp	.LB100
	.size	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv, .-_ZN12_GLOBAL__N_18Emission13buildBottomUpEv
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission3popEv, @function
_ZN12_GLOBAL__N_18Emission3popEv:
	movq	32(%rdi), %rax
	movl	$2, %edx
	testq	%rax, %rax
	je	.LB169
	leaq	-1(%rax), %rdx
	movq	%rdx, 32(%rdi)
	movq	48(%rdi), %rax
	leaq	1(%rax), %rcx
	movq	%rcx, 48(%rdi)
	leaq	(%rax,%rax,2), %rax
	salq	$2, %rax
	addq	40(%rdi), %rax
	movb	$2, (%rax)
	movb	$0, 1(%rax)
	movl	$0, 4(%rax)
	movb	$1, 8(%rax)
	movb	$5, 9(%rax)
	movq	56(%rdi,%rdx,8), %rax
	cmpq	$-1, %rax
	je	.LB171
	movq	$-1, 8248(%rdi,%rax,8)
.LB171:
	movl	$0, %edx
.LB169:
	movl	%edx, %eax
	ret
	.size	_ZN12_GLOBAL__N_18Emission3popEv, .-_ZN12_GLOBAL__N_18Emission3popEv
	.globl	build_bottom_up
	.type	build_bottom_up, @function
build_bottom_up:
	cmpq	%rdi, %rsi
	jb	.LB192
	movq	%rdx, %r10
	cmpq	$1024, %rsi
	ja	.LB192
	subq	$32872, %rsp
	testq	%rdi, %rdi
	je	.LB175
	movl	$0, %eax
	.p2align 5
.LB176:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB176
	testq	%rsi, %rsi
	je	.LB191
.LB190:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%rsi,8), %rdx
	.p2align 5
.LB178:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB178
	testq	%rdi, %rdi
	je	.LB179
.LB191:
	movl	$0, %eax
	jmp	.LB181
	.p2align 5
.LB180:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rdi
	je	.LB205
	movq	%rdx, %rax
.LB181:
	movq	(%r8,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB180
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	jmp	.LB180
.LB205:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	%rdx, 32(%rsp)
	movq	32880(%rsp), %rdi
	movq	%rdi, 40(%rsp)
	movq	$0, 48(%rsp)
	movl	$0, %edx
	addq	$1, %rax
	.p2align 5
.LB182:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB182
.LB189:
	testq	%rsi, %rsi
	je	.LB183
	leaq	0(,%rsi,8), %rdx
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB184:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB184
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rdx
	jmp	.LB186
	.p2align 5
.LB185:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB188
.LB186:
	cmpq	$-1, 8248(%rax)
	jne	.LB185
	addq	$1, 16440(%rsp)
	jmp	.LB185
.LB206:
	movq	32888(%rsp), %rax
	movq	$0, (%rax)
	movq	$0, 8(%rax)
	movq	48(%rsp), %rdx
	jmp	.LB173
.LB187:
	movq	16448(%rsp), %rax
	movq	32888(%rsp), %rsi
	movq	%rax, (%rsi)
	movq	16456(%rsp), %rax
	movq	%rax, 8(%rsi)
	movq	48(%rsp), %rdx
	jmp	.LB173
.LB192:
	movq	$-2, %rdx
	movq	%rdx, %rax
	ret
.LB183:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB188:
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv
	cmpb	$1, %al
	je	.LB187
	movq	$-2, %rdx
	cmpb	$2, %al
	jne	.LB206
.LB173:
	movq	%rdx, %rax
	addq	$32872, %rsp
	ret
.LB175:
	testq	%rsi, %rsi
	jne	.LB190
.LB179:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32880(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB189
	.size	build_bottom_up, .-build_bottom_up
	.globl	emission_pop
	.type	emission_pop, @function
emission_pop:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$32872, %rsp
	movq	32928(%rsp), %r13
	movq	32952(%rsp), %r15
	cmpq	$1024, %rdi
	ja	.LB231
	movq	%rdi, %rbx
	movq	%rsi, %r12
	movq	%rdx, %rsi
	cmpq	$1024, %r12
	ja	.LB231
	testq	%rdi, %rdi
	je	.LB209
	movl	$0, %eax
	.p2align 5
.LB210:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rbx
	jne	.LB210
	testq	%r12, %r12
	je	.LB230
.LB229:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%r12,8), %rdx
	.p2align 5
.LB212:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB212
	testq	%rbx, %rbx
	je	.LB213
.LB230:
	movl	$0, %eax
	jmp	.LB215
	.p2align 5
.LB214:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rbx
	je	.LB244
	movq	%rdx, %rax
.LB215:
	movq	(%r8,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB214
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	jmp	.LB214
.LB244:
	movq	%rcx, (%rsp)
	movq	%r12, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%rsi, 24(%rsp)
	movq	%rdx, 32(%rsp)
	movq	32936(%rsp), %rdi
	movq	%rdi, 40(%rsp)
	movq	$0, 48(%rsp)
	movl	$0, %edx
	addq	$1, %rax
	.p2align 5
.LB216:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB216
.LB228:
	testq	%r12, %r12
	je	.LB217
	leaq	0(,%r12,8), %rdx
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB218:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB218
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rdx
	jmp	.LB220
	.p2align 5
.LB219:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB227
.LB220:
	cmpq	$-1, 8248(%rax)
	jne	.LB219
	addq	$1, 16440(%rsp)
	jmp	.LB219
.LB231:
	movq	$-2, %rax
	jmp	.LB207
.LB233:
	movq	$-2, %rax
	jmp	.LB207
.LB217:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB227:
	testq	%r13, %r13
	je	.LB221
	movl	$0, %ebp
	movq	%rsp, %r14
.LB222:
	movq	%r14, %rdi
	call	_ZN12_GLOBAL__N_18Emission3popEv
	testb	%al, %al
	jne	.LB233
	addq	$1, %rbp
	cmpq	%rbp, %r13
	jne	.LB222
.LB221:
	cmpq	%r13, %rbx
	je	.LB223
	subq	%r13, %rbx
	movl	$0, %eax
	.p2align 5
.LB224:
	movq	56(%rsp,%rax,8), %rdx
	movq	32944(%rsp), %rsi
	movq	%rdx, (%rsi,%rax,8)
	addq	$1, %rax
	cmpq	%rbx, %rax
	jb	.LB224
.LB223:
	testq	%r12, %r12
	je	.LB225
	salq	$3, %r12
	movl	$0, %eax
	leaq	8248(%rsp), %rcx
	.p2align 5
.LB226:
	movq	(%rcx,%rax), %rdx
	movq	%rdx, (%r15,%rax)
	addq	$8, %rax
	cmpq	%rax, %r12
	jne	.LB226
.LB225:
	movq	32960(%rsp), %rax
	movq	16440(%rsp), %rdx
	movq	%rdx, (%rax)
	movq	48(%rsp), %rax
.LB207:
	addq	$32872, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB209:
	testq	%r12, %r12
	jne	.LB229
.LB213:
	movq	%rcx, (%rsp)
	movq	%r12, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%rsi, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32936(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB228
	.size	emission_pop, .-emission_pop
	.align 2
	.type	_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot, @function
_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot:
	movq	%rsi, %rdx
	shrq	$32, %rdx
	movl	$2, %eax
	testb	%dl, %dl
	jne	.LB245
	movq	%rsi, %rdx
	shrq	$40, %rdx
	testb	%dl, %dl
	je	.LB245
	movl	%esi, %esi
	addq	(%rdi), %rsi
	movzbl	(%rsi), %eax
	testb	%al, %al
	jne	.LB249
	movb	$1, (%rsi)
	ret
.LB249:
	movl	$2, %eax
.LB245:
	ret
	.size	_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot, .-_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot
	.globl	spill_set
	.type	spill_set, @function
spill_set:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$24, %rsp
	movq	%rsi, (%rsp)
	movq	%rdx, %rbx
	movq	%rcx, %r12
	movq	%r8, %rbp
	movq	%r9, %r13
	testq	%rcx, %rcx
	je	.LB251
	movl	$0, %eax
	jmp	.LB254
	.p2align 4
.LB252:
	addq	$1, %rax
	cmpq	%rax, %r12
	je	.LB278
.LB254:
	cmpb	$0, 5(%rbx,%rax,8)
	je	.LB252
	cmpb	$0, 4(%rbx,%rax,8)
	jne	.LB252
	movl	(%rbx,%rax,8), %edx
	cmpq	%rdi, %rdx
	jb	.LB252
	movq	$-2, %rax
	jmp	.LB250
	.p2align 4
.LB256:
	addq	$1, %rax
	cmpq	%rax, %r13
	je	.LB279
.LB257:
	cmpb	$0, 5(%rbp,%rax,8)
	je	.LB256
	cmpb	$0, 4(%rbp,%rax,8)
	jne	.LB256
	movl	0(%rbp,%rax,8), %edx
	cmpq	%rdi, %rdx
	jb	.LB256
	movq	$-2, %rax
	jmp	.LB250
.LB279:
	movq	(%rsp), %rax
	movq	%rax, 16(%rsp)
	testq	%r12, %r12
	je	.LB258
.LB263:
	movl	$0, %r14d
	leaq	16(%rsp), %r15
.LB259:
	movq	(%rbx), %rsi
	movq	%r15, %rdi
	call	_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot
	testb	%al, %al
	jne	.LB267
	addq	$1, %r14
	addq	$8, %rbx
	cmpq	%r12, %r14
	jb	.LB259
	testq	%r13, %r13
	je	.LB268
.LB258:
	movl	$0, %eax
	jmp	.LB261
	.p2align 6
.LB260:
	movq	80(%rsp), %rcx
	movb	%dl, (%rcx,%rax)
	addq	$1, %rax
	cmpq	%rax, %r13
	je	.LB280
.LB261:
	cmpb	$0, 5(%rbp,%rax,8)
	setne	%dl
	cmpb	$0, 4(%rbp,%rax,8)
	sete	%cl
	andb	%cl, %dl
	je	.LB260
	movl	0(%rbp,%rax,8), %edx
	movq	(%rsp), %rcx
	cmpb	$0, (%rcx,%rdx)
	setne	%dl
	jmp	.LB260
.LB280:
	movl	$0, %eax
	jmp	.LB250
.LB267:
	movq	$-2, %rax
.LB250:
	addq	$24, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB268:
	movl	$0, %eax
	jmp	.LB250
.LB251:
	movq	%rcx, %rax
	testq	%r9, %r9
	jne	.LB257
	movl	$0, %eax
	jmp	.LB250
.LB278:
	movl	$0, %eax
	testq	%r13, %r13
	jne	.LB257
	movq	(%rsp), %rax
	movq	%rax, 16(%rsp)
	jmp	.LB263
	.size	spill_set, .-spill_set
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission13removeSurplusEv, @function
_ZN12_GLOBAL__N_18Emission13removeSurplusEv:
	pushq	%rbx
	movq	%rdi, %rbx
.LB282:
	movq	32(%rbx), %r8
	testq	%r8, %r8
	je	.LB301
	leaq	-1(%r8), %rdi
	movq	%rdi, %rax
	movq	$-1, %rdx
	movq	$-1, %rsi
	jmp	.LB285
	.p2align 5
.LB283:
	subq	$1, %rax
	cmpq	$-1, %rax
	je	.LB306
.LB285:
	cmpq	$-1, 56(%rbx,%rax,8)
	jne	.LB283
	cmpq	$-1, %rdx
	cmove	%rax, %rdx
	movq	%rdi, %rcx
	subq	%rax, %rcx
	cmpq	$16, %rcx
	cmovbe	%rax, %rsi
	jmp	.LB283
.LB306:
	cmpq	$-1, %rdx
	je	.LB299
	cmpq	$-1, %rsi
	je	.LB287
	cmpq	%rdx, %rdi
	je	.LB288
	leaq	0(,%rdi,8), %r8
	movq	%rdi, %rax
	.p2align 5
.LB289:
	testq	%rax, %rax
	je	.LB307
	subq	$1, %rax
	cmpq	$-1, 56(%rbx,%rax,8)
	jne	.LB289
	movq	24(%rbx), %rcx
	movq	(%rcx,%rax,8), %rdx
	xorq	(%rcx,%r8), %rdx
	salq	$16, %rdx
	jne	.LB289
	movq	56(%rbx,%rax,8), %rdx
	movq	56(%rbx,%rdi,8), %rcx
	movq	%rcx, 56(%rbx,%rax,8)
	movq	%rdx, 56(%rbx,%rdi,8)
	movq	56(%rbx,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB295
	movq	%rax, 8248(%rbx,%rdx,8)
.LB295:
	movq	56(%rbx,%rdi,8), %rax
	cmpq	$-1, %rax
	je	.LB288
	movq	%rdi, 8248(%rbx,%rax,8)
	jmp	.LB288
.LB287:
	subq	$17, %r8
	movl	$2, %eax
	subq	%rdx, %r8
	je	.LB281
	movq	%rdx, 16448(%rbx)
	movq	%r8, 16456(%rbx)
	movl	$1, %eax
	jmp	.LB281
.LB299:
	movl	$0, %eax
.LB281:
	popq	%rbx
	ret
.LB301:
	movl	$0, %eax
	jmp	.LB281
.LB307:
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	testb	%al, %al
	jne	.LB281
.LB288:
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission3popEv
	testb	%al, %al
	je	.LB282
	jmp	.LB281
	.size	_ZN12_GLOBAL__N_18Emission13removeSurplusEv, .-_ZN12_GLOBAL__N_18Emission13removeSurplusEv
	.globl	remove_surplus
	.type	remove_surplus, @function
remove_surplus:
	cmpq	$1024, %rdi
	ja	.LB341
	pushq	%rbx
	subq	$32864, %rsp
	movq	%rdx, %r10
	movq	%r8, %rbx
	cmpq	$1024, %rsi
	ja	.LB330
	testq	%rdi, %rdi
	je	.LB310
	movl	$0, %eax
	.p2align 5
.LB311:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB311
	testq	%rsi, %rsi
	je	.LB329
.LB328:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%rsi,8), %rdx
	.p2align 5
.LB313:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB313
	testq	%rdi, %rdi
	je	.LB314
.LB329:
	movl	$0, %eax
	jmp	.LB316
	.p2align 5
.LB315:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rdi
	je	.LB344
	movq	%rdx, %rax
.LB316:
	movq	(%rbx,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB315
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	jmp	.LB315
.LB344:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	%rdx, 32(%rsp)
	movq	32888(%rsp), %rdi
	movq	%rdi, 40(%rsp)
	movq	$0, 48(%rsp)
	movl	$0, %edx
	addq	$1, %rax
	.p2align 5
.LB317:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB317
.LB327:
	testq	%rsi, %rsi
	je	.LB318
	leaq	0(,%rsi,8), %rdx
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB319:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB319
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rdx
	jmp	.LB321
	.p2align 5
.LB320:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB326
.LB321:
	cmpq	$-1, 8248(%rax)
	jne	.LB320
	addq	$1, 16440(%rsp)
	jmp	.LB320
.LB322:
	movq	16448(%rsp), %rax
	movq	32896(%rsp), %rsi
	movq	%rax, (%rsi)
	movq	16456(%rsp), %rax
	movq	%rax, 8(%rsi)
	jmp	.LB323
.LB330:
	movq	$-2, %rdx
	jmp	.LB308
.LB318:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB326:
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission13removeSurplusEv
	cmpb	$1, %al
	je	.LB322
	movq	$-2, %rdx
	cmpb	$2, %al
	je	.LB308
	testb	%al, %al
	jne	.LB323
	movq	32896(%rsp), %rax
	movq	$0, (%rax)
	movq	$0, 8(%rax)
.LB323:
	movq	32(%rsp), %rcx
	movq	32904(%rsp), %rax
	movq	%rcx, (%rax)
	testq	%rcx, %rcx
	je	.LB324
	salq	$3, %rcx
	movl	$0, %eax
	leaq	56(%rsp), %rsi
	.p2align 5
.LB325:
	movq	(%rsi,%rax), %rdx
	movq	%rdx, (%rbx,%rax)
	addq	$8, %rax
	cmpq	%rax, %rcx
	jne	.LB325
.LB324:
	movq	48(%rsp), %rdx
.LB308:
	movq	%rdx, %rax
	addq	$32864, %rsp
	popq	%rbx
	ret
.LB310:
	testq	%rsi, %rsi
	jne	.LB328
.LB314:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32888(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB327
.LB341:
	movq	$-2, %rdx
	movq	%rdx, %rax
	ret
	.size	remove_surplus, .-remove_surplus
	.globl	permute
	.type	permute, @function
permute:
	pushq	%r14
	pushq	%rbp
	pushq	%rbx
	subq	$49248, %rsp
	movq	%rdi, %rbx
	cmpq	$1024, %rdi
	ja	.LB362
	movq	%rsi, %rdi
	movq	%rdx, %r10
	movq	%rcx, %r11
	movq	%r8, %r14
	movq	%r9, %rbp
	testq	%rbx, %rbx
	je	.LB347
	leaq	16480(%rsp), %rax
	leaq	0(,%rbx,8), %rcx
	leaq	(%rax,%rcx), %rsi
	movq	%rax, %rdx
	.p2align 4
.LB348:
	movq	$-1, (%rdx)
	addq	$8, %rdx
	cmpq	%rsi, %rdx
	jne	.LB348
	.p2align 5
.LB349:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rsi, %rax
	jne	.LB349
	movl	$0, %eax
	.p2align 6
.LB350:
	movq	(%r10,%rax,8), %rdx
	movq	%rdx, 41056(%rsp,%rax,8)
	movq	(%rdi,%rax,8), %rsi
	movq	%rsi, 32864(%rsp,%rdx,8)
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	addq	$1, %rax
	cmpq	%rax, %rbx
	jne	.LB350
	leaq	32864(%rsp), %rdx
	movq	%rdx, (%rsp)
	movq	%rax, 8(%rsp)
	movq	$0, 16(%rsp)
	movq	%rdi, 24(%rsp)
	movq	%rax, 32(%rsp)
	movq	%r11, 40(%rsp)
	movq	$0, 48(%rsp)
	movl	$0, %eax
	leaq	56(%rsp), %rsi
	.p2align 5
.LB351:
	movq	16480(%rsp,%rax), %rdx
	movq	%rdx, (%rsi,%rax)
	addq	$8, %rax
	cmpq	%rcx, %rax
	jne	.LB351
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB352:
	movq	(%rsi,%rax), %rdx
	movq	%rdx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rcx, %rax
	jne	.LB352
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rcx
	jmp	.LB354
	.p2align 5
.LB353:
	addq	$8, %rax
	cmpq	%rcx, %rax
	je	.LB374
.LB354:
	cmpq	$-1, 8248(%rax)
	jne	.LB353
	addq	$1, 16440(%rsp)
	jmp	.LB353
.LB374:
	leaq	41056(%rsp), %rsi
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE
	cmpb	$1, %al
	je	.LB355
	movq	$-2, %rdx
	cmpb	$2, %al
	je	.LB345
	testb	%al, %al
	jne	.LB356
.LB360:
	movl	$0, %edx
	movl	$0, %eax
.LB358:
	movq	%rdx, (%r14)
	movq	%rax, 8(%r14)
	testq	%rbx, %rbx
	je	.LB357
.LB356:
	salq	$3, %rbx
	movl	$0, %eax
	leaq	56(%rsp), %rcx
	.p2align 5
.LB359:
	movq	(%rcx,%rax), %rdx
	movq	%rdx, 0(%rbp,%rax)
	addq	$8, %rax
	cmpq	%rax, %rbx
	jne	.LB359
.LB357:
	movq	48(%rsp), %rdx
.LB345:
	movq	%rdx, %rax
	addq	$49248, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r14
	ret
.LB355:
	movq	16448(%rsp), %rdx
	movq	16456(%rsp), %rax
	jmp	.LB358
.LB362:
	movq	$-2, %rdx
	jmp	.LB345
.LB347:
	leaq	32864(%rsp), %rax
	movq	%rax, (%rsp)
	movq	%rbx, 8(%rsp)
	movq	$0, 16(%rsp)
	movq	%rsi, 24(%rsp)
	movq	%rbx, 32(%rsp)
	movq	%rcx, 40(%rsp)
	movq	$0, 48(%rsp)
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	leaq	41056(%rsp), %rsi
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE
	cmpb	$1, %al
	je	.LB355
	movq	$-2, %rdx
	cmpb	$2, %al
	je	.LB345
	testb	%al, %al
	je	.LB360
	jmp	.LB357
	.size	permute, .-permute
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission21permuteAtLowestHeightEv, @function
_ZN12_GLOBAL__N_18Emission21permuteAtLowestHeightEv:
	subq	$24584, %rsp
	movq	32(%rdi), %rcx
	testq	%rcx, %rcx
	je	.LB376
	movl	$0, %eax
	movl	$0, %esi
	movl	$0, %r8d
.LB381:
	movq	56(%rdi,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB377
	cmpq	8(%rdi), %rax
	jnb	.LB377
	movq	16464(%rdi), %r9
	movq	8192(%r9,%rax,8), %r9
	cmpq	%rcx, %rdx
	je	.LB378
	jb	.LB379
.LB378:
	cmpq	$-1, %r9
	jne	.LB392
	movq	%rax, 16384(%rsp,%rax,8)
.LB380:
	addq	$1, %rax
	cmpq	%rcx, %rax
	jne	.LB381
	movl	$2, %eax
	cmpq	%rsi, %r8
	jne	.LB375
	testq	%rsi, %rsi
	je	.LB376
	salq	$3, %rsi
	movl	$0, %eax
	.p2align 5
.LB384:
	movq	(%rsp,%rax), %rdx
	movq	8192(%rsp,%rax), %rcx
	movq	%rcx, 16384(%rsp,%rdx,8)
	addq	$8, %rax
	cmpq	%rax, %rsi
	jne	.LB384
.LB376:
	leaq	16384(%rsp), %rsi
	call	_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE
	jmp	.LB375
.LB377:
	movl	$2, %eax
.LB375:
	addq	$24584, %rsp
	ret
.LB379:
	movq	%rdx, 16384(%rsp,%rax,8)
	cmpq	$-1, %r9
	jne	.LB380
	movq	%rax, 8192(%rsp,%r8,8)
	leaq	1(%r8), %r8
	jmp	.LB380
.LB392:
	movq	%rax, (%rsp,%rsi,8)
	leaq	1(%rsi), %rsi
	jmp	.LB380
	.size	_ZN12_GLOBAL__N_18Emission21permuteAtLowestHeightEv, .-_ZN12_GLOBAL__N_18Emission21permuteAtLowestHeightEv
	.globl	permute_at_lowest_height
	.type	permute_at_lowest_height, @function
permute_at_lowest_height:
	pushq	%rbp
	pushq	%rbx
	subq	$32872, %rsp
	movq	%rdi, %rbx
	cmpq	$1024, %rdi
	ja	.LB416
	movq	%rdx, %rdi
	movq	%r8, %rbp
	cmpq	$1024, %rsi
	ja	.LB416
	testq	%rbx, %rbx
	je	.LB395
	movl	$0, %eax
	.p2align 5
.LB396:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rbx
	jne	.LB396
	testq	%rsi, %rsi
	je	.LB415
.LB414:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%rsi,8), %rdx
	.p2align 5
.LB398:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB398
	testq	%rbx, %rbx
	je	.LB399
.LB415:
	movl	$0, %eax
	jmp	.LB401
	.p2align 5
.LB400:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rbx
	je	.LB428
	movq	%rdx, %rax
.LB401:
	movq	0(%rbp,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB400
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	jmp	.LB400
.LB428:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%rdi, 24(%rsp)
	movq	%rdx, 32(%rsp)
	movq	32904(%rsp), %rdi
	movq	%rdi, 40(%rsp)
	movq	$0, 48(%rsp)
	movl	$0, %edx
	addq	$1, %rax
	.p2align 5
.LB402:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB402
.LB413:
	testq	%rsi, %rsi
	je	.LB403
	leaq	0(,%rsi,8), %rdx
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB404:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB404
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rdx
	jmp	.LB406
	.p2align 5
.LB405:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB412
.LB406:
	cmpq	$-1, 8248(%rax)
	jne	.LB405
	addq	$1, 16440(%rsp)
	jmp	.LB405
.LB407:
	movq	16448(%rsp), %rax
	movq	32912(%rsp), %rdi
	movq	%rax, (%rdi)
	movq	16456(%rsp), %rax
	movq	%rax, 8(%rdi)
	jmp	.LB408
.LB416:
	movq	$-2, %rdx
	jmp	.LB393
.LB403:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB412:
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission21permuteAtLowestHeightEv
	cmpb	$1, %al
	je	.LB407
	movq	$-2, %rdx
	cmpb	$2, %al
	je	.LB393
	testb	%al, %al
	jne	.LB408
	movq	32912(%rsp), %rax
	movq	$0, (%rax)
	movq	$0, 8(%rax)
.LB408:
	leaq	0(,%rbx,8), %rsi
	movl	$0, %eax
	leaq	56(%rsp), %rcx
	testq	%rbx, %rbx
	je	.LB410
	.p2align 5
.LB411:
	movq	(%rcx,%rax), %rdx
	movq	%rdx, 0(%rbp,%rax)
	addq	$8, %rax
	cmpq	%rsi, %rax
	jne	.LB411
.LB410:
	movq	48(%rsp), %rdx
.LB393:
	movq	%rdx, %rax
	addq	$32872, %rsp
	popq	%rbx
	popq	%rbp
	ret
.LB395:
	testq	%rsi, %rsi
	jne	.LB414
.LB399:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%rdi, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32904(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB413
	.size	permute_at_lowest_height, .-permute_at_lowest_height
	.align 2
	.type	_ZNK12_GLOBAL__N_18Emission11isAvailableE11StackOffset, @function
_ZNK12_GLOBAL__N_18Emission11isAvailableE11StackOffset:
	pushq	%rbp
	pushq	%rbx
	movq	(%rdi), %rax
	leaq	(%rax,%rsi,8), %rdx
	movq	(%rdx), %rbp
	movzbl	4(%rdx), %eax
	subl	$1, %eax
	cmpb	$1, %al
	setbe	%al
	cmpb	$0, 5(%rdx)
	sete	%dl
	orb	%dl, %al
	je	.LB432
.LB429:
	popq	%rbx
	popq	%rbp
	ret
.LB432:
	movq	%rdi, %rbx
	movq	%rbp, %rsi
	call	_ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot
	testb	%al, %al
	jne	.LB429
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	call	_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot
	cmpq	$-1, %rax
	setne	%al
	jmp	.LB429
	.size	_ZNK12_GLOBAL__N_18Emission11isAvailableE11StackOffset, .-_ZNK12_GLOBAL__N_18Emission11isAvailableE11StackOffset
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission3runEv, @function
_ZN12_GLOBAL__N_18Emission3runEv:
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbx
	call	_ZN12_GLOBAL__N_18Emission13removeSurplusEv
	testb	%al, %al
	je	.LB453
.LB433:
	popq	%rbx
	popq	%rbp
	popq	%r12
	ret
.LB453:
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission21permuteAtLowestHeightEv
	testb	%al, %al
	jne	.LB433
	movq	16440(%rbx), %rcx
	movq	8(%rbx), %r12
	movq	%rcx, %rdx
	addq	32(%rbx), %rdx
	movl	$2, %eax
	cmpq	%r12, %rdx
	jne	.LB433
	testq	%r12, %r12
	je	.LB435
	movl	$0, %eax
	movl	$0, %edx
	jmp	.LB437
	.p2align 5
.LB436:
	addq	$1, %rax
	cmpq	%rax, %r12
	je	.LB454
.LB437:
	cmpq	$-1, 8248(%rbx,%rax,8)
	jne	.LB436
	addq	$1, %rdx
	jmp	.LB436
	.p2align 4
.LB440:
	addq	$1, %rax
	cmpq	%rax, %r12
	je	.LB442
.LB441:
	cmpb	$3, 4(%rdx,%rax,8)
	jne	.LB440
	cmpq	$-1, 8248(%rbx,%rax,8)
	jne	.LB440
	movl	$2, %eax
	jmp	.LB433
.LB444:
	movl	$2, %eax
	jmp	.LB433
.LB435:
	movl	$2, %eax
	testq	%rcx, %rcx
	jne	.LB433
.LB442:
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv
	jmp	.LB433
.LB454:
	movl	$2, %eax
	movl	$0, %ebp
	cmpq	%rdx, %rcx
	jne	.LB433
.LB439:
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	call	_ZNK12_GLOBAL__N_18Emission11isAvailableE11StackOffset
	testb	%al, %al
	je	.LB444
	addq	$1, %rbp
	cmpq	%rbp, %r12
	jne	.LB439
	movq	(%rbx), %rdx
	movl	$0, %eax
	jmp	.LB441
	.size	_ZN12_GLOBAL__N_18Emission3runEv, .-_ZN12_GLOBAL__N_18Emission3runEv
	.globl	emit
	.type	emit, @function
emit:
	pushq	%rbx
	subq	$32864, %rsp
	movq	%r8, %rbx
	movq	32880(%rsp), %r8
	cmpq	$1024, %rdi
	ja	.LB480
	movq	%rdx, %r10
	movq	%rcx, %rdx
	cmpq	$1024, %rsi
	ja	.LB480
	testq	%rsi, %rsi
	je	.LB457
	movl	$0, %eax
	jmp	.LB459
	.p2align 4
.LB458:
	addq	$1, %rax
	cmpq	%rax, %rsi
	je	.LB457
.LB459:
	cmpb	$0, 4(%rdx,%rax,8)
	jne	.LB458
	cmpb	$0, 5(%rdx,%rax,8)
	je	.LB458
	movl	(%rdx,%rax,8), %ecx
	cmpq	%r8, %rcx
	jb	.LB458
	movq	$-2, %rdx
	jmp	.LB455
.LB457:
	testq	%rdi, %rdi
	je	.LB460
	movl	$0, %eax
	.p2align 5
.LB461:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB461
	testq	%rsi, %rsi
	je	.LB479
.LB478:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%rsi,8), %rcx
	.p2align 5
.LB463:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rcx, %rax
	jne	.LB463
	testq	%rdi, %rdi
	je	.LB464
.LB479:
	movl	$0, %eax
	jmp	.LB466
	.p2align 5
.LB465:
	leaq	1(%rax), %rcx
	cmpq	%rcx, %rdi
	je	.LB493
	movq	%rcx, %rax
.LB466:
	movq	(%rbx,%rax,8), %rcx
	cmpq	$-1, %rcx
	je	.LB465
	movq	%rcx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rcx,8)
	jmp	.LB465
.LB493:
	movq	%rdx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	%rcx, 32(%rsp)
	movq	32888(%rsp), %rdi
	movq	%rdi, 40(%rsp)
	movq	$0, 48(%rsp)
	movl	$0, %edx
	movq	%rcx, %rax
	.p2align 5
.LB467:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB467
.LB477:
	testq	%rsi, %rsi
	je	.LB468
	salq	$3, %rsi
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rcx
	.p2align 5
.LB469:
	movq	(%rcx,%rax), %rdx
	movq	%rdx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rsi, %rax
	jne	.LB469
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rsi
	jmp	.LB471
	.p2align 5
.LB470:
	addq	$8, %rax
	cmpq	%rsi, %rax
	je	.LB476
.LB471:
	cmpq	$-1, 8248(%rax)
	jne	.LB470
	addq	$1, 16440(%rsp)
	jmp	.LB470
.LB472:
	movq	16448(%rsp), %rax
	movq	32896(%rsp), %rdi
	movq	%rax, (%rdi)
	movq	16456(%rsp), %rax
	movq	%rax, 8(%rdi)
	jmp	.LB473
.LB480:
	movq	$-2, %rdx
	jmp	.LB455
.LB468:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB476:
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission3runEv
	cmpb	$1, %al
	je	.LB472
	movq	$-2, %rdx
	cmpb	$2, %al
	je	.LB455
	testb	%al, %al
	jne	.LB473
	movq	32896(%rsp), %rax
	movq	$0, (%rax)
	movq	$0, 8(%rax)
.LB473:
	movq	32(%rsp), %rcx
	movq	32904(%rsp), %rax
	movq	%rcx, (%rax)
	testq	%rcx, %rcx
	je	.LB474
	salq	$3, %rcx
	movl	$0, %eax
	leaq	56(%rsp), %rsi
	.p2align 5
.LB475:
	movq	(%rsi,%rax), %rdx
	movq	%rdx, (%rbx,%rax)
	addq	$8, %rax
	cmpq	%rax, %rcx
	jne	.LB475
.LB474:
	movq	48(%rsp), %rdx
.LB455:
	movq	%rdx, %rax
	addq	$32864, %rsp
	popq	%rbx
	ret
.LB460:
	testq	%rsi, %rsi
	jne	.LB478
.LB464:
	movq	%rdx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32888(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB477
	.size	emit, .-emit
	.section	.note.GNU-stack,"",@progbits
