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
	.type	_ZN12_GLOBAL__N_18Emission7permuteEv, @function
_ZN12_GLOBAL__N_18Emission7permuteEv:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$16408, %rsp
	movq	32(%rdi), %rbx
	movl	$0, %eax
	testq	%rbx, %rbx
	je	.LB54
	movq	%rdi, %r15
	movl	$0, %eax
.LB57:
	movq	56(%r15,%rax,8), %rdx
	cmpq	$-1, %rdx
	jne	.LB56
	movl	$2, %eax
.LB54:
	addq	$16408, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB56:
	movq	%rdx, 8208(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rbx
	jne	.LB57
	leaq	16(%rsp), %rax
	leaq	(%rax,%rbx,8), %rdx
	.p2align 4
.LB58:
	movq	$-1, (%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB58
	movq	$8, 8(%rsp)
	movq	$1, (%rsp)
	movl	$0, %ebp
	leaq	16(%rsp), %r12
	jmp	.LB71
	.p2align 5
.LB61:
	addq	$8, %rax
	movq	8(%rsp), %rdi
	cmpq	%rdi, %rax
	je	.LB95
.LB62:
	movq	%r14, %rdx
	xorq	0(%r13,%rax), %rdx
	salq	$16, %rdx
	jne	.LB61
	movq	8208(%rsp,%rax), %rdx
	movq	%rbp, 16(%rsp,%rdx,8)
	jmp	.LB61
.LB95:
	movl	$0, %ecx
	movl	$0, %eax
	jmp	.LB70
.LB64:
	cmpq	%rbx, %rax
	jb	.LB68
.LB65:
	movl	$2, %eax
	jmp	.LB54
	.p2align 4
.LB66:
	addq	$1, %rax
	cmpq	%rbx, %rax
	je	.LB65
.LB68:
	cmpq	%rbp, (%r12,%rax,8)
	jne	.LB66
	movq	%r14, %rdx
	xorq	0(%r13,%rax,8), %rdx
	salq	$16, %rdx
	je	.LB66
	cmpq	%rbx, %rax
	jnb	.LB65
	movq	%rax, 8208(%rsp,%rcx,8)
	addq	$1, %rax
.LB63:
	addq	$1, %rcx
	cmpq	%rcx, (%rsp)
	je	.LB60
.LB70:
	movq	%r14, %rdx
	xorq	0(%r13,%rcx,8), %rdx
	salq	$16, %rdx
	jne	.LB63
	cmpq	%rbp, (%r12,%rcx,8)
	jne	.LB64
	movq	%rcx, 8208(%rsp,%rcx,8)
	jmp	.LB63
.LB60:
	addq	$1, %rbp
	addq	$1, (%rsp)
	addq	$8, 8(%rsp)
	cmpq	%rbp, %rbx
	je	.LB96
.LB71:
	movq	24(%r15), %r13
	movq	0(%r13,%rbp,8), %r14
	movq	%r14, %rsi
	movq	%r15, %rdi
	call	_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot
	cmpq	%rbp, %rax
	jne	.LB60
	movl	$0, %eax
	jmp	.LB62
.LB96:
	leaq	-1(%rbx), %rcx
	leaq	8208(%rsp), %rsi
	jmp	.LB84
.LB86:
	movq	%rcx, %rdx
.LB72:
	testq	%rdx, %rdx
	je	.LB97
	leaq	-1(%rdx), %rax
	cmpq	(%rsi,%rax,8), %rax
	jne	.LB74
	movq	%rax, %rdx
	jmp	.LB72
.LB97:
	movl	$0, %eax
	jmp	.LB54
.LB74:
	cmpq	%rdx, %rbx
	jne	.LB73
	movl	$0, %eax
	jmp	.LB54
.LB98:
	movq	56(%r15,%rax,8), %rdx
	movq	56(%r15,%rcx,8), %rdi
	movq	%rdi, 56(%r15,%rax,8)
	movq	%rdx, 56(%r15,%rcx,8)
	movq	56(%r15,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB78
	movq	%rax, 8248(%r15,%rdx,8)
.LB78:
	movq	56(%r15,%rcx,8), %rdx
	cmpq	$-1, %rdx
	je	.LB80
	movq	%rcx, 8248(%r15,%rdx,8)
.LB80:
	movq	8208(%rsp,%rax,8), %rdx
	movq	8208(%rsp,%rcx,8), %rdi
	movq	%rdi, 8208(%rsp,%rax,8)
	movq	%rdx, 8208(%rsp,%rcx,8)
.LB84:
	movq	8208(%rsp,%rcx,8), %rax
	cmpq	%rcx, %rax
	je	.LB86
.LB73:
	movq	24(%r15), %rdx
	movq	32(%r15), %rdi
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
	movq	32(%r15), %r8
	movq	24(%r15), %rdx
	leaq	-8(%rdx,%r8,8), %rdx
	movl	%r11d, (%rdx)
	movb	%r10b, 4(%rdx)
	movb	%dil, 5(%rdx)
	movq	%rax, %rdi
	notq	%rdi
	addq	32(%r15), %rdi
	movq	48(%r15), %rdx
	leaq	1(%rdx), %r8
	movq	%r8, 48(%r15)
	leaq	(%rdx,%rdx,2), %rdx
	salq	$2, %rdx
	addq	40(%r15), %rdx
	movb	$0, (%rdx)
	movb	%dil, 1(%rdx)
	movl	$0, 4(%rdx)
	movb	$1, 8(%rdx)
	movb	$5, 9(%rdx)
	movq	56(%r15,%rax,8), %rdx
	movq	56(%r15,%rcx,8), %rdi
	movq	%rdi, 56(%r15,%rax,8)
	movq	%rdx, 56(%r15,%rcx,8)
	movq	56(%r15,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB82
	movq	%rax, 8248(%r15,%rdx,8)
.LB82:
	movq	56(%r15,%rcx,8), %rdx
	cmpq	$-1, %rdx
	je	.LB80
	movq	%rcx, 8248(%r15,%rdx,8)
	jmp	.LB80
.LB99:
	movq	%rax, 16448(%r15)
	subq	$17, %rdi
	movq	%rdi, 16456(%r15)
	movl	$1, %eax
	jmp	.LB54
	.size	_ZN12_GLOBAL__N_18Emission7permuteEv, .-_ZN12_GLOBAL__N_18Emission7permuteEv
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv, @function
_ZN12_GLOBAL__N_18Emission13buildBottomUpEv:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$24, %rsp
	movq	%rdi, %r12
	movq	8(%rdi), %r13
	testq	%r13, %r13
	je	.LB101
	movl	$0, %r14d
	jmp	.LB135
.LB104:
	movl	$2, %eax
	cmpq	%r13, %r15
	jne	.LB100
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission7permuteEv
	jmp	.LB100
.LB155:
	movq	%rax, 16448(%r12)
	subq	$16, %rcx
	movq	%rcx, 16456(%r12)
	movl	$1, %eax
	jmp	.LB100
	.p2align 5
.LB111:
	addq	$1, %rbx
	cmpq	%r13, %rbx
	je	.LB154
.LB105:
	cmpq	$-1, 8248(%r12,%rbx,8)
	jne	.LB111
	movq	(%r12), %rax
	leaq	(%rax,%rbx,8), %rax
	movq	(%rax), %rbp
	movzbl	4(%rax), %edx
	cmpb	$1, %dl
	je	.LB111
	movzbl	5(%rax), %ecx
	movzbl	%dl, %eax
	salq	$32, %rax
	movabsq	$-1095216660481, %rsi
	andq	%rsi, %rbp
	orq	%rax, %rbp
	testb	%cl, %cl
	je	.LB111
	cmpb	$2, %dl
	je	.LB111
	movzbl	%cl, %ecx
	salq	$40, %rcx
	movabsq	$-280375465082881, %rax
	andq	%rax, %rbp
	orq	%rcx, %rbp
	movq	%rbp, %rsi
	movq	%r12, %rdi
	call	_ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot
	testb	%al, %al
	jne	.LB111
	movq	%rbp, %rsi
	movq	%r12, %rdi
	call	_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot
	cmpq	$-1, %rax
	je	.LB111
	movq	%r15, %rcx
	subq	%rax, %rcx
	leaq	-1(%rcx), %rdx
	cmpq	$15, %rdx
	ja	.LB155
	cmpq	%r14, %rax
	sete	%al
	cmpq	$15, %rdx
	setne	%dl
	orb	%dl, %al
	jne	.LB111
	movq	8(%rsp), %rax
	cmpq	$-1, %rax
	cmove	%rbx, %rax
	movq	%rax, 8(%rsp)
	jmp	.LB111
.LB154:
	movq	8(%rsp), %rdi
	cmpq	$-1, %rdi
	sete	%al
	cmpq	%r14, %rdi
	je	.LB106
	testb	%al, %al
	je	.LB156
.LB106:
	cmpq	%r13, %r15
	setb	%cl
	cmpq	%r15, %r14
	setb	%dl
	testb	%dl, %cl
	je	.LB113
	testb	%al, %al
	jne	.LB157
.LB113:
	leaq	0(,%r14,8), %rbx
	movq	8248(%r12,%rbx), %rdx
	cmpq	$-1, %rdx
	je	.LB117
	cmpq	%r14, %rdx
	jb	.LB158
	movq	24(%r12), %rcx
	movq	(%rcx,%rdx,8), %rsi
	movq	%rsi, %rdi
	xorq	(%rcx,%r14,8), %rdi
	movq	%r14, %rax
	salq	$16, %rdi
	jne	.LB159
.LB125:
	movq	%rax, %rsi
	movq	56(%r12,%rax,8), %rcx
	movq	56(%r12,%rdx,8), %rdi
	movq	%rdi, 56(%r12,%rax,8)
	movq	%rcx, 56(%r12,%rdx,8)
	movq	56(%r12,%rax,8), %rcx
	cmpq	$-1, %rcx
	je	.LB126
	movq	%rax, 8248(%r12,%rcx,8)
.LB126:
	movq	56(%r12,%rdx,8), %rcx
	cmpq	$-1, %rcx
	je	.LB127
	movq	%rdx, 8248(%r12,%rcx,8)
.LB127:
	cmpq	%rax, %r14
	je	.LB142
	leaq	-1(%r15), %rdx
	cmpq	%rax, %rdx
	je	.LB128
	subq	%rax, %r15
	leaq	-1(%r15), %rdx
	cmpq	$16, %rdx
	ja	.LB160
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	testb	%al, %al
	jne	.LB100
.LB128:
	movq	32(%r12), %rax
	cmpq	%rax, %r14
	jnb	.LB144
	cmpq	%r14, 56(%r12,%rbx)
	jne	.LB130
	movl	$2, %eax
.LB100:
	addq	$24, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB156:
	movq	%r15, %rax
	subq	%r14, %rax
	cmpq	$15, %rax
	ja	.LB113
	movq	8(%rsp), %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
	testb	%al, %al
	jne	.LB100
	subq	$1, %r14
	jmp	.LB133
.LB157:
	cmpq	$-1, 8248(%r12,%r15,8)
	jne	.LB113
	movq	%r15, %rax
	subq	%r14, %rax
	cmpq	$15, %rax
	ja	.LB113
	movq	%r15, %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
	testb	%al, %al
	jne	.LB100
	subq	$1, %r14
	jmp	.LB133
.LB117:
	movq	%r14, %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
	testb	%al, %al
	jne	.LB100
	movq	32(%r12), %rax
	cmpq	%rax, %r14
	jnb	.LB143
	cmpq	%r14, 56(%r12,%rbx)
	je	.LB133
.LB130:
	leaq	-1(%rax), %rdx
	cmpq	%r14, %rdx
	je	.LB133
	subq	%r14, %rax
	leaq	-1(%rax), %rdx
	cmpq	$16, %rdx
	ja	.LB161
	movq	%r14, %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	testb	%al, %al
	je	.LB133
	jmp	.LB100
.LB159:
	leaq	-1(%r15), %rax
	cmpq	%rax, %rdx
	jb	.LB124
	movq	%rdx, %rax
	jmp	.LB125
	.p2align 5
.LB122:
	subq	$1, %rax
	cmpq	%rax, %rdx
	jnb	.LB162
.LB124:
	movq	%rsi, %rdi
	xorq	(%rcx,%rax,8), %rdi
	salq	$16, %rdi
	jne	.LB122
	cmpq	%rax, 56(%r12,%rax,8)
	je	.LB122
	xorq	(%rcx,%rax,8), %rsi
	salq	$16, %rsi
	je	.LB125
	movl	$2, %eax
	jmp	.LB100
.LB162:
	movq	%rdx, %rax
	jmp	.LB125
.LB160:
	movq	%rax, 16448(%r12)
	subq	$17, %r15
	movq	%r15, 16456(%r12)
	movl	$1, %eax
	jmp	.LB100
.LB161:
	movq	%r14, 16448(%r12)
	subq	$17, %rax
	movq	%rax, 16456(%r12)
	movl	$1, %eax
	jmp	.LB100
.LB142:
	movq	%rax, %r14
.LB133:
	addq	$1, %r14
	movq	8(%r12), %r13
	cmpq	%r13, %r14
	jnb	.LB101
.LB135:
	movq	32(%r12), %r15
	cmpq	%r15, %r14
	jnb	.LB102
	cmpq	%r14, 56(%r12,%r14,8)
	je	.LB133
.LB102:
	cmpq	$0, 16440(%r12)
	je	.LB104
	movq	%r14, %rbx
	movq	$-1, 8(%rsp)
	movl	$1, %eax
	cmpq	%r13, %r14
	jb	.LB105
	jmp	.LB106
.LB158:
	movl	$2, %eax
	jmp	.LB100
.LB143:
	movl	$2, %eax
	jmp	.LB100
.LB144:
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
	je	.LB163
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
	je	.LB165
	movq	$-1, 8248(%rdi,%rax,8)
.LB165:
	movl	$0, %edx
.LB163:
	movl	%edx, %eax
	ret
	.size	_ZN12_GLOBAL__N_18Emission3popEv, .-_ZN12_GLOBAL__N_18Emission3popEv
	.globl	build_bottom_up
	.type	build_bottom_up, @function
build_bottom_up:
	cmpq	%rdi, %rsi
	jb	.LB186
	movq	%rdx, %r10
	cmpq	$1024, %rsi
	ja	.LB186
	subq	$32872, %rsp
	testq	%rdi, %rdi
	je	.LB169
	movl	$0, %eax
	.p2align 5
.LB170:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB170
	testq	%rsi, %rsi
	je	.LB185
.LB184:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%rsi,8), %rdx
	.p2align 5
.LB172:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB172
	testq	%rdi, %rdi
	je	.LB173
.LB185:
	movl	$0, %eax
	jmp	.LB175
	.p2align 5
.LB174:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rdi
	je	.LB199
	movq	%rdx, %rax
.LB175:
	movq	(%r8,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB174
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	jmp	.LB174
.LB199:
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
.LB176:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB176
.LB183:
	testq	%rsi, %rsi
	je	.LB177
	leaq	0(,%rsi,8), %rdx
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB178:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB178
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rdx
	jmp	.LB180
	.p2align 5
.LB179:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB182
.LB180:
	cmpq	$-1, 8248(%rax)
	jne	.LB179
	addq	$1, 16440(%rsp)
	jmp	.LB179
.LB200:
	movq	32888(%rsp), %rax
	movq	$0, (%rax)
	movq	$0, 8(%rax)
	movq	48(%rsp), %rdx
	jmp	.LB167
.LB181:
	movq	16448(%rsp), %rax
	movq	32888(%rsp), %rsi
	movq	%rax, (%rsi)
	movq	16456(%rsp), %rax
	movq	%rax, 8(%rsi)
	movq	48(%rsp), %rdx
	jmp	.LB167
.LB186:
	movq	$-2, %rdx
	movq	%rdx, %rax
	ret
.LB177:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB182:
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv
	cmpb	$1, %al
	je	.LB181
	movq	$-2, %rdx
	cmpb	$2, %al
	jne	.LB200
.LB167:
	movq	%rdx, %rax
	addq	$32872, %rsp
	ret
.LB169:
	testq	%rsi, %rsi
	jne	.LB184
.LB173:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32880(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB183
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
	ja	.LB225
	movq	%rdi, %rbx
	movq	%rsi, %r12
	movq	%rdx, %rsi
	cmpq	$1024, %r12
	ja	.LB225
	testq	%rdi, %rdi
	je	.LB203
	movl	$0, %eax
	.p2align 5
.LB204:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rbx
	jne	.LB204
	testq	%r12, %r12
	je	.LB224
.LB223:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%r12,8), %rdx
	.p2align 5
.LB206:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB206
	testq	%rbx, %rbx
	je	.LB207
.LB224:
	movl	$0, %eax
	jmp	.LB209
	.p2align 5
.LB208:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rbx
	je	.LB238
	movq	%rdx, %rax
.LB209:
	movq	(%r8,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB208
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	jmp	.LB208
.LB238:
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
.LB210:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB210
.LB222:
	testq	%r12, %r12
	je	.LB211
	leaq	0(,%r12,8), %rdx
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB212:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB212
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rdx
	jmp	.LB214
	.p2align 5
.LB213:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB221
.LB214:
	cmpq	$-1, 8248(%rax)
	jne	.LB213
	addq	$1, 16440(%rsp)
	jmp	.LB213
.LB225:
	movq	$-2, %rax
	jmp	.LB201
.LB227:
	movq	$-2, %rax
	jmp	.LB201
.LB211:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB221:
	testq	%r13, %r13
	je	.LB215
	movl	$0, %ebp
	movq	%rsp, %r14
.LB216:
	movq	%r14, %rdi
	call	_ZN12_GLOBAL__N_18Emission3popEv
	testb	%al, %al
	jne	.LB227
	addq	$1, %rbp
	cmpq	%rbp, %r13
	jne	.LB216
.LB215:
	cmpq	%r13, %rbx
	je	.LB217
	subq	%r13, %rbx
	movl	$0, %eax
	.p2align 5
.LB218:
	movq	56(%rsp,%rax,8), %rdx
	movq	32944(%rsp), %rsi
	movq	%rdx, (%rsi,%rax,8)
	addq	$1, %rax
	cmpq	%rbx, %rax
	jb	.LB218
.LB217:
	testq	%r12, %r12
	je	.LB219
	salq	$3, %r12
	movl	$0, %eax
	leaq	8248(%rsp), %rcx
	.p2align 5
.LB220:
	movq	(%rcx,%rax), %rdx
	movq	%rdx, (%r15,%rax)
	addq	$8, %rax
	cmpq	%rax, %r12
	jne	.LB220
.LB219:
	movq	32960(%rsp), %rax
	movq	16440(%rsp), %rdx
	movq	%rdx, (%rax)
	movq	48(%rsp), %rax
.LB201:
	addq	$32872, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB203:
	testq	%r12, %r12
	jne	.LB223
.LB207:
	movq	%rcx, (%rsp)
	movq	%r12, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%rsi, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32936(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB222
	.size	emission_pop, .-emission_pop
	.section	.note.GNU-stack,"",@progbits
