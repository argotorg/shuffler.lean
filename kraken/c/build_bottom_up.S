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
	movq	32(%rdi), %rdi
	subq	%rsi, %rdi
	movq	48(%rax), %rcx
	leaq	1(%rcx), %r8
	movq	%r8, 48(%rax)
	leaq	(%rcx,%rcx,2), %rcx
	salq	$2, %rcx
	addq	40(%rax), %rcx
	movb	$1, (%rcx)
	movb	%dil, 1(%rcx)
	movl	$0, 4(%rcx)
	movb	$1, 8(%rcx)
	movb	$5, 9(%rcx)
	movq	24(%rax), %rcx
	movq	32(%rax), %rdi
	movq	(%rcx,%rsi,8), %rsi
	movq	%rsi, (%rcx,%rdi,8)
	movq	32(%rax), %rcx
	leaq	1(%rcx), %rsi
	movq	%rsi, 32(%rax)
	movl	$2, %esi
	cmpq	$-1, 8248(%rax,%rdx,8)
	jne	.LB14
	movq	%rdx, 56(%rax,%rcx,8)
	movq	%rcx, 8248(%rax,%rdx,8)
	movl	$0, %esi
.LB14:
	movl	%esi, %eax
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
	je	.LB32
	movq	(%rsp), %rax
	cmpq	$-1, %rax
	je	.LB20
	notq	%rax
	addq	32(%rbx), %rax
	cmpq	$15, %rax
	jbe	.LB21
.LB20:
	cmpb	$2, %r13b
	je	.LB22
	testb	%r15b, %r15b
	jne	.LB33
.LB22:
	movq	%r12, %rdx
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission4pushE9StackSlot11StackOffset
.LB19:
	testb	%al, %al
	jne	.LB17
	movq	32(%rbx), %rcx
	leaq	-1(%rcx), %rdx
	cmpq	%rdx, 8248(%rbx,%r14)
	jne	.LB28
	subq	$1, 16440(%rbx)
.LB17:
	addq	$8, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB32:
	movq	%r12, %rdx
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission4pushE9StackSlot11StackOffset
	jmp	.LB19
.LB21:
	movq	%r12, %rdx
	movq	(%rsp), %rsi
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission3dupE11StackOffsetS1_
	jmp	.LB19
.LB33:
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	call	_ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot
	testb	%al, %al
	jne	.LB22
	movl	$2, %eax
	cmpq	$-1, (%rsp)
	je	.LB17
	movq	$-16, %rdx
	movq	(%rsp), %rcx
	subq	%rcx, %rdx
	movl	$2, %eax
	addq	32(%rbx), %rdx
	je	.LB17
	movq	%rcx, 16448(%rbx)
	movq	%rdx, 16456(%rbx)
	movl	$1, %eax
	jmp	.LB17
.LB28:
	movl	$2, %eax
	jmp	.LB17
	.size	_ZN12_GLOBAL__N_18Emission7produceE11StackOffset, .-_ZN12_GLOBAL__N_18Emission7produceE11StackOffset
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission19permuteDestinationsEv, @function
_ZN12_GLOBAL__N_18Emission19permuteDestinationsEv:
	pushq	%rbp
	pushq	%rbx
	subq	$4120, %rsp
	movq	%rdi, %rbx
	movq	32(%rdi), %rdi
	testq	%rdi, %rdi
	je	.LB35
	movl	$0, %eax
.LB37:
	movq	56(%rbx,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB41
	movw	%dx, 2064(%rsp,%rax,2)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB37
.LB35:
	leaq	12(%rsp), %rcx
	leaq	16(%rsp), %rdx
	leaq	2064(%rsp), %rsi
	call	permute
	testq	%rax, %rax
	js	.LB38
	leaq	16(%rsp), %rcx
	leaq	(%rax,%rcx), %r9
	movl	$0, %eax
	jle	.LB34
.LB40:
	movzbl	(%rcx), %eax
	movq	32(%rbx), %rsi
	leaq	-1(%rsi), %r8
	movq	24(%rbx), %rdi
	movq	%r8, %rdx
	subq	%rax, %rdx
	leaq	(%rdi,%rdx,8), %rdx
	movl	(%rdx), %ebp
	movzbl	4(%rdx), %r11d
	movzbl	5(%rdx), %r10d
	movq	(%rdi,%r8,8), %rdi
	movq	%rdi, (%rdx)
	movq	32(%rbx), %rdi
	movq	24(%rbx), %rdx
	leaq	-8(%rdx,%rdi,8), %rdx
	movl	%ebp, (%rdx)
	movb	%r11b, 4(%rdx)
	movb	%r10b, 5(%rdx)
	addq	32(%rbx), %rax
	subq	%rsi, %rax
	movq	%rax, %rdx
	movq	48(%rbx), %rax
	leaq	1(%rax), %rsi
	movq	%rsi, 48(%rbx)
	leaq	(%rax,%rax,2), %rax
	salq	$2, %rax
	addq	40(%rbx), %rax
	movb	$0, (%rax)
	movb	%dl, 1(%rax)
	movl	$0, 4(%rax)
	movb	$1, 8(%rax)
	movb	$5, 9(%rax)
	addq	$1, %rcx
	cmpq	%r9, %rcx
	jne	.LB40
	movl	$0, %eax
	jmp	.LB34
.LB38:
	movzwl	14(%rsp), %eax
	movzwl	12(%rsp), %edx
	movq	%rdx, 16448(%rbx)
	movq	%rax, 16456(%rbx)
	movl	$1, %eax
	jmp	.LB34
.LB41:
	movl	$2, %eax
.LB34:
	addq	$4120, %rsp
	popq	%rbx
	popq	%rbp
	ret
	.size	_ZN12_GLOBAL__N_18Emission19permuteDestinationsEv, .-_ZN12_GLOBAL__N_18Emission19permuteDestinationsEv
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset, @function
_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset:
	movq	%rdi, %rax
	movq	%rsi, %rdx
	movq	32(%rdi), %rsi
	movl	$2, %ecx
	cmpq	%rsi, %rdx
	jnb	.LB46
	leaq	0(,%rdx,8), %rdi
	cmpq	56(%rax,%rdx,8), %rdx
	je	.LB46
	movq	%rsi, %rcx
	subq	%rdx, %rcx
	leaq	-2(%rcx), %r8
	movl	$2, %ecx
	cmpq	$15, %r8
	ja	.LB46
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
	je	.LB48
	movq	%rdx, 8248(%rax,%rsi,8)
.LB48:
	movq	56(%rax,%rcx,8), %rdx
	cmpq	$-1, %rdx
	je	.LB49
	movq	%rcx, 8248(%rax,%rdx,8)
.LB49:
	movl	$0, %ecx
.LB46:
	movl	%ecx, %eax
	ret
	.size	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset, .-_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset, @function
_ZN12_GLOBAL__N_18Emission8generateE11StackOffset:
	movl	$2, %eax
	cmpq	8(%rdi), %rsi
	jnb	.LB60
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movq	%rsi, %rbx
	call	_ZN12_GLOBAL__N_18Emission7produceE11StackOffset
	testb	%al, %al
	jne	.LB53
	movq	32(%rbp), %rdx
	leaq	1(%rbx), %rcx
	cmpq	%rdx, %rcx
	jnb	.LB53
	cmpq	%rbx, 56(%rbp,%rbx,8)
	je	.LB53
	movq	24(%rbp), %rdi
	leaq	-1(%rdx), %rsi
	movq	(%rdi,%rsi,8), %rcx
	xorq	(%rdi,%rbx,8), %rcx
	salq	$16, %rcx
	je	.LB63
	subq	%rbx, %rdx
	subq	$1, %rdx
	cmpq	$16, %rdx
	jbe	.LB64
.LB53:
	popq	%rbx
	popq	%rbp
	ret
.LB63:
	movq	56(%rbp,%rbx,8), %rdx
	movq	56(%rbp,%rsi,8), %rcx
	movq	%rcx, 56(%rbp,%rbx,8)
	movq	%rdx, 56(%rbp,%rsi,8)
	movq	56(%rbp,%rbx,8), %rdx
	cmpq	$-1, %rdx
	je	.LB56
	movq	%rbx, 8248(%rbp,%rdx,8)
.LB56:
	movq	56(%rbp,%rsi,8), %rdx
	cmpq	$-1, %rdx
	je	.LB53
	movq	%rsi, 8248(%rbp,%rdx,8)
	jmp	.LB53
.LB64:
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	jmp	.LB53
.LB60:
	ret
	.size	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset, .-_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
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
	je	.LB66
	movl	$0, %r14d
	jmp	.LB100
.LB69:
	movl	$2, %eax
	cmpq	%r13, %r15
	jne	.LB65
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission19permuteDestinationsEv
	jmp	.LB65
.LB120:
	movq	%rax, 16448(%r12)
	subq	$16, %rcx
	movq	%rcx, 16456(%r12)
	movl	$1, %eax
	jmp	.LB65
	.p2align 5
.LB76:
	addq	$1, %rbx
	cmpq	%r13, %rbx
	je	.LB119
.LB70:
	cmpq	$-1, 8248(%r12,%rbx,8)
	jne	.LB76
	movq	(%r12), %rax
	leaq	(%rax,%rbx,8), %rax
	movq	(%rax), %rbp
	movzbl	4(%rax), %edx
	cmpb	$1, %dl
	je	.LB76
	movzbl	5(%rax), %ecx
	movzbl	%dl, %eax
	salq	$32, %rax
	movabsq	$-1095216660481, %rsi
	andq	%rsi, %rbp
	orq	%rax, %rbp
	testb	%cl, %cl
	je	.LB76
	cmpb	$2, %dl
	je	.LB76
	movzbl	%cl, %ecx
	salq	$40, %rcx
	movabsq	$-280375465082881, %rax
	andq	%rax, %rbp
	orq	%rcx, %rbp
	movq	%rbp, %rsi
	movq	%r12, %rdi
	call	_ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot
	testb	%al, %al
	jne	.LB76
	movq	%rbp, %rsi
	movq	%r12, %rdi
	call	_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot
	cmpq	$-1, %rax
	je	.LB76
	movq	%r15, %rcx
	subq	%rax, %rcx
	leaq	-1(%rcx), %rdx
	cmpq	$15, %rdx
	ja	.LB120
	cmpq	%r14, %rax
	sete	%al
	cmpq	$15, %rdx
	setne	%dl
	orb	%dl, %al
	jne	.LB76
	movq	8(%rsp), %rax
	cmpq	$-1, %rax
	cmove	%rbx, %rax
	movq	%rax, 8(%rsp)
	jmp	.LB76
.LB119:
	movq	8(%rsp), %rdi
	cmpq	$-1, %rdi
	sete	%al
	cmpq	%r14, %rdi
	je	.LB71
	testb	%al, %al
	je	.LB121
.LB71:
	cmpq	%r13, %r15
	setb	%cl
	cmpq	%r15, %r14
	setb	%dl
	testb	%dl, %cl
	je	.LB78
	testb	%al, %al
	jne	.LB122
.LB78:
	leaq	0(,%r14,8), %rbx
	movq	8248(%r12,%rbx), %rdx
	cmpq	$-1, %rdx
	je	.LB82
	cmpq	%r14, %rdx
	jb	.LB123
	movq	24(%r12), %rcx
	movq	(%rcx,%rdx,8), %rsi
	movq	%rsi, %rdi
	xorq	(%rcx,%r14,8), %rdi
	movq	%r14, %rax
	salq	$16, %rdi
	jne	.LB124
.LB90:
	movq	%rax, %rsi
	movq	56(%r12,%rax,8), %rcx
	movq	56(%r12,%rdx,8), %rdi
	movq	%rdi, 56(%r12,%rax,8)
	movq	%rcx, 56(%r12,%rdx,8)
	movq	56(%r12,%rax,8), %rcx
	cmpq	$-1, %rcx
	je	.LB91
	movq	%rax, 8248(%r12,%rcx,8)
.LB91:
	movq	56(%r12,%rdx,8), %rcx
	cmpq	$-1, %rcx
	je	.LB92
	movq	%rdx, 8248(%r12,%rcx,8)
.LB92:
	cmpq	%rax, %r14
	je	.LB107
	leaq	-1(%r15), %rdx
	cmpq	%rax, %rdx
	je	.LB93
	subq	%rax, %r15
	leaq	-1(%r15), %rdx
	cmpq	$16, %rdx
	ja	.LB125
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	testb	%al, %al
	jne	.LB65
.LB93:
	movq	32(%r12), %rax
	cmpq	%rax, %r14
	jnb	.LB109
	cmpq	%r14, 56(%r12,%rbx)
	jne	.LB95
	movl	$2, %eax
.LB65:
	addq	$24, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB121:
	movq	%r15, %rax
	subq	%r14, %rax
	cmpq	$15, %rax
	ja	.LB78
	movq	8(%rsp), %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
	testb	%al, %al
	jne	.LB65
	subq	$1, %r14
	jmp	.LB98
.LB122:
	cmpq	$-1, 8248(%r12,%r15,8)
	jne	.LB78
	movq	%r15, %rax
	subq	%r14, %rax
	cmpq	$15, %rax
	ja	.LB78
	movq	%r15, %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
	testb	%al, %al
	jne	.LB65
	subq	$1, %r14
	jmp	.LB98
.LB82:
	movq	%r14, %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
	testb	%al, %al
	jne	.LB65
	movq	32(%r12), %rax
	cmpq	%rax, %r14
	jnb	.LB108
	cmpq	%r14, 56(%r12,%rbx)
	je	.LB98
.LB95:
	leaq	-1(%rax), %rdx
	cmpq	%r14, %rdx
	je	.LB98
	subq	%r14, %rax
	leaq	-1(%rax), %rdx
	cmpq	$16, %rdx
	ja	.LB126
	movq	%r14, %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	testb	%al, %al
	je	.LB98
	jmp	.LB65
.LB124:
	leaq	-1(%r15), %rax
	cmpq	%rax, %rdx
	jb	.LB89
	movq	%rdx, %rax
	jmp	.LB90
	.p2align 5
.LB87:
	subq	$1, %rax
	cmpq	%rax, %rdx
	jnb	.LB127
.LB89:
	movq	%rsi, %rdi
	xorq	(%rcx,%rax,8), %rdi
	salq	$16, %rdi
	jne	.LB87
	cmpq	%rax, 56(%r12,%rax,8)
	je	.LB87
	xorq	(%rcx,%rax,8), %rsi
	salq	$16, %rsi
	je	.LB90
	movl	$2, %eax
	jmp	.LB65
.LB127:
	movq	%rdx, %rax
	jmp	.LB90
.LB125:
	movq	%rax, 16448(%r12)
	subq	$17, %r15
	movq	%r15, 16456(%r12)
	movl	$1, %eax
	jmp	.LB65
.LB126:
	movq	%r14, 16448(%r12)
	subq	$17, %rax
	movq	%rax, 16456(%r12)
	movl	$1, %eax
	jmp	.LB65
.LB107:
	movq	%rax, %r14
.LB98:
	addq	$1, %r14
	movq	8(%r12), %r13
	cmpq	%r13, %r14
	jnb	.LB66
.LB100:
	movq	32(%r12), %r15
	cmpq	%r15, %r14
	jnb	.LB67
	cmpq	%r14, 56(%r12,%r14,8)
	je	.LB98
.LB67:
	cmpq	$0, 16440(%r12)
	je	.LB69
	movq	%r14, %rbx
	movq	$-1, 8(%rsp)
	movl	$1, %eax
	cmpq	%r13, %r14
	jb	.LB70
	jmp	.LB71
.LB123:
	movl	$2, %eax
	jmp	.LB65
.LB108:
	movl	$2, %eax
	jmp	.LB65
.LB109:
	movl	$2, %eax
	jmp	.LB65
.LB66:
	cmpq	%r13, 32(%r12)
	setne	%al
	addl	%eax, %eax
	jmp	.LB65
	.size	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv, .-_ZN12_GLOBAL__N_18Emission13buildBottomUpEv
	.globl	build_bottom_up
	.type	build_bottom_up, @function
build_bottom_up:
	cmpq	%rdi, %rsi
	jb	.LB141
	cmpq	$1024, %rsi
	ja	.LB141
	subq	$16472, %rsp
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%rdx, 24(%rsp)
	movq	%rdi, 32(%rsp)
	movq	16480(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	testq	%rsi, %rsi
	je	.LB130
	movl	$0, %eax
	.p2align 5
.LB131:
	movq	$-1, 8248(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rsi
	jne	.LB131
	testq	%rdi, %rdi
	je	.LB132
.LB138:
	movl	$0, %eax
	.p2align 5
.LB133:
	movq	(%r8,%rax,8), %rdx
	movq	%rdx, 56(%rsp,%rax,8)
	movq	%rax, 8248(%rsp,%rdx,8)
	addq	$1, %rax
	cmpq	%rdi, %rax
	jb	.LB133
	movq	$0, 16440(%rsp)
	testq	%rsi, %rsi
	je	.LB134
.LB140:
	movq	%rsp, %rax
	leaq	(%rax,%rsi,8), %rdx
	jmp	.LB136
	.p2align 5
.LB135:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB134
.LB136:
	cmpq	$-1, 8248(%rax)
	jne	.LB135
	addq	$1, 16440(%rsp)
	jmp	.LB135
.LB137:
	movq	16448(%rsp), %rax
	movq	16488(%rsp), %rcx
	movq	%rax, (%rcx)
	movq	16456(%rsp), %rax
	movq	%rax, 8(%rcx)
	movq	$-1, %rax
	jmp	.LB128
.LB141:
	movq	$-2, %rax
	ret
.LB130:
	testq	%rdi, %rdi
	jne	.LB138
	movq	$0, 16440(%rsp)
.LB134:
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv
	cmpb	$1, %al
	je	.LB137
	cmpb	$2, %al
	movq	$-2, %rax
	cmovne	48(%rsp), %rax
.LB128:
	addq	$16472, %rsp
	ret
.LB132:
	movq	$0, 16440(%rsp)
	jmp	.LB140
	.size	build_bottom_up, .-build_bottom_up
	.section	.note.GNU-stack,"",@progbits
