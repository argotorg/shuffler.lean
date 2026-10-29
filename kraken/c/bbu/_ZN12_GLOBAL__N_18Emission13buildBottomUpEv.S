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
