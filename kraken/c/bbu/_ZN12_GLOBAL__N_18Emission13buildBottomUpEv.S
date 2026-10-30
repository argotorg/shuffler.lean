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
	je	.LB.Emission.buildBottomUp.31
	movl	$0, %r14d
	jmp	.LB.Emission.buildBottomUp.26
.LB.Emission.buildBottomUp.0:
	movl	$2, %eax
	cmpq	%r13, %r15
	jne	.LB.Emission.buildBottomUp.13
.LB.Emission.buildBottomUp.1:
	movq	56(%r12,%rdx,8), %rax
	cmpq	$-1, %rax
	je	.LB.Emission.buildBottomUp.2
	movq	%rax, 16(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rdx, %r13
	jne	.LB.Emission.buildBottomUp.1
	leaq	16(%rsp), %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE
	jmp	.LB.Emission.buildBottomUp.13
.LB.Emission.buildBottomUp.2:
	movl	$2, %eax
	jmp	.LB.Emission.buildBottomUp.13
.LB.Emission.buildBottomUp.3:
	movq	%rax, 16448(%r12)
	subq	$16, %rcx
	movq	%rcx, 16456(%r12)
	movl	$1, %eax
	jmp	.LB.Emission.buildBottomUp.13
	.p2align 5
.LB.Emission.buildBottomUp.4:
	addq	$1, %rbx
	cmpq	%r13, %rbx
	je	.LB.Emission.buildBottomUp.6
.LB.Emission.buildBottomUp.5:
	cmpq	$-1, 8248(%r12,%rbx,8)
	jne	.LB.Emission.buildBottomUp.4
	movq	(%r12), %rax
	leaq	(%rax,%rbx,8), %rax
	movq	(%rax), %rbp
	movzbl	4(%rax), %edx
	cmpb	$1, %dl
	je	.LB.Emission.buildBottomUp.4
	movzbl	5(%rax), %ecx
	movzbl	%dl, %eax
	salq	$32, %rax
	movabsq	$-1095216660481, %rsi
	andq	%rsi, %rbp
	orq	%rax, %rbp
	testb	%cl, %cl
	je	.LB.Emission.buildBottomUp.4
	cmpb	$2, %dl
	je	.LB.Emission.buildBottomUp.4
	movzbl	%cl, %ecx
	salq	$40, %rcx
	movabsq	$-280375465082881, %rax
	andq	%rax, %rbp
	orq	%rcx, %rbp
	movq	%rbp, %rsi
	movq	%r12, %rdi
	call	_ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot
	testb	%al, %al
	jne	.LB.Emission.buildBottomUp.4
	movq	%rbp, %rsi
	movq	%r12, %rdi
	call	_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot
	cmpq	$-1, %rax
	je	.LB.Emission.buildBottomUp.4
	movq	%r15, %rcx
	subq	%rax, %rcx
	leaq	-1(%rcx), %rdx
	cmpq	$15, %rdx
	ja	.LB.Emission.buildBottomUp.3
	cmpq	%r14, %rax
	sete	%al
	cmpq	$15, %rdx
	setne	%dl
	orb	%dl, %al
	jne	.LB.Emission.buildBottomUp.4
	movq	8(%rsp), %rax
	cmpq	$-1, %rax
	cmove	%rbx, %rax
	movq	%rax, 8(%rsp)
	jmp	.LB.Emission.buildBottomUp.4
.LB.Emission.buildBottomUp.6:
	movq	8(%rsp), %rdi
	cmpq	$-1, %rdi
	sete	%al
	cmpq	%r14, %rdi
	je	.LB.Emission.buildBottomUp.7
	testb	%al, %al
	je	.LB.Emission.buildBottomUp.14
.LB.Emission.buildBottomUp.7:
	cmpq	%r13, %r15
	setb	%cl
	cmpq	%r15, %r14
	setb	%dl
	testb	%dl, %cl
	je	.LB.Emission.buildBottomUp.8
	testb	%al, %al
	jne	.LB.Emission.buildBottomUp.15
.LB.Emission.buildBottomUp.8:
	leaq	0(,%r14,8), %rbx
	movq	8248(%r12,%rbx), %rdx
	cmpq	$-1, %rdx
	je	.LB.Emission.buildBottomUp.16
	cmpq	%r14, %rdx
	jb	.LB.Emission.buildBottomUp.28
	movq	24(%r12), %rcx
	movq	(%rcx,%rdx,8), %rsi
	movq	%rsi, %rdi
	xorq	(%rcx,%r14,8), %rdi
	movq	%r14, %rax
	salq	$16, %rdi
	jne	.LB.Emission.buildBottomUp.18
.LB.Emission.buildBottomUp.9:
	movq	%rax, %rsi
	movq	56(%r12,%rax,8), %rcx
	movq	56(%r12,%rdx,8), %rdi
	movq	%rdi, 56(%r12,%rax,8)
	movq	%rcx, 56(%r12,%rdx,8)
	movq	56(%r12,%rax,8), %rcx
	cmpq	$-1, %rcx
	je	.LB.Emission.buildBottomUp.10
	movq	%rax, 8248(%r12,%rcx,8)
.LB.Emission.buildBottomUp.10:
	movq	56(%r12,%rdx,8), %rcx
	cmpq	$-1, %rcx
	je	.LB.Emission.buildBottomUp.11
	movq	%rdx, 8248(%r12,%rcx,8)
.LB.Emission.buildBottomUp.11:
	cmpq	%rax, %r14
	je	.LB.Emission.buildBottomUp.24
	leaq	-1(%r15), %rdx
	cmpq	%rax, %rdx
	je	.LB.Emission.buildBottomUp.12
	subq	%rax, %r15
	leaq	-1(%r15), %rdx
	cmpq	$16, %rdx
	ja	.LB.Emission.buildBottomUp.22
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	testb	%al, %al
	jne	.LB.Emission.buildBottomUp.13
.LB.Emission.buildBottomUp.12:
	movq	32(%r12), %rax
	cmpq	%rax, %r14
	jnb	.LB.Emission.buildBottomUp.30
	cmpq	%r14, 56(%r12,%rbx)
	jne	.LB.Emission.buildBottomUp.17
	movl	$2, %eax
.LB.Emission.buildBottomUp.13:
	addq	$8216, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB.Emission.buildBottomUp.14:
	movq	%r15, %rax
	subq	%r14, %rax
	cmpq	$15, %rax
	ja	.LB.Emission.buildBottomUp.8
	movq	8(%rsp), %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
	testb	%al, %al
	jne	.LB.Emission.buildBottomUp.13
	subq	$1, %r14
	jmp	.LB.Emission.buildBottomUp.25
.LB.Emission.buildBottomUp.15:
	cmpq	$-1, 8248(%r12,%r15,8)
	jne	.LB.Emission.buildBottomUp.8
	movq	%r15, %rax
	subq	%r14, %rax
	cmpq	$15, %rax
	ja	.LB.Emission.buildBottomUp.8
	movq	%r15, %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
	testb	%al, %al
	jne	.LB.Emission.buildBottomUp.13
	subq	$1, %r14
	jmp	.LB.Emission.buildBottomUp.25
.LB.Emission.buildBottomUp.16:
	movq	%r14, %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
	testb	%al, %al
	jne	.LB.Emission.buildBottomUp.13
	movq	32(%r12), %rax
	cmpq	%rax, %r14
	jnb	.LB.Emission.buildBottomUp.29
	cmpq	%r14, 56(%r12,%rbx)
	je	.LB.Emission.buildBottomUp.25
.LB.Emission.buildBottomUp.17:
	leaq	-1(%rax), %rdx
	cmpq	%r14, %rdx
	je	.LB.Emission.buildBottomUp.25
	subq	%r14, %rax
	leaq	-1(%rax), %rdx
	cmpq	$16, %rdx
	ja	.LB.Emission.buildBottomUp.23
	movq	%r14, %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	testb	%al, %al
	je	.LB.Emission.buildBottomUp.25
	jmp	.LB.Emission.buildBottomUp.13
.LB.Emission.buildBottomUp.18:
	leaq	-1(%r15), %rax
	cmpq	%rax, %rdx
	jb	.LB.Emission.buildBottomUp.20
	movq	%rdx, %rax
	jmp	.LB.Emission.buildBottomUp.9
	.p2align 5
.LB.Emission.buildBottomUp.19:
	subq	$1, %rax
	cmpq	%rax, %rdx
	jnb	.LB.Emission.buildBottomUp.21
.LB.Emission.buildBottomUp.20:
	movq	%rsi, %rdi
	xorq	(%rcx,%rax,8), %rdi
	salq	$16, %rdi
	jne	.LB.Emission.buildBottomUp.19
	cmpq	%rax, 56(%r12,%rax,8)
	je	.LB.Emission.buildBottomUp.19
	xorq	(%rcx,%rax,8), %rsi
	salq	$16, %rsi
	je	.LB.Emission.buildBottomUp.9
	movl	$2, %eax
	jmp	.LB.Emission.buildBottomUp.13
.LB.Emission.buildBottomUp.21:
	movq	%rdx, %rax
	jmp	.LB.Emission.buildBottomUp.9
.LB.Emission.buildBottomUp.22:
	movq	%rax, 16448(%r12)
	subq	$17, %r15
	movq	%r15, 16456(%r12)
	movl	$1, %eax
	jmp	.LB.Emission.buildBottomUp.13
.LB.Emission.buildBottomUp.23:
	movq	%r14, 16448(%r12)
	subq	$17, %rax
	movq	%rax, 16456(%r12)
	movl	$1, %eax
	jmp	.LB.Emission.buildBottomUp.13
.LB.Emission.buildBottomUp.24:
	movq	%rax, %r14
.LB.Emission.buildBottomUp.25:
	addq	$1, %r14
	movq	8(%r12), %r13
	cmpq	%r13, %r14
	jnb	.LB.Emission.buildBottomUp.31
.LB.Emission.buildBottomUp.26:
	movq	32(%r12), %r15
	cmpq	%r15, %r14
	jnb	.LB.Emission.buildBottomUp.27
	cmpq	%r14, 56(%r12,%r14,8)
	je	.LB.Emission.buildBottomUp.25
.LB.Emission.buildBottomUp.27:
	movq	16440(%r12), %rdx
	testq	%rdx, %rdx
	je	.LB.Emission.buildBottomUp.0
	movq	%r14, %rbx
	movq	$-1, 8(%rsp)
	movl	$1, %eax
	cmpq	%r13, %r14
	jb	.LB.Emission.buildBottomUp.5
	jmp	.LB.Emission.buildBottomUp.7
.LB.Emission.buildBottomUp.28:
	movl	$2, %eax
	jmp	.LB.Emission.buildBottomUp.13
.LB.Emission.buildBottomUp.29:
	movl	$2, %eax
	jmp	.LB.Emission.buildBottomUp.13
.LB.Emission.buildBottomUp.30:
	movl	$2, %eax
	jmp	.LB.Emission.buildBottomUp.13
.LB.Emission.buildBottomUp.31:
	cmpq	%r13, 32(%r12)
	setne	%al
	addl	%eax, %eax
	jmp	.LB.Emission.buildBottomUp.13
	.size	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv, .-_ZN12_GLOBAL__N_18Emission13buildBottomUpEv
