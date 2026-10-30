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
