_ZN12_GLOBAL__N_18Emission13removeSurplusEv:
	pushq	%rbx
	movq	%rdi, %rbx
.LB276:
	movq	32(%rbx), %r8
	testq	%r8, %r8
	je	.LB295
	leaq	-1(%r8), %rdi
	movq	%rdi, %rax
	movq	$-1, %rdx
	movq	$-1, %rsi
	jmp	.LB279
	.p2align 5
.LB277:
	subq	$1, %rax
	cmpq	$-1, %rax
	je	.LB300
.LB279:
	cmpq	$-1, 56(%rbx,%rax,8)
	jne	.LB277
	cmpq	$-1, %rdx
	cmove	%rax, %rdx
	movq	%rdi, %rcx
	subq	%rax, %rcx
	cmpq	$16, %rcx
	cmovbe	%rax, %rsi
	jmp	.LB277
.LB300:
	cmpq	$-1, %rdx
	je	.LB293
	cmpq	$-1, %rsi
	je	.LB281
	cmpq	%rdx, %rdi
	je	.LB282
	leaq	0(,%rdi,8), %r8
	movq	%rdi, %rax
	.p2align 5
.LB283:
	testq	%rax, %rax
	je	.LB301
	subq	$1, %rax
	cmpq	$-1, 56(%rbx,%rax,8)
	jne	.LB283
	movq	24(%rbx), %rcx
	movq	(%rcx,%rax,8), %rdx
	xorq	(%rcx,%r8), %rdx
	salq	$16, %rdx
	jne	.LB283
	movq	56(%rbx,%rax,8), %rdx
	movq	56(%rbx,%rdi,8), %rcx
	movq	%rcx, 56(%rbx,%rax,8)
	movq	%rdx, 56(%rbx,%rdi,8)
	movq	56(%rbx,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB289
	movq	%rax, 8248(%rbx,%rdx,8)
.LB289:
	movq	56(%rbx,%rdi,8), %rax
	cmpq	$-1, %rax
	je	.LB282
	movq	%rdi, 8248(%rbx,%rax,8)
	jmp	.LB282
.LB281:
	subq	$17, %r8
	movl	$2, %eax
	subq	%rdx, %r8
	je	.LB275
	movq	%rdx, 16448(%rbx)
	movq	%r8, 16456(%rbx)
	movl	$1, %eax
	jmp	.LB275
.LB293:
	movl	$0, %eax
.LB275:
	popq	%rbx
	ret
.LB295:
	movl	$0, %eax
	jmp	.LB275
.LB301:
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	testb	%al, %al
	jne	.LB275
.LB282:
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission3popEv
	testb	%al, %al
	je	.LB276
	jmp	.LB275
	.size	_ZN12_GLOBAL__N_18Emission13removeSurplusEv, .-_ZN12_GLOBAL__N_18Emission13removeSurplusEv
