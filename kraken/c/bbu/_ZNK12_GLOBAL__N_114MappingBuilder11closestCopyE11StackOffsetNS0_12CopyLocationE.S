_ZNK12_GLOBAL__N_114MappingBuilder11closestCopyE11StackOffsetNS0_12CopyLocationE:
	movq	%rsi, %r10
	movq	8(%rdi), %rsi
	testq	%rsi, %rsi
	je	.LB352
	pushq	%r15
	pushq	%r14
	pushq	%rbp
	pushq	%rbx
	cmpb	$1, %dl
	sete	%bpl
	movq	16(%rdi), %rbx
	movq	(%rdi), %r9
	movq	(%rbx,%r10,8), %r8
	movq	%r10, %rcx
	negq	%rcx
	movl	$0, %eax
	movq	$-1, %r11
	jmp	.LB351
.LB347:
	cmpb	%dl, %bpl
	je	.LB361
	.p2align 5
.LB346:
	addq	$1, %rax
	addq	$1, %rcx
	cmpq	%rsi, %rax
	je	.LB362
.LB351:
	movq	%r8, %rdx
	xorq	(%r9,%rax,8), %rdx
	salq	$16, %rdx
	jne	.LB346
	movq	32(%rdi), %rdx
	cmpb	$0, (%rdx,%rax)
	jne	.LB346
	movq	48(%rdi), %rdx
	cmpq	$-1, (%rdx,%rax,8)
	jne	.LB346
	movl	$0, %edx
	cmpq	24(%rdi), %rax
	jnb	.LB347
	cmpb	$1, 4(%rbx,%rax,8)
	sete	%dl
	jmp	.LB347
.LB361:
	cmpq	$-1, %r11
	je	.LB354
	movq	%r10, %rdx
	subq	%rax, %rdx
	cmpq	%rax, %r10
	cmovb	%rcx, %rdx
	movq	%r11, %r14
	subq	%r10, %r14
	movq	%r10, %r15
	subq	%r11, %r15
	cmpq	%r11, %r10
	cmovnb	%r15, %r14
	cmpq	%rdx, %r14
	cmovnb	%rax, %r11
	jmp	.LB346
.LB354:
	movq	%rax, %r11
	jmp	.LB346
.LB352:
	movq	$-1, %r11
	movq	%r11, %rax
	ret
.LB362:
	movq	%r11, %rax
	popq	%rbx
	popq	%rbp
	popq	%r14
	popq	%r15
	ret
	.size	_ZNK12_GLOBAL__N_114MappingBuilder11closestCopyE11StackOffsetNS0_12CopyLocationE, .-_ZNK12_GLOBAL__N_114MappingBuilder11closestCopyE11StackOffsetNS0_12CopyLocationE
