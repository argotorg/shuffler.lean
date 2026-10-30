_ZNK12_GLOBAL__N_114MappingBuilder11closestCopyE11StackOffsetNS0_12CopyLocationE:
	movq	%rsi, %r10
	movq	8(%rdi), %rsi
	testq	%rsi, %rsi
	je	.LB442
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
	jmp	.LB441
.LB437:
	cmpb	%dl, %bpl
	je	.LB451
	.p2align 5
.LB436:
	addq	$1, %rax
	addq	$1, %rcx
	cmpq	%rsi, %rax
	je	.LB452
.LB441:
	movq	%r8, %rdx
	xorq	(%r9,%rax,8), %rdx
	salq	$16, %rdx
	jne	.LB436
	movq	32(%rdi), %rdx
	cmpb	$0, (%rdx,%rax)
	jne	.LB436
	movq	48(%rdi), %rdx
	cmpq	$-1, (%rdx,%rax,8)
	jne	.LB436
	movl	$0, %edx
	cmpq	24(%rdi), %rax
	jnb	.LB437
	cmpb	$1, 4(%rbx,%rax,8)
	sete	%dl
	jmp	.LB437
.LB451:
	cmpq	$-1, %r11
	je	.LB444
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
	jmp	.LB436
.LB444:
	movq	%rax, %r11
	jmp	.LB436
.LB442:
	movq	$-1, %r11
	movq	%r11, %rax
	ret
.LB452:
	movq	%r11, %rax
	popq	%rbx
	popq	%rbp
	popq	%r14
	popq	%r15
	ret
	.size	_ZNK12_GLOBAL__N_114MappingBuilder11closestCopyE11StackOffsetNS0_12CopyLocationE, .-_ZNK12_GLOBAL__N_114MappingBuilder11closestCopyE11StackOffsetNS0_12CopyLocationE
