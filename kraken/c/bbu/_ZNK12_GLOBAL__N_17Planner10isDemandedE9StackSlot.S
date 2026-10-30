_ZNK12_GLOBAL__N_17Planner10isDemandedE9StackSlot:
	movq	24(%rdi), %r8
	testq	%r8, %r8
	je	.LB554
	movq	16(%rdi), %rcx
	movl	$0, %eax
	jmp	.LB553
	.p2align 4
.LB552:
	addq	$1, %rax
	cmpq	%r8, %rax
	je	.LB557
.LB553:
	cmpb	$1, 4(%rcx,%rax,8)
	je	.LB552
	movq	%rsi, %rdx
	xorq	(%rcx,%rax,8), %rdx
	salq	$16, %rdx
	jne	.LB552
	movl	$1, %eax
	ret
.LB557:
	movl	$0, %eax
	ret
.LB554:
	movl	$0, %eax
	ret
	.size	_ZNK12_GLOBAL__N_17Planner10isDemandedE9StackSlot, .-_ZNK12_GLOBAL__N_17Planner10isDemandedE9StackSlot
