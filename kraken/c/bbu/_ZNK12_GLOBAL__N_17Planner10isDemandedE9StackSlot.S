_ZNK12_GLOBAL__N_17Planner10isDemandedE9StackSlot:
	movq	24(%rdi), %r8
	testq	%r8, %r8
	je	.LB.Planner.isDemanded.3
	movq	16(%rdi), %rcx
	movl	$0, %eax
	jmp	.LB.Planner.isDemanded.1
	.p2align 4
.LB.Planner.isDemanded.0:
	addq	$1, %rax
	cmpq	%r8, %rax
	je	.LB.Planner.isDemanded.2
.LB.Planner.isDemanded.1:
	cmpb	$1, 4(%rcx,%rax,8)
	je	.LB.Planner.isDemanded.0
	movq	%rsi, %rdx
	xorq	(%rcx,%rax,8), %rdx
	salq	$16, %rdx
	jne	.LB.Planner.isDemanded.0
	movl	$1, %eax
	ret
.LB.Planner.isDemanded.2:
	movl	$0, %eax
	ret
.LB.Planner.isDemanded.3:
	movl	$0, %eax
	ret
	.size	_ZNK12_GLOBAL__N_17Planner10isDemandedE9StackSlot, .-_ZNK12_GLOBAL__N_17Planner10isDemandedE9StackSlot
