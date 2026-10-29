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
