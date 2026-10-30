_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot:
	movq	32(%rdi), %rax
	.p2align 5
.LB.Emission.shallowestCopyPosition.0:
	testq	%rax, %rax
	je	.LB.Emission.shallowestCopyPosition.1
	subq	$1, %rax
	movq	24(%rdi), %rdx
	movq	%rsi, %rcx
	xorq	(%rdx,%rax,8), %rcx
	movq	%rcx, %rdx
	salq	$16, %rdx
	jne	.LB.Emission.shallowestCopyPosition.0
	ret
.LB.Emission.shallowestCopyPosition.1:
	movq	$-1, %rax
.LB.Emission.shallowestCopyPosition.2:
	ret
	.size	_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot, .-_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot
