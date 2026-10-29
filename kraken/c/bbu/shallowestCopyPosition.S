shallowestCopyPosition:
	movq	(%rdi), %rax
	.p2align 4
.LB11:
	testq	%rax, %rax
	je	.LB14
	subq	$1, %rax
	cmpq	%rsi, 64(%rdi,%rax,8)
	jne	.LB11
	ret
.LB14:
	movq	$-1, %rax
.LB10:
	ret
	.size	shallowestCopyPosition, .-shallowestCopyPosition
