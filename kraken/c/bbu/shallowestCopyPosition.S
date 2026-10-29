shallowestCopyPosition:
	movq	(%rdi), %rax
	.p2align 5
.LB6:
	testq	%rax, %rax
	je	.LB9
	subq	$1, %rax
	movq	64(%rdi), %rdx
	movq	%rsi, %rcx
	xorq	(%rdx,%rax,8), %rcx
	movq	%rcx, %rdx
	salq	$16, %rdx
	jne	.LB6
	ret
.LB9:
	movq	$-1, %rax
.LB7:
	ret
	.size	shallowestCopyPosition, .-shallowestCopyPosition
