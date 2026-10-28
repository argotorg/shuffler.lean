shallowest_copy:
	movq	(%rdi), %rax
	.p2align 4
.LB12:
	testq	%rax, %rax
	je	.LB16
	subq	$1, %rax
	cmpq	%rsi, 64(%rdi,%rax,8)
	jne	.LB12
	ret
.LB16:
	movq	$-1, %rax
.LB11:
	ret
	.size	shallowest_copy, .-shallowest_copy
