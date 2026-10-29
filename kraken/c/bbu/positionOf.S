positionOf:
	movq	(%rdi), %rdx
	testq	%rdx, %rdx
	je	.LB8
	movl	$0, %eax
	.p2align 5
.LB7:
	cmpq	%rsi, 8256(%rdi,%rax,8)
	je	.LB5
	addq	$1, %rax
	cmpq	%rdx, %rax
	jne	.LB7
	movq	$-1, %rax
	ret
.LB8:
	movq	$-1, %rax
.LB5:
	ret
	.size	positionOf, .-positionOf
