position_of:
	movq	(%rdi), %rdx
	testq	%rdx, %rdx
	je	.LB9
	movl	$0, %eax
	.p2align 5
.LB8:
	cmpq	%rsi, 8256(%rdi,%rax,8)
	je	.LB5
	addq	$1, %rax
	cmpq	%rdx, %rax
	jne	.LB8
	movq	$-1, %rax
	ret
.LB9:
	movq	$-1, %rax
.LB5:
	ret
	.size	position_of, .-position_of
