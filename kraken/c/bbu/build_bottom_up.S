build_bottom_up:
	subq	$16472, %rsp
	movq	%rcx, 32(%rsp)
	movq	%rsi, 24(%rsp)
	movq	%r9, 40(%rsp)
	movq	%rdx, 64(%rsp)
	movq	%rdi, (%rsp)
	testq	%rsi, %rsi
	je	.LB111
	movq	%rsp, %rax
	leaq	(%rax,%rsi,8), %rdx
	.p2align 5
.LB112:
	movq	$-1, 8264(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB112
.LB111:
	testq	%rdi, %rdi
	je	.LB113
	movl	$0, %eax
	.p2align 5
.LB114:
	movq	(%r8,%rax,8), %rdx
	movq	%rdx, 72(%rsp,%rax,8)
	movq	%rax, 8264(%rsp,%rdx,8)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB114
.LB113:
	subq	%rdi, %rsi
	movq	%rsi, 8(%rsp)
	movq	$0, 16(%rsp)
	movq	16480(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	16488(%rsp), %rax
	movq	%rax, 56(%rsp)
	movq	%rsp, %rdi
	call	buildBottomUp
	testq	%rax, %rax
	cmove	16(%rsp), %rax
	addq	$16472, %rsp
	ret
	.size	build_bottom_up, .-build_bottom_up
