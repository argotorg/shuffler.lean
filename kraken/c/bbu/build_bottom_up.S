build_bottom_up:
	subq	$16456, %rsp
	movq	%rcx, 32(%rsp)
	movq	%rsi, 24(%rsp)
	movq	%r9, 40(%rsp)
	movq	%rdi, (%rsp)
	testq	%rdi, %rdi
	je	.LB113
	movl	$0, %eax
	.p2align 5
.LB114:
	movq	(%rdx,%rax,8), %rcx
	movq	%rcx, 64(%rsp,%rax,8)
	movq	(%r8,%rax,8), %rcx
	movq	%rcx, 8256(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB114
.LB113:
	subq	%rdi, %rsi
	movq	%rsi, 8(%rsp)
	movq	$0, 16(%rsp)
	movq	16464(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	16472(%rsp), %rax
	movq	%rax, 56(%rsp)
	movq	%rsp, %rdi
	call	buildBottomUp
	testq	%rax, %rax
	cmove	16(%rsp), %rax
	addq	$16456, %rsp
	ret
	.size	build_bottom_up, .-build_bottom_up
