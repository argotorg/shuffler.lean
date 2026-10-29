dup:
	movq	%rdi, %rax
	cmpq	$-1, 8264(%rdi,%rdx,8)
	jne	.LB27
	movq	(%rdi), %rcx
	movq	%rdx, 72(%rdi,%rcx,8)
	movq	%rcx, 8264(%rdi,%rdx,8)
	movq	16(%rdi), %rdx
	leaq	(%rdx,%rdx,2), %rdi
	movq	48(%rax), %rdx
	leaq	(%rdx,%rdi,4), %rdx
	movb	$1, (%rdx)
	subq	%rsi, %rcx
	movb	%cl, 1(%rdx)
	movl	$0, 4(%rdx)
	movb	$1, 8(%rdx)
	movb	$5, 9(%rdx)
	addq	$1, 16(%rax)
	movq	64(%rax), %rdx
	movq	(%rax), %rcx
	movq	(%rdx,%rsi,8), %rsi
	movq	%rsi, (%rdx,%rcx,8)
	addq	$1, (%rax)
	movl	$0, %eax
	ret
.LB27:
	movq	$-2, %rax
	ret
	.size	dup, .-dup
