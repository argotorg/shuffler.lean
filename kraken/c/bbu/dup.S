dup:
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbx
	movq	%rsi, %rbp
	movq	%rdx, %r12
	movq	%rdx, %rsi
	call	positionOf
	cmpq	$-1, %rax
	jne	.LB26
	movq	(%rbx), %rdx
	movq	%r12, 8256(%rbx,%rdx,8)
	movq	16(%rbx), %rax
	salq	$4, %rax
	addq	48(%rbx), %rax
	movq	$1, (%rax)
	movq	16(%rbx), %rax
	salq	$4, %rax
	addq	48(%rbx), %rax
	subq	%rbp, %rdx
	movq	%rdx, 8(%rax)
	addq	$1, 16(%rbx)
	movq	(%rbx), %rax
	movq	64(%rbx,%rbp,8), %rdx
	movq	%rdx, 64(%rbx,%rax,8)
	addq	$1, %rax
	movq	%rax, (%rbx)
	movl	$0, %eax
.LB24:
	popq	%rbx
	popq	%rbp
	popq	%r12
	ret
.LB26:
	movq	$-2, %rax
	jmp	.LB24
	.size	dup, .-dup
