add:
	pushq	%r15
	pushq	%r14
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbx
	movq	%rsi, %r12
	movq	%rdx, %rbp
	movq	%rcx, %r14
	movq	%r8, %r15
	movq	%rdx, %rsi
	call	position_of
	testq	%rax, %rax
	jns	.LB19
	movq	16(%rbx), %rax
	salq	$4, %rax
	addq	48(%rbx), %rax
	movq	%r14, (%rax)
	movq	16(%rbx), %rax
	salq	$4, %rax
	addq	48(%rbx), %rax
	movq	%r15, 8(%rax)
	addq	$1, 16(%rbx)
	movq	(%rbx), %rax
	movq	%r12, 64(%rbx,%rax,8)
	movq	%rbp, 2112(%rbx,%rax,8)
	addq	$1, %rax
	movq	%rax, (%rbx)
	movl	$0, %eax
.LB17:
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r14
	popq	%r15
	ret
.LB19:
	movq	$-2, %rax
	jmp	.LB17
	.size	add, .-add
