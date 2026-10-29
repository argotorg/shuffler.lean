push:
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbx
	movq	%rsi, %rbp
	movq	%rdx, %r12
	movq	%rdx, %rsi
	call	positionOf
	cmpq	$-1, %rax
	jne	.LB22
	movq	(%rbx), %rax
	movq	%r12, 8256(%rbx,%rax,8)
	movq	16(%rbx), %rax
	salq	$4, %rax
	addq	48(%rbx), %rax
	movq	$2, (%rax)
	movq	16(%rbx), %rax
	salq	$4, %rax
	addq	48(%rbx), %rax
	movq	%rbp, 8(%rax)
	addq	$1, 16(%rbx)
	movq	(%rbx), %rax
	movq	%rbp, 64(%rbx,%rax,8)
	addq	$1, %rax
	movq	%rax, (%rbx)
	movl	$0, %eax
.LB20:
	popq	%rbx
	popq	%rbp
	popq	%r12
	ret
.LB22:
	movq	$-2, %rax
	jmp	.LB20
	.size	push, .-push
