generate:
	cmpq	24(%rdi), %rsi
	jnb	.LB47
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movq	%rsi, %rbx
	call	produce
	testq	%rax, %rax
	jne	.LB44
	movq	0(%rbp), %rdx
	leaq	1(%rbx), %rcx
	cmpq	%rdx, %rcx
	jnb	.LB44
	leaq	0(%rbp,%rbx,8), %rcx
	movq	8256(%rcx), %rsi
	cmpq	%rsi, %rbx
	je	.LB44
	leaq	0(%rbp,%rdx,8), %rdi
	movq	56(%rdi), %r8
	cmpq	%r8, 64(%rcx)
	je	.LB52
	subq	%rbx, %rdx
	subq	$1, %rdx
	cmpq	$16, %rdx
	jbe	.LB53
.LB44:
	popq	%rbx
	popq	%rbp
	ret
.LB52:
	movq	8248(%rdi), %rdx
	movq	%rdx, 8256(%rcx)
	movq	%rsi, 8248(%rdi)
	jmp	.LB44
.LB53:
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	swapWith
	jmp	.LB44
.LB47:
	movq	$-2, %rax
	ret
	.size	generate, .-generate
