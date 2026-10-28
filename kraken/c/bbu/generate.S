generate:
	cmpq	24(%rdi), %rsi
	jnb	.LB44
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movq	%rsi, %rbx
	call	produce
	testq	%rax, %rax
	js	.LB41
	movq	0(%rbp), %rdx
	leaq	1(%rbx), %rcx
	movl	$0, %eax
	cmpq	%rdx, %rcx
	jnb	.LB41
	leaq	0(%rbp,%rbx,8), %rcx
	movq	2112(%rcx), %rsi
	cmpq	%rbx, %rsi
	je	.LB41
	leaq	0(%rbp,%rdx,8), %rax
	movq	56(%rax), %rdi
	cmpq	%rdi, 64(%rcx)
	je	.LB52
	subq	$1, %rdx
	subq	%rbx, %rdx
	movl	$0, %eax
	cmpq	$16, %rdx
	jbe	.LB53
.LB41:
	popq	%rbx
	popq	%rbp
	ret
.LB52:
	movq	2104(%rax), %rdx
	movq	%rdx, 2112(%rcx)
	movq	%rsi, 2104(%rax)
	movl	$0, %eax
	jmp	.LB41
.LB53:
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	swap_with
	jmp	.LB41
.LB44:
	movq	$-2, %rax
	ret
	.size	generate, .-generate
