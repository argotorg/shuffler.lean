generate:
	cmpq	24(%rdi), %rsi
	jnb	.LB45
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movq	%rsi, %rbx
	call	produce
	testq	%rax, %rax
	jne	.LB42
	movq	0(%rbp), %rdx
	leaq	1(%rbx), %rcx
	cmpq	%rdx, %rcx
	jnb	.LB42
	leaq	0(%rbp,%rbx,8), %rdi
	movq	72(%rdi), %rsi
	cmpq	%rbx, %rsi
	je	.LB42
	movq	64(%rbp), %r9
	leaq	-1(%rdx), %r8
	leaq	0(,%r8,8), %r10
	movq	(%r9,%rbx,8), %rcx
	xorq	(%r9,%r8,8), %rcx
	salq	$16, %rcx
	jne	.LB44
	movq	72(%rbp,%r8,8), %rdx
	movq	%rdx, 72(%rdi)
	movq	%rsi, 72(%rbp,%r10)
	movq	72(%rdi), %rdx
	movq	%rbx, 8264(%rbp,%rdx,8)
	movq	%r8, 8264(%rbp,%rsi,8)
.LB42:
	popq	%rbx
	popq	%rbp
	ret
.LB44:
	subq	%rbx, %rdx
	subq	$1, %rdx
	cmpq	$16, %rdx
	ja	.LB42
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	swapWith
	jmp	.LB42
.LB45:
	movq	$-2, %rax
	ret
	.size	generate, .-generate
