swap_with:
	movq	(%rdi), %r8
	cmpq	%r8, %rsi
	jnb	.LB23
	leaq	(%rdi,%rsi,8), %rax
	cmpq	%rsi, 8256(%rax)
	je	.LB24
	leaq	-1(%r8), %rcx
	subq	%rsi, %rcx
	leaq	-1(%rcx), %rdx
	cmpq	$15, %rdx
	ja	.LB25
	movq	16(%rdi), %rdx
	salq	$4, %rdx
	addq	48(%rdi), %rdx
	movq	$0, (%rdx)
	movq	16(%rdi), %rdx
	salq	$4, %rdx
	addq	48(%rdi), %rdx
	movq	%rcx, 8(%rdx)
	addq	$1, 16(%rdi)
	movq	64(%rax), %rcx
	leaq	(%rdi,%r8,8), %rdx
	movq	56(%rdx), %rsi
	movq	%rsi, 64(%rax)
	movq	%rcx, 56(%rdx)
	movq	8256(%rax), %rcx
	movq	8248(%rdx), %rsi
	movq	%rsi, 8256(%rax)
	movq	%rcx, 8248(%rdx)
	movl	$0, %eax
	ret
.LB23:
	movq	$-2, %rax
	ret
.LB24:
	movq	$-2, %rax
	ret
.LB25:
	movq	$-2, %rax
	ret
	.size	swap_with, .-swap_with
