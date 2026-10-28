take_bound:
	movq	%rsi, %rcx
	movq	%rdx, %rsi
	cmpq	%rcx, %rdx
	jb	.LB73
	leaq	(%rdi,%rcx,8), %rax
	leaq	(%rdi,%rdx,8), %r8
	movq	64(%r8), %rdx
	cmpq	%rdx, 64(%rax)
	je	.LB68
	movq	(%rdi), %rax
	subq	$1, %rax
	cmpq	%rax, %rsi
	jb	.LB71
	jmp	.LB69
	.p2align 4
.LB70:
	subq	$1, %rax
	cmpq	%rax, %rsi
	jnb	.LB69
.LB71:
	cmpq	64(%rdi,%rax,8), %rdx
	jne	.LB70
	cmpq	%rax, 2112(%rdi,%rax,8)
	je	.LB70
	movq	%rax, %rsi
.LB69:
	leaq	264(%rsi), %rax
	movq	(%rdi,%rax,8), %rdx
	movq	2112(%r8), %r9
	movq	%r9, (%rdi,%rax,8)
	movq	%rdx, 2112(%r8)
	cmpq	%rcx, %rsi
	je	.LB75
	movq	(%rdi), %rdx
	leaq	-1(%rdx), %rcx
	movl	$1, %eax
	cmpq	%rsi, %rcx
	je	.LB66
	subq	%rsi, %rdx
	leaq	-1(%rdx), %rax
	cmpq	$16, %rax
	ja	.LB78
	call	swap_with
	testq	%rax, %rax
	movl	$1, %edx
	cmovns	%rdx, %rax
	ret
.LB78:
	movq	56(%rdi), %rax
	movq	%rsi, (%rax)
	movq	56(%rdi), %rax
	subq	$17, %rdx
	movq	%rdx, 8(%rax)
	movq	$-1, %rax
	ret
.LB73:
	movq	$-2, %rax
	ret
.LB75:
	movl	$0, %eax
	ret
.LB68:
	movq	2112(%rax), %rdx
	movq	2112(%r8), %rcx
	movq	%rcx, 2112(%rax)
	movq	%rdx, 2112(%r8)
	movl	$0, %eax
.LB66:
	ret
	.size	take_bound, .-take_bound
