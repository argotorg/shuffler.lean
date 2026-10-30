_ZN12_GLOBAL__N_18Emission3dupE11StackOffsetS1_:
	movq	%rdi, %rax
	movq	%rdx, %rcx
	movq	24(%rdi), %rdi
	movl	$2, %edx
	cmpb	$3, 4(%rdi,%rsi,8)
	je	.LB14
	movq	32(%rax), %rdi
	subq	%rsi, %rdi
	movq	48(%rax), %rdx
	leaq	1(%rdx), %r8
	movq	%r8, 48(%rax)
	leaq	(%rdx,%rdx,2), %rdx
	salq	$2, %rdx
	addq	40(%rax), %rdx
	movb	$1, (%rdx)
	movb	%dil, 1(%rdx)
	movl	$0, 4(%rdx)
	movb	$1, 8(%rdx)
	movb	$5, 9(%rdx)
	movq	24(%rax), %rdx
	movq	32(%rax), %rdi
	movq	(%rdx,%rsi,8), %rsi
	movq	%rsi, (%rdx,%rdi,8)
	movq	32(%rax), %rsi
	leaq	1(%rsi), %rdx
	movq	%rdx, 32(%rax)
	movl	$2, %edx
	cmpq	$-1, 8248(%rax,%rcx,8)
	jne	.LB14
	movq	%rcx, 56(%rax,%rsi,8)
	movq	%rsi, 8248(%rax,%rcx,8)
	movl	$0, %edx
.LB14:
	movl	%edx, %eax
	ret
	.size	_ZN12_GLOBAL__N_18Emission3dupE11StackOffsetS1_, .-_ZN12_GLOBAL__N_18Emission3dupE11StackOffsetS1_
