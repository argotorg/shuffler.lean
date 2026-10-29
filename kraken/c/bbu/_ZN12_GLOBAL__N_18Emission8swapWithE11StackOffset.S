_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset:
	movq	%rdi, %rax
	movq	%rsi, %rdx
	movq	32(%rdi), %rsi
	movl	$2, %ecx
	cmpq	%rsi, %rdx
	jnb	.LB46
	leaq	0(,%rdx,8), %rdi
	cmpq	56(%rax,%rdx,8), %rdx
	je	.LB46
	movq	%rsi, %rcx
	subq	%rdx, %rcx
	leaq	-2(%rcx), %r8
	movl	$2, %ecx
	cmpq	$15, %r8
	ja	.LB46
	movq	24(%rax), %r8
	leaq	(%r8,%rdi), %rcx
	movl	(%rcx), %r10d
	movzbl	4(%rcx), %r9d
	movzbl	5(%rcx), %edi
	movq	-8(%r8,%rsi,8), %rsi
	movq	%rsi, (%rcx)
	movq	32(%rax), %rsi
	movq	24(%rax), %rcx
	leaq	-8(%rcx,%rsi,8), %rcx
	movl	%r10d, (%rcx)
	movb	%r9b, 4(%rcx)
	movb	%dil, 5(%rcx)
	movq	%rdx, %rsi
	notq	%rsi
	addq	32(%rax), %rsi
	movq	48(%rax), %rcx
	leaq	1(%rcx), %rdi
	movq	%rdi, 48(%rax)
	leaq	(%rcx,%rcx,2), %rcx
	salq	$2, %rcx
	addq	40(%rax), %rcx
	movb	$0, (%rcx)
	movb	%sil, 1(%rcx)
	movl	$0, 4(%rcx)
	movb	$1, 8(%rcx)
	movb	$5, 9(%rcx)
	movq	32(%rax), %rdi
	leaq	-1(%rdi), %rcx
	movq	56(%rax,%rdx,8), %rsi
	movq	56(%rax,%rcx,8), %rdi
	movq	%rdi, 56(%rax,%rdx,8)
	movq	%rsi, 56(%rax,%rcx,8)
	movq	56(%rax,%rdx,8), %rsi
	cmpq	$-1, %rsi
	je	.LB48
	movq	%rdx, 8248(%rax,%rsi,8)
.LB48:
	movq	56(%rax,%rcx,8), %rdx
	cmpq	$-1, %rdx
	je	.LB49
	movq	%rcx, 8248(%rax,%rdx,8)
.LB49:
	movl	$0, %ecx
.LB46:
	movl	%ecx, %eax
	ret
	.size	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset, .-_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
