_ZN12_GLOBAL__N_18Emission3dupE11StackOffsetS1_:
	subq	$8, %rsp
	movq	24(%rdi), %rcx
	cmpb	$3, 4(%rcx,%rsi,8)
	je	.LB.Emission.dup.0
	movq	%rdi, %rax
	movq	32(%rdi), %rdi
	subq	%rsi, %rdi
	movq	48(%rax), %rcx
	leaq	1(%rcx), %r8
	movq	%r8, 48(%rax)
	leaq	(%rcx,%rcx,2), %rcx
	salq	$2, %rcx
	addq	40(%rax), %rcx
	movb	$1, (%rcx)
	movb	%dil, 1(%rcx)
	movl	$0, 4(%rcx)
	movb	$1, 8(%rcx)
	movb	$5, 9(%rcx)
	movq	24(%rax), %rcx
	movq	32(%rax), %rdi
	movq	(%rcx,%rsi,8), %rsi
	movq	%rsi, (%rcx,%rdi,8)
	movq	32(%rax), %rcx
	leaq	1(%rcx), %rsi
	movq	%rsi, 32(%rax)
	cmpq	$-1, 8248(%rax,%rdx,8)
	je	.LB.Emission.dup.1
	movl	$1, %edi
	call	exit
.LB.Emission.dup.0:
	movl	$1, %edi
	call	exit
.LB.Emission.dup.1:
	movq	%rdx, 56(%rax,%rcx,8)
	movq	%rcx, 8248(%rax,%rdx,8)
	movl	$0, %eax
	addq	$8, %rsp
	ret
	.size	_ZN12_GLOBAL__N_18Emission3dupE11StackOffsetS1_, .-_ZN12_GLOBAL__N_18Emission3dupE11StackOffsetS1_
