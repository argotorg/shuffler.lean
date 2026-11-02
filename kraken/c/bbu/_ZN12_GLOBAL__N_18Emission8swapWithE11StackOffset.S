_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset:
	subq	$8, %rsp
	movq	%rsi, %rdx
	movq	32(%rdi), %rsi
	cmpq	%rsi, %rdx
	jnb	.LB.Emission.swapWith.0
	movq	%rdi, %rax
	leaq	0(,%rdx,8), %rcx
	cmpq	56(%rdi,%rdx,8), %rdx
	jne	.LB.Emission.swapWith.1
	movl	$1, %edi
	call	exit
.LB.Emission.swapWith.0:
	movl	$1, %edi
	call	exit
.LB.Emission.swapWith.1:
	movq	%rsi, %rdi
	subq	%rdx, %rdi
	leaq	-2(%rdi), %rdi
	cmpq	$15, %rdi
	ja	.LB.Emission.swapWith.4
	movq	24(%rax), %rdi
	addq	%rdi, %rcx
	movl	(%rcx), %r10d
	movzbl	4(%rcx), %r9d
	movzbl	5(%rcx), %r8d
	movq	-8(%rdi,%rsi,8), %rsi
	movq	%rsi, (%rcx)
	movq	32(%rax), %rsi
	movq	24(%rax), %rcx
	leaq	-8(%rcx,%rsi,8), %rcx
	movl	%r10d, (%rcx)
	movb	%r9b, 4(%rcx)
	movb	%r8b, 5(%rcx)
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
	je	.LB.Emission.swapWith.2
	movq	%rdx, 8248(%rax,%rsi,8)
.LB.Emission.swapWith.2:
	movq	56(%rax,%rcx,8), %rdx
	cmpq	$-1, %rdx
	je	.LB.Emission.swapWith.3
	movq	%rcx, 8248(%rax,%rdx,8)
.LB.Emission.swapWith.3:
	movl	$0, %eax
	addq	$8, %rsp
	ret
.LB.Emission.swapWith.4:
	movl	$1, %edi
	call	exit
	.size	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset, .-_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
