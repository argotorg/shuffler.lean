swapWith:
	movq	(%rdi), %r10
	cmpq	%r10, %rsi
	jnb	.LB12
	movq	%rdi, %rax
	movq	%rsi, %rdx
	leaq	0(,%rsi,8), %rdi
	leaq	(%rax,%rdi), %r11
	cmpq	%rsi, 72(%r11)
	je	.LB13
	movq	%r10, %rsi
	subq	%rdx, %rsi
	leaq	-2(%rsi), %rcx
	cmpq	$15, %rcx
	ja	.LB14
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	leaq	-1(%r10), %r8
	movq	16(%rax), %rcx
	leaq	(%rcx,%rcx,2), %r9
	movq	48(%rax), %rcx
	leaq	(%rcx,%r9,4), %rcx
	movb	$0, (%rcx)
	subq	$1, %rsi
	movb	%sil, 1(%rcx)
	movl	$0, 4(%rcx)
	movb	$1, 8(%rcx)
	movb	$5, 9(%rcx)
	addq	$1, 16(%rax)
	movq	64(%rax), %r9
	leaq	(%r9,%rdi), %rcx
	movl	(%rcx), %r12d
	movzbl	4(%rcx), %ebp
	movzbl	5(%rcx), %ebx
	leaq	0(,%r8,8), %rsi
	movq	(%r9,%r8,8), %r9
	movq	%r9, (%rcx)
	movq	%rsi, %rcx
	addq	64(%rax), %rcx
	movl	%r12d, (%rcx)
	movb	%bpl, 4(%rcx)
	movb	%bl, 5(%rcx)
	movq	72(%rax,%rdi), %rcx
	movq	64(%rax,%r10,8), %rdi
	movq	%rdi, 72(%r11)
	movq	%rcx, 72(%rax,%rsi)
	movq	72(%r11), %rsi
	movq	%rdx, 8264(%rax,%rsi,8)
	movq	%r8, 8264(%rax,%rcx,8)
	movl	$0, %eax
	popq	%rbx
	popq	%rbp
	popq	%r12
	ret
.LB12:
	movq	$-2, %rax
	ret
.LB13:
	movq	$-2, %rax
	ret
.LB14:
	movq	$-2, %rax
	ret
	.size	swapWith, .-swapWith
