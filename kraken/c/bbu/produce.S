produce:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$8, %rsp
	movq	%rdi, %rbx
	movq	%rsi, %rbp
	leaq	0(,%rsi,8), %r14
	movq	%r14, %rax
	addq	32(%rdi), %rax
	movq	(%rax), %r13
	movzbl	4(%rax), %r15d
	movzbl	5(%rax), %eax
	movb	%al, 7(%rsp)
	movq	%r13, %rsi
	call	shallowestCopyPosition
	cmpb	$1, %r15b
	je	.LB39
	movq	%rax, %r12
	cmpq	$-1, %rax
	je	.LB31
	notq	%rax
	addq	(%rbx), %rax
	cmpq	$15, %rax
	jbe	.LB40
.LB31:
	cmpb	$0, 7(%rsp)
	je	.LB32
	cmpb	$2, %r15b
	jne	.LB41
.LB32:
	movq	%rbp, %rdx
	movq	%r13, %rsi
	movq	%rbx, %rdi
	call	push
.LB30:
	testq	%rax, %rax
	jne	.LB28
	movq	(%rbx), %rcx
	leaq	-1(%rcx), %rdx
	cmpq	%rdx, 8264(%rbx,%r14)
	jne	.LB37
	movq	8(%rbx), %rdx
	testq	%rdx, %rdx
	je	.LB28
	subq	$1, %rdx
	movq	%rdx, 8(%rbx)
.LB28:
	addq	$8, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB39:
	movq	%rbp, %rdx
	movq	%r13, %rsi
	movq	%rbx, %rdi
	call	push
	jmp	.LB30
.LB40:
	movq	%rbp, %rdx
	movq	%r12, %rsi
	movq	%rbx, %rdi
	call	dup
	jmp	.LB30
.LB41:
	movq	%r13, %rsi
	movq	%rbx, %rdi
	call	isSpilled
	testl	%eax, %eax
	jne	.LB32
	cmpq	$-1, %r12
	je	.LB35
	movq	$-16, %rdx
	subq	%r12, %rdx
	movq	$-2, %rax
	addq	(%rbx), %rdx
	je	.LB28
	movq	56(%rbx), %rax
	movq	%r12, (%rax)
	movq	56(%rbx), %rax
	movq	%rdx, 8(%rax)
	movq	$-1, %rax
	jmp	.LB28
.LB35:
	movq	$-2, %rax
	jmp	.LB28
.LB37:
	movq	$-2, %rax
	jmp	.LB28
	.size	produce, .-produce
