produce:
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbx
	movq	%rsi, %rbp
	movq	32(%rdi), %rax
	movq	(%rax,%rsi,8), %r12
	testq	%r12, %r12
	je	.LB39
	movq	%r12, %rsi
	call	shallowest_copy
	movq	%rax, %r13
	testq	%rax, %rax
	js	.LB29
	movq	(%rbx), %r8
	subq	%rax, %r8
	leaq	-1(%r8), %rax
	cmpq	$15, %rax
	jbe	.LB40
.LB29:
	testb	$1, %r12b
	je	.LB37
	cmpq	$1, %r12
	jne	.LB30
.LB37:
	movq	%r12, %rsi
	movq	%rbx, %rdi
	call	is_spilled
	testl	%eax, %eax
	je	.LB32
.LB30:
	movq	%r12, %r8
	movl	$2, %ecx
	movq	%rbp, %rdx
	movq	%r12, %rsi
	movq	%rbx, %rdi
	call	add
.LB28:
	testq	%rax, %rax
	js	.LB26
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	call	position_of
	movq	%rax, %rdx
	movq	(%rbx), %rax
	subq	$1, %rax
	cmpq	%rax, %rdx
	jne	.LB35
	movq	8(%rbx), %rdx
	movl	$0, %eax
	testq	%rdx, %rdx
	je	.LB26
	subq	$1, %rdx
	movq	%rdx, 8(%rbx)
.LB26:
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	ret
.LB39:
	movl	$0, %r8d
	movl	$2, %ecx
	movq	%rsi, %rdx
	movl	$0, %esi
	call	add
	jmp	.LB28
.LB40:
	movl	$1, %ecx
	movq	%rbp, %rdx
	movq	%r12, %rsi
	movq	%rbx, %rdi
	call	add
	jmp	.LB28
.LB32:
	testq	%r13, %r13
	js	.LB34
	movq	(%rbx), %rax
	subq	$16, %rax
	subq	%r13, %rax
	movq	56(%rbx), %rdx
	movq	%r13, (%rdx)
	movq	56(%rbx), %rdx
	movq	%rax, 8(%rdx)
	movq	$-1, %rax
	jmp	.LB26
.LB34:
	movq	$-2, %rax
	jmp	.LB26
.LB35:
	movq	$-2, %rax
	jmp	.LB26
	.size	produce, .-produce
