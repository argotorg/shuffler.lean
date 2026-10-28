urgent:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	movq	24(%rdi), %r13
	movq	%r13, %r14
	cmpq	%r13, %rsi
	jnb	.LB79
	movq	%rdi, %rbp
	movq	%rsi, %r15
	movq	%rsi, %rbx
	jmp	.LB84
.LB88:
	movq	56(%rbp), %rcx
	movq	%rax, (%rcx)
	movq	56(%rbp), %rax
	subq	$16, %rdx
	movq	%rdx, 8(%rax)
	movq	$-1, %r14
.LB79:
	movq	%r14, %rax
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB81:
	addq	$1, %rbx
	cmpq	%rbx, %r13
	je	.LB79
.LB84:
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	position_of
	testq	%rax, %rax
	jns	.LB81
	movq	32(%rbp), %rax
	movq	(%rax,%rbx,8), %r12
	testq	%r12, %r12
	je	.LB81
	testb	$1, %r12b
	je	.LB85
	cmpq	$1, %r12
	jne	.LB81
.LB85:
	movq	%r12, %rsi
	movq	%rbp, %rdi
	call	is_spilled
	testl	%eax, %eax
	jne	.LB81
	movq	%r12, %rsi
	movq	%rbp, %rdi
	call	shallowest_copy
	testq	%rax, %rax
	js	.LB81
	movq	0(%rbp), %rdx
	subq	%rax, %rdx
	leaq	-1(%rdx), %rcx
	cmpq	$15, %rcx
	ja	.LB88
	cmpq	%rax, %r15
	setne	%dl
	cmpq	%r13, %r14
	sete	%al
	testb	%al, %dl
	je	.LB81
	cmpq	$15, %rcx
	cmove	%rbx, %r14
	jmp	.LB81
	.size	urgent, .-urgent
