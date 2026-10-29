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
	je	.LB41
	movq	%r12, %rsi
	call	shallowestCopyPosition
	movq	%rax, %r13
	cmpq	$-1, %rax
	je	.LB31
	notq	%rax
	addq	(%rbx), %rax
	cmpq	$15, %rax
	jbe	.LB42
.LB31:
	testb	$1, %r12b
	je	.LB39
	cmpq	$1, %r12
	jne	.LB32
.LB39:
	movq	%r12, %rsi
	movq	%rbx, %rdi
	call	isSpilled
	testl	%eax, %eax
	je	.LB34
.LB32:
	movq	%rbp, %rdx
	movq	%r12, %rsi
	movq	%rbx, %rdi
	call	push
	movq	%rax, %r12
.LB30:
	testq	%r12, %r12
	je	.LB43
.LB28:
	movq	%r12, %rax
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	ret
.LB41:
	movq	%rsi, %rdx
	movl	$0, %esi
	call	push
	movq	%rax, %r12
	jmp	.LB30
.LB42:
	movq	%rbp, %rdx
	movq	%r13, %rsi
	movq	%rbx, %rdi
	call	dup
	movq	%rax, %r12
	jmp	.LB30
.LB34:
	cmpq	$-1, %r13
	je	.LB36
	movq	(%rbx), %rax
	subq	$16, %rax
	movq	$-2, %r12
	subq	%r13, %rax
	je	.LB28
	movq	56(%rbx), %rdx
	movq	%r13, (%rdx)
	movq	56(%rbx), %rdx
	movq	%rax, 8(%rdx)
	movq	$-1, %r12
	jmp	.LB28
.LB43:
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	call	positionOf
	movq	%rax, %rdx
	movq	(%rbx), %rax
	subq	$1, %rax
	cmpq	%rax, %rdx
	jne	.LB38
	movq	8(%rbx), %rax
	testq	%rax, %rax
	je	.LB28
	subq	$1, %rax
	movq	%rax, 8(%rbx)
	jmp	.LB28
.LB36:
	movq	$-2, %r12
	jmp	.LB28
.LB38:
	movq	$-2, %r12
	jmp	.LB28
	.size	produce, .-produce
