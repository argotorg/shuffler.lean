step:
	pushq	%r14
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movq	%rsi, %rbx
	cmpq	(%rdi), %rsi
	jnb	.LB90
	leaq	1(%rsi), %rax
	cmpq	%rsi, 2112(%rdi,%rsi,8)
	je	.LB89
.LB90:
	cmpq	$0, 8(%rbp)
	je	.LB99
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	urgent
	testq	%rax, %rax
	js	.LB89
	movq	24(%rbp), %rdx
	movq	%rax, %rcx
	cmpq	%rax, %rbx
	je	.LB92
	cmpq	%rax, %rdx
	je	.LB92
	leaq	16(%rbx), %rdx
	cmpq	%rdx, 0(%rbp)
	jb	.LB106
.LB93:
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	position_of
	testq	%rax, %rax
	js	.LB94
	movq	%rax, %rdx
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	take_bound
	testq	%rax, %rax
	js	.LB89
	leaq	1(%rbx), %rax
	je	.LB89
	movq	0(%rbp), %rdx
	cmpq	%rdx, %rbx
	jnb	.LB103
	cmpq	%rbx, 2112(%rbp,%rbx,8)
	je	.LB104
.LB96:
	leaq	-1(%rdx), %rax
	cmpq	%rbx, %rax
	je	.LB97
	subq	%rbx, %rdx
	leaq	-1(%rdx), %rax
	cmpq	$16, %rax
	ja	.LB107
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	swap_with
	testq	%rax, %rax
	js	.LB89
.LB97:
	leaq	1(%rbx), %rax
.LB89:
	popq	%rbx
	popq	%rbp
	popq	%r14
	ret
.LB106:
	movq	%rax, %rsi
	movq	%rbp, %rdi
	call	generate
	testq	%rax, %rax
	cmovns	%rbx, %rax
	jmp	.LB89
.LB92:
	movq	0(%rbp), %rax
	movq	%rax, %r14
	cmpq	%rax, %rbx
	setb	%sil
	cmpq	%rdx, %rax
	setb	%al
	testb	%al, %sil
	je	.LB93
	cmpq	%rcx, %rdx
	jne	.LB93
	movq	%r14, %rsi
	movq	%rbp, %rdi
	call	position_of
	testq	%rax, %rax
	jns	.LB93
	leaq	16(%rbx), %rax
	cmpq	%rax, %r14
	jnb	.LB93
	movq	%r14, %rsi
	movq	%rbp, %rdi
	call	generate
	testq	%rax, %rax
	cmovns	%rbx, %rax
	jmp	.LB89
.LB94:
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	generate
	testq	%rax, %rax
	js	.LB89
	movq	0(%rbp), %rdx
	movq	$-2, %rax
	cmpq	%rdx, %rbx
	jnb	.LB89
	leaq	1(%rbx), %rax
	cmpq	%rbx, 2112(%rbp,%rbx,8)
	jne	.LB96
	jmp	.LB89
.LB107:
	movq	56(%rbp), %rax
	movq	%rbx, (%rax)
	movq	56(%rbp), %rax
	subq	$17, %rdx
	movq	%rdx, 8(%rax)
	movq	$-1, %rax
	jmp	.LB89
.LB99:
	movq	$-3, %rax
	jmp	.LB89
.LB103:
	movq	$-2, %rax
	jmp	.LB89
.LB104:
	movq	$-2, %rax
	jmp	.LB89
	.size	step, .-step
