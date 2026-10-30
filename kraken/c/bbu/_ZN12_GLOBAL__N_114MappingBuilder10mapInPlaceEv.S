_ZN12_GLOBAL__N_114MappingBuilder10mapInPlaceEv:
	movq	8(%rdi), %rax
	movq	24(%rdi), %rdx
	cmpq	%rdx, %rax
	cmova	%rdx, %rax
	testq	%rax, %rax
	je	.LB367
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movl	$0, %ebx
	jmp	.LB366
	.p2align 6
.LB365:
	addq	$1, %rbx
	movq	8(%rbp), %rax
	movq	24(%rbp), %rdx
	cmpq	%rdx, %rax
	cmova	%rdx, %rax
	cmpq	%rax, %rbx
	jnb	.LB373
.LB366:
	movq	16(%rbp), %rax
	movq	0(%rbp), %rdx
	movq	(%rax,%rbx,8), %rax
	xorq	(%rdx,%rbx,8), %rax
	salq	$16, %rax
	jne	.LB365
	movq	32(%rbp), %rax
	cmpb	$0, (%rax,%rbx)
	jne	.LB365
	movq	48(%rbp), %rax
	cmpq	$-1, (%rax,%rbx,8)
	jne	.LB365
	movq	%rbx, %rdx
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
	testb	%al, %al
	je	.LB365
	jmp	.LB363
.LB373:
	movl	$0, %eax
.LB363:
	popq	%rbx
	popq	%rbp
	ret
.LB367:
	movl	$0, %eax
	ret
	.size	_ZN12_GLOBAL__N_114MappingBuilder10mapInPlaceEv, .-_ZN12_GLOBAL__N_114MappingBuilder10mapInPlaceEv
