_ZN12_GLOBAL__N_114MappingBuilder17keepWildcardSlotsEv:
	movq	8(%rdi), %rax
	movq	24(%rdi), %rdx
	cmpq	%rdx, %rax
	cmova	%rdx, %rax
	testq	%rax, %rax
	je	.LB405
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movl	$0, %ebx
	jmp	.LB404
	.p2align 6
.LB403:
	addq	$1, %rbx
	movq	8(%rbp), %rax
	movq	24(%rbp), %rdx
	cmpq	%rdx, %rax
	cmova	%rdx, %rax
	cmpq	%rax, %rbx
	jnb	.LB411
.LB404:
	leaq	0(,%rbx,8), %rdx
	movq	16(%rbp), %rax
	cmpb	$1, 4(%rax,%rbx,8)
	jne	.LB403
	movq	48(%rbp), %rax
	cmpq	$-1, 8192(%rax,%rdx)
	jne	.LB403
	movq	32(%rbp), %rdx
	cmpb	$0, (%rdx,%rbx)
	jne	.LB403
	cmpq	$-1, (%rax,%rbx,8)
	jne	.LB403
	movq	%rbx, %rdx
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
	testb	%al, %al
	je	.LB403
	jmp	.LB401
.LB411:
	movl	$0, %eax
.LB401:
	popq	%rbx
	popq	%rbp
	ret
.LB405:
	movl	$0, %eax
	ret
	.size	_ZN12_GLOBAL__N_114MappingBuilder17keepWildcardSlotsEv, .-_ZN12_GLOBAL__N_114MappingBuilder17keepWildcardSlotsEv
