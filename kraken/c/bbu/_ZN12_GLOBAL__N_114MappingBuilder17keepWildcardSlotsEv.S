_ZN12_GLOBAL__N_114MappingBuilder17keepWildcardSlotsEv:
	movq	8(%rdi), %rax
	movq	24(%rdi), %rdx
	cmpq	%rdx, %rax
	cmova	%rdx, %rax
	testq	%rax, %rax
	je	.LB.MappingBuilder.keepWildcardSlots.4
	pushq	%rbp
	pushq	%rbx
	subq	$8, %rsp
	movq	%rdi, %rbp
	movl	$0, %ebx
	jmp	.LB.MappingBuilder.keepWildcardSlots.1
	.p2align 6
.LB.MappingBuilder.keepWildcardSlots.0:
	addq	$1, %rbx
	movq	8(%rbp), %rax
	movq	24(%rbp), %rdx
	cmpq	%rdx, %rax
	cmova	%rdx, %rax
	cmpq	%rax, %rbx
	jnb	.LB.MappingBuilder.keepWildcardSlots.2
.LB.MappingBuilder.keepWildcardSlots.1:
	leaq	0(,%rbx,8), %rdx
	movq	16(%rbp), %rax
	cmpb	$1, 4(%rax,%rbx,8)
	jne	.LB.MappingBuilder.keepWildcardSlots.0
	movq	48(%rbp), %rax
	cmpq	$-1, 8192(%rax,%rdx)
	jne	.LB.MappingBuilder.keepWildcardSlots.0
	movq	32(%rbp), %rdx
	cmpb	$0, (%rdx,%rbx)
	jne	.LB.MappingBuilder.keepWildcardSlots.0
	cmpq	$-1, (%rax,%rbx,8)
	jne	.LB.MappingBuilder.keepWildcardSlots.0
	movq	%rbx, %rdx
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
	testb	%al, %al
	je	.LB.MappingBuilder.keepWildcardSlots.0
	jmp	.LB.MappingBuilder.keepWildcardSlots.3
.LB.MappingBuilder.keepWildcardSlots.2:
	movl	$0, %eax
.LB.MappingBuilder.keepWildcardSlots.3:
	addq	$8, %rsp
	popq	%rbx
	popq	%rbp
	ret
.LB.MappingBuilder.keepWildcardSlots.4:
	movl	$0, %eax
	ret
	.size	_ZN12_GLOBAL__N_114MappingBuilder17keepWildcardSlotsEv, .-_ZN12_GLOBAL__N_114MappingBuilder17keepWildcardSlotsEv
