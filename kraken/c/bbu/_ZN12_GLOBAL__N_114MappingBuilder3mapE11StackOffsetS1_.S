_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_:
	movq	32(%rdi), %rax
	movzbl	(%rax,%rsi), %eax
	testb	%al, %al
	jne	.LB341
	movq	48(%rdi), %rcx
	cmpq	$-1, (%rcx,%rsi,8)
	jne	.LB342
	cmpq	$-1, 8192(%rcx,%rdx,8)
	jne	.LB343
	movq	%rdx, (%rcx,%rsi,8)
	movq	%rsi, 8192(%rcx,%rdx,8)
	ret
.LB341:
	movl	$2, %eax
	ret
.LB342:
	movl	$2, %eax
	ret
.LB343:
	movl	$2, %eax
	ret
	.size	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_, .-_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
