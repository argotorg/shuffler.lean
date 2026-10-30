_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_:
	movq	32(%rdi), %rax
	movzbl	(%rax,%rsi), %eax
	testb	%al, %al
	jne	.LB431
	movq	48(%rdi), %rcx
	cmpq	$-1, (%rcx,%rsi,8)
	jne	.LB432
	cmpq	$-1, 8192(%rcx,%rdx,8)
	jne	.LB433
	movq	%rdx, (%rcx,%rsi,8)
	movq	%rsi, 8192(%rcx,%rdx,8)
	ret
.LB431:
	movl	$2, %eax
	ret
.LB432:
	movl	$2, %eax
	ret
.LB433:
	movl	$2, %eax
	ret
	.size	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_, .-_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
