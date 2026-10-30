_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_:
	movq	32(%rdi), %rax
	movzbl	(%rax,%rsi), %eax
	testb	%al, %al
	jne	.LB.MappingBuilder.map.0
	movq	48(%rdi), %rcx
	cmpq	$-1, (%rcx,%rsi,8)
	jne	.LB.MappingBuilder.map.1
	cmpq	$-1, 8192(%rcx,%rdx,8)
	jne	.LB.MappingBuilder.map.2
	movq	%rdx, (%rcx,%rsi,8)
	movq	%rsi, 8192(%rcx,%rdx,8)
	ret
.LB.MappingBuilder.map.0:
	movl	$2, %eax
	ret
.LB.MappingBuilder.map.1:
	movl	$2, %eax
	ret
.LB.MappingBuilder.map.2:
	movl	$2, %eax
	ret
	.size	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_, .-_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
