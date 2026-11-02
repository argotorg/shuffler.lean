_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_:
	subq	$8, %rsp
	movq	32(%rdi), %rax
	cmpb	$0, (%rax,%rsi)
	jne	.LB.MappingBuilder.map.0
	movq	48(%rdi), %rax
	cmpq	$-1, (%rax,%rsi,8)
	je	.LB.MappingBuilder.map.1
.LB.MappingBuilder.map.0:
	movl	$1, %edi
	call	exit
.LB.MappingBuilder.map.1:
	cmpq	$-1, 8192(%rax,%rdx,8)
	je	.LB.MappingBuilder.map.2
	movl	$1, %edi
	call	exit
.LB.MappingBuilder.map.2:
	movq	%rdx, (%rax,%rsi,8)
	movq	%rsi, 8192(%rax,%rdx,8)
	movl	$0, %eax
	addq	$8, %rsp
	ret
	.size	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_, .-_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
