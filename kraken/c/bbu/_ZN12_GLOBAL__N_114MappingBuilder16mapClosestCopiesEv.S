_ZN12_GLOBAL__N_114MappingBuilder16mapClosestCopiesEv:
	cmpq	$0, 24(%rdi)
	je	.LB.MappingBuilder.mapClosestCopies.4
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movl	$0, %ebx
	jmp	.LB.MappingBuilder.mapClosestCopies.1
	.p2align 6
.LB.MappingBuilder.mapClosestCopies.0:
	addq	$1, %rbx
	cmpq	24(%rbp), %rbx
	jnb	.LB.MappingBuilder.mapClosestCopies.2
.LB.MappingBuilder.mapClosestCopies.1:
	leaq	0(,%rbx,8), %rdx
	movq	48(%rbp), %rax
	cmpq	$-1, 8192(%rax,%rbx,8)
	jne	.LB.MappingBuilder.mapClosestCopies.0
	movq	16(%rbp), %rax
	cmpb	$1, 4(%rax,%rdx)
	je	.LB.MappingBuilder.mapClosestCopies.0
	movl	$0, %edx
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	_ZNK12_GLOBAL__N_114MappingBuilder11closestCopyE11StackOffsetNS0_12CopyLocationE
	cmpq	$-1, %rax
	je	.LB.MappingBuilder.mapClosestCopies.0
	movq	%rbx, %rdx
	movq	%rax, %rsi
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
	testb	%al, %al
	je	.LB.MappingBuilder.mapClosestCopies.0
	jmp	.LB.MappingBuilder.mapClosestCopies.3
.LB.MappingBuilder.mapClosestCopies.2:
	movl	$0, %eax
.LB.MappingBuilder.mapClosestCopies.3:
	popq	%rbx
	popq	%rbp
	ret
.LB.MappingBuilder.mapClosestCopies.4:
	movl	$0, %eax
	ret
	.size	_ZN12_GLOBAL__N_114MappingBuilder16mapClosestCopiesEv, .-_ZN12_GLOBAL__N_114MappingBuilder16mapClosestCopiesEv
