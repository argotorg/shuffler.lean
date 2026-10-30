_ZN12_GLOBAL__N_114MappingBuilder21mapWildcardSlotCopiesEv:
	cmpq	$0, 24(%rdi)
	je	.LB.MappingBuilder.mapWildcardSlotCopies.5
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movl	$0, %ebx
	jmp	.LB.MappingBuilder.mapWildcardSlotCopies.2
.LB.MappingBuilder.mapWildcardSlotCopies.0:
	movq	%rbx, %rdx
	movq	%rax, %rsi
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
	testb	%al, %al
	jne	.LB.MappingBuilder.mapWildcardSlotCopies.4
	.p2align 6
.LB.MappingBuilder.mapWildcardSlotCopies.1:
	addq	$1, %rbx
	cmpq	24(%rbp), %rbx
	jnb	.LB.MappingBuilder.mapWildcardSlotCopies.3
.LB.MappingBuilder.mapWildcardSlotCopies.2:
	leaq	0(,%rbx,8), %rdx
	movq	48(%rbp), %rax
	cmpq	$-1, 8192(%rax,%rbx,8)
	jne	.LB.MappingBuilder.mapWildcardSlotCopies.1
	movq	16(%rbp), %rax
	movzbl	4(%rax,%rdx), %r12d
	cmpb	$1, %r12b
	je	.LB.MappingBuilder.mapWildcardSlotCopies.1
	movl	$1, %edx
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	_ZNK12_GLOBAL__N_114MappingBuilder11closestCopyE11StackOffsetNS0_12CopyLocationE
	cmpq	$-1, %rax
	je	.LB.MappingBuilder.mapWildcardSlotCopies.1
	cmpb	$3, %r12b
	je	.LB.MappingBuilder.mapWildcardSlotCopies.0
	movb	$1, 56(%rbp)
	cmpb	$1, 40(%rbp)
	jne	.LB.MappingBuilder.mapWildcardSlotCopies.1
	movq	%rbx, %rdx
	movq	%rax, %rsi
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
	testb	%al, %al
	je	.LB.MappingBuilder.mapWildcardSlotCopies.1
	jmp	.LB.MappingBuilder.mapWildcardSlotCopies.4
.LB.MappingBuilder.mapWildcardSlotCopies.3:
	movl	$0, %eax
.LB.MappingBuilder.mapWildcardSlotCopies.4:
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	ret
.LB.MappingBuilder.mapWildcardSlotCopies.5:
	movl	$0, %eax
	ret
	.size	_ZN12_GLOBAL__N_114MappingBuilder21mapWildcardSlotCopiesEv, .-_ZN12_GLOBAL__N_114MappingBuilder21mapWildcardSlotCopiesEv
