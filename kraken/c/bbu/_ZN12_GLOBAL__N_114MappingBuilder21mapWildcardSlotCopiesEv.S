_ZN12_GLOBAL__N_114MappingBuilder21mapWildcardSlotCopiesEv:
	cmpq	$0, 24(%rdi)
	je	.LB483
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movl	$0, %ebx
	jmp	.LB482
.LB490:
	movq	%rbx, %rdx
	movq	%rax, %rsi
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
	testb	%al, %al
	jne	.LB476
	.p2align 6
.LB478:
	addq	$1, %rbx
	cmpq	24(%rbp), %rbx
	jnb	.LB489
.LB482:
	leaq	0(,%rbx,8), %rdx
	movq	48(%rbp), %rax
	cmpq	$-1, 8192(%rax,%rbx,8)
	jne	.LB478
	movq	16(%rbp), %rax
	movzbl	4(%rax,%rdx), %r12d
	cmpb	$1, %r12b
	je	.LB478
	movl	$1, %edx
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	_ZNK12_GLOBAL__N_114MappingBuilder11closestCopyE11StackOffsetNS0_12CopyLocationE
	cmpq	$-1, %rax
	je	.LB478
	cmpb	$3, %r12b
	je	.LB490
	movb	$1, 56(%rbp)
	cmpb	$1, 40(%rbp)
	jne	.LB478
	movq	%rbx, %rdx
	movq	%rax, %rsi
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
	testb	%al, %al
	je	.LB478
	jmp	.LB476
.LB489:
	movl	$0, %eax
.LB476:
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	ret
.LB483:
	movl	$0, %eax
	ret
	.size	_ZN12_GLOBAL__N_114MappingBuilder21mapWildcardSlotCopiesEv, .-_ZN12_GLOBAL__N_114MappingBuilder21mapWildcardSlotCopiesEv
