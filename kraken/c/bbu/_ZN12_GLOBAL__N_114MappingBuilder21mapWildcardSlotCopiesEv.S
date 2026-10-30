_ZN12_GLOBAL__N_114MappingBuilder21mapWildcardSlotCopiesEv:
	cmpq	$0, 24(%rdi)
	je	.LB393
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movl	$0, %ebx
	jmp	.LB392
.LB400:
	movq	%rbx, %rdx
	movq	%rax, %rsi
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
	testb	%al, %al
	jne	.LB386
	.p2align 6
.LB388:
	addq	$1, %rbx
	cmpq	24(%rbp), %rbx
	jnb	.LB399
.LB392:
	leaq	0(,%rbx,8), %rdx
	movq	48(%rbp), %rax
	cmpq	$-1, 8192(%rax,%rbx,8)
	jne	.LB388
	movq	16(%rbp), %rax
	movzbl	4(%rax,%rdx), %r12d
	cmpb	$1, %r12b
	je	.LB388
	movl	$1, %edx
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	_ZNK12_GLOBAL__N_114MappingBuilder11closestCopyE11StackOffsetNS0_12CopyLocationE
	cmpq	$-1, %rax
	je	.LB388
	cmpb	$3, %r12b
	je	.LB400
	movb	$1, 56(%rbp)
	cmpb	$1, 40(%rbp)
	jne	.LB388
	movq	%rbx, %rdx
	movq	%rax, %rsi
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
	testb	%al, %al
	je	.LB388
	jmp	.LB386
.LB399:
	movl	$0, %eax
.LB386:
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	ret
.LB393:
	movl	$0, %eax
	ret
	.size	_ZN12_GLOBAL__N_114MappingBuilder21mapWildcardSlotCopiesEv, .-_ZN12_GLOBAL__N_114MappingBuilder21mapWildcardSlotCopiesEv
