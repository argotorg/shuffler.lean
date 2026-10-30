_ZN12_GLOBAL__N_114MappingBuilder16mapClosestCopiesEv:
	cmpq	$0, 24(%rdi)
	je	.LB379
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movl	$0, %ebx
	jmp	.LB378
	.p2align 6
.LB376:
	addq	$1, %rbx
	cmpq	24(%rbp), %rbx
	jnb	.LB385
.LB378:
	leaq	0(,%rbx,8), %rdx
	movq	48(%rbp), %rax
	cmpq	$-1, 8192(%rax,%rbx,8)
	jne	.LB376
	movq	16(%rbp), %rax
	cmpb	$1, 4(%rax,%rdx)
	je	.LB376
	movl	$0, %edx
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	_ZNK12_GLOBAL__N_114MappingBuilder11closestCopyE11StackOffsetNS0_12CopyLocationE
	cmpq	$-1, %rax
	je	.LB376
	movq	%rbx, %rdx
	movq	%rax, %rsi
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
	testb	%al, %al
	je	.LB376
	jmp	.LB374
.LB385:
	movl	$0, %eax
.LB374:
	popq	%rbx
	popq	%rbp
	ret
.LB379:
	movl	$0, %eax
	ret
	.size	_ZN12_GLOBAL__N_114MappingBuilder16mapClosestCopiesEv, .-_ZN12_GLOBAL__N_114MappingBuilder16mapClosestCopiesEv
