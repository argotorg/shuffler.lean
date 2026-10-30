_ZN12_GLOBAL__N_114MappingBuilder13absorbSurplusEv:
	cmpq	$0, 24(%rdi)
	je	.LB511
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movl	$0, %ebx
	jmp	.LB510
.LB512:
	movq	%rax, %rsi
	.p2align 5
.LB505:
	addq	$1, %rax
	addq	$1, %rdx
	cmpq	%rcx, %rax
	je	.LB521
.LB509:
	cmpb	$0, (%rdi,%rax)
	jne	.LB505
	cmpq	$-1, (%r8,%rax,8)
	jne	.LB505
	cmpq	$-1, %rsi
	je	.LB512
	movq	%rbx, %r10
	subq	%rax, %r10
	cmpq	%rax, %rbx
	cmovb	%rdx, %r10
	movq	%rsi, %r11
	subq	%rbx, %r11
	movq	%rbx, %r9
	subq	%rsi, %r9
	cmpq	%rsi, %rbx
	cmovb	%r11, %r9
	cmpq	%r9, %r10
	cmovb	%rax, %rsi
	jmp	.LB505
.LB521:
	cmpq	$-1, %rsi
	je	.LB504
	movq	%rbx, %rdx
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
	testb	%al, %al
	jne	.LB502
	.p2align 5
.LB504:
	addq	$1, %rbx
	cmpq	24(%rbp), %rbx
	jnb	.LB522
.LB510:
	leaq	0(,%rbx,8), %rdx
	movq	16(%rbp), %rax
	cmpb	$1, 4(%rax,%rbx,8)
	jne	.LB504
	movq	48(%rbp), %r8
	movq	8192(%r8,%rdx), %rsi
	cmpq	$-1, %rsi
	jne	.LB504
	movq	8(%rbp), %rcx
	testq	%rcx, %rcx
	je	.LB504
	movq	32(%rbp), %rdi
	movq	%rbx, %rdx
	negq	%rdx
	movl	$0, %eax
	jmp	.LB509
.LB522:
	movl	$0, %eax
.LB502:
	popq	%rbx
	popq	%rbp
	ret
.LB511:
	movl	$0, %eax
	ret
	.size	_ZN12_GLOBAL__N_114MappingBuilder13absorbSurplusEv, .-_ZN12_GLOBAL__N_114MappingBuilder13absorbSurplusEv
