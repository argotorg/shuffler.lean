_ZN12_GLOBAL__N_114MappingBuilder13absorbSurplusEv:
	cmpq	$0, 24(%rdi)
	je	.LB421
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movl	$0, %ebx
	jmp	.LB420
.LB422:
	movq	%rax, %rsi
	.p2align 5
.LB415:
	addq	$1, %rax
	addq	$1, %rdx
	cmpq	%rcx, %rax
	je	.LB431
.LB419:
	cmpb	$0, (%rdi,%rax)
	jne	.LB415
	cmpq	$-1, (%r8,%rax,8)
	jne	.LB415
	cmpq	$-1, %rsi
	je	.LB422
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
	jmp	.LB415
.LB431:
	cmpq	$-1, %rsi
	je	.LB414
	movq	%rbx, %rdx
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
	testb	%al, %al
	jne	.LB412
	.p2align 5
.LB414:
	addq	$1, %rbx
	cmpq	24(%rbp), %rbx
	jnb	.LB432
.LB420:
	leaq	0(,%rbx,8), %rdx
	movq	16(%rbp), %rax
	cmpb	$1, 4(%rax,%rbx,8)
	jne	.LB414
	movq	48(%rbp), %r8
	movq	8192(%r8,%rdx), %rsi
	cmpq	$-1, %rsi
	jne	.LB414
	movq	8(%rbp), %rcx
	testq	%rcx, %rcx
	je	.LB414
	movq	32(%rbp), %rdi
	movq	%rbx, %rdx
	negq	%rdx
	movl	$0, %eax
	jmp	.LB419
.LB432:
	movl	$0, %eax
.LB412:
	popq	%rbx
	popq	%rbp
	ret
.LB421:
	movl	$0, %eax
	ret
	.size	_ZN12_GLOBAL__N_114MappingBuilder13absorbSurplusEv, .-_ZN12_GLOBAL__N_114MappingBuilder13absorbSurplusEv
