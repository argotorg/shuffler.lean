_ZN12_GLOBAL__N_114MappingBuilder13absorbSurplusEv:
	cmpq	$0, 24(%rdi)
	je	.LB.MappingBuilder.absorbSurplus.8
	pushq	%rbp
	pushq	%rbx
	subq	$8, %rsp
	movq	%rdi, %rbp
	movl	$0, %ebx
	jmp	.LB.MappingBuilder.absorbSurplus.5
.LB.MappingBuilder.absorbSurplus.0:
	movq	%rax, %rsi
	.p2align 5
.LB.MappingBuilder.absorbSurplus.1:
	addq	$1, %rax
	addq	$1, %rdx
	cmpq	%rcx, %rax
	je	.LB.MappingBuilder.absorbSurplus.3
.LB.MappingBuilder.absorbSurplus.2:
	cmpb	$0, (%rdi,%rax)
	jne	.LB.MappingBuilder.absorbSurplus.1
	cmpq	$-1, (%r8,%rax,8)
	jne	.LB.MappingBuilder.absorbSurplus.1
	cmpq	$-1, %rsi
	je	.LB.MappingBuilder.absorbSurplus.0
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
	jmp	.LB.MappingBuilder.absorbSurplus.1
.LB.MappingBuilder.absorbSurplus.3:
	cmpq	$-1, %rsi
	je	.LB.MappingBuilder.absorbSurplus.4
	movq	%rbx, %rdx
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
	testb	%al, %al
	jne	.LB.MappingBuilder.absorbSurplus.7
	.p2align 5
.LB.MappingBuilder.absorbSurplus.4:
	addq	$1, %rbx
	cmpq	24(%rbp), %rbx
	jnb	.LB.MappingBuilder.absorbSurplus.6
.LB.MappingBuilder.absorbSurplus.5:
	leaq	0(,%rbx,8), %rdx
	movq	16(%rbp), %rax
	cmpb	$1, 4(%rax,%rbx,8)
	jne	.LB.MappingBuilder.absorbSurplus.4
	movq	48(%rbp), %r8
	movq	8192(%r8,%rdx), %rsi
	cmpq	$-1, %rsi
	jne	.LB.MappingBuilder.absorbSurplus.4
	movq	8(%rbp), %rcx
	testq	%rcx, %rcx
	je	.LB.MappingBuilder.absorbSurplus.4
	movq	32(%rbp), %rdi
	movq	%rbx, %rdx
	negq	%rdx
	movl	$0, %eax
	jmp	.LB.MappingBuilder.absorbSurplus.2
.LB.MappingBuilder.absorbSurplus.6:
	movl	$0, %eax
.LB.MappingBuilder.absorbSurplus.7:
	addq	$8, %rsp
	popq	%rbx
	popq	%rbp
	ret
.LB.MappingBuilder.absorbSurplus.8:
	movl	$0, %eax
	ret
	.size	_ZN12_GLOBAL__N_114MappingBuilder13absorbSurplusEv, .-_ZN12_GLOBAL__N_114MappingBuilder13absorbSurplusEv
