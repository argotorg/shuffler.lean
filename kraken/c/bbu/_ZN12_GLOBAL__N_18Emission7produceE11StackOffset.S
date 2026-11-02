_ZN12_GLOBAL__N_18Emission7produceE11StackOffset:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$24, %rsp
	movq	%rdi, %rbx
	movq	%rsi, %r12
	leaq	0(,%rsi,8), %r14
	movq	%r14, %rdx
	addq	(%rdi), %rdx
	movzbl	5(%rdx), %r13d
	movzbl	4(%rdx), %r15d
	movzbl	%r13b, %eax
	salq	$40, %rax
	movabsq	$-280375465082881, %rbp
	andq	(%rdx), %rbp
	orq	%rax, %rbp
	movq	%rbp, %rsi
	call	_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot
	movq	%rax, 8(%rsp)
	cmpb	$1, %r15b
	je	.LB.Emission.produce.3
	movq	8(%rsp), %rax
	cmpq	$-1, %rax
	je	.LB.Emission.produce.0
	notq	%rax
	addq	32(%rbx), %rax
	cmpq	$15, %rax
	jbe	.LB.Emission.produce.4
.LB.Emission.produce.0:
	testb	%r13b, %r13b
	je	.LB.Emission.produce.1
	cmpb	$2, %r15b
	jne	.LB.Emission.produce.5
.LB.Emission.produce.1:
	movq	%r12, %rdx
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission4pushE9StackSlot11StackOffset
.LB.Emission.produce.2:
	testb	%al, %al
	jne	.LB.Emission.produce.9
	movq	32(%rbx), %rcx
	leaq	-1(%rcx), %rdx
	cmpq	%rdx, 8248(%rbx,%r14)
	je	.LB.Emission.produce.8
	movl	$1, %edi
	call	exit
.LB.Emission.produce.3:
	movq	%r12, %rdx
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission4pushE9StackSlot11StackOffset
	jmp	.LB.Emission.produce.2
.LB.Emission.produce.4:
	movq	%r12, %rdx
	movq	8(%rsp), %rsi
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission3dupE11StackOffsetS1_
	jmp	.LB.Emission.produce.2
.LB.Emission.produce.5:
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	call	_ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot
	testb	%al, %al
	jne	.LB.Emission.produce.1
	cmpq	$-1, 8(%rsp)
	je	.LB.Emission.produce.7
	movq	$-16, %rax
	movq	8(%rsp), %rcx
	subq	%rcx, %rax
	addq	32(%rbx), %rax
	je	.LB.Emission.produce.6
	movq	8(%rsp), %rcx
	movq	%rcx, 16448(%rbx)
	movq	%rax, 16456(%rbx)
	movl	$1, %eax
	jmp	.LB.Emission.produce.9
.LB.Emission.produce.6:
	movl	$1, %edi
	call	exit
.LB.Emission.produce.7:
	movl	$1, %edi
	call	exit
.LB.Emission.produce.8:
	subq	$1, 16440(%rbx)
.LB.Emission.produce.9:
	addq	$24, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
	.size	_ZN12_GLOBAL__N_18Emission7produceE11StackOffset, .-_ZN12_GLOBAL__N_18Emission7produceE11StackOffset
