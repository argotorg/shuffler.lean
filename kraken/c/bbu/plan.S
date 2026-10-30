plan:
	pushq	%rbx
	subq	$80, %rsp
	movl	96(%rsp), %ebx
	movl	104(%rsp), %eax
	cmpq	$1024, %rdi
	ja	.LB.plan.12
	movl	%eax, %r11d
	cmpq	$1024, %rsi
	ja	.LB.plan.12
	orl	%ebx, %eax
	cmpb	$1, %al
	ja	.LB.plan.13
	testq	%rdi, %rdi
	je	.LB.plan.14
	movl	$0, %eax
	jmp	.LB.plan.1
	.p2align 4
.LB.plan.0:
	addq	$1, %rax
	cmpq	%rax, %rdi
	je	.LB.plan.2
.LB.plan.1:
	cmpb	$0, 5(%rdx,%rax,8)
	je	.LB.plan.0
	cmpb	$0, 4(%rdx,%rax,8)
	jne	.LB.plan.0
	movl	(%rdx,%rax,8), %r10d
	cmpq	%r9, %r10
	jb	.LB.plan.0
	movq	$-2, %rdx
	jmp	.LB.plan.9
.LB.plan.2:
	testq	%rsi, %rsi
	je	.LB.plan.6
	movl	$0, %eax
	jmp	.LB.plan.4
	.p2align 4
.LB.plan.3:
	addq	$1, %rax
	cmpq	%rsi, %rax
	jnb	.LB.plan.5
.LB.plan.4:
	cmpb	$0, 5(%rcx,%rax,8)
	je	.LB.plan.3
	cmpb	$0, 4(%rcx,%rax,8)
	jne	.LB.plan.3
	movl	(%rcx,%rax,8), %r10d
	cmpq	%r9, %r10
	jb	.LB.plan.3
	movq	$-2, %rdx
	jmp	.LB.plan.9
.LB.plan.5:
	testq	%rdi, %rdi
	je	.LB.plan.8
.LB.plan.6:
	movq	112(%rsp), %rax
	movq	%rdi, %r9
	addq	%rax, %r9
	.p2align 4
.LB.plan.7:
	movb	$0, (%rax)
	addq	$1, %rax
	cmpq	%rax, %r9
	jne	.LB.plan.7
.LB.plan.8:
	movq	%rdx, 16(%rsp)
	movq	%rdi, 24(%rsp)
	movq	%rcx, 32(%rsp)
	movq	%rsi, 40(%rsp)
	movq	%r8, 48(%rsp)
	cmpb	$1, %bl
	sete	56(%rsp)
	movq	112(%rsp), %rax
	movq	%rax, 64(%rsp)
	movq	$0, 8(%rsp)
	leaq	16(%rsp), %rdi
	leaq	8(%rsp), %r9
	movq	144(%rsp), %r8
	movq	136(%rsp), %rcx
	movq	128(%rsp), %rdx
	movl	%r11d, %esi
	call	_ZN12_GLOBAL__N_17Planner3runENS_14MappingBuilder21WildcardSlotsStrategyEP9StackSlotP9ShuffleOpPNS_8OptionalI11StackOffsetEERm
	cmpb	$1, %al
	je	.LB.plan.11
	movq	$-2, %rdx
	cmpb	$2, %al
	jne	.LB.plan.10
.LB.plan.9:
	movq	%rdx, %rax
	addq	$80, %rsp
	popq	%rbx
	ret
.LB.plan.10:
	movzbl	72(%rsp), %eax
	movq	120(%rsp), %rbx
	movb	%al, (%rbx)
	movq	8(%rsp), %rdx
	jmp	.LB.plan.9
.LB.plan.11:
	movzbl	72(%rsp), %eax
	movq	120(%rsp), %rbx
	movb	%al, (%rbx)
	movq	$-1, %rdx
	jmp	.LB.plan.9
.LB.plan.12:
	movq	$-2, %rdx
	jmp	.LB.plan.9
.LB.plan.13:
	movq	$-2, %rdx
	jmp	.LB.plan.9
.LB.plan.14:
	movq	%rdi, %rax
	testq	%rsi, %rsi
	jne	.LB.plan.4
	jmp	.LB.plan.8
	.size	plan, .-plan
