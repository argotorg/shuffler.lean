plan:
	pushq	%rbx
	subq	$80, %rsp
	movl	96(%rsp), %ebx
	movl	104(%rsp), %eax
	cmpq	$1024, %rdi
	ja	.LB775
	movl	%eax, %r11d
	cmpq	$1024, %rsi
	ja	.LB775
	orl	%ebx, %eax
	cmpb	$1, %al
	ja	.LB776
	testq	%rdi, %rdi
	je	.LB765
	movl	$0, %eax
	jmp	.LB767
	.p2align 4
.LB766:
	addq	$1, %rax
	cmpq	%rax, %rdi
	je	.LB785
.LB767:
	cmpb	$0, 5(%rdx,%rax,8)
	je	.LB766
	cmpb	$0, 4(%rdx,%rax,8)
	jne	.LB766
	movl	(%rdx,%rax,8), %r10d
	cmpq	%r9, %r10
	jb	.LB766
	movq	$-2, %rdx
	jmp	.LB763
.LB785:
	testq	%rsi, %rsi
	je	.LB768
	movl	$0, %eax
	jmp	.LB770
	.p2align 4
.LB769:
	addq	$1, %rax
	cmpq	%rsi, %rax
	jnb	.LB786
.LB770:
	cmpb	$0, 5(%rcx,%rax,8)
	je	.LB769
	cmpb	$0, 4(%rcx,%rax,8)
	jne	.LB769
	movl	(%rcx,%rax,8), %r10d
	cmpq	%r9, %r10
	jb	.LB769
	movq	$-2, %rdx
	jmp	.LB763
.LB786:
	testq	%rdi, %rdi
	je	.LB771
.LB768:
	movq	112(%rsp), %rax
	movq	%rdi, %r9
	addq	%rax, %r9
	.p2align 4
.LB772:
	movb	$0, (%rax)
	addq	$1, %rax
	cmpq	%rax, %r9
	jne	.LB772
.LB771:
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
	je	.LB773
	movq	$-2, %rdx
	cmpb	$2, %al
	jne	.LB787
.LB763:
	movq	%rdx, %rax
	addq	$80, %rsp
	popq	%rbx
	ret
.LB787:
	movzbl	72(%rsp), %eax
	movq	120(%rsp), %rbx
	movb	%al, (%rbx)
	movq	8(%rsp), %rdx
	jmp	.LB763
.LB773:
	movzbl	72(%rsp), %eax
	movq	120(%rsp), %rbx
	movb	%al, (%rbx)
	movq	$-1, %rdx
	jmp	.LB763
.LB775:
	movq	$-2, %rdx
	jmp	.LB763
.LB776:
	movq	$-2, %rdx
	jmp	.LB763
.LB765:
	movq	%rdi, %rax
	testq	%rsi, %rsi
	jne	.LB770
	jmp	.LB771
	.size	plan, .-plan
