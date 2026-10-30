_ZN12_GLOBAL__N_18Emission3runEv:
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbx
	call	_ZN12_GLOBAL__N_18Emission13removeSurplusEv
	testb	%al, %al
	je	.LB668
.LB648:
	popq	%rbx
	popq	%rbp
	popq	%r12
	ret
.LB668:
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission21permuteAtLowestHeightEv
	testb	%al, %al
	jne	.LB648
	movq	16440(%rbx), %rcx
	movq	8(%rbx), %r12
	movq	%rcx, %rdx
	addq	32(%rbx), %rdx
	movl	$2, %eax
	cmpq	%r12, %rdx
	jne	.LB648
	testq	%r12, %r12
	je	.LB650
	movl	$0, %eax
	movl	$0, %edx
	jmp	.LB652
	.p2align 5
.LB651:
	addq	$1, %rax
	cmpq	%rax, %r12
	je	.LB669
.LB652:
	cmpq	$-1, 8248(%rbx,%rax,8)
	jne	.LB651
	addq	$1, %rdx
	jmp	.LB651
	.p2align 4
.LB655:
	addq	$1, %rax
	cmpq	%rax, %r12
	je	.LB657
.LB656:
	cmpb	$3, 4(%rdx,%rax,8)
	jne	.LB655
	cmpq	$-1, 8248(%rbx,%rax,8)
	jne	.LB655
	movl	$2, %eax
	jmp	.LB648
.LB659:
	movl	$2, %eax
	jmp	.LB648
.LB650:
	movl	$2, %eax
	testq	%rcx, %rcx
	jne	.LB648
.LB657:
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv
	jmp	.LB648
.LB669:
	movl	$2, %eax
	movl	$0, %ebp
	cmpq	%rdx, %rcx
	jne	.LB648
.LB654:
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	call	_ZNK12_GLOBAL__N_18Emission11isAvailableE11StackOffset
	testb	%al, %al
	je	.LB659
	addq	$1, %rbp
	cmpq	%rbp, %r12
	jne	.LB654
	movq	(%rbx), %rdx
	movl	$0, %eax
	jmp	.LB656
	.size	_ZN12_GLOBAL__N_18Emission3runEv, .-_ZN12_GLOBAL__N_18Emission3runEv
