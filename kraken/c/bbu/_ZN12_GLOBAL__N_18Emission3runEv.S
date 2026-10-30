_ZN12_GLOBAL__N_18Emission3runEv:
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbx
	call	_ZN12_GLOBAL__N_18Emission13removeSurplusEv
	testb	%al, %al
	je	.LB453
.LB433:
	popq	%rbx
	popq	%rbp
	popq	%r12
	ret
.LB453:
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission21permuteAtLowestHeightEv
	testb	%al, %al
	jne	.LB433
	movq	16440(%rbx), %rcx
	movq	8(%rbx), %r12
	movq	%rcx, %rdx
	addq	32(%rbx), %rdx
	movl	$2, %eax
	cmpq	%r12, %rdx
	jne	.LB433
	testq	%r12, %r12
	je	.LB435
	movl	$0, %eax
	movl	$0, %edx
	jmp	.LB437
	.p2align 5
.LB436:
	addq	$1, %rax
	cmpq	%rax, %r12
	je	.LB454
.LB437:
	cmpq	$-1, 8248(%rbx,%rax,8)
	jne	.LB436
	addq	$1, %rdx
	jmp	.LB436
	.p2align 4
.LB440:
	addq	$1, %rax
	cmpq	%rax, %r12
	je	.LB442
.LB441:
	cmpb	$3, 4(%rdx,%rax,8)
	jne	.LB440
	cmpq	$-1, 8248(%rbx,%rax,8)
	jne	.LB440
	movl	$2, %eax
	jmp	.LB433
.LB444:
	movl	$2, %eax
	jmp	.LB433
.LB435:
	movl	$2, %eax
	testq	%rcx, %rcx
	jne	.LB433
.LB442:
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv
	jmp	.LB433
.LB454:
	movl	$2, %eax
	movl	$0, %ebp
	cmpq	%rdx, %rcx
	jne	.LB433
.LB439:
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	call	_ZNK12_GLOBAL__N_18Emission11isAvailableE11StackOffset
	testb	%al, %al
	je	.LB444
	addq	$1, %rbp
	cmpq	%rbp, %r12
	jne	.LB439
	movq	(%rbx), %rdx
	movl	$0, %eax
	jmp	.LB441
	.size	_ZN12_GLOBAL__N_18Emission3runEv, .-_ZN12_GLOBAL__N_18Emission3runEv
