_ZN12_GLOBAL__N_18Emission3runEv:
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbx
	call	_ZN12_GLOBAL__N_18Emission13removeSurplusEv
	testb	%al, %al
	je	.LB.Emission.run.1
.LB.Emission.run.0:
	popq	%rbx
	popq	%rbp
	popq	%r12
	ret
.LB.Emission.run.1:
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission21permuteAtLowestHeightEv
	testb	%al, %al
	jne	.LB.Emission.run.0
	movq	16440(%rbx), %rcx
	movq	8(%rbx), %r12
	movq	%rcx, %rdx
	addq	32(%rbx), %rdx
	movl	$2, %eax
	cmpq	%r12, %rdx
	jne	.LB.Emission.run.0
	testq	%r12, %r12
	je	.LB.Emission.run.7
	movl	$0, %eax
	movl	$0, %edx
	jmp	.LB.Emission.run.3
	.p2align 5
.LB.Emission.run.2:
	addq	$1, %rax
	cmpq	%rax, %r12
	je	.LB.Emission.run.9
.LB.Emission.run.3:
	cmpq	$-1, 8248(%rbx,%rax,8)
	jne	.LB.Emission.run.2
	addq	$1, %rdx
	jmp	.LB.Emission.run.2
	.p2align 4
.LB.Emission.run.4:
	addq	$1, %rax
	cmpq	%rax, %r12
	je	.LB.Emission.run.8
.LB.Emission.run.5:
	cmpb	$3, 4(%rdx,%rax,8)
	jne	.LB.Emission.run.4
	cmpq	$-1, 8248(%rbx,%rax,8)
	jne	.LB.Emission.run.4
	movl	$2, %eax
	jmp	.LB.Emission.run.0
.LB.Emission.run.6:
	movl	$2, %eax
	jmp	.LB.Emission.run.0
.LB.Emission.run.7:
	movl	$2, %eax
	testq	%rcx, %rcx
	jne	.LB.Emission.run.0
.LB.Emission.run.8:
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv
	jmp	.LB.Emission.run.0
.LB.Emission.run.9:
	movl	$2, %eax
	movl	$0, %ebp
	cmpq	%rdx, %rcx
	jne	.LB.Emission.run.0
.LB.Emission.run.10:
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	call	_ZNK12_GLOBAL__N_18Emission11isAvailableE11StackOffset
	testb	%al, %al
	je	.LB.Emission.run.6
	addq	$1, %rbp
	cmpq	%rbp, %r12
	jne	.LB.Emission.run.10
	movq	(%rbx), %rdx
	movl	$0, %eax
	jmp	.LB.Emission.run.5
	.size	_ZN12_GLOBAL__N_18Emission3runEv, .-_ZN12_GLOBAL__N_18Emission3runEv
