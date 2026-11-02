_ZN12_GLOBAL__N_18Emission3runEv:
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	call	_ZN12_GLOBAL__N_18Emission13removeSurplusEv
	testb	%al, %al
	je	.LB.Emission.run.1
.LB.Emission.run.0:
	popq	%rbx
	popq	%rbp
	popq	%r12
	ret
.LB.Emission.run.1:
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_18Emission21permuteAtLowestHeightEv
	testb	%al, %al
	jne	.LB.Emission.run.0
	movq	16440(%rbp), %rcx
	movq	8(%rbp), %r12
	movq	%rcx, %rax
	addq	32(%rbp), %rax
	cmpq	%r12, %rax
	jne	.LB.Emission.run.3
	movl	$0, %eax
	movl	$0, %edx
	testq	%r12, %r12
	jne	.LB.Emission.run.5
	testq	%rcx, %rcx
	je	.LB.Emission.run.9
.LB.Emission.run.2:
	movl	$1, %edi
	call	exit
.LB.Emission.run.3:
	movl	$1, %edi
	call	exit
	.p2align 5
.LB.Emission.run.4:
	addq	$1, %rax
	cmpq	%rax, %r12
	je	.LB.Emission.run.10
.LB.Emission.run.5:
	cmpq	$-1, 8248(%rbp,%rax,8)
	jne	.LB.Emission.run.4
	addq	$1, %rdx
	jmp	.LB.Emission.run.4
.LB.Emission.run.6:
	movl	$1, %edi
	call	exit
	.p2align 4
.LB.Emission.run.7:
	addq	$1, %rax
	cmpq	%rax, %r12
	je	.LB.Emission.run.9
.LB.Emission.run.8:
	cmpb	$3, 4(%rdx,%rax,8)
	jne	.LB.Emission.run.7
	cmpq	$-1, 8248(%rbp,%rax,8)
	jne	.LB.Emission.run.7
	movl	$1, %edi
	call	exit
.LB.Emission.run.9:
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv
	jmp	.LB.Emission.run.0
.LB.Emission.run.10:
	cmpq	%rdx, %rcx
	jne	.LB.Emission.run.2
	movl	$0, %ebx
.LB.Emission.run.11:
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	_ZNK12_GLOBAL__N_18Emission11isAvailableE11StackOffset
	testb	%al, %al
	je	.LB.Emission.run.6
	addq	$1, %rbx
	cmpq	%rbx, %r12
	jne	.LB.Emission.run.11
	movq	0(%rbp), %rdx
	movl	$0, %eax
	jmp	.LB.Emission.run.8
	.size	_ZN12_GLOBAL__N_18Emission3runEv, .-_ZN12_GLOBAL__N_18Emission3runEv
