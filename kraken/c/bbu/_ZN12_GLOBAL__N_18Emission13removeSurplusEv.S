_ZN12_GLOBAL__N_18Emission13removeSurplusEv:
	pushq	%rbx
	movq	%rdi, %rbx
.LB.Emission.removeSurplus.0:
	movq	32(%rbx), %r8
	testq	%r8, %r8
	je	.LB.Emission.removeSurplus.10
	leaq	-1(%r8), %rdi
	movq	%rdi, %rax
	movq	$-1, %rdx
	movq	$-1, %rsi
	jmp	.LB.Emission.removeSurplus.2
	.p2align 5
.LB.Emission.removeSurplus.1:
	subq	$1, %rax
	cmpq	$-1, %rax
	je	.LB.Emission.removeSurplus.3
.LB.Emission.removeSurplus.2:
	cmpq	$-1, 56(%rbx,%rax,8)
	jne	.LB.Emission.removeSurplus.1
	cmpq	$-1, %rdx
	cmove	%rax, %rdx
	movq	%rdi, %rcx
	subq	%rax, %rcx
	cmpq	$16, %rcx
	cmovbe	%rax, %rsi
	jmp	.LB.Emission.removeSurplus.1
.LB.Emission.removeSurplus.3:
	cmpq	$-1, %rdx
	je	.LB.Emission.removeSurplus.8
	cmpq	$-1, %rsi
	je	.LB.Emission.removeSurplus.6
	cmpq	%rdi, %rdx
	je	.LB.Emission.removeSurplus.12
	leaq	0(,%rdi,8), %r8
	movq	%rdi, %rax
	.p2align 5
.LB.Emission.removeSurplus.4:
	testq	%rax, %rax
	je	.LB.Emission.removeSurplus.11
	subq	$1, %rax
	cmpq	$-1, 56(%rbx,%rax,8)
	jne	.LB.Emission.removeSurplus.4
	movq	24(%rbx), %rcx
	movq	(%rcx,%rax,8), %rdx
	xorq	(%rcx,%r8), %rdx
	salq	$16, %rdx
	jne	.LB.Emission.removeSurplus.4
	movq	56(%rbx,%rax,8), %rdx
	movq	56(%rbx,%rdi,8), %rcx
	movq	%rcx, 56(%rbx,%rax,8)
	movq	%rdx, 56(%rbx,%rdi,8)
	movq	56(%rbx,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB.Emission.removeSurplus.5
	movq	%rax, 8248(%rbx,%rdx,8)
.LB.Emission.removeSurplus.5:
	movq	56(%rbx,%rdi,8), %rax
	cmpq	$-1, %rax
	je	.LB.Emission.removeSurplus.12
	movq	%rdi, 8248(%rbx,%rax,8)
	jmp	.LB.Emission.removeSurplus.12
.LB.Emission.removeSurplus.6:
	subq	$17, %r8
	subq	%rdx, %r8
	je	.LB.Emission.removeSurplus.7
	movq	%rdx, 16448(%rbx)
	movq	%r8, 16456(%rbx)
	movl	$1, %eax
	jmp	.LB.Emission.removeSurplus.9
.LB.Emission.removeSurplus.7:
	movl	$1, %edi
	call	exit
.LB.Emission.removeSurplus.8:
	movl	$0, %eax
.LB.Emission.removeSurplus.9:
	popq	%rbx
	ret
.LB.Emission.removeSurplus.10:
	movl	$0, %eax
	jmp	.LB.Emission.removeSurplus.9
.LB.Emission.removeSurplus.11:
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	testb	%al, %al
	jne	.LB.Emission.removeSurplus.9
.LB.Emission.removeSurplus.12:
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission3popEv
	testb	%al, %al
	je	.LB.Emission.removeSurplus.0
	jmp	.LB.Emission.removeSurplus.9
	.size	_ZN12_GLOBAL__N_18Emission13removeSurplusEv, .-_ZN12_GLOBAL__N_18Emission13removeSurplusEv
