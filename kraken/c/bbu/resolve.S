resolve:
	pushq	%rbp
	pushq	%rbx
	subq	$32840, %rsp
	movq	%r8, %rbx
	movq	32864(%rsp), %r11
	movq	32896(%rsp), %rbp
	movl	32904(%rsp), %r8d
	cmpq	$1024, %rdi
	ja	.LB629
	movq	%rsi, %r10
	movq	%rdx, %rsi
	cmpq	$1024, %r10
	ja	.LB629
	cmpq	$1024, %r9
	seta	%al
	cmpq	%r9, 32872(%rsp)
	setnb	%dl
	orb	%dl, %al
	jne	.LB630
	cmpb	$1, %r8b
	ja	.LB630
	testq	%rdi, %rdi
	je	.LB614
	movl	$0, %eax
	jmp	.LB616
	.p2align 5
.LB615:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rdi
	je	.LB642
	movq	%rdx, %rax
.LB616:
	cmpb	$0, 5(%rsi,%rax,8)
	je	.LB615
	cmpb	$0, 4(%rsi,%rax,8)
	jne	.LB615
	movl	(%rsi,%rax,8), %edx
	cmpq	%rbp, %rdx
	jb	.LB615
	movq	$-2, %rdx
	jmp	.LB612
.LB642:
	movl	$0, %edx
	addq	$1, %rax
	.p2align 5
.LB617:
	movq	$-1, 16448(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB617
	testq	%r10, %r10
	je	.LB618
.LB628:
	movl	$0, %eax
	.p2align 5
.LB619:
	movq	$-1, 24640(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%r10, %rax
	jb	.LB619
	testq	%rdi, %rdi
	je	.LB620
.LB618:
	movl	$0, %eax
	jmp	.LB622
	.p2align 5
.LB621:
	addq	$1, %rax
	cmpq	%rax, %rdi
	je	.LB620
.LB622:
	movq	(%rbx,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB621
	movq	%rdx, 16448(%rsp,%rax,8)
	movq	%rax, 24640(%rsp,%rdx,8)
	jmp	.LB621
	.p2align 5
.LB626:
	addq	$1, %rax
	cmpq	%r9, %rax
	jnb	.LB643
.LB627:
	movq	(%r11,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB626
	movq	%rdx, 64(%rsp,%rax,8)
	movq	%rax, 8256(%rsp,%rdx,8)
	jmp	.LB626
.LB643:
	movq	%rsi, (%rsp)
	movq	%rdi, 8(%rsp)
	movq	%rcx, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	32888(%rsp), %rax
	movq	%rax, 32(%rsp)
	cmpb	$1, %r8b
	sete	40(%rsp)
	movq	32912(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	32872(%rsp), %rax
	movq	32880(%rsp), %rdx
	leaq	16448(%rsp), %rsi
	movq	%rsp, %rdi
	leaq	64(%rsp), %r8
	movq	%rdx, %rcx
	movq	%rax, %rdx
	call	_ZN12_GLOBAL__N_17Planner7resolveERKNS_7MappingENS_8Emission7BlockedES3_m
	movq	$-1, %rdx
	cmpb	$1, %al
	je	.LB612
	cmpb	$2, %al
	setne	%dl
	movzbl	%dl, %edx
	leaq	-2(%rdx,%rdx), %rdx
.LB612:
	movq	%rdx, %rax
	addq	$32840, %rsp
	popq	%rbx
	popq	%rbp
	ret
.LB629:
	movq	$-2, %rdx
	jmp	.LB612
.LB630:
	movq	$-2, %rdx
	jmp	.LB612
.LB614:
	testq	%r10, %r10
	jne	.LB628
.LB620:
	movl	$0, %eax
	.p2align 5
.LB623:
	movq	$-1, 64(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%r9, %rax
	jb	.LB623
	testq	%r10, %r10
	je	.LB624
	leaq	64(%rsp), %rax
	leaq	(%rax,%r10,8), %rdx
	.p2align 5
.LB625:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rax, %rdx
	jne	.LB625
.LB624:
	movl	$0, %eax
	jmp	.LB627
	.size	resolve, .-resolve
