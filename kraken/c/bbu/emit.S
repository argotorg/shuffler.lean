emit:
	pushq	%rbx
	subq	$32864, %rsp
	movq	%r8, %rbx
	movq	32880(%rsp), %r8
	cmpq	$1024, %rdi
	ja	.LB695
	movq	%rdx, %r10
	movq	%rcx, %rdx
	cmpq	$1024, %rsi
	ja	.LB695
	testq	%rsi, %rsi
	je	.LB672
	movl	$0, %eax
	jmp	.LB674
	.p2align 4
.LB673:
	addq	$1, %rax
	cmpq	%rax, %rsi
	je	.LB672
.LB674:
	cmpb	$0, 4(%rdx,%rax,8)
	jne	.LB673
	cmpb	$0, 5(%rdx,%rax,8)
	je	.LB673
	movl	(%rdx,%rax,8), %ecx
	cmpq	%r8, %rcx
	jb	.LB673
	movq	$-2, %rdx
	jmp	.LB670
.LB672:
	testq	%rdi, %rdi
	je	.LB675
	movl	$0, %eax
	.p2align 5
.LB676:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB676
	testq	%rsi, %rsi
	je	.LB694
.LB693:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%rsi,8), %rcx
	.p2align 5
.LB678:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rcx, %rax
	jne	.LB678
	testq	%rdi, %rdi
	je	.LB679
.LB694:
	movl	$0, %eax
	jmp	.LB681
	.p2align 5
.LB680:
	leaq	1(%rax), %rcx
	cmpq	%rcx, %rdi
	je	.LB708
	movq	%rcx, %rax
.LB681:
	movq	(%rbx,%rax,8), %rcx
	cmpq	$-1, %rcx
	je	.LB680
	movq	%rcx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rcx,8)
	jmp	.LB680
.LB708:
	movq	%rdx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	%rcx, 32(%rsp)
	movq	32888(%rsp), %rdi
	movq	%rdi, 40(%rsp)
	movq	$0, 48(%rsp)
	movl	$0, %edx
	movq	%rcx, %rax
	.p2align 5
.LB682:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB682
.LB692:
	testq	%rsi, %rsi
	je	.LB683
	salq	$3, %rsi
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rcx
	.p2align 5
.LB684:
	movq	(%rcx,%rax), %rdx
	movq	%rdx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rsi, %rax
	jne	.LB684
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rsi
	jmp	.LB686
	.p2align 5
.LB685:
	addq	$8, %rax
	cmpq	%rsi, %rax
	je	.LB691
.LB686:
	cmpq	$-1, 8248(%rax)
	jne	.LB685
	addq	$1, 16440(%rsp)
	jmp	.LB685
.LB687:
	movq	16448(%rsp), %rax
	movq	32896(%rsp), %rdi
	movq	%rax, (%rdi)
	movq	16456(%rsp), %rax
	movq	%rax, 8(%rdi)
	jmp	.LB688
.LB695:
	movq	$-2, %rdx
	jmp	.LB670
.LB683:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB691:
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission3runEv
	cmpb	$1, %al
	je	.LB687
	movq	$-2, %rdx
	cmpb	$2, %al
	je	.LB670
	testb	%al, %al
	jne	.LB688
	movq	32896(%rsp), %rax
	movq	$0, (%rax)
	movq	$0, 8(%rax)
.LB688:
	movq	32(%rsp), %rcx
	movq	32904(%rsp), %rax
	movq	%rcx, (%rax)
	testq	%rcx, %rcx
	je	.LB689
	salq	$3, %rcx
	movl	$0, %eax
	leaq	56(%rsp), %rsi
	.p2align 5
.LB690:
	movq	(%rsi,%rax), %rdx
	movq	%rdx, (%rbx,%rax)
	addq	$8, %rax
	cmpq	%rax, %rcx
	jne	.LB690
.LB689:
	movq	48(%rsp), %rdx
.LB670:
	movq	%rdx, %rax
	addq	$32864, %rsp
	popq	%rbx
	ret
.LB675:
	testq	%rsi, %rsi
	jne	.LB693
.LB679:
	movq	%rdx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32888(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB692
	.size	emit, .-emit
