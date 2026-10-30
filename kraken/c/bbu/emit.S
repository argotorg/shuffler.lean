emit:
	pushq	%rbx
	subq	$32864, %rsp
	movq	%r8, %rbx
	movq	32880(%rsp), %r8
	cmpq	$1024, %rdi
	ja	.LB480
	movq	%rdx, %r10
	movq	%rcx, %rdx
	cmpq	$1024, %rsi
	ja	.LB480
	testq	%rsi, %rsi
	je	.LB457
	movl	$0, %eax
	jmp	.LB459
	.p2align 4
.LB458:
	addq	$1, %rax
	cmpq	%rax, %rsi
	je	.LB457
.LB459:
	cmpb	$0, 4(%rdx,%rax,8)
	jne	.LB458
	cmpb	$0, 5(%rdx,%rax,8)
	je	.LB458
	movl	(%rdx,%rax,8), %ecx
	cmpq	%r8, %rcx
	jb	.LB458
	movq	$-2, %rdx
	jmp	.LB455
.LB457:
	testq	%rdi, %rdi
	je	.LB460
	movl	$0, %eax
	.p2align 5
.LB461:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB461
	testq	%rsi, %rsi
	je	.LB479
.LB478:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%rsi,8), %rcx
	.p2align 5
.LB463:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rcx, %rax
	jne	.LB463
	testq	%rdi, %rdi
	je	.LB464
.LB479:
	movl	$0, %eax
	jmp	.LB466
	.p2align 5
.LB465:
	leaq	1(%rax), %rcx
	cmpq	%rcx, %rdi
	je	.LB493
	movq	%rcx, %rax
.LB466:
	movq	(%rbx,%rax,8), %rcx
	cmpq	$-1, %rcx
	je	.LB465
	movq	%rcx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rcx,8)
	jmp	.LB465
.LB493:
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
.LB467:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB467
.LB477:
	testq	%rsi, %rsi
	je	.LB468
	salq	$3, %rsi
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rcx
	.p2align 5
.LB469:
	movq	(%rcx,%rax), %rdx
	movq	%rdx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rsi, %rax
	jne	.LB469
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rsi
	jmp	.LB471
	.p2align 5
.LB470:
	addq	$8, %rax
	cmpq	%rsi, %rax
	je	.LB476
.LB471:
	cmpq	$-1, 8248(%rax)
	jne	.LB470
	addq	$1, 16440(%rsp)
	jmp	.LB470
.LB472:
	movq	16448(%rsp), %rax
	movq	32896(%rsp), %rdi
	movq	%rax, (%rdi)
	movq	16456(%rsp), %rax
	movq	%rax, 8(%rdi)
	jmp	.LB473
.LB480:
	movq	$-2, %rdx
	jmp	.LB455
.LB468:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB476:
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission3runEv
	cmpb	$1, %al
	je	.LB472
	movq	$-2, %rdx
	cmpb	$2, %al
	je	.LB455
	testb	%al, %al
	jne	.LB473
	movq	32896(%rsp), %rax
	movq	$0, (%rax)
	movq	$0, 8(%rax)
.LB473:
	movq	32(%rsp), %rcx
	movq	32904(%rsp), %rax
	movq	%rcx, (%rax)
	testq	%rcx, %rcx
	je	.LB474
	salq	$3, %rcx
	movl	$0, %eax
	leaq	56(%rsp), %rsi
	.p2align 5
.LB475:
	movq	(%rsi,%rax), %rdx
	movq	%rdx, (%rbx,%rax)
	addq	$8, %rax
	cmpq	%rax, %rcx
	jne	.LB475
.LB474:
	movq	48(%rsp), %rdx
.LB455:
	movq	%rdx, %rax
	addq	$32864, %rsp
	popq	%rbx
	ret
.LB460:
	testq	%rsi, %rsi
	jne	.LB478
.LB464:
	movq	%rdx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32888(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB477
	.size	emit, .-emit
