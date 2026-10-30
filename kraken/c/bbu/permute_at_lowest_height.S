permute_at_lowest_height:
	pushq	%rbp
	pushq	%rbx
	subq	$32872, %rsp
	movq	%rdi, %rbx
	cmpq	$1024, %rdi
	ja	.LB416
	movq	%rdx, %rdi
	movq	%r8, %rbp
	cmpq	$1024, %rsi
	ja	.LB416
	testq	%rbx, %rbx
	je	.LB395
	movl	$0, %eax
	.p2align 5
.LB396:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rbx
	jne	.LB396
	testq	%rsi, %rsi
	je	.LB415
.LB414:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%rsi,8), %rdx
	.p2align 5
.LB398:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB398
	testq	%rbx, %rbx
	je	.LB399
.LB415:
	movl	$0, %eax
	jmp	.LB401
	.p2align 5
.LB400:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rbx
	je	.LB428
	movq	%rdx, %rax
.LB401:
	movq	0(%rbp,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB400
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	jmp	.LB400
.LB428:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%rdi, 24(%rsp)
	movq	%rdx, 32(%rsp)
	movq	32904(%rsp), %rdi
	movq	%rdi, 40(%rsp)
	movq	$0, 48(%rsp)
	movl	$0, %edx
	addq	$1, %rax
	.p2align 5
.LB402:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB402
.LB413:
	testq	%rsi, %rsi
	je	.LB403
	leaq	0(,%rsi,8), %rdx
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB404:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB404
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rdx
	jmp	.LB406
	.p2align 5
.LB405:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB412
.LB406:
	cmpq	$-1, 8248(%rax)
	jne	.LB405
	addq	$1, 16440(%rsp)
	jmp	.LB405
.LB407:
	movq	16448(%rsp), %rax
	movq	32912(%rsp), %rdi
	movq	%rax, (%rdi)
	movq	16456(%rsp), %rax
	movq	%rax, 8(%rdi)
	jmp	.LB408
.LB416:
	movq	$-2, %rdx
	jmp	.LB393
.LB403:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB412:
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission21permuteAtLowestHeightEv
	cmpb	$1, %al
	je	.LB407
	movq	$-2, %rdx
	cmpb	$2, %al
	je	.LB393
	testb	%al, %al
	jne	.LB408
	movq	32912(%rsp), %rax
	movq	$0, (%rax)
	movq	$0, 8(%rax)
.LB408:
	leaq	0(,%rbx,8), %rsi
	movl	$0, %eax
	leaq	56(%rsp), %rcx
	testq	%rbx, %rbx
	je	.LB410
	.p2align 5
.LB411:
	movq	(%rcx,%rax), %rdx
	movq	%rdx, 0(%rbp,%rax)
	addq	$8, %rax
	cmpq	%rsi, %rax
	jne	.LB411
.LB410:
	movq	48(%rsp), %rdx
.LB393:
	movq	%rdx, %rax
	addq	$32872, %rsp
	popq	%rbx
	popq	%rbp
	ret
.LB395:
	testq	%rsi, %rsi
	jne	.LB414
.LB399:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%rdi, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32904(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB413
	.size	permute_at_lowest_height, .-permute_at_lowest_height
