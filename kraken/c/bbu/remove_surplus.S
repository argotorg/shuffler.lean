remove_surplus:
	cmpq	$1024, %rdi
	ja	.LB341
	pushq	%rbx
	subq	$32864, %rsp
	movq	%rdx, %r10
	movq	%r8, %rbx
	cmpq	$1024, %rsi
	ja	.LB330
	testq	%rdi, %rdi
	je	.LB310
	movl	$0, %eax
	.p2align 5
.LB311:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB311
	testq	%rsi, %rsi
	je	.LB329
.LB328:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%rsi,8), %rdx
	.p2align 5
.LB313:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB313
	testq	%rdi, %rdi
	je	.LB314
.LB329:
	movl	$0, %eax
	jmp	.LB316
	.p2align 5
.LB315:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rdi
	je	.LB344
	movq	%rdx, %rax
.LB316:
	movq	(%rbx,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB315
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	jmp	.LB315
.LB344:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	%rdx, 32(%rsp)
	movq	32888(%rsp), %rdi
	movq	%rdi, 40(%rsp)
	movq	$0, 48(%rsp)
	movl	$0, %edx
	addq	$1, %rax
	.p2align 5
.LB317:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB317
.LB327:
	testq	%rsi, %rsi
	je	.LB318
	leaq	0(,%rsi,8), %rdx
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB319:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB319
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rdx
	jmp	.LB321
	.p2align 5
.LB320:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB326
.LB321:
	cmpq	$-1, 8248(%rax)
	jne	.LB320
	addq	$1, 16440(%rsp)
	jmp	.LB320
.LB322:
	movq	16448(%rsp), %rax
	movq	32896(%rsp), %rsi
	movq	%rax, (%rsi)
	movq	16456(%rsp), %rax
	movq	%rax, 8(%rsi)
	jmp	.LB323
.LB330:
	movq	$-2, %rdx
	jmp	.LB308
.LB318:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB326:
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission13removeSurplusEv
	cmpb	$1, %al
	je	.LB322
	movq	$-2, %rdx
	cmpb	$2, %al
	je	.LB308
	testb	%al, %al
	jne	.LB323
	movq	32896(%rsp), %rax
	movq	$0, (%rax)
	movq	$0, 8(%rax)
.LB323:
	movq	32(%rsp), %rcx
	movq	32904(%rsp), %rax
	movq	%rcx, (%rax)
	testq	%rcx, %rcx
	je	.LB324
	salq	$3, %rcx
	movl	$0, %eax
	leaq	56(%rsp), %rsi
	.p2align 5
.LB325:
	movq	(%rsi,%rax), %rdx
	movq	%rdx, (%rbx,%rax)
	addq	$8, %rax
	cmpq	%rax, %rcx
	jne	.LB325
.LB324:
	movq	48(%rsp), %rdx
.LB308:
	movq	%rdx, %rax
	addq	$32864, %rsp
	popq	%rbx
	ret
.LB310:
	testq	%rsi, %rsi
	jne	.LB328
.LB314:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32888(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB327
.LB341:
	movq	$-2, %rdx
	movq	%rdx, %rax
	ret
	.size	remove_surplus, .-remove_surplus
