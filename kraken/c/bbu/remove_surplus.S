remove_surplus:
	cmpq	$1024, %rdi
	ja	.LB335
	pushq	%rbx
	subq	$32864, %rsp
	movq	%rdx, %r10
	movq	%r8, %rbx
	cmpq	$1024, %rsi
	ja	.LB324
	testq	%rdi, %rdi
	je	.LB304
	movl	$0, %eax
	.p2align 5
.LB305:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB305
	testq	%rsi, %rsi
	je	.LB323
.LB322:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%rsi,8), %rdx
	.p2align 5
.LB307:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB307
	testq	%rdi, %rdi
	je	.LB308
.LB323:
	movl	$0, %eax
	jmp	.LB310
	.p2align 5
.LB309:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rdi
	je	.LB338
	movq	%rdx, %rax
.LB310:
	movq	(%rbx,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB309
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	jmp	.LB309
.LB338:
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
.LB311:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB311
.LB321:
	testq	%rsi, %rsi
	je	.LB312
	leaq	0(,%rsi,8), %rdx
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB313:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB313
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rdx
	jmp	.LB315
	.p2align 5
.LB314:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB320
.LB315:
	cmpq	$-1, 8248(%rax)
	jne	.LB314
	addq	$1, 16440(%rsp)
	jmp	.LB314
.LB316:
	movq	16448(%rsp), %rax
	movq	32896(%rsp), %rsi
	movq	%rax, (%rsi)
	movq	16456(%rsp), %rax
	movq	%rax, 8(%rsi)
	jmp	.LB317
.LB324:
	movq	$-2, %rdx
	jmp	.LB302
.LB312:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB320:
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission13removeSurplusEv
	cmpb	$1, %al
	je	.LB316
	movq	$-2, %rdx
	cmpb	$2, %al
	je	.LB302
	testb	%al, %al
	jne	.LB317
	movq	32896(%rsp), %rax
	movq	$0, (%rax)
	movq	$0, 8(%rax)
.LB317:
	movq	32(%rsp), %rcx
	movq	32904(%rsp), %rax
	movq	%rcx, (%rax)
	testq	%rcx, %rcx
	je	.LB318
	salq	$3, %rcx
	movl	$0, %eax
	leaq	56(%rsp), %rsi
	.p2align 5
.LB319:
	movq	(%rsi,%rax), %rdx
	movq	%rdx, (%rbx,%rax)
	addq	$8, %rax
	cmpq	%rax, %rcx
	jne	.LB319
.LB318:
	movq	48(%rsp), %rdx
.LB302:
	movq	%rdx, %rax
	addq	$32864, %rsp
	popq	%rbx
	ret
.LB304:
	testq	%rsi, %rsi
	jne	.LB322
.LB308:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32888(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB321
.LB335:
	movq	$-2, %rdx
	movq	%rdx, %rax
	ret
	.size	remove_surplus, .-remove_surplus
