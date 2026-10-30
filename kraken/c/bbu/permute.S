permute:
	pushq	%r14
	pushq	%rbp
	pushq	%rbx
	subq	$49248, %rsp
	movq	%rdi, %rbx
	cmpq	$1024, %rdi
	ja	.LB362
	movq	%rsi, %rdi
	movq	%rdx, %r10
	movq	%rcx, %r11
	movq	%r8, %r14
	movq	%r9, %rbp
	testq	%rbx, %rbx
	je	.LB347
	leaq	16480(%rsp), %rax
	leaq	0(,%rbx,8), %rcx
	leaq	(%rax,%rcx), %rsi
	movq	%rax, %rdx
	.p2align 4
.LB348:
	movq	$-1, (%rdx)
	addq	$8, %rdx
	cmpq	%rsi, %rdx
	jne	.LB348
	.p2align 5
.LB349:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rsi, %rax
	jne	.LB349
	movl	$0, %eax
	.p2align 6
.LB350:
	movq	(%r10,%rax,8), %rdx
	movq	%rdx, 41056(%rsp,%rax,8)
	movq	(%rdi,%rax,8), %rsi
	movq	%rsi, 32864(%rsp,%rdx,8)
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	addq	$1, %rax
	cmpq	%rax, %rbx
	jne	.LB350
	leaq	32864(%rsp), %rdx
	movq	%rdx, (%rsp)
	movq	%rax, 8(%rsp)
	movq	$0, 16(%rsp)
	movq	%rdi, 24(%rsp)
	movq	%rax, 32(%rsp)
	movq	%r11, 40(%rsp)
	movq	$0, 48(%rsp)
	movl	$0, %eax
	leaq	56(%rsp), %rsi
	.p2align 5
.LB351:
	movq	16480(%rsp,%rax), %rdx
	movq	%rdx, (%rsi,%rax)
	addq	$8, %rax
	cmpq	%rcx, %rax
	jne	.LB351
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB352:
	movq	(%rsi,%rax), %rdx
	movq	%rdx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rcx, %rax
	jne	.LB352
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rcx
	jmp	.LB354
	.p2align 5
.LB353:
	addq	$8, %rax
	cmpq	%rcx, %rax
	je	.LB374
.LB354:
	cmpq	$-1, 8248(%rax)
	jne	.LB353
	addq	$1, 16440(%rsp)
	jmp	.LB353
.LB374:
	leaq	41056(%rsp), %rsi
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE
	cmpb	$1, %al
	je	.LB355
	movq	$-2, %rdx
	cmpb	$2, %al
	je	.LB345
	testb	%al, %al
	jne	.LB356
.LB360:
	movl	$0, %edx
	movl	$0, %eax
.LB358:
	movq	%rdx, (%r14)
	movq	%rax, 8(%r14)
	testq	%rbx, %rbx
	je	.LB357
.LB356:
	salq	$3, %rbx
	movl	$0, %eax
	leaq	56(%rsp), %rcx
	.p2align 5
.LB359:
	movq	(%rcx,%rax), %rdx
	movq	%rdx, 0(%rbp,%rax)
	addq	$8, %rax
	cmpq	%rax, %rbx
	jne	.LB359
.LB357:
	movq	48(%rsp), %rdx
.LB345:
	movq	%rdx, %rax
	addq	$49248, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r14
	ret
.LB355:
	movq	16448(%rsp), %rdx
	movq	16456(%rsp), %rax
	jmp	.LB358
.LB362:
	movq	$-2, %rdx
	jmp	.LB345
.LB347:
	leaq	32864(%rsp), %rax
	movq	%rax, (%rsp)
	movq	%rbx, 8(%rsp)
	movq	$0, 16(%rsp)
	movq	%rsi, 24(%rsp)
	movq	%rbx, 32(%rsp)
	movq	%rcx, 40(%rsp)
	movq	$0, 48(%rsp)
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	leaq	41056(%rsp), %rsi
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE
	cmpb	$1, %al
	je	.LB355
	movq	$-2, %rdx
	cmpb	$2, %al
	je	.LB345
	testb	%al, %al
	je	.LB360
	jmp	.LB357
	.size	permute, .-permute
