_ZN12_GLOBAL__N_18Emission21permuteAtLowestHeightEv:
	subq	$24584, %rsp
	movq	32(%rdi), %rcx
	testq	%rcx, %rcx
	je	.LB376
	movl	$0, %eax
	movl	$0, %esi
	movl	$0, %r8d
.LB381:
	movq	56(%rdi,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB377
	cmpq	8(%rdi), %rax
	jnb	.LB377
	movq	16464(%rdi), %r9
	movq	8192(%r9,%rax,8), %r9
	cmpq	%rcx, %rdx
	je	.LB378
	jb	.LB379
.LB378:
	cmpq	$-1, %r9
	jne	.LB392
	movq	%rax, 16384(%rsp,%rax,8)
.LB380:
	addq	$1, %rax
	cmpq	%rcx, %rax
	jne	.LB381
	movl	$2, %eax
	cmpq	%rsi, %r8
	jne	.LB375
	testq	%rsi, %rsi
	je	.LB376
	salq	$3, %rsi
	movl	$0, %eax
	.p2align 5
.LB384:
	movq	(%rsp,%rax), %rdx
	movq	8192(%rsp,%rax), %rcx
	movq	%rcx, 16384(%rsp,%rdx,8)
	addq	$8, %rax
	cmpq	%rax, %rsi
	jne	.LB384
.LB376:
	leaq	16384(%rsp), %rsi
	call	_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE
	jmp	.LB375
.LB377:
	movl	$2, %eax
.LB375:
	addq	$24584, %rsp
	ret
.LB379:
	movq	%rdx, 16384(%rsp,%rax,8)
	cmpq	$-1, %r9
	jne	.LB380
	movq	%rax, 8192(%rsp,%r8,8)
	leaq	1(%r8), %r8
	jmp	.LB380
.LB392:
	movq	%rax, (%rsp,%rsi,8)
	leaq	1(%rsi), %rsi
	jmp	.LB380
	.size	_ZN12_GLOBAL__N_18Emission21permuteAtLowestHeightEv, .-_ZN12_GLOBAL__N_18Emission21permuteAtLowestHeightEv
