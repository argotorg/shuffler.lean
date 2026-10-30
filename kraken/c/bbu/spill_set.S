spill_set:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$24, %rsp
	movq	%rsi, (%rsp)
	movq	%rdx, %rbx
	movq	%rcx, %r12
	movq	%r8, %rbp
	movq	%r9, %r13
	testq	%rcx, %rcx
	je	.LB251
	movl	$0, %eax
	jmp	.LB254
	.p2align 4
.LB252:
	addq	$1, %rax
	cmpq	%rax, %r12
	je	.LB278
.LB254:
	cmpb	$0, 5(%rbx,%rax,8)
	je	.LB252
	cmpb	$0, 4(%rbx,%rax,8)
	jne	.LB252
	movl	(%rbx,%rax,8), %edx
	cmpq	%rdi, %rdx
	jb	.LB252
	movq	$-2, %rax
	jmp	.LB250
	.p2align 4
.LB256:
	addq	$1, %rax
	cmpq	%rax, %r13
	je	.LB279
.LB257:
	cmpb	$0, 5(%rbp,%rax,8)
	je	.LB256
	cmpb	$0, 4(%rbp,%rax,8)
	jne	.LB256
	movl	0(%rbp,%rax,8), %edx
	cmpq	%rdi, %rdx
	jb	.LB256
	movq	$-2, %rax
	jmp	.LB250
.LB279:
	movq	(%rsp), %rax
	movq	%rax, 16(%rsp)
	testq	%r12, %r12
	je	.LB258
.LB263:
	movl	$0, %r14d
	leaq	16(%rsp), %r15
.LB259:
	movq	(%rbx), %rsi
	movq	%r15, %rdi
	call	_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot
	testb	%al, %al
	jne	.LB267
	addq	$1, %r14
	addq	$8, %rbx
	cmpq	%r12, %r14
	jb	.LB259
	testq	%r13, %r13
	je	.LB268
.LB258:
	movl	$0, %eax
	jmp	.LB261
	.p2align 6
.LB260:
	movq	80(%rsp), %rcx
	movb	%dl, (%rcx,%rax)
	addq	$1, %rax
	cmpq	%rax, %r13
	je	.LB280
.LB261:
	cmpb	$0, 5(%rbp,%rax,8)
	setne	%dl
	cmpb	$0, 4(%rbp,%rax,8)
	sete	%cl
	andb	%cl, %dl
	je	.LB260
	movl	0(%rbp,%rax,8), %edx
	movq	(%rsp), %rcx
	cmpb	$0, (%rcx,%rdx)
	setne	%dl
	jmp	.LB260
.LB280:
	movl	$0, %eax
	jmp	.LB250
.LB267:
	movq	$-2, %rax
.LB250:
	addq	$24, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB268:
	movl	$0, %eax
	jmp	.LB250
.LB251:
	movq	%rcx, %rax
	testq	%r9, %r9
	jne	.LB257
	movl	$0, %eax
	jmp	.LB250
.LB278:
	movl	$0, %eax
	testq	%r13, %r13
	jne	.LB257
	movq	(%rsp), %rax
	movq	%rax, 16(%rsp)
	jmp	.LB263
	.size	spill_set, .-spill_set
