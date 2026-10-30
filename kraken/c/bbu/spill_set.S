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
	je	.LB245
	movl	$0, %eax
	jmp	.LB248
	.p2align 4
.LB246:
	addq	$1, %rax
	cmpq	%rax, %r12
	je	.LB272
.LB248:
	cmpb	$0, 5(%rbx,%rax,8)
	je	.LB246
	cmpb	$0, 4(%rbx,%rax,8)
	jne	.LB246
	movl	(%rbx,%rax,8), %edx
	cmpq	%rdi, %rdx
	jb	.LB246
	movq	$-2, %rax
	jmp	.LB244
	.p2align 4
.LB250:
	addq	$1, %rax
	cmpq	%rax, %r13
	je	.LB273
.LB251:
	cmpb	$0, 5(%rbp,%rax,8)
	je	.LB250
	cmpb	$0, 4(%rbp,%rax,8)
	jne	.LB250
	movl	0(%rbp,%rax,8), %edx
	cmpq	%rdi, %rdx
	jb	.LB250
	movq	$-2, %rax
	jmp	.LB244
.LB273:
	movq	(%rsp), %rax
	movq	%rax, 16(%rsp)
	testq	%r12, %r12
	je	.LB252
.LB257:
	movl	$0, %r14d
	leaq	16(%rsp), %r15
.LB253:
	movq	(%rbx), %rsi
	movq	%r15, %rdi
	call	_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot
	testb	%al, %al
	jne	.LB261
	addq	$1, %r14
	addq	$8, %rbx
	cmpq	%r12, %r14
	jb	.LB253
	testq	%r13, %r13
	je	.LB262
.LB252:
	movl	$0, %eax
	jmp	.LB255
	.p2align 6
.LB254:
	movq	80(%rsp), %rcx
	movb	%dl, (%rcx,%rax)
	addq	$1, %rax
	cmpq	%rax, %r13
	je	.LB274
.LB255:
	cmpb	$0, 5(%rbp,%rax,8)
	setne	%dl
	cmpb	$0, 4(%rbp,%rax,8)
	sete	%cl
	andb	%cl, %dl
	je	.LB254
	movl	0(%rbp,%rax,8), %edx
	movq	(%rsp), %rcx
	cmpb	$0, (%rcx,%rdx)
	setne	%dl
	jmp	.LB254
.LB274:
	movl	$0, %eax
	jmp	.LB244
.LB261:
	movq	$-2, %rax
.LB244:
	addq	$24, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB262:
	movl	$0, %eax
	jmp	.LB244
.LB245:
	movq	%rcx, %rax
	testq	%r9, %r9
	jne	.LB251
	movl	$0, %eax
	jmp	.LB244
.LB272:
	movl	$0, %eax
	testq	%r13, %r13
	jne	.LB251
	movq	(%rsp), %rax
	movq	%rax, 16(%rsp)
	jmp	.LB257
	.size	spill_set, .-spill_set
