spill_set:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$40, %rsp
	movq	%rsi, 8(%rsp)
	movq	%rdx, %rbx
	movq	%rcx, %r12
	movq	%r8, %rbp
	movq	%r9, %r13
	testq	%rcx, %rcx
	je	.LB.spill_set.14
	movl	$0, %eax
	jmp	.LB.spill_set.1
	.p2align 4
.LB.spill_set.0:
	addq	$1, %rax
	cmpq	%rax, %r12
	je	.LB.spill_set.15
.LB.spill_set.1:
	cmpb	$0, 5(%rbx,%rax,8)
	je	.LB.spill_set.0
	cmpb	$0, 4(%rbx,%rax,8)
	jne	.LB.spill_set.0
	movl	(%rbx,%rax,8), %edx
	cmpq	%rdi, %rdx
	jb	.LB.spill_set.0
	movq	$-2, %rax
	jmp	.LB.spill_set.12
	.p2align 4
.LB.spill_set.2:
	addq	$1, %rax
	cmpq	%rax, %r13
	je	.LB.spill_set.4
.LB.spill_set.3:
	cmpb	$0, 5(%rbp,%rax,8)
	je	.LB.spill_set.2
	cmpb	$0, 4(%rbp,%rax,8)
	jne	.LB.spill_set.2
	movl	0(%rbp,%rax,8), %edx
	cmpq	%rdi, %rdx
	jb	.LB.spill_set.2
	movq	$-2, %rax
	jmp	.LB.spill_set.12
.LB.spill_set.4:
	movq	8(%rsp), %rax
	movq	%rax, 24(%rsp)
	testq	%r12, %r12
	je	.LB.spill_set.7
.LB.spill_set.5:
	movl	$0, %r14d
	leaq	24(%rsp), %r15
.LB.spill_set.6:
	movq	(%rbx), %rsi
	movq	%r15, %rdi
	call	_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot
	testb	%al, %al
	jne	.LB.spill_set.11
	addq	$1, %r14
	addq	$8, %rbx
	cmpq	%r12, %r14
	jb	.LB.spill_set.6
	testq	%r13, %r13
	je	.LB.spill_set.13
.LB.spill_set.7:
	movl	$0, %eax
	jmp	.LB.spill_set.9
	.p2align 6
.LB.spill_set.8:
	movq	96(%rsp), %rcx
	movb	%dl, (%rcx,%rax)
	addq	$1, %rax
	cmpq	%rax, %r13
	je	.LB.spill_set.10
.LB.spill_set.9:
	cmpb	$0, 5(%rbp,%rax,8)
	setne	%dl
	cmpb	$0, 4(%rbp,%rax,8)
	sete	%cl
	andb	%cl, %dl
	je	.LB.spill_set.8
	movl	0(%rbp,%rax,8), %edx
	movq	8(%rsp), %rcx
	cmpb	$0, (%rcx,%rdx)
	setne	%dl
	jmp	.LB.spill_set.8
.LB.spill_set.10:
	movl	$0, %eax
	jmp	.LB.spill_set.12
.LB.spill_set.11:
	movq	$-2, %rax
.LB.spill_set.12:
	addq	$40, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB.spill_set.13:
	movl	$0, %eax
	jmp	.LB.spill_set.12
.LB.spill_set.14:
	movq	%rcx, %rax
	testq	%r9, %r9
	jne	.LB.spill_set.3
	movl	$0, %eax
	jmp	.LB.spill_set.12
.LB.spill_set.15:
	movl	$0, %eax
	testq	%r13, %r13
	jne	.LB.spill_set.3
	movq	8(%rsp), %rax
	movq	%rax, 24(%rsp)
	jmp	.LB.spill_set.5
	.size	spill_set, .-spill_set
