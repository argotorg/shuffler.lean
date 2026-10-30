emission_pop:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$32872, %rsp
	movq	32928(%rsp), %r13
	movq	32952(%rsp), %r15
	cmpq	$1024, %rdi
	ja	.LB.emission_pop.12
	movq	%rdi, %rbx
	movq	%rsi, %r12
	movq	%rdx, %rsi
	cmpq	$1024, %r12
	ja	.LB.emission_pop.12
	testq	%rdi, %rdi
	je	.LB.emission_pop.23
	movl	$0, %eax
	.p2align 5
.LB.emission_pop.0:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rbx
	jne	.LB.emission_pop.0
	testq	%r12, %r12
	je	.LB.emission_pop.3
.LB.emission_pop.1:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%r12,8), %rdx
	.p2align 5
.LB.emission_pop.2:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB.emission_pop.2
	testq	%rbx, %rbx
	je	.LB.emission_pop.24
.LB.emission_pop.3:
	movl	$0, %eax
	jmp	.LB.emission_pop.5
	.p2align 5
.LB.emission_pop.4:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rbx
	je	.LB.emission_pop.6
	movq	%rdx, %rax
.LB.emission_pop.5:
	movq	(%r8,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB.emission_pop.4
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	jmp	.LB.emission_pop.4
.LB.emission_pop.6:
	movq	%rcx, (%rsp)
	movq	%r12, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%rsi, 24(%rsp)
	movq	%rdx, 32(%rsp)
	movq	32936(%rsp), %rdi
	movq	%rdi, 40(%rsp)
	movq	$0, 48(%rsp)
	movl	$0, %edx
	addq	$1, %rax
	.p2align 5
.LB.emission_pop.7:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB.emission_pop.7
.LB.emission_pop.8:
	testq	%r12, %r12
	je	.LB.emission_pop.14
	leaq	0(,%r12,8), %rdx
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB.emission_pop.9:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB.emission_pop.9
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rdx
	jmp	.LB.emission_pop.11
	.p2align 5
.LB.emission_pop.10:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB.emission_pop.15
.LB.emission_pop.11:
	cmpq	$-1, 8248(%rax)
	jne	.LB.emission_pop.10
	addq	$1, 16440(%rsp)
	jmp	.LB.emission_pop.10
.LB.emission_pop.12:
	movq	$-2, %rax
	jmp	.LB.emission_pop.22
.LB.emission_pop.13:
	movq	$-2, %rax
	jmp	.LB.emission_pop.22
.LB.emission_pop.14:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB.emission_pop.15:
	testq	%r13, %r13
	je	.LB.emission_pop.17
	movl	$0, %ebp
	movq	%rsp, %r14
.LB.emission_pop.16:
	movq	%r14, %rdi
	call	_ZN12_GLOBAL__N_18Emission3popEv
	testb	%al, %al
	jne	.LB.emission_pop.13
	addq	$1, %rbp
	cmpq	%rbp, %r13
	jne	.LB.emission_pop.16
.LB.emission_pop.17:
	cmpq	%r13, %rbx
	je	.LB.emission_pop.19
	subq	%r13, %rbx
	movl	$0, %eax
	.p2align 5
.LB.emission_pop.18:
	movq	56(%rsp,%rax,8), %rdx
	movq	32944(%rsp), %rsi
	movq	%rdx, (%rsi,%rax,8)
	addq	$1, %rax
	cmpq	%rbx, %rax
	jb	.LB.emission_pop.18
.LB.emission_pop.19:
	testq	%r12, %r12
	je	.LB.emission_pop.21
	salq	$3, %r12
	movl	$0, %eax
	leaq	8248(%rsp), %rcx
	.p2align 5
.LB.emission_pop.20:
	movq	(%rcx,%rax), %rdx
	movq	%rdx, (%r15,%rax)
	addq	$8, %rax
	cmpq	%rax, %r12
	jne	.LB.emission_pop.20
.LB.emission_pop.21:
	movq	32960(%rsp), %rax
	movq	16440(%rsp), %rdx
	movq	%rdx, (%rax)
	movq	48(%rsp), %rax
.LB.emission_pop.22:
	addq	$32872, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB.emission_pop.23:
	testq	%r12, %r12
	jne	.LB.emission_pop.1
.LB.emission_pop.24:
	movq	%rcx, (%rsp)
	movq	%r12, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%rsi, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32936(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB.emission_pop.8
	.size	emission_pop, .-emission_pop
