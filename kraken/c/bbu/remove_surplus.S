remove_surplus:
	cmpq	$1024, %rdi
	ja	.LB.remove_surplus.22
	pushq	%rbx
	subq	$32864, %rsp
	movq	%rdx, %r10
	movq	%r8, %rbx
	cmpq	$1024, %rsi
	ja	.LB.remove_surplus.13
	testq	%rdi, %rdi
	je	.LB.remove_surplus.20
	movl	$0, %eax
	.p2align 5
.LB.remove_surplus.0:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB.remove_surplus.0
	testq	%rsi, %rsi
	je	.LB.remove_surplus.3
.LB.remove_surplus.1:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%rsi,8), %rdx
	.p2align 5
.LB.remove_surplus.2:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB.remove_surplus.2
	testq	%rdi, %rdi
	je	.LB.remove_surplus.21
.LB.remove_surplus.3:
	movl	$0, %eax
	jmp	.LB.remove_surplus.5
	.p2align 5
.LB.remove_surplus.4:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rdi
	je	.LB.remove_surplus.6
	movq	%rdx, %rax
.LB.remove_surplus.5:
	movq	(%rbx,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB.remove_surplus.4
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	jmp	.LB.remove_surplus.4
.LB.remove_surplus.6:
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
.LB.remove_surplus.7:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB.remove_surplus.7
.LB.remove_surplus.8:
	testq	%rsi, %rsi
	je	.LB.remove_surplus.14
	leaq	0(,%rsi,8), %rdx
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB.remove_surplus.9:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB.remove_surplus.9
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rdx
	jmp	.LB.remove_surplus.11
	.p2align 5
.LB.remove_surplus.10:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB.remove_surplus.15
.LB.remove_surplus.11:
	cmpq	$-1, 8248(%rax)
	jne	.LB.remove_surplus.10
	addq	$1, 16440(%rsp)
	jmp	.LB.remove_surplus.10
.LB.remove_surplus.12:
	movq	16448(%rsp), %rax
	movq	32896(%rsp), %rsi
	movq	%rax, (%rsi)
	movq	16456(%rsp), %rax
	movq	%rax, 8(%rsi)
	jmp	.LB.remove_surplus.16
.LB.remove_surplus.13:
	movq	$-2, %rdx
	jmp	.LB.remove_surplus.19
.LB.remove_surplus.14:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB.remove_surplus.15:
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission13removeSurplusEv
	cmpb	$1, %al
	je	.LB.remove_surplus.12
	movq	$-2, %rdx
	cmpb	$2, %al
	je	.LB.remove_surplus.19
	testb	%al, %al
	jne	.LB.remove_surplus.16
	movq	32896(%rsp), %rax
	movq	$0, (%rax)
	movq	$0, 8(%rax)
.LB.remove_surplus.16:
	movq	32(%rsp), %rcx
	movq	32904(%rsp), %rax
	movq	%rcx, (%rax)
	testq	%rcx, %rcx
	je	.LB.remove_surplus.18
	salq	$3, %rcx
	movl	$0, %eax
	leaq	56(%rsp), %rsi
	.p2align 5
.LB.remove_surplus.17:
	movq	(%rsi,%rax), %rdx
	movq	%rdx, (%rbx,%rax)
	addq	$8, %rax
	cmpq	%rax, %rcx
	jne	.LB.remove_surplus.17
.LB.remove_surplus.18:
	movq	48(%rsp), %rdx
.LB.remove_surplus.19:
	movq	%rdx, %rax
	addq	$32864, %rsp
	popq	%rbx
	ret
.LB.remove_surplus.20:
	testq	%rsi, %rsi
	jne	.LB.remove_surplus.1
.LB.remove_surplus.21:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32888(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB.remove_surplus.8
.LB.remove_surplus.22:
	movq	$-2, %rdx
	movq	%rdx, %rax
	ret
	.size	remove_surplus, .-remove_surplus
