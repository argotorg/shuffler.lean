build_bottom_up:
	cmpq	%rdi, %rsi
	jb	.LB.build_bottom_up.14
	movq	%rdx, %r10
	cmpq	$1024, %rsi
	ja	.LB.build_bottom_up.14
	subq	$32872, %rsp
	testq	%rdi, %rdi
	je	.LB.build_bottom_up.18
	movl	$0, %eax
	.p2align 5
.LB.build_bottom_up.0:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB.build_bottom_up.0
	testq	%rsi, %rsi
	je	.LB.build_bottom_up.3
.LB.build_bottom_up.1:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%rsi,8), %rdx
	.p2align 5
.LB.build_bottom_up.2:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB.build_bottom_up.2
	testq	%rdi, %rdi
	je	.LB.build_bottom_up.19
.LB.build_bottom_up.3:
	movl	$0, %eax
	jmp	.LB.build_bottom_up.5
	.p2align 5
.LB.build_bottom_up.4:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rdi
	je	.LB.build_bottom_up.6
	movq	%rdx, %rax
.LB.build_bottom_up.5:
	movq	(%r8,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB.build_bottom_up.4
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	jmp	.LB.build_bottom_up.4
.LB.build_bottom_up.6:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	%rdx, 32(%rsp)
	movq	32880(%rsp), %rdi
	movq	%rdi, 40(%rsp)
	movq	$0, 48(%rsp)
	movl	$0, %edx
	addq	$1, %rax
	.p2align 5
.LB.build_bottom_up.7:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB.build_bottom_up.7
.LB.build_bottom_up.8:
	testq	%rsi, %rsi
	je	.LB.build_bottom_up.15
	leaq	0(,%rsi,8), %rdx
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB.build_bottom_up.9:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB.build_bottom_up.9
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rdx
	jmp	.LB.build_bottom_up.11
	.p2align 5
.LB.build_bottom_up.10:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB.build_bottom_up.16
.LB.build_bottom_up.11:
	cmpq	$-1, 8248(%rax)
	jne	.LB.build_bottom_up.10
	addq	$1, 16440(%rsp)
	jmp	.LB.build_bottom_up.10
.LB.build_bottom_up.12:
	movq	32888(%rsp), %rax
	movq	$0, (%rax)
	movq	$0, 8(%rax)
	movq	48(%rsp), %rdx
	jmp	.LB.build_bottom_up.17
.LB.build_bottom_up.13:
	movq	16448(%rsp), %rax
	movq	32888(%rsp), %rsi
	movq	%rax, (%rsi)
	movq	16456(%rsp), %rax
	movq	%rax, 8(%rsi)
	movq	48(%rsp), %rdx
	jmp	.LB.build_bottom_up.17
.LB.build_bottom_up.14:
	movq	$-2, %rdx
	movq	%rdx, %rax
	ret
.LB.build_bottom_up.15:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB.build_bottom_up.16:
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv
	cmpb	$1, %al
	je	.LB.build_bottom_up.13
	movq	$-2, %rdx
	cmpb	$2, %al
	jne	.LB.build_bottom_up.12
.LB.build_bottom_up.17:
	movq	%rdx, %rax
	addq	$32872, %rsp
	ret
.LB.build_bottom_up.18:
	testq	%rsi, %rsi
	jne	.LB.build_bottom_up.1
.LB.build_bottom_up.19:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32880(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB.build_bottom_up.8
	.size	build_bottom_up, .-build_bottom_up
