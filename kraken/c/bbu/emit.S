emit:
	pushq	%rbx
	subq	$32864, %rsp
	movq	%r8, %rbx
	movq	32880(%rsp), %r8
	cmpq	$1024, %rdi
	ja	.LB.emit.16
	movq	%rdx, %r10
	movq	%rcx, %rdx
	cmpq	$1024, %rsi
	ja	.LB.emit.16
	testq	%rsi, %rsi
	je	.LB.emit.2
	movl	$0, %eax
	jmp	.LB.emit.1
	.p2align 4
.LB.emit.0:
	addq	$1, %rax
	cmpq	%rax, %rsi
	je	.LB.emit.2
.LB.emit.1:
	cmpb	$0, 4(%rdx,%rax,8)
	jne	.LB.emit.0
	cmpb	$0, 5(%rdx,%rax,8)
	je	.LB.emit.0
	movl	(%rdx,%rax,8), %ecx
	cmpq	%r8, %rcx
	jb	.LB.emit.0
	movq	$-2, %rdx
	jmp	.LB.emit.22
.LB.emit.2:
	testq	%rdi, %rdi
	je	.LB.emit.23
	movl	$0, %eax
	.p2align 5
.LB.emit.3:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB.emit.3
	testq	%rsi, %rsi
	je	.LB.emit.6
.LB.emit.4:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%rsi,8), %rcx
	.p2align 5
.LB.emit.5:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rcx, %rax
	jne	.LB.emit.5
	testq	%rdi, %rdi
	je	.LB.emit.24
.LB.emit.6:
	movl	$0, %eax
	jmp	.LB.emit.8
	.p2align 5
.LB.emit.7:
	leaq	1(%rax), %rcx
	cmpq	%rcx, %rdi
	je	.LB.emit.9
	movq	%rcx, %rax
.LB.emit.8:
	movq	(%rbx,%rax,8), %rcx
	cmpq	$-1, %rcx
	je	.LB.emit.7
	movq	%rcx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rcx,8)
	jmp	.LB.emit.7
.LB.emit.9:
	movq	%rdx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	%rcx, 32(%rsp)
	movq	32888(%rsp), %rdi
	movq	%rdi, 40(%rsp)
	movq	$0, 48(%rsp)
	movl	$0, %edx
	movq	%rcx, %rax
	.p2align 5
.LB.emit.10:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB.emit.10
.LB.emit.11:
	testq	%rsi, %rsi
	je	.LB.emit.17
	salq	$3, %rsi
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rcx
	.p2align 5
.LB.emit.12:
	movq	(%rcx,%rax), %rdx
	movq	%rdx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rsi, %rax
	jne	.LB.emit.12
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rsi
	jmp	.LB.emit.14
	.p2align 5
.LB.emit.13:
	addq	$8, %rax
	cmpq	%rsi, %rax
	je	.LB.emit.18
.LB.emit.14:
	cmpq	$-1, 8248(%rax)
	jne	.LB.emit.13
	addq	$1, 16440(%rsp)
	jmp	.LB.emit.13
.LB.emit.15:
	movq	16448(%rsp), %rax
	movq	32896(%rsp), %rdi
	movq	%rax, (%rdi)
	movq	16456(%rsp), %rax
	movq	%rax, 8(%rdi)
	jmp	.LB.emit.19
.LB.emit.16:
	movq	$-2, %rdx
	jmp	.LB.emit.22
.LB.emit.17:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB.emit.18:
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission3runEv
	cmpb	$1, %al
	je	.LB.emit.15
	movq	$-2, %rdx
	cmpb	$2, %al
	je	.LB.emit.22
	testb	%al, %al
	jne	.LB.emit.19
	movq	32896(%rsp), %rax
	movq	$0, (%rax)
	movq	$0, 8(%rax)
.LB.emit.19:
	movq	32(%rsp), %rcx
	movq	32904(%rsp), %rax
	movq	%rcx, (%rax)
	testq	%rcx, %rcx
	je	.LB.emit.21
	salq	$3, %rcx
	movl	$0, %eax
	leaq	56(%rsp), %rsi
	.p2align 5
.LB.emit.20:
	movq	(%rsi,%rax), %rdx
	movq	%rdx, (%rbx,%rax)
	addq	$8, %rax
	cmpq	%rax, %rcx
	jne	.LB.emit.20
.LB.emit.21:
	movq	48(%rsp), %rdx
.LB.emit.22:
	movq	%rdx, %rax
	addq	$32864, %rsp
	popq	%rbx
	ret
.LB.emit.23:
	testq	%rsi, %rsi
	jne	.LB.emit.4
.LB.emit.24:
	movq	%rdx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32888(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB.emit.11
	.size	emit, .-emit
