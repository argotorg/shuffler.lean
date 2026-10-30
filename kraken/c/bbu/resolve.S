resolve:
	pushq	%rbp
	pushq	%rbx
	subq	$32840, %rsp
	movq	%r8, %rbx
	movq	32864(%rsp), %r11
	movq	32896(%rsp), %rbp
	movl	32904(%rsp), %r8d
	cmpq	$1024, %rdi
	ja	.LB.resolve.13
	movq	%rsi, %r10
	movq	%rdx, %rsi
	cmpq	$1024, %r10
	ja	.LB.resolve.13
	cmpq	$1024, %r9
	seta	%al
	cmpq	%r9, 32872(%rsp)
	setnb	%dl
	orb	%dl, %al
	jne	.LB.resolve.14
	cmpb	$1, %r8b
	ja	.LB.resolve.14
	testq	%rdi, %rdi
	je	.LB.resolve.15
	movl	$0, %eax
	jmp	.LB.resolve.1
	.p2align 5
.LB.resolve.0:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rdi
	je	.LB.resolve.2
	movq	%rdx, %rax
.LB.resolve.1:
	cmpb	$0, 5(%rsi,%rax,8)
	je	.LB.resolve.0
	cmpb	$0, 4(%rsi,%rax,8)
	jne	.LB.resolve.0
	movl	(%rsi,%rax,8), %edx
	cmpq	%rbp, %rdx
	jb	.LB.resolve.0
	movq	$-2, %rdx
	jmp	.LB.resolve.12
.LB.resolve.2:
	movl	$0, %edx
	addq	$1, %rax
	.p2align 5
.LB.resolve.3:
	movq	$-1, 16448(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB.resolve.3
	testq	%r10, %r10
	je	.LB.resolve.6
.LB.resolve.4:
	movl	$0, %eax
	.p2align 5
.LB.resolve.5:
	movq	$-1, 24640(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%r10, %rax
	jb	.LB.resolve.5
	testq	%rdi, %rdi
	je	.LB.resolve.16
.LB.resolve.6:
	movl	$0, %eax
	jmp	.LB.resolve.8
	.p2align 5
.LB.resolve.7:
	addq	$1, %rax
	cmpq	%rax, %rdi
	je	.LB.resolve.16
.LB.resolve.8:
	movq	(%rbx,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB.resolve.7
	movq	%rdx, 16448(%rsp,%rax,8)
	movq	%rax, 24640(%rsp,%rdx,8)
	jmp	.LB.resolve.7
	.p2align 5
.LB.resolve.9:
	addq	$1, %rax
	cmpq	%r9, %rax
	jnb	.LB.resolve.11
.LB.resolve.10:
	movq	(%r11,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB.resolve.9
	movq	%rdx, 64(%rsp,%rax,8)
	movq	%rax, 8256(%rsp,%rdx,8)
	jmp	.LB.resolve.9
.LB.resolve.11:
	movq	%rsi, (%rsp)
	movq	%rdi, 8(%rsp)
	movq	%rcx, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	32888(%rsp), %rax
	movq	%rax, 32(%rsp)
	cmpb	$1, %r8b
	sete	40(%rsp)
	movq	32912(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	32872(%rsp), %rax
	movq	32880(%rsp), %rdx
	leaq	16448(%rsp), %rsi
	movq	%rsp, %rdi
	leaq	64(%rsp), %r8
	movq	%rdx, %rcx
	movq	%rax, %rdx
	call	_ZN12_GLOBAL__N_17Planner7resolveERKNS_7MappingENS_8Emission7BlockedES3_m
	movq	$-1, %rdx
	cmpb	$1, %al
	je	.LB.resolve.12
	cmpb	$2, %al
	setne	%dl
	movzbl	%dl, %edx
	leaq	-2(%rdx,%rdx), %rdx
.LB.resolve.12:
	movq	%rdx, %rax
	addq	$32840, %rsp
	popq	%rbx
	popq	%rbp
	ret
.LB.resolve.13:
	movq	$-2, %rdx
	jmp	.LB.resolve.12
.LB.resolve.14:
	movq	$-2, %rdx
	jmp	.LB.resolve.12
.LB.resolve.15:
	testq	%r10, %r10
	jne	.LB.resolve.4
.LB.resolve.16:
	movl	$0, %eax
	.p2align 5
.LB.resolve.17:
	movq	$-1, 64(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%r9, %rax
	jb	.LB.resolve.17
	testq	%r10, %r10
	je	.LB.resolve.19
	leaq	64(%rsp), %rax
	leaq	(%rax,%r10,8), %rdx
	.p2align 5
.LB.resolve.18:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rax, %rdx
	jne	.LB.resolve.18
.LB.resolve.19:
	movl	$0, %eax
	jmp	.LB.resolve.10
	.size	resolve, .-resolve
