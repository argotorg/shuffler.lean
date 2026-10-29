buildBottomUp:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$24, %rsp
	movq	%rdi, %rbp
	movq	24(%rdi), %r13
	testq	%r13, %r13
	je	.LB62
	movl	$0, %r14d
	jmp	.LB85
.LB65:
	cmpq	%r13, %r15
	jne	.LB87
	movq	%rbp, %rdi
	call	permuteDestinations
	jmp	.LB61
.LB103:
	movq	56(%rbp), %rdx
	movq	%rax, (%rdx)
	movq	56(%rbp), %rax
	subq	$16, %rcx
	movq	%rcx, 8(%rax)
	movq	$-1, %rax
	jmp	.LB61
	.p2align 5
.LB73:
	addq	$1, %rbx
	cmpq	%r13, %rbx
	je	.LB102
.LB66:
	cmpq	$-1, 8264(%rbp,%rbx,8)
	jne	.LB73
	movq	32(%rbp), %rax
	leaq	(%rax,%rbx,8), %rax
	movq	(%rax), %r12
	movzbl	4(%rax), %edx
	movzbl	5(%rax), %eax
	leal	-1(%rdx), %ecx
	cmpb	$1, %cl
	jbe	.LB73
	testb	%al, %al
	je	.LB73
	movzbl	%dl, %edx
	salq	$32, %rdx
	movabsq	$-1095216660481, %rdi
	andq	%rdi, %r12
	orq	%rdx, %r12
	movzbl	%al, %eax
	salq	$40, %rax
	movabsq	$-280375465082881, %rdi
	andq	%rdi, %r12
	orq	%rax, %r12
	movq	%r12, %rsi
	movq	%rbp, %rdi
	call	isSpilled
	testl	%eax, %eax
	jne	.LB73
	movq	%r12, %rsi
	movq	%rbp, %rdi
	call	shallowestCopyPosition
	cmpq	$-1, %rax
	je	.LB73
	movq	%r15, %rcx
	subq	%rax, %rcx
	leaq	-1(%rcx), %rdx
	cmpq	$15, %rdx
	ja	.LB103
	cmpq	%r14, %rax
	setne	%cl
	cmpq	$15, %rdx
	sete	%al
	testb	%al, %cl
	je	.LB73
	movq	8(%rsp), %rax
	cmpq	$-1, %rax
	cmove	%rbx, %rax
	movq	%rax, 8(%rsp)
	jmp	.LB73
.LB102:
	movq	8(%rsp), %rax
	cmpq	%r14, %rax
	je	.LB67
	cmpq	$-1, %rax
	je	.LB67
	movq	%r15, %rax
	subq	%r14, %rax
	cmpq	$15, %rax
	jbe	.LB104
.LB74:
	movq	8264(%rbp,%r14,8), %rax
	cmpq	$-1, %rax
	je	.LB75
	cmpq	%r14, %rax
	jb	.LB89
	movq	64(%rbp), %rcx
	leaq	0(,%rax,8), %r8
	movq	(%rcx,%rax,8), %rdi
	movq	%rdi, %rdx
	xorq	(%rcx,%r14,8), %rdx
	salq	$16, %rdx
	jne	.LB105
	movq	72(%rbp,%r14,8), %rdx
	leaq	8(%r14), %rcx
	movq	72(%rbp,%rax,8), %rsi
	movq	%rsi, 8(%rbp,%rcx,8)
	movq	%rdx, 72(%rbp,%r8)
	movq	8(%rbp,%rcx,8), %rcx
	movq	%r14, 8264(%rbp,%rcx,8)
	movq	%rax, 8264(%rbp,%rdx,8)
.LB64:
	addq	$1, %r14
	movq	24(%rbp), %r13
	cmpq	%r13, %r14
	jnb	.LB62
.LB85:
	movq	0(%rbp), %r15
	cmpq	%r15, %r14
	jnb	.LB63
	cmpq	%r14, 72(%rbp,%r14,8)
	je	.LB64
.LB63:
	cmpq	$0, 8(%rbp)
	je	.LB65
	movq	%r14, %rbx
	movq	$-1, 8(%rsp)
	cmpq	%r13, %r14
	jb	.LB66
.LB67:
	cmpq	%r15, %r14
	setb	%dl
	cmpq	%r13, %r15
	setb	%al
	testb	%al, %dl
	je	.LB74
	cmpq	$-1, 8(%rsp)
	jne	.LB74
	cmpq	$-1, 8264(%rbp,%r15,8)
	jne	.LB74
	movq	%r15, %rax
	subq	%r14, %rax
	cmpq	$15, %rax
	ja	.LB74
	movq	%r15, %rsi
	movq	%rbp, %rdi
	call	generate
	testq	%rax, %rax
	jne	.LB61
	subq	$1, %r14
	jmp	.LB64
.LB104:
	movq	8(%rsp), %rsi
	movq	%rbp, %rdi
	call	generate
	testq	%rax, %rax
	je	.LB106
.LB61:
	addq	$24, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB106:
	subq	$1, %r14
	jmp	.LB64
.LB105:
	movq	%r15, %rdx
	subq	%rax, %rdx
	cmpq	$1, %rdx
	je	.LB90
	leaq	-1(%r15), %rsi
	jmp	.LB80
	.p2align 5
.LB78:
	subq	$1, %rsi
	cmpq	%rsi, %rax
	je	.LB107
.LB80:
	movq	%rdi, %rdx
	xorq	(%rcx,%rsi,8), %rdx
	salq	$16, %rdx
	jne	.LB78
	cmpq	%rsi, 72(%rbp,%rsi,8)
	je	.LB78
	xorq	(%rcx,%rsi,8), %rdi
	salq	$16, %rdi
	je	.LB77
	movq	$-2, %rax
	jmp	.LB61
.LB107:
	movq	%rax, %rsi
.LB77:
	movq	72(%rbp,%rsi,8), %rdx
	leaq	8(%rsi), %rcx
	movq	72(%rbp,%rax,8), %rdi
	movq	%rdi, 8(%rbp,%rcx,8)
	movq	%rdx, 72(%rbp,%r8)
	movq	8(%rbp,%rcx,8), %rcx
	movq	%rsi, 8264(%rbp,%rcx,8)
	movq	%rax, 8264(%rbp,%rdx,8)
	cmpq	%rsi, %r14
	je	.LB92
	leaq	-1(%r15), %rax
	cmpq	%rsi, %rax
	je	.LB81
	subq	%rsi, %r15
	leaq	-1(%r15), %rax
	cmpq	$16, %rax
	ja	.LB108
	movq	%rbp, %rdi
	call	swapWith
	testq	%rax, %rax
	jne	.LB61
.LB81:
	movq	0(%rbp), %rax
	cmpq	%rax, %r14
	jnb	.LB94
	cmpq	%r14, 72(%rbp,%r14,8)
	je	.LB95
.LB83:
	leaq	-1(%rax), %rdx
	cmpq	%r14, %rdx
	je	.LB64
	subq	%r14, %rax
	leaq	-1(%rax), %rdx
	cmpq	$16, %rdx
	ja	.LB109
	movq	%r14, %rsi
	movq	%rbp, %rdi
	call	swapWith
	testq	%rax, %rax
	je	.LB64
	jmp	.LB61
.LB90:
	movq	%rax, %rsi
	jmp	.LB77
.LB108:
	movq	56(%rbp), %rax
	movq	%rsi, (%rax)
	movq	56(%rbp), %rax
	subq	$17, %r15
	movq	%r15, 8(%rax)
	movq	$-1, %rax
	jmp	.LB61
.LB75:
	movq	%r14, %rsi
	movq	%rbp, %rdi
	call	generate
	testq	%rax, %rax
	jne	.LB61
	movq	0(%rbp), %rax
	cmpq	%rax, %r14
	jnb	.LB93
	cmpq	%r14, 72(%rbp,%r14,8)
	jne	.LB83
	jmp	.LB64
.LB109:
	movq	56(%rbp), %rdx
	movq	%r14, (%rdx)
	movq	56(%rbp), %rdx
	subq	$17, %rax
	movq	%rax, 8(%rdx)
	movq	$-1, %rax
	jmp	.LB61
.LB92:
	movq	%rsi, %r14
	jmp	.LB64
.LB62:
	cmpq	%r13, 0(%rbp)
	jne	.LB96
	movl	$0, %eax
	jmp	.LB61
.LB87:
	movq	$-2, %rax
	jmp	.LB61
.LB89:
	movq	$-2, %rax
	jmp	.LB61
.LB93:
	movq	$-2, %rax
	jmp	.LB61
.LB94:
	movq	$-2, %rax
	jmp	.LB61
.LB95:
	movq	$-2, %rax
	jmp	.LB61
.LB96:
	movq	$-2, %rax
	jmp	.LB61
	.size	buildBottomUp, .-buildBottomUp
