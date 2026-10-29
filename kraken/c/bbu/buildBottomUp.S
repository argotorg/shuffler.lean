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
	je	.LB66
	movl	$0, %r14d
	jmp	.LB88
.LB69:
	cmpq	%r13, %r15
	jne	.LB90
	movq	%rbp, %rdi
	call	permuteDestinations
	jmp	.LB65
.LB107:
	movq	56(%rbp), %rcx
	movq	%rax, (%rcx)
	movq	56(%rbp), %rax
	subq	$16, %rdx
	movq	%rdx, 8(%rax)
	movq	$-1, %rax
.LB65:
	addq	$24, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB73:
	addq	$1, %rbx
	cmpq	%r13, %rbx
	je	.LB106
.LB70:
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	positionOf
	cmpq	$-1, %rax
	jne	.LB73
	movq	32(%rbp), %rax
	movq	(%rax,%rbx,8), %r12
	testq	%r12, %r12
	je	.LB73
	testb	$1, %r12b
	je	.LB100
	cmpq	$1, %r12
	jne	.LB73
.LB100:
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
	movq	%r15, %rdx
	subq	%rax, %rdx
	leaq	-1(%rdx), %rcx
	cmpq	$15, %rcx
	ja	.LB107
	cmpq	$16, %rdx
	jne	.LB73
	cmpq	%r14, %rax
	je	.LB73
	movq	8(%rsp), %rax
	cmpq	$-1, %rax
	cmove	%rbx, %rax
	movq	%rax, 8(%rsp)
	jmp	.LB73
.LB106:
	movq	8(%rsp), %rax
	cmpq	$-1, %rax
	je	.LB71
	cmpq	%r14, %rax
	je	.LB71
	movq	%r15, %rax
	subq	%r14, %rax
	cmpq	$15, %rax
	jbe	.LB108
.LB77:
	movq	%r14, %rsi
	movq	%rbp, %rdi
	call	positionOf
	movq	%rax, %rsi
	cmpq	$-1, %rax
	je	.LB78
	cmpq	%r14, %rax
	jb	.LB92
	leaq	0(%rbp,%rax,8), %rcx
	movq	64(%rcx), %rax
	cmpq	%rax, 64(%rbp,%r14,8)
	jne	.LB109
	leaq	1032(%r14), %rax
	movq	0(%rbp,%rax,8), %rdx
	movq	8256(%rcx), %rsi
	movq	%rsi, 0(%rbp,%rax,8)
	movq	%rdx, 8256(%rcx)
	jmp	.LB68
.LB108:
	movq	8(%rsp), %rsi
	movq	%rbp, %rdi
	call	generate
	testq	%rax, %rax
	jne	.LB65
	subq	$1, %r14
	jmp	.LB68
.LB109:
	movq	%r15, %rdx
	subq	%rsi, %rdx
	cmpq	$1, %rdx
	je	.LB80
	leaq	-1(%r15), %rdx
	jmp	.LB83
	.p2align 4
.LB81:
	subq	$1, %rdx
	cmpq	%rdx, %rsi
	je	.LB82
.LB83:
	cmpq	64(%rbp,%rdx,8), %rax
	jne	.LB81
	cmpq	%rdx, 8256(%rbp,%rdx,8)
	je	.LB81
	movq	%rdx, %rsi
.LB82:
	cmpq	64(%rbp,%rsi,8), %rax
	jne	.LB94
.LB80:
	leaq	1032(%rsi), %rax
	movq	0(%rbp,%rax,8), %rdx
	movq	8256(%rcx), %rdi
	movq	%rdi, 0(%rbp,%rax,8)
	movq	%rdx, 8256(%rcx)
	cmpq	%rsi, %r14
	je	.LB95
	leaq	-1(%r15), %rax
	cmpq	%rsi, %rax
	je	.LB84
	subq	%rsi, %r15
	leaq	-1(%r15), %rax
	cmpq	$16, %rax
	ja	.LB110
	movq	%rbp, %rdi
	call	swapWith
	testq	%rax, %rax
	jne	.LB65
.LB84:
	movq	0(%rbp), %rax
	cmpq	%rax, %r14
	jnb	.LB97
	cmpq	%r14, 8256(%rbp,%r14,8)
	je	.LB98
.LB86:
	leaq	-1(%rax), %rdx
	cmpq	%r14, %rdx
	je	.LB68
	subq	%r14, %rax
	leaq	-1(%rax), %rdx
	cmpq	$16, %rdx
	ja	.LB111
	movq	%r14, %rsi
	movq	%rbp, %rdi
	call	swapWith
	testq	%rax, %rax
	jne	.LB65
.LB68:
	addq	$1, %r14
	movq	24(%rbp), %r13
	cmpq	%r13, %r14
	jnb	.LB66
.LB88:
	movq	0(%rbp), %r15
	cmpq	%r15, %r14
	jnb	.LB67
	cmpq	%r14, 8256(%rbp,%r14,8)
	je	.LB68
.LB67:
	cmpq	$0, 8(%rbp)
	je	.LB69
	movq	%r14, %rbx
	movq	$-1, 8(%rsp)
	cmpq	%r13, %r14
	jb	.LB70
.LB71:
	cmpq	%r15, %r14
	setb	%dl
	cmpq	%r13, %r15
	setb	%al
	testb	%al, %dl
	je	.LB77
	cmpq	$-1, 8(%rsp)
	jne	.LB77
	movq	%r15, %rsi
	movq	%rbp, %rdi
	call	positionOf
	cmpq	$-1, %rax
	jne	.LB77
	movq	%r15, %rax
	subq	%r14, %rax
	cmpq	$15, %rax
	ja	.LB77
	movq	%r15, %rsi
	movq	%rbp, %rdi
	call	generate
	testq	%rax, %rax
	jne	.LB65
	subq	$1, %r14
	jmp	.LB68
.LB110:
	movq	56(%rbp), %rax
	movq	%rsi, (%rax)
	movq	56(%rbp), %rax
	subq	$17, %r15
	movq	%r15, 8(%rax)
	movq	$-1, %rax
	jmp	.LB65
.LB78:
	movq	%r14, %rsi
	movq	%rbp, %rdi
	call	generate
	testq	%rax, %rax
	jne	.LB65
	movq	0(%rbp), %rax
	cmpq	%rax, %r14
	jnb	.LB96
	cmpq	%r14, 8256(%rbp,%r14,8)
	jne	.LB86
	jmp	.LB68
.LB111:
	movq	56(%rbp), %rdx
	movq	%r14, (%rdx)
	movq	56(%rbp), %rdx
	subq	$17, %rax
	movq	%rax, 8(%rdx)
	movq	$-1, %rax
	jmp	.LB65
.LB95:
	movq	%rsi, %r14
	jmp	.LB68
.LB66:
	cmpq	%r13, 0(%rbp)
	jne	.LB99
	movl	$0, %eax
	jmp	.LB65
.LB90:
	movq	$-2, %rax
	jmp	.LB65
.LB92:
	movq	$-2, %rax
	jmp	.LB65
.LB94:
	movq	$-2, %rax
	jmp	.LB65
.LB96:
	movq	$-2, %rax
	jmp	.LB65
.LB97:
	movq	$-2, %rax
	jmp	.LB65
.LB98:
	movq	$-2, %rax
	jmp	.LB65
.LB99:
	movq	$-2, %rax
	jmp	.LB65
	.size	buildBottomUp, .-buildBottomUp
