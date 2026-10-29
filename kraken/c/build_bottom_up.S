	.file	"build_bottom_up.c"
	.text
	.type	isSpilled, @function
isSpilled:
	movl	$0, %eax
	cmpq	$1, %rsi
	jbe	.LB1
	testb	$1, %sil
	jne	.LB1
	subq	$2, %rsi
	shrq	%rsi
	movq	40(%rdi), %rax
	cmpb	$0, (%rax,%rsi)
	setne	%al
	movzbl	%al, %eax
.LB1:
	ret
	.size	isSpilled, .-isSpilled
	.type	positionOf, @function
positionOf:
	movq	(%rdi), %rdx
	testq	%rdx, %rdx
	je	.LB8
	movl	$0, %eax
	.p2align 5
.LB7:
	cmpq	%rsi, 8256(%rdi,%rax,8)
	je	.LB5
	addq	$1, %rax
	cmpq	%rdx, %rax
	jne	.LB7
	movq	$-1, %rax
	ret
.LB8:
	movq	$-1, %rax
.LB5:
	ret
	.size	positionOf, .-positionOf
	.type	shallowestCopyPosition, @function
shallowestCopyPosition:
	movq	(%rdi), %rax
	.p2align 4
.LB11:
	testq	%rax, %rax
	je	.LB14
	subq	$1, %rax
	cmpq	%rsi, 64(%rdi,%rax,8)
	jne	.LB11
	ret
.LB14:
	movq	$-1, %rax
.LB10:
	ret
	.size	shallowestCopyPosition, .-shallowestCopyPosition
	.type	swapWith, @function
swapWith:
	movq	(%rdi), %r8
	cmpq	%r8, %rsi
	jnb	.LB17
	leaq	(%rdi,%rsi,8), %rax
	cmpq	8256(%rax), %rsi
	je	.LB18
	movq	%r8, %rcx
	subq	%rsi, %rcx
	leaq	-2(%rcx), %rdx
	cmpq	$15, %rdx
	ja	.LB19
	movq	16(%rdi), %rdx
	salq	$4, %rdx
	addq	48(%rdi), %rdx
	movq	$0, (%rdx)
	movq	16(%rdi), %rdx
	salq	$4, %rdx
	addq	48(%rdi), %rdx
	subq	$1, %rcx
	movq	%rcx, 8(%rdx)
	addq	$1, 16(%rdi)
	movq	64(%rax), %rcx
	leaq	(%rdi,%r8,8), %rdx
	movq	56(%rdx), %rsi
	movq	%rsi, 64(%rax)
	movq	%rcx, 56(%rdx)
	movq	8256(%rax), %rcx
	movq	8248(%rdx), %rsi
	movq	%rsi, 8256(%rax)
	movq	%rcx, 8248(%rdx)
	movl	$0, %eax
	ret
.LB17:
	movq	$-2, %rax
	ret
.LB18:
	movq	$-2, %rax
	ret
.LB19:
	movq	$-2, %rax
	ret
	.size	swapWith, .-swapWith
	.type	push, @function
push:
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbx
	movq	%rsi, %rbp
	movq	%rdx, %r12
	movq	%rdx, %rsi
	call	positionOf
	cmpq	$-1, %rax
	jne	.LB22
	movq	(%rbx), %rax
	movq	%r12, 8256(%rbx,%rax,8)
	movq	16(%rbx), %rax
	salq	$4, %rax
	addq	48(%rbx), %rax
	movq	$2, (%rax)
	movq	16(%rbx), %rax
	salq	$4, %rax
	addq	48(%rbx), %rax
	movq	%rbp, 8(%rax)
	addq	$1, 16(%rbx)
	movq	(%rbx), %rax
	movq	%rbp, 64(%rbx,%rax,8)
	addq	$1, %rax
	movq	%rax, (%rbx)
	movl	$0, %eax
.LB20:
	popq	%rbx
	popq	%rbp
	popq	%r12
	ret
.LB22:
	movq	$-2, %rax
	jmp	.LB20
	.size	push, .-push
	.type	dup, @function
dup:
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbx
	movq	%rsi, %rbp
	movq	%rdx, %r12
	movq	%rdx, %rsi
	call	positionOf
	cmpq	$-1, %rax
	jne	.LB26
	movq	(%rbx), %rdx
	movq	%r12, 8256(%rbx,%rdx,8)
	movq	16(%rbx), %rax
	salq	$4, %rax
	addq	48(%rbx), %rax
	movq	$1, (%rax)
	movq	16(%rbx), %rax
	salq	$4, %rax
	addq	48(%rbx), %rax
	subq	%rbp, %rdx
	movq	%rdx, 8(%rax)
	addq	$1, 16(%rbx)
	movq	(%rbx), %rax
	movq	64(%rbx,%rbp,8), %rdx
	movq	%rdx, 64(%rbx,%rax,8)
	addq	$1, %rax
	movq	%rax, (%rbx)
	movl	$0, %eax
.LB24:
	popq	%rbx
	popq	%rbp
	popq	%r12
	ret
.LB26:
	movq	$-2, %rax
	jmp	.LB24
	.size	dup, .-dup
	.type	produce, @function
produce:
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbx
	movq	%rsi, %rbp
	movq	32(%rdi), %rax
	movq	(%rax,%rsi,8), %r12
	testq	%r12, %r12
	je	.LB41
	movq	%r12, %rsi
	call	shallowestCopyPosition
	movq	%rax, %r13
	cmpq	$-1, %rax
	je	.LB31
	notq	%rax
	addq	(%rbx), %rax
	cmpq	$15, %rax
	jbe	.LB42
.LB31:
	testb	$1, %r12b
	je	.LB39
	cmpq	$1, %r12
	jne	.LB32
.LB39:
	movq	%r12, %rsi
	movq	%rbx, %rdi
	call	isSpilled
	testl	%eax, %eax
	je	.LB34
.LB32:
	movq	%rbp, %rdx
	movq	%r12, %rsi
	movq	%rbx, %rdi
	call	push
	movq	%rax, %r12
.LB30:
	testq	%r12, %r12
	je	.LB43
.LB28:
	movq	%r12, %rax
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	ret
.LB41:
	movq	%rsi, %rdx
	movl	$0, %esi
	call	push
	movq	%rax, %r12
	jmp	.LB30
.LB42:
	movq	%rbp, %rdx
	movq	%r13, %rsi
	movq	%rbx, %rdi
	call	dup
	movq	%rax, %r12
	jmp	.LB30
.LB34:
	cmpq	$-1, %r13
	je	.LB36
	movq	(%rbx), %rax
	subq	$16, %rax
	movq	$-2, %r12
	subq	%r13, %rax
	je	.LB28
	movq	56(%rbx), %rdx
	movq	%r13, (%rdx)
	movq	56(%rbx), %rdx
	movq	%rax, 8(%rdx)
	movq	$-1, %r12
	jmp	.LB28
.LB43:
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	call	positionOf
	movq	%rax, %rdx
	movq	(%rbx), %rax
	subq	$1, %rax
	cmpq	%rax, %rdx
	jne	.LB38
	movq	8(%rbx), %rax
	testq	%rax, %rax
	je	.LB28
	subq	$1, %rax
	movq	%rax, 8(%rbx)
	jmp	.LB28
.LB36:
	movq	$-2, %r12
	jmp	.LB28
.LB38:
	movq	$-2, %r12
	jmp	.LB28
	.size	produce, .-produce
	.type	generate, @function
generate:
	cmpq	24(%rdi), %rsi
	jnb	.LB47
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movq	%rsi, %rbx
	call	produce
	testq	%rax, %rax
	jne	.LB44
	movq	0(%rbp), %rdx
	leaq	1(%rbx), %rcx
	cmpq	%rdx, %rcx
	jnb	.LB44
	leaq	0(%rbp,%rbx,8), %rcx
	movq	8256(%rcx), %rsi
	cmpq	%rsi, %rbx
	je	.LB44
	leaq	0(%rbp,%rdx,8), %rdi
	movq	56(%rdi), %r8
	cmpq	%r8, 64(%rcx)
	je	.LB52
	subq	%rbx, %rdx
	subq	$1, %rdx
	cmpq	$16, %rdx
	jbe	.LB53
.LB44:
	popq	%rbx
	popq	%rbp
	ret
.LB52:
	movq	8248(%rdi), %rdx
	movq	%rdx, 8256(%rcx)
	movq	%rsi, 8248(%rdi)
	jmp	.LB44
.LB53:
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	swapWith
	jmp	.LB44
.LB47:
	movq	$-2, %rax
	ret
	.size	generate, .-generate
	.type	permuteDestinations, @function
permuteDestinations:
	pushq	%rbx
	subq	$4112, %rsp
	movq	%rdi, %rbx
	movq	(%rdi), %rdi
	testq	%rdi, %rdi
	je	.LB55
	movl	$0, %eax
	.p2align 5
.LB56:
	movq	8256(%rbx,%rax,8), %rdx
	movw	%dx, 2064(%rsp,%rax,2)
	addq	$1, %rax
	cmpq	%rdi, %rax
	jne	.LB56
.LB55:
	leaq	12(%rsp), %rcx
	leaq	16(%rsp), %rdx
	leaq	2064(%rsp), %rsi
	call	permute
	testq	%rax, %rax
	js	.LB57
	leaq	16(%rsp), %rdx
	leaq	(%rax,%rdx), %rsi
	movl	$0, %eax
	jle	.LB54
	.p2align 6
.LB60:
	movzbl	(%rdx), %ecx
	movq	16(%rbx), %rax
	salq	$4, %rax
	addq	48(%rbx), %rax
	movq	$0, (%rax)
	movq	16(%rbx), %rax
	salq	$4, %rax
	addq	48(%rbx), %rax
	movq	%rcx, 8(%rax)
	addq	$1, 16(%rbx)
	addq	$1, %rdx
	cmpq	%rsi, %rdx
	jne	.LB60
	movl	$0, %eax
.LB54:
	addq	$4112, %rsp
	popq	%rbx
	ret
.LB57:
	movq	56(%rbx), %rax
	movzwl	12(%rsp), %edx
	movq	%rdx, (%rax)
	movq	56(%rbx), %rax
	movzwl	14(%rsp), %edx
	movq	%rdx, 8(%rax)
	movq	$-1, %rax
	jmp	.LB54
	.size	permuteDestinations, .-permuteDestinations
	.type	buildBottomUp, @function
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
	.globl	build_bottom_up
	.type	build_bottom_up, @function
build_bottom_up:
	subq	$16456, %rsp
	movq	%rcx, 32(%rsp)
	movq	%rsi, 24(%rsp)
	movq	%r9, 40(%rsp)
	movq	%rdi, (%rsp)
	testq	%rdi, %rdi
	je	.LB113
	movl	$0, %eax
	.p2align 5
.LB114:
	movq	(%rdx,%rax,8), %rcx
	movq	%rcx, 64(%rsp,%rax,8)
	movq	(%r8,%rax,8), %rcx
	movq	%rcx, 8256(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB114
.LB113:
	subq	%rdi, %rsi
	movq	%rsi, 8(%rsp)
	movq	$0, 16(%rsp)
	movq	16464(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	16472(%rsp), %rax
	movq	%rax, 56(%rsp)
	movq	%rsp, %rdi
	call	buildBottomUp
	testq	%rax, %rax
	cmove	16(%rsp), %rax
	addq	$16456, %rsp
	ret
	.size	build_bottom_up, .-build_bottom_up
	.section	.note.GNU-stack,"",@progbits
