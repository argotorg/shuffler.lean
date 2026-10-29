	.file	"build_bottom_up.c"
	.text
	.type	isSpilled, @function
isSpilled:
	movq	%rsi, %rdx
	shrq	$32, %rdx
	movl	$0, %eax
	testb	%dl, %dl
	jne	.LB1
	movq	%rsi, %rdx
	shrq	$40, %rdx
	testb	%dl, %dl
	je	.LB1
	movl	%esi, %esi
	movq	40(%rdi), %rax
	cmpb	$0, (%rax,%rsi)
	setne	%al
	movzbl	%al, %eax
.LB1:
	ret
	.size	isSpilled, .-isSpilled
	.type	shallowestCopyPosition, @function
shallowestCopyPosition:
	movq	(%rdi), %rax
	.p2align 5
.LB6:
	testq	%rax, %rax
	je	.LB9
	subq	$1, %rax
	movq	64(%rdi), %rdx
	movq	%rsi, %rcx
	xorq	(%rdx,%rax,8), %rcx
	movq	%rcx, %rdx
	salq	$16, %rdx
	jne	.LB6
	ret
.LB9:
	movq	$-1, %rax
.LB7:
	ret
	.size	shallowestCopyPosition, .-shallowestCopyPosition
	.type	swapWith, @function
swapWith:
	movq	(%rdi), %r10
	cmpq	%r10, %rsi
	jnb	.LB12
	movq	%rdi, %rax
	movq	%rsi, %rdx
	leaq	0(,%rsi,8), %rdi
	leaq	(%rax,%rdi), %r11
	cmpq	%rsi, 72(%r11)
	je	.LB13
	movq	%r10, %rsi
	subq	%rdx, %rsi
	leaq	-2(%rsi), %rcx
	cmpq	$15, %rcx
	ja	.LB14
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	leaq	-1(%r10), %r8
	movq	16(%rax), %rcx
	leaq	(%rcx,%rcx,2), %r9
	movq	48(%rax), %rcx
	leaq	(%rcx,%r9,4), %rcx
	movb	$0, (%rcx)
	subq	$1, %rsi
	movb	%sil, 1(%rcx)
	movl	$0, 4(%rcx)
	movb	$1, 8(%rcx)
	movb	$5, 9(%rcx)
	addq	$1, 16(%rax)
	movq	64(%rax), %r9
	leaq	(%r9,%rdi), %rcx
	movl	(%rcx), %r12d
	movzbl	4(%rcx), %ebp
	movzbl	5(%rcx), %ebx
	leaq	0(,%r8,8), %rsi
	movq	(%r9,%r8,8), %r9
	movq	%r9, (%rcx)
	movq	%rsi, %rcx
	addq	64(%rax), %rcx
	movl	%r12d, (%rcx)
	movb	%bpl, 4(%rcx)
	movb	%bl, 5(%rcx)
	movq	72(%rax,%rdi), %rcx
	movq	64(%rax,%r10,8), %rdi
	movq	%rdi, 72(%r11)
	movq	%rcx, 72(%rax,%rsi)
	movq	72(%r11), %rsi
	movq	%rdx, 8264(%rax,%rsi,8)
	movq	%r8, 8264(%rax,%rcx,8)
	movl	$0, %eax
	popq	%rbx
	popq	%rbp
	popq	%r12
	ret
.LB12:
	movq	$-2, %rax
	ret
.LB13:
	movq	$-2, %rax
	ret
.LB14:
	movq	$-2, %rax
	ret
	.size	swapWith, .-swapWith
	.type	push, @function
push:
	movq	%rdi, %rax
	movq	%rsi, %rcx
	cmpq	$-1, 8264(%rdi,%rdx,8)
	jne	.LB22
	movq	(%rdi), %rsi
	movq	%rdx, 72(%rdi,%rsi,8)
	movq	%rsi, 8264(%rdi,%rdx,8)
	movq	%rcx, %rsi
	shrq	$32, %rsi
	movq	%rcx, %rdx
	shrq	$40, %rdx
	cmpb	$1, %dl
	movl	$3, %edx
	sbbb	$-1, %dl
	testb	%sil, %sil
	movl	$3, %esi
	cmovne	%esi, %edx
	movq	16(%rdi), %rsi
	leaq	(%rsi,%rsi,2), %rdi
	movq	48(%rax), %rsi
	leaq	(%rsi,%rdi,4), %rsi
	movb	%dl, (%rsi)
	movb	$0, 1(%rsi)
	movq	%rcx, 4(%rsi)
	addq	$1, 16(%rax)
	movq	(%rax), %rsi
	movq	64(%rax), %rdx
	movq	%rcx, (%rdx,%rsi,8)
	addq	$1, (%rax)
	movl	$0, %eax
	ret
.LB22:
	movq	$-2, %rax
	ret
	.size	push, .-push
	.type	dup, @function
dup:
	movq	%rdi, %rax
	cmpq	$-1, 8264(%rdi,%rdx,8)
	jne	.LB27
	movq	(%rdi), %rcx
	movq	%rdx, 72(%rdi,%rcx,8)
	movq	%rcx, 8264(%rdi,%rdx,8)
	movq	16(%rdi), %rdx
	leaq	(%rdx,%rdx,2), %rdi
	movq	48(%rax), %rdx
	leaq	(%rdx,%rdi,4), %rdx
	movb	$1, (%rdx)
	subq	%rsi, %rcx
	movb	%cl, 1(%rdx)
	movl	$0, 4(%rdx)
	movb	$1, 8(%rdx)
	movb	$5, 9(%rdx)
	addq	$1, 16(%rax)
	movq	64(%rax), %rdx
	movq	(%rax), %rcx
	movq	(%rdx,%rsi,8), %rsi
	movq	%rsi, (%rdx,%rcx,8)
	addq	$1, (%rax)
	movl	$0, %eax
	ret
.LB27:
	movq	$-2, %rax
	ret
	.size	dup, .-dup
	.type	produce, @function
produce:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$8, %rsp
	movq	%rdi, %rbx
	movq	%rsi, %rbp
	leaq	0(,%rsi,8), %r14
	movq	%r14, %rax
	addq	32(%rdi), %rax
	movq	(%rax), %r13
	movzbl	4(%rax), %r15d
	movzbl	5(%rax), %eax
	movb	%al, 7(%rsp)
	movq	%r13, %rsi
	call	shallowestCopyPosition
	cmpb	$1, %r15b
	je	.LB39
	movq	%rax, %r12
	cmpq	$-1, %rax
	je	.LB31
	notq	%rax
	addq	(%rbx), %rax
	cmpq	$15, %rax
	jbe	.LB40
.LB31:
	cmpb	$0, 7(%rsp)
	je	.LB32
	cmpb	$2, %r15b
	jne	.LB41
.LB32:
	movq	%rbp, %rdx
	movq	%r13, %rsi
	movq	%rbx, %rdi
	call	push
.LB30:
	testq	%rax, %rax
	jne	.LB28
	movq	(%rbx), %rcx
	leaq	-1(%rcx), %rdx
	cmpq	%rdx, 8264(%rbx,%r14)
	jne	.LB37
	movq	8(%rbx), %rdx
	testq	%rdx, %rdx
	je	.LB28
	subq	$1, %rdx
	movq	%rdx, 8(%rbx)
.LB28:
	addq	$8, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB39:
	movq	%rbp, %rdx
	movq	%r13, %rsi
	movq	%rbx, %rdi
	call	push
	jmp	.LB30
.LB40:
	movq	%rbp, %rdx
	movq	%r12, %rsi
	movq	%rbx, %rdi
	call	dup
	jmp	.LB30
.LB41:
	movq	%r13, %rsi
	movq	%rbx, %rdi
	call	isSpilled
	testl	%eax, %eax
	jne	.LB32
	cmpq	$-1, %r12
	je	.LB35
	movq	$-16, %rdx
	subq	%r12, %rdx
	movq	$-2, %rax
	addq	(%rbx), %rdx
	je	.LB28
	movq	56(%rbx), %rax
	movq	%r12, (%rax)
	movq	56(%rbx), %rax
	movq	%rdx, 8(%rax)
	movq	$-1, %rax
	jmp	.LB28
.LB35:
	movq	$-2, %rax
	jmp	.LB28
.LB37:
	movq	$-2, %rax
	jmp	.LB28
	.size	produce, .-produce
	.type	generate, @function
generate:
	cmpq	24(%rdi), %rsi
	jnb	.LB45
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movq	%rsi, %rbx
	call	produce
	testq	%rax, %rax
	jne	.LB42
	movq	0(%rbp), %rdx
	leaq	1(%rbx), %rcx
	cmpq	%rdx, %rcx
	jnb	.LB42
	leaq	0(%rbp,%rbx,8), %rdi
	movq	72(%rdi), %rsi
	cmpq	%rbx, %rsi
	je	.LB42
	movq	64(%rbp), %r9
	leaq	-1(%rdx), %r8
	leaq	0(,%r8,8), %r10
	movq	(%r9,%rbx,8), %rcx
	xorq	(%r9,%r8,8), %rcx
	salq	$16, %rcx
	jne	.LB44
	movq	72(%rbp,%r8,8), %rdx
	movq	%rdx, 72(%rdi)
	movq	%rsi, 72(%rbp,%r10)
	movq	72(%rdi), %rdx
	movq	%rbx, 8264(%rbp,%rdx,8)
	movq	%r8, 8264(%rbp,%rsi,8)
.LB42:
	popq	%rbx
	popq	%rbp
	ret
.LB44:
	subq	%rbx, %rdx
	subq	$1, %rdx
	cmpq	$16, %rdx
	ja	.LB42
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	swapWith
	jmp	.LB42
.LB45:
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
	je	.LB51
	movl	$0, %eax
	.p2align 5
.LB52:
	movq	72(%rbx,%rax,8), %rdx
	movw	%dx, 2064(%rsp,%rax,2)
	addq	$1, %rax
	cmpq	%rdi, %rax
	jne	.LB52
.LB51:
	leaq	12(%rsp), %rcx
	leaq	16(%rsp), %rdx
	leaq	2064(%rsp), %rsi
	call	permute
	testq	%rax, %rax
	js	.LB60
	jle	.LB56
	movq	(%rbx), %rsi
	leaq	-1(%rsi), %r10
	leaq	0(,%r10,8), %rsi
	leaq	16(%rsp), %rdx
	leaq	(%rax,%rdx), %r9
.LB55:
	movq	64(%rbx), %rcx
	movzbl	(%rdx), %edi
	movq	%r10, %rax
	subq	%rdi, %rax
	leaq	(%rcx,%rax,8), %rax
	movl	(%rax), %r11d
	movzbl	4(%rax), %r8d
	movzbl	5(%rax), %edi
	movq	(%rcx,%rsi), %rcx
	movq	%rcx, (%rax)
	movq	%rsi, %rax
	addq	64(%rbx), %rax
	movl	%r11d, (%rax)
	movb	%r8b, 4(%rax)
	movb	%dil, 5(%rax)
	movzbl	(%rdx), %ecx
	movq	16(%rbx), %rax
	leaq	(%rax,%rax,2), %rdi
	movq	48(%rbx), %rax
	leaq	(%rax,%rdi,4), %rax
	movb	$0, (%rax)
	movb	%cl, 1(%rax)
	movl	$0, 4(%rax)
	movb	$1, 8(%rax)
	movb	$5, 9(%rax)
	addq	$1, 16(%rbx)
	addq	$1, %rdx
	cmpq	%r9, %rdx
	jne	.LB55
	movl	$0, %eax
.LB50:
	addq	$4112, %rsp
	popq	%rbx
	ret
.LB60:
	movq	56(%rbx), %rax
	movzwl	12(%rsp), %edx
	movq	%rdx, (%rax)
	movq	56(%rbx), %rax
	movzwl	14(%rsp), %edx
	movq	%rdx, 8(%rax)
	movq	$-1, %rax
	jmp	.LB50
.LB56:
	movl	$0, %eax
	jmp	.LB50
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
	.globl	build_bottom_up
	.type	build_bottom_up, @function
build_bottom_up:
	subq	$16472, %rsp
	movq	%rcx, 32(%rsp)
	movq	%rsi, 24(%rsp)
	movq	%r9, 40(%rsp)
	movq	%rdx, 64(%rsp)
	movq	%rdi, (%rsp)
	testq	%rsi, %rsi
	je	.LB111
	movq	%rsp, %rax
	leaq	(%rax,%rsi,8), %rdx
	.p2align 5
.LB112:
	movq	$-1, 8264(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB112
.LB111:
	testq	%rdi, %rdi
	je	.LB113
	movl	$0, %eax
	.p2align 5
.LB114:
	movq	(%r8,%rax,8), %rdx
	movq	%rdx, 72(%rsp,%rax,8)
	movq	%rax, 8264(%rsp,%rdx,8)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB114
.LB113:
	subq	%rdi, %rsi
	movq	%rsi, 8(%rsp)
	movq	$0, 16(%rsp)
	movq	16480(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	16488(%rsp), %rax
	movq	%rax, 56(%rsp)
	movq	%rsp, %rdi
	call	buildBottomUp
	testq	%rax, %rax
	cmove	16(%rsp), %rax
	addq	$16472, %rsp
	ret
	.size	build_bottom_up, .-build_bottom_up
	.section	.note.GNU-stack,"",@progbits
