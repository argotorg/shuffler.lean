	.file	"build_bottom_up.c"
	.text
	.type	is_spilled, @function
is_spilled:
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
	.size	is_spilled, .-is_spilled
	.type	position_of, @function
position_of:
	movq	(%rdi), %rdx
	testq	%rdx, %rdx
	je	.LB9
	movl	$0, %eax
	.p2align 5
.LB8:
	cmpq	%rsi, 2112(%rdi,%rax,8)
	je	.LB5
	addq	$1, %rax
	cmpq	%rdx, %rax
	jne	.LB8
	movq	$-1, %rax
	ret
.LB9:
	movq	$-1, %rax
.LB5:
	ret
	.size	position_of, .-position_of
	.type	shallowest_copy, @function
shallowest_copy:
	movq	(%rdi), %rax
	.p2align 4
.LB12:
	testq	%rax, %rax
	je	.LB16
	subq	$1, %rax
	cmpq	%rsi, 64(%rdi,%rax,8)
	jne	.LB12
	ret
.LB16:
	movq	$-1, %rax
.LB11:
	ret
	.size	shallowest_copy, .-shallowest_copy
	.type	add, @function
add:
	pushq	%r15
	pushq	%r14
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbx
	movq	%rsi, %r12
	movq	%rdx, %rbp
	movq	%rcx, %r14
	movq	%r8, %r15
	movq	%rdx, %rsi
	call	position_of
	testq	%rax, %rax
	jns	.LB19
	movq	16(%rbx), %rax
	salq	$4, %rax
	addq	48(%rbx), %rax
	movq	%r14, (%rax)
	movq	16(%rbx), %rax
	salq	$4, %rax
	addq	48(%rbx), %rax
	movq	%r15, 8(%rax)
	addq	$1, 16(%rbx)
	movq	(%rbx), %rax
	movq	%r12, 64(%rbx,%rax,8)
	movq	%rbp, 2112(%rbx,%rax,8)
	addq	$1, %rax
	movq	%rax, (%rbx)
	movl	$0, %eax
.LB17:
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r14
	popq	%r15
	ret
.LB19:
	movq	$-2, %rax
	jmp	.LB17
	.size	add, .-add
	.type	swap_with, @function
swap_with:
	movq	(%rdi), %r8
	cmpq	%r8, %rsi
	jnb	.LB23
	leaq	(%rdi,%rsi,8), %rax
	cmpq	%rsi, 2112(%rax)
	je	.LB24
	leaq	-1(%r8), %rcx
	subq	%rsi, %rcx
	leaq	-1(%rcx), %rdx
	cmpq	$15, %rdx
	ja	.LB25
	movq	16(%rdi), %rdx
	salq	$4, %rdx
	addq	48(%rdi), %rdx
	movq	$0, (%rdx)
	movq	16(%rdi), %rdx
	salq	$4, %rdx
	addq	48(%rdi), %rdx
	movq	%rcx, 8(%rdx)
	addq	$1, 16(%rdi)
	movq	64(%rax), %rcx
	leaq	(%rdi,%r8,8), %rdx
	movq	56(%rdx), %rsi
	movq	%rsi, 64(%rax)
	movq	%rcx, 56(%rdx)
	movq	2112(%rax), %rcx
	movq	2104(%rdx), %rsi
	movq	%rsi, 2112(%rax)
	movq	%rcx, 2104(%rdx)
	movl	$0, %eax
	ret
.LB23:
	movq	$-2, %rax
	ret
.LB24:
	movq	$-2, %rax
	ret
.LB25:
	movq	$-2, %rax
	ret
	.size	swap_with, .-swap_with
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
	je	.LB39
	movq	%r12, %rsi
	call	shallowest_copy
	movq	%rax, %r13
	testq	%rax, %rax
	js	.LB29
	movq	(%rbx), %r8
	subq	%rax, %r8
	leaq	-1(%r8), %rax
	cmpq	$15, %rax
	jbe	.LB40
.LB29:
	testb	$1, %r12b
	je	.LB37
	cmpq	$1, %r12
	jne	.LB30
.LB37:
	movq	%r12, %rsi
	movq	%rbx, %rdi
	call	is_spilled
	testl	%eax, %eax
	je	.LB32
.LB30:
	movq	%r12, %r8
	movl	$2, %ecx
	movq	%rbp, %rdx
	movq	%r12, %rsi
	movq	%rbx, %rdi
	call	add
.LB28:
	testq	%rax, %rax
	js	.LB26
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	call	position_of
	movq	%rax, %rdx
	movq	(%rbx), %rax
	subq	$1, %rax
	cmpq	%rax, %rdx
	jne	.LB35
	movq	8(%rbx), %rdx
	movl	$0, %eax
	testq	%rdx, %rdx
	je	.LB26
	subq	$1, %rdx
	movq	%rdx, 8(%rbx)
.LB26:
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	ret
.LB39:
	movl	$0, %r8d
	movl	$2, %ecx
	movq	%rsi, %rdx
	movl	$0, %esi
	call	add
	jmp	.LB28
.LB40:
	movl	$1, %ecx
	movq	%rbp, %rdx
	movq	%r12, %rsi
	movq	%rbx, %rdi
	call	add
	jmp	.LB28
.LB32:
	testq	%r13, %r13
	js	.LB34
	movq	(%rbx), %rax
	subq	$16, %rax
	subq	%r13, %rax
	movq	56(%rbx), %rdx
	movq	%r13, (%rdx)
	movq	56(%rbx), %rdx
	movq	%rax, 8(%rdx)
	movq	$-1, %rax
	jmp	.LB26
.LB34:
	movq	$-2, %rax
	jmp	.LB26
.LB35:
	movq	$-2, %rax
	jmp	.LB26
	.size	produce, .-produce
	.type	generate, @function
generate:
	cmpq	24(%rdi), %rsi
	jnb	.LB44
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movq	%rsi, %rbx
	call	produce
	testq	%rax, %rax
	js	.LB41
	movq	0(%rbp), %rdx
	leaq	1(%rbx), %rcx
	movl	$0, %eax
	cmpq	%rdx, %rcx
	jnb	.LB41
	leaq	0(%rbp,%rbx,8), %rcx
	movq	2112(%rcx), %rsi
	cmpq	%rbx, %rsi
	je	.LB41
	leaq	0(%rbp,%rdx,8), %rax
	movq	56(%rax), %rdi
	cmpq	%rdi, 64(%rcx)
	je	.LB52
	subq	$1, %rdx
	subq	%rbx, %rdx
	movl	$0, %eax
	cmpq	$16, %rdx
	jbe	.LB53
.LB41:
	popq	%rbx
	popq	%rbp
	ret
.LB52:
	movq	2104(%rax), %rdx
	movq	%rdx, 2112(%rcx)
	movq	%rsi, 2104(%rax)
	movl	$0, %eax
	jmp	.LB41
.LB53:
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	swap_with
	jmp	.LB41
.LB44:
	movq	$-2, %rax
	ret
	.size	generate, .-generate
	.type	finish, @function
finish:
	pushq	%rbx
	subq	$784, %rsp
	movq	%rdi, %rbx
	movq	(%rdi), %rdi
	testq	%rdi, %rdi
	je	.LB55
	movl	$0, %eax
	.p2align 5
.LB56:
	movq	2112(%rbx,%rax,8), %rdx
	movb	%dl, 528(%rsp,%rax)
	addq	$1, %rax
	cmpq	%rdi, %rax
	jne	.LB56
.LB55:
	leaq	14(%rsp), %rcx
	leaq	16(%rsp), %rdx
	leaq	528(%rsp), %rsi
	call	permute
	testq	%rax, %rax
	js	.LB57
	leaq	16(%rsp), %rdx
	leaq	(%rax,%rdx), %rsi
	jle	.LB59
	.p2align 6
.LB61:
	movq	16(%rbx), %rax
	salq	$4, %rax
	addq	48(%rbx), %rax
	movq	$0, (%rax)
	movq	16(%rbx), %rax
	salq	$4, %rax
	addq	48(%rbx), %rax
	movzbl	(%rdx), %ecx
	movq	%rcx, 8(%rax)
	addq	$1, 16(%rbx)
	addq	$1, %rdx
	cmpq	%rsi, %rdx
	jne	.LB61
.LB59:
	movq	16(%rbx), %rax
.LB54:
	addq	$784, %rsp
	popq	%rbx
	ret
.LB57:
	movzbl	15(%rsp), %edx
	movq	56(%rbx), %rax
	movzbl	14(%rsp), %ecx
	movq	%rcx, (%rax)
	movq	56(%rbx), %rax
	movq	%rdx, 8(%rax)
	movq	$-1, %rax
	jmp	.LB54
	.size	finish, .-finish
	.type	take_bound, @function
take_bound:
	movq	%rsi, %rcx
	movq	%rdx, %rsi
	cmpq	%rcx, %rdx
	jb	.LB73
	leaq	(%rdi,%rcx,8), %rax
	leaq	(%rdi,%rdx,8), %r8
	movq	64(%r8), %rdx
	cmpq	%rdx, 64(%rax)
	je	.LB68
	movq	(%rdi), %rax
	subq	$1, %rax
	cmpq	%rax, %rsi
	jb	.LB71
	jmp	.LB69
	.p2align 4
.LB70:
	subq	$1, %rax
	cmpq	%rax, %rsi
	jnb	.LB69
.LB71:
	cmpq	64(%rdi,%rax,8), %rdx
	jne	.LB70
	cmpq	%rax, 2112(%rdi,%rax,8)
	je	.LB70
	movq	%rax, %rsi
.LB69:
	leaq	264(%rsi), %rax
	movq	(%rdi,%rax,8), %rdx
	movq	2112(%r8), %r9
	movq	%r9, (%rdi,%rax,8)
	movq	%rdx, 2112(%r8)
	cmpq	%rcx, %rsi
	je	.LB75
	movq	(%rdi), %rdx
	leaq	-1(%rdx), %rcx
	movl	$1, %eax
	cmpq	%rsi, %rcx
	je	.LB66
	subq	%rsi, %rdx
	leaq	-1(%rdx), %rax
	cmpq	$16, %rax
	ja	.LB78
	call	swap_with
	testq	%rax, %rax
	movl	$1, %edx
	cmovns	%rdx, %rax
	ret
.LB78:
	movq	56(%rdi), %rax
	movq	%rsi, (%rax)
	movq	56(%rdi), %rax
	subq	$17, %rdx
	movq	%rdx, 8(%rax)
	movq	$-1, %rax
	ret
.LB73:
	movq	$-2, %rax
	ret
.LB75:
	movl	$0, %eax
	ret
.LB68:
	movq	2112(%rax), %rdx
	movq	2112(%r8), %rcx
	movq	%rcx, 2112(%rax)
	movq	%rdx, 2112(%r8)
	movl	$0, %eax
.LB66:
	ret
	.size	take_bound, .-take_bound
	.type	urgent, @function
urgent:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	movq	24(%rdi), %r13
	movq	%r13, %r14
	cmpq	%r13, %rsi
	jnb	.LB79
	movq	%rdi, %rbp
	movq	%rsi, %r15
	movq	%rsi, %rbx
	jmp	.LB84
.LB88:
	movq	56(%rbp), %rcx
	movq	%rax, (%rcx)
	movq	56(%rbp), %rax
	subq	$16, %rdx
	movq	%rdx, 8(%rax)
	movq	$-1, %r14
.LB79:
	movq	%r14, %rax
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB81:
	addq	$1, %rbx
	cmpq	%rbx, %r13
	je	.LB79
.LB84:
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	position_of
	testq	%rax, %rax
	jns	.LB81
	movq	32(%rbp), %rax
	movq	(%rax,%rbx,8), %r12
	testq	%r12, %r12
	je	.LB81
	testb	$1, %r12b
	je	.LB85
	cmpq	$1, %r12
	jne	.LB81
.LB85:
	movq	%r12, %rsi
	movq	%rbp, %rdi
	call	is_spilled
	testl	%eax, %eax
	jne	.LB81
	movq	%r12, %rsi
	movq	%rbp, %rdi
	call	shallowest_copy
	testq	%rax, %rax
	js	.LB81
	movq	0(%rbp), %rdx
	subq	%rax, %rdx
	leaq	-1(%rdx), %rcx
	cmpq	$15, %rcx
	ja	.LB88
	cmpq	%rax, %r15
	setne	%dl
	cmpq	%r13, %r14
	sete	%al
	testb	%al, %dl
	je	.LB81
	cmpq	$15, %rcx
	cmove	%rbx, %r14
	jmp	.LB81
	.size	urgent, .-urgent
	.type	step, @function
step:
	pushq	%r14
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movq	%rsi, %rbx
	cmpq	(%rdi), %rsi
	jnb	.LB90
	leaq	1(%rsi), %rax
	cmpq	%rsi, 2112(%rdi,%rsi,8)
	je	.LB89
.LB90:
	cmpq	$0, 8(%rbp)
	je	.LB99
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	urgent
	testq	%rax, %rax
	js	.LB89
	movq	24(%rbp), %rdx
	movq	%rax, %rcx
	cmpq	%rax, %rbx
	je	.LB92
	cmpq	%rax, %rdx
	je	.LB92
	leaq	16(%rbx), %rdx
	cmpq	%rdx, 0(%rbp)
	jb	.LB106
.LB93:
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	position_of
	testq	%rax, %rax
	js	.LB94
	movq	%rax, %rdx
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	take_bound
	testq	%rax, %rax
	js	.LB89
	leaq	1(%rbx), %rax
	je	.LB89
	movq	0(%rbp), %rdx
	cmpq	%rdx, %rbx
	jnb	.LB103
	cmpq	%rbx, 2112(%rbp,%rbx,8)
	je	.LB104
.LB96:
	leaq	-1(%rdx), %rax
	cmpq	%rbx, %rax
	je	.LB97
	subq	%rbx, %rdx
	leaq	-1(%rdx), %rax
	cmpq	$16, %rax
	ja	.LB107
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	swap_with
	testq	%rax, %rax
	js	.LB89
.LB97:
	leaq	1(%rbx), %rax
.LB89:
	popq	%rbx
	popq	%rbp
	popq	%r14
	ret
.LB106:
	movq	%rax, %rsi
	movq	%rbp, %rdi
	call	generate
	testq	%rax, %rax
	cmovns	%rbx, %rax
	jmp	.LB89
.LB92:
	movq	0(%rbp), %rax
	movq	%rax, %r14
	cmpq	%rax, %rbx
	setb	%sil
	cmpq	%rdx, %rax
	setb	%al
	testb	%al, %sil
	je	.LB93
	cmpq	%rcx, %rdx
	jne	.LB93
	movq	%r14, %rsi
	movq	%rbp, %rdi
	call	position_of
	testq	%rax, %rax
	jns	.LB93
	leaq	16(%rbx), %rax
	cmpq	%rax, %r14
	jnb	.LB93
	movq	%r14, %rsi
	movq	%rbp, %rdi
	call	generate
	testq	%rax, %rax
	cmovns	%rbx, %rax
	jmp	.LB89
.LB94:
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	generate
	testq	%rax, %rax
	js	.LB89
	movq	0(%rbp), %rdx
	movq	$-2, %rax
	cmpq	%rdx, %rbx
	jnb	.LB89
	leaq	1(%rbx), %rax
	cmpq	%rbx, 2112(%rbp,%rbx,8)
	jne	.LB96
	jmp	.LB89
.LB107:
	movq	56(%rbp), %rax
	movq	%rbx, (%rax)
	movq	56(%rbp), %rax
	subq	$17, %rdx
	movq	%rdx, 8(%rax)
	movq	$-1, %rax
	jmp	.LB89
.LB99:
	movq	$-3, %rax
	jmp	.LB89
.LB103:
	movq	$-2, %rax
	jmp	.LB89
.LB104:
	movq	$-2, %rax
	jmp	.LB89
	.size	step, .-step
	.globl	build_bottom_up
	.type	build_bottom_up, @function
build_bottom_up:
	pushq	%rbp
	pushq	%rbx
	subq	$4168, %rsp
	movq	%rsi, %rbx
	movq	%rdi, (%rsp)
	movq	%rsi, %rax
	subq	%rdi, %rax
	movq	%rax, 8(%rsp)
	movq	$0, 16(%rsp)
	movq	%rsi, 24(%rsp)
	movq	%rcx, 32(%rsp)
	movq	%r9, 40(%rsp)
	movq	4192(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	4200(%rsp), %rax
	movq	%rax, 56(%rsp)
	testq	%rdi, %rdi
	je	.LB109
	movq	%rdx, %rsi
	movl	$0, %eax
	.p2align 5
.LB110:
	movq	(%rsi,%rax,8), %rdx
	movq	%rdx, 64(%rsp,%rax,8)
	movq	(%r8,%rax,8), %rdx
	movq	%rdx, 2112(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB110
	testq	%rbx, %rbx
	je	.LB111
.LB115:
	movl	$0, %esi
	movq	%rsp, %rbp
.LB114:
	movq	%rbp, %rdi
	call	step
	cmpq	$-3, %rax
	je	.LB122
	testq	%rax, %rax
	js	.LB108
	movq	%rax, %rsi
	cmpq	%rbx, %rax
	jb	.LB114
.LB111:
	cmpq	%rbx, (%rsp)
	jne	.LB118
.LB116:
	movq	16(%rsp), %rax
.LB108:
	addq	$4168, %rsp
	popq	%rbx
	popq	%rbp
	ret
.LB122:
	cmpq	%rbx, (%rsp)
	jne	.LB117
	movq	%rsp, %rdi
	call	finish
	jmp	.LB108
.LB117:
	movq	$-2, %rax
	jmp	.LB108
.LB118:
	movq	$-2, %rax
	jmp	.LB108
.LB109:
	testq	%rsi, %rsi
	jne	.LB115
	jmp	.LB116
	.size	build_bottom_up, .-build_bottom_up
	.section	.note.GNU-stack,"",@progbits
