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
