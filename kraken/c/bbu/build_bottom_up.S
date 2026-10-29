build_bottom_up:
	cmpq	%rdi, %rsi
	jb	.LB141
	cmpq	$1024, %rsi
	ja	.LB141
	subq	$16472, %rsp
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%rdx, 24(%rsp)
	movq	%rdi, 32(%rsp)
	movq	16480(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	testq	%rsi, %rsi
	je	.LB130
	movl	$0, %eax
	.p2align 5
.LB131:
	movq	$-1, 8248(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rsi
	jne	.LB131
	testq	%rdi, %rdi
	je	.LB132
.LB138:
	movl	$0, %eax
	.p2align 5
.LB133:
	movq	(%r8,%rax,8), %rdx
	movq	%rdx, 56(%rsp,%rax,8)
	movq	%rax, 8248(%rsp,%rdx,8)
	addq	$1, %rax
	cmpq	%rdi, %rax
	jb	.LB133
	movq	$0, 16440(%rsp)
	testq	%rsi, %rsi
	je	.LB134
.LB140:
	movq	%rsp, %rax
	leaq	(%rax,%rsi,8), %rdx
	jmp	.LB136
	.p2align 5
.LB135:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB134
.LB136:
	cmpq	$-1, 8248(%rax)
	jne	.LB135
	addq	$1, 16440(%rsp)
	jmp	.LB135
.LB137:
	movq	16448(%rsp), %rax
	movq	16488(%rsp), %rcx
	movq	%rax, (%rcx)
	movq	16456(%rsp), %rax
	movq	%rax, 8(%rcx)
	movq	$-1, %rax
	jmp	.LB128
.LB141:
	movq	$-2, %rax
	ret
.LB130:
	testq	%rdi, %rdi
	jne	.LB138
	movq	$0, 16440(%rsp)
.LB134:
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv
	cmpb	$1, %al
	je	.LB137
	cmpb	$2, %al
	movq	$-2, %rax
	cmovne	48(%rsp), %rax
.LB128:
	addq	$16472, %rsp
	ret
.LB132:
	movq	$0, 16440(%rsp)
	jmp	.LB140
	.size	build_bottom_up, .-build_bottom_up
