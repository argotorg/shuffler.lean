build_bottom_up:
	cmpq	%rdi, %rsi
	jb	.LB176
	cmpq	$1024, %rsi
	ja	.LB176
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
	je	.LB165
	movl	$0, %eax
	.p2align 5
.LB166:
	movq	$-1, 8248(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rsi
	jne	.LB166
	testq	%rdi, %rdi
	je	.LB167
.LB173:
	movl	$0, %eax
	.p2align 5
.LB168:
	movq	(%r8,%rax,8), %rdx
	movq	%rdx, 56(%rsp,%rax,8)
	movq	%rax, 8248(%rsp,%rdx,8)
	addq	$1, %rax
	cmpq	%rdi, %rax
	jb	.LB168
	movq	$0, 16440(%rsp)
	testq	%rsi, %rsi
	je	.LB169
.LB175:
	movq	%rsp, %rax
	leaq	(%rax,%rsi,8), %rdx
	jmp	.LB171
	.p2align 5
.LB170:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB169
.LB171:
	cmpq	$-1, 8248(%rax)
	jne	.LB170
	addq	$1, 16440(%rsp)
	jmp	.LB170
.LB186:
	movq	16488(%rsp), %rax
	movq	$0, (%rax)
	movq	$0, 8(%rax)
	movq	48(%rsp), %rdx
	jmp	.LB163
.LB172:
	movq	16448(%rsp), %rax
	movq	16488(%rsp), %rcx
	movq	%rax, (%rcx)
	movq	16456(%rsp), %rax
	movq	%rax, 8(%rcx)
	movq	48(%rsp), %rdx
	jmp	.LB163
.LB176:
	movq	$-2, %rdx
	movq	%rdx, %rax
	ret
.LB165:
	testq	%rdi, %rdi
	jne	.LB173
	movq	$0, 16440(%rsp)
.LB169:
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv
	cmpb	$1, %al
	je	.LB172
	movq	$-2, %rdx
	cmpb	$2, %al
	jne	.LB186
.LB163:
	movq	%rdx, %rax
	addq	$16472, %rsp
	ret
.LB167:
	movq	$0, 16440(%rsp)
	jmp	.LB175
	.size	build_bottom_up, .-build_bottom_up
