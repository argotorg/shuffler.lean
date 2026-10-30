build_bottom_up:
	cmpq	%rdi, %rsi
	jb	.LB186
	movq	%rdx, %r10
	cmpq	$1024, %rsi
	ja	.LB186
	subq	$32872, %rsp
	testq	%rdi, %rdi
	je	.LB169
	movl	$0, %eax
	.p2align 5
.LB170:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB170
	testq	%rsi, %rsi
	je	.LB185
.LB184:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%rsi,8), %rdx
	.p2align 5
.LB172:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB172
	testq	%rdi, %rdi
	je	.LB173
.LB185:
	movl	$0, %eax
	jmp	.LB175
	.p2align 5
.LB174:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rdi
	je	.LB199
	movq	%rdx, %rax
.LB175:
	movq	(%r8,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB174
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	jmp	.LB174
.LB199:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	%rdx, 32(%rsp)
	movq	32880(%rsp), %rdi
	movq	%rdi, 40(%rsp)
	movq	$0, 48(%rsp)
	movl	$0, %edx
	addq	$1, %rax
	.p2align 5
.LB176:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB176
.LB183:
	testq	%rsi, %rsi
	je	.LB177
	leaq	0(,%rsi,8), %rdx
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB178:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB178
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rdx
	jmp	.LB180
	.p2align 5
.LB179:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB182
.LB180:
	cmpq	$-1, 8248(%rax)
	jne	.LB179
	addq	$1, 16440(%rsp)
	jmp	.LB179
.LB200:
	movq	32888(%rsp), %rax
	movq	$0, (%rax)
	movq	$0, 8(%rax)
	movq	48(%rsp), %rdx
	jmp	.LB167
.LB181:
	movq	16448(%rsp), %rax
	movq	32888(%rsp), %rsi
	movq	%rax, (%rsi)
	movq	16456(%rsp), %rax
	movq	%rax, 8(%rsi)
	movq	48(%rsp), %rdx
	jmp	.LB167
.LB186:
	movq	$-2, %rdx
	movq	%rdx, %rax
	ret
.LB177:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB182:
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv
	cmpb	$1, %al
	je	.LB181
	movq	$-2, %rdx
	cmpb	$2, %al
	jne	.LB200
.LB167:
	movq	%rdx, %rax
	addq	$32872, %rsp
	ret
.LB169:
	testq	%rsi, %rsi
	jne	.LB184
.LB173:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32880(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB183
	.size	build_bottom_up, .-build_bottom_up
