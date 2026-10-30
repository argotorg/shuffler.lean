build_bottom_up:
	cmpq	%rdi, %rsi
	jb	.LB192
	movq	%rdx, %r10
	cmpq	$1024, %rsi
	ja	.LB192
	subq	$32872, %rsp
	testq	%rdi, %rdi
	je	.LB175
	movl	$0, %eax
	.p2align 5
.LB176:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB176
	testq	%rsi, %rsi
	je	.LB191
.LB190:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%rsi,8), %rdx
	.p2align 5
.LB178:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB178
	testq	%rdi, %rdi
	je	.LB179
.LB191:
	movl	$0, %eax
	jmp	.LB181
	.p2align 5
.LB180:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rdi
	je	.LB205
	movq	%rdx, %rax
.LB181:
	movq	(%r8,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB180
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	jmp	.LB180
.LB205:
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
.LB182:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB182
.LB189:
	testq	%rsi, %rsi
	je	.LB183
	leaq	0(,%rsi,8), %rdx
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB184:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB184
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rdx
	jmp	.LB186
	.p2align 5
.LB185:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB188
.LB186:
	cmpq	$-1, 8248(%rax)
	jne	.LB185
	addq	$1, 16440(%rsp)
	jmp	.LB185
.LB206:
	movq	32888(%rsp), %rax
	movq	$0, (%rax)
	movq	$0, 8(%rax)
	movq	48(%rsp), %rdx
	jmp	.LB173
.LB187:
	movq	16448(%rsp), %rax
	movq	32888(%rsp), %rsi
	movq	%rax, (%rsi)
	movq	16456(%rsp), %rax
	movq	%rax, 8(%rsi)
	movq	48(%rsp), %rdx
	jmp	.LB173
.LB192:
	movq	$-2, %rdx
	movq	%rdx, %rax
	ret
.LB183:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB188:
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv
	cmpb	$1, %al
	je	.LB187
	movq	$-2, %rdx
	cmpb	$2, %al
	jne	.LB206
.LB173:
	movq	%rdx, %rax
	addq	$32872, %rsp
	ret
.LB175:
	testq	%rsi, %rsi
	jne	.LB190
.LB179:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32880(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB189
	.size	build_bottom_up, .-build_bottom_up
