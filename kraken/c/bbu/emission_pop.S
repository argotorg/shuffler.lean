emission_pop:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$32872, %rsp
	movq	32928(%rsp), %r13
	movq	32952(%rsp), %r15
	cmpq	$1024, %rdi
	ja	.LB225
	movq	%rdi, %rbx
	movq	%rsi, %r12
	movq	%rdx, %rsi
	cmpq	$1024, %r12
	ja	.LB225
	testq	%rdi, %rdi
	je	.LB203
	movl	$0, %eax
	.p2align 5
.LB204:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rbx
	jne	.LB204
	testq	%r12, %r12
	je	.LB224
.LB223:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%r12,8), %rdx
	.p2align 5
.LB206:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB206
	testq	%rbx, %rbx
	je	.LB207
.LB224:
	movl	$0, %eax
	jmp	.LB209
	.p2align 5
.LB208:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rbx
	je	.LB238
	movq	%rdx, %rax
.LB209:
	movq	(%r8,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB208
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	jmp	.LB208
.LB238:
	movq	%rcx, (%rsp)
	movq	%r12, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%rsi, 24(%rsp)
	movq	%rdx, 32(%rsp)
	movq	32936(%rsp), %rdi
	movq	%rdi, 40(%rsp)
	movq	$0, 48(%rsp)
	movl	$0, %edx
	addq	$1, %rax
	.p2align 5
.LB210:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB210
.LB222:
	testq	%r12, %r12
	je	.LB211
	leaq	0(,%r12,8), %rdx
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB212:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB212
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rdx
	jmp	.LB214
	.p2align 5
.LB213:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB221
.LB214:
	cmpq	$-1, 8248(%rax)
	jne	.LB213
	addq	$1, 16440(%rsp)
	jmp	.LB213
.LB225:
	movq	$-2, %rax
	jmp	.LB201
.LB227:
	movq	$-2, %rax
	jmp	.LB201
.LB211:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB221:
	testq	%r13, %r13
	je	.LB215
	movl	$0, %ebp
	movq	%rsp, %r14
.LB216:
	movq	%r14, %rdi
	call	_ZN12_GLOBAL__N_18Emission3popEv
	testb	%al, %al
	jne	.LB227
	addq	$1, %rbp
	cmpq	%rbp, %r13
	jne	.LB216
.LB215:
	cmpq	%r13, %rbx
	je	.LB217
	subq	%r13, %rbx
	movl	$0, %eax
	.p2align 5
.LB218:
	movq	56(%rsp,%rax,8), %rdx
	movq	32944(%rsp), %rsi
	movq	%rdx, (%rsi,%rax,8)
	addq	$1, %rax
	cmpq	%rbx, %rax
	jb	.LB218
.LB217:
	testq	%r12, %r12
	je	.LB219
	salq	$3, %r12
	movl	$0, %eax
	leaq	8248(%rsp), %rcx
	.p2align 5
.LB220:
	movq	(%rcx,%rax), %rdx
	movq	%rdx, (%r15,%rax)
	addq	$8, %rax
	cmpq	%rax, %r12
	jne	.LB220
.LB219:
	movq	32960(%rsp), %rax
	movq	16440(%rsp), %rdx
	movq	%rdx, (%rax)
	movq	48(%rsp), %rax
.LB201:
	addq	$32872, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB203:
	testq	%r12, %r12
	jne	.LB223
.LB207:
	movq	%rcx, (%rsp)
	movq	%r12, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%rsi, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32936(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB222
	.size	emission_pop, .-emission_pop
