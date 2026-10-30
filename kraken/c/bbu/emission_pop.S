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
	ja	.LB231
	movq	%rdi, %rbx
	movq	%rsi, %r12
	movq	%rdx, %rsi
	cmpq	$1024, %r12
	ja	.LB231
	testq	%rdi, %rdi
	je	.LB209
	movl	$0, %eax
	.p2align 5
.LB210:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rbx
	jne	.LB210
	testq	%r12, %r12
	je	.LB230
.LB229:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%r12,8), %rdx
	.p2align 5
.LB212:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB212
	testq	%rbx, %rbx
	je	.LB213
.LB230:
	movl	$0, %eax
	jmp	.LB215
	.p2align 5
.LB214:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rbx
	je	.LB244
	movq	%rdx, %rax
.LB215:
	movq	(%r8,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB214
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	jmp	.LB214
.LB244:
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
.LB216:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB216
.LB228:
	testq	%r12, %r12
	je	.LB217
	leaq	0(,%r12,8), %rdx
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB218:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB218
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rdx
	jmp	.LB220
	.p2align 5
.LB219:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB227
.LB220:
	cmpq	$-1, 8248(%rax)
	jne	.LB219
	addq	$1, 16440(%rsp)
	jmp	.LB219
.LB231:
	movq	$-2, %rax
	jmp	.LB207
.LB233:
	movq	$-2, %rax
	jmp	.LB207
.LB217:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB227:
	testq	%r13, %r13
	je	.LB221
	movl	$0, %ebp
	movq	%rsp, %r14
.LB222:
	movq	%r14, %rdi
	call	_ZN12_GLOBAL__N_18Emission3popEv
	testb	%al, %al
	jne	.LB233
	addq	$1, %rbp
	cmpq	%rbp, %r13
	jne	.LB222
.LB221:
	cmpq	%r13, %rbx
	je	.LB223
	subq	%r13, %rbx
	movl	$0, %eax
	.p2align 5
.LB224:
	movq	56(%rsp,%rax,8), %rdx
	movq	32944(%rsp), %rsi
	movq	%rdx, (%rsi,%rax,8)
	addq	$1, %rax
	cmpq	%rbx, %rax
	jb	.LB224
.LB223:
	testq	%r12, %r12
	je	.LB225
	salq	$3, %r12
	movl	$0, %eax
	leaq	8248(%rsp), %rcx
	.p2align 5
.LB226:
	movq	(%rcx,%rax), %rdx
	movq	%rdx, (%r15,%rax)
	addq	$8, %rax
	cmpq	%rax, %r12
	jne	.LB226
.LB225:
	movq	32960(%rsp), %rax
	movq	16440(%rsp), %rdx
	movq	%rdx, (%rax)
	movq	48(%rsp), %rax
.LB207:
	addq	$32872, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB209:
	testq	%r12, %r12
	jne	.LB229
.LB213:
	movq	%rcx, (%rsp)
	movq	%r12, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%rsi, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32936(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB228
	.size	emission_pop, .-emission_pop
