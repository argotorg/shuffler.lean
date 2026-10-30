permute:
	pushq	%r14
	pushq	%rbp
	pushq	%rbx
	subq	$49248, %rsp
	movq	%rdi, %rbx
	cmpq	$1024, %rdi
	ja	.LB.permute.15
	movq	%rsi, %rdi
	movq	%rdx, %r10
	movq	%rcx, %r11
	movq	%r8, %r14
	movq	%r9, %rbp
	testq	%rbx, %rbx
	je	.LB.permute.16
	leaq	16480(%rsp), %rax
	leaq	0(,%rbx,8), %rcx
	leaq	(%rax,%rcx), %rsi
	movq	%rax, %rdx
	.p2align 4
.LB.permute.0:
	movq	$-1, (%rdx)
	addq	$8, %rdx
	cmpq	%rsi, %rdx
	jne	.LB.permute.0
	.p2align 5
.LB.permute.1:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rsi, %rax
	jne	.LB.permute.1
	movl	$0, %eax
	.p2align 6
.LB.permute.2:
	movq	(%r10,%rax,8), %rdx
	movq	%rdx, 41056(%rsp,%rax,8)
	movq	(%rdi,%rax,8), %rsi
	movq	%rsi, 32864(%rsp,%rdx,8)
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	addq	$1, %rax
	cmpq	%rax, %rbx
	jne	.LB.permute.2
	leaq	32864(%rsp), %rdx
	movq	%rdx, (%rsp)
	movq	%rax, 8(%rsp)
	movq	$0, 16(%rsp)
	movq	%rdi, 24(%rsp)
	movq	%rax, 32(%rsp)
	movq	%r11, 40(%rsp)
	movq	$0, 48(%rsp)
	movl	$0, %eax
	leaq	56(%rsp), %rsi
	.p2align 5
.LB.permute.3:
	movq	16480(%rsp,%rax), %rdx
	movq	%rdx, (%rsi,%rax)
	addq	$8, %rax
	cmpq	%rcx, %rax
	jne	.LB.permute.3
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB.permute.4:
	movq	(%rsi,%rax), %rdx
	movq	%rdx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rcx, %rax
	jne	.LB.permute.4
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rcx
	jmp	.LB.permute.6
	.p2align 5
.LB.permute.5:
	addq	$8, %rax
	cmpq	%rcx, %rax
	je	.LB.permute.7
.LB.permute.6:
	cmpq	$-1, 8248(%rax)
	jne	.LB.permute.5
	addq	$1, 16440(%rsp)
	jmp	.LB.permute.5
.LB.permute.7:
	leaq	41056(%rsp), %rsi
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE
	cmpb	$1, %al
	je	.LB.permute.14
	movq	$-2, %rdx
	cmpb	$2, %al
	je	.LB.permute.13
	testb	%al, %al
	jne	.LB.permute.10
.LB.permute.8:
	movl	$0, %edx
	movl	$0, %eax
.LB.permute.9:
	movq	%rdx, (%r14)
	movq	%rax, 8(%r14)
	testq	%rbx, %rbx
	je	.LB.permute.12
.LB.permute.10:
	salq	$3, %rbx
	movl	$0, %eax
	leaq	56(%rsp), %rcx
	.p2align 5
.LB.permute.11:
	movq	(%rcx,%rax), %rdx
	movq	%rdx, 0(%rbp,%rax)
	addq	$8, %rax
	cmpq	%rax, %rbx
	jne	.LB.permute.11
.LB.permute.12:
	movq	48(%rsp), %rdx
.LB.permute.13:
	movq	%rdx, %rax
	addq	$49248, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r14
	ret
.LB.permute.14:
	movq	16448(%rsp), %rdx
	movq	16456(%rsp), %rax
	jmp	.LB.permute.9
.LB.permute.15:
	movq	$-2, %rdx
	jmp	.LB.permute.13
.LB.permute.16:
	leaq	32864(%rsp), %rax
	movq	%rax, (%rsp)
	movq	%rbx, 8(%rsp)
	movq	$0, 16(%rsp)
	movq	%rsi, 24(%rsp)
	movq	%rbx, 32(%rsp)
	movq	%rcx, 40(%rsp)
	movq	$0, 48(%rsp)
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	leaq	41056(%rsp), %rsi
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE
	cmpb	$1, %al
	je	.LB.permute.14
	movq	$-2, %rdx
	cmpb	$2, %al
	je	.LB.permute.13
	testb	%al, %al
	je	.LB.permute.8
	jmp	.LB.permute.12
	.size	permute, .-permute
