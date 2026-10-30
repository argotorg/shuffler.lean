permute_at_lowest_height:
	pushq	%rbp
	pushq	%rbx
	subq	$32872, %rsp
	movq	%rdi, %rbx
	cmpq	$1024, %rdi
	ja	.LB.permute_at_lowest_height.13
	movq	%rdx, %rdi
	movq	%r8, %rbp
	cmpq	$1024, %rsi
	ja	.LB.permute_at_lowest_height.13
	testq	%rbx, %rbx
	je	.LB.permute_at_lowest_height.20
	movl	$0, %eax
	.p2align 5
.LB.permute_at_lowest_height.0:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rbx
	jne	.LB.permute_at_lowest_height.0
	testq	%rsi, %rsi
	je	.LB.permute_at_lowest_height.3
.LB.permute_at_lowest_height.1:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%rsi,8), %rdx
	.p2align 5
.LB.permute_at_lowest_height.2:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB.permute_at_lowest_height.2
	testq	%rbx, %rbx
	je	.LB.permute_at_lowest_height.21
.LB.permute_at_lowest_height.3:
	movl	$0, %eax
	jmp	.LB.permute_at_lowest_height.5
	.p2align 5
.LB.permute_at_lowest_height.4:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rbx
	je	.LB.permute_at_lowest_height.6
	movq	%rdx, %rax
.LB.permute_at_lowest_height.5:
	movq	0(%rbp,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB.permute_at_lowest_height.4
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	jmp	.LB.permute_at_lowest_height.4
.LB.permute_at_lowest_height.6:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%rdi, 24(%rsp)
	movq	%rdx, 32(%rsp)
	movq	32904(%rsp), %rdi
	movq	%rdi, 40(%rsp)
	movq	$0, 48(%rsp)
	movl	$0, %edx
	addq	$1, %rax
	.p2align 5
.LB.permute_at_lowest_height.7:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB.permute_at_lowest_height.7
.LB.permute_at_lowest_height.8:
	testq	%rsi, %rsi
	je	.LB.permute_at_lowest_height.14
	leaq	0(,%rsi,8), %rdx
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB.permute_at_lowest_height.9:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB.permute_at_lowest_height.9
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rdx
	jmp	.LB.permute_at_lowest_height.11
	.p2align 5
.LB.permute_at_lowest_height.10:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB.permute_at_lowest_height.15
.LB.permute_at_lowest_height.11:
	cmpq	$-1, 8248(%rax)
	jne	.LB.permute_at_lowest_height.10
	addq	$1, 16440(%rsp)
	jmp	.LB.permute_at_lowest_height.10
.LB.permute_at_lowest_height.12:
	movq	16448(%rsp), %rax
	movq	32912(%rsp), %rdi
	movq	%rax, (%rdi)
	movq	16456(%rsp), %rax
	movq	%rax, 8(%rdi)
	jmp	.LB.permute_at_lowest_height.16
.LB.permute_at_lowest_height.13:
	movq	$-2, %rdx
	jmp	.LB.permute_at_lowest_height.19
.LB.permute_at_lowest_height.14:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB.permute_at_lowest_height.15:
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission21permuteAtLowestHeightEv
	cmpb	$1, %al
	je	.LB.permute_at_lowest_height.12
	movq	$-2, %rdx
	cmpb	$2, %al
	je	.LB.permute_at_lowest_height.19
	testb	%al, %al
	jne	.LB.permute_at_lowest_height.16
	movq	32912(%rsp), %rax
	movq	$0, (%rax)
	movq	$0, 8(%rax)
.LB.permute_at_lowest_height.16:
	leaq	0(,%rbx,8), %rsi
	movl	$0, %eax
	leaq	56(%rsp), %rcx
	testq	%rbx, %rbx
	je	.LB.permute_at_lowest_height.18
	.p2align 5
.LB.permute_at_lowest_height.17:
	movq	(%rcx,%rax), %rdx
	movq	%rdx, 0(%rbp,%rax)
	addq	$8, %rax
	cmpq	%rsi, %rax
	jne	.LB.permute_at_lowest_height.17
.LB.permute_at_lowest_height.18:
	movq	48(%rsp), %rdx
.LB.permute_at_lowest_height.19:
	movq	%rdx, %rax
	addq	$32872, %rsp
	popq	%rbx
	popq	%rbp
	ret
.LB.permute_at_lowest_height.20:
	testq	%rsi, %rsi
	jne	.LB.permute_at_lowest_height.1
.LB.permute_at_lowest_height.21:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%rdi, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32904(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB.permute_at_lowest_height.8
	.size	permute_at_lowest_height, .-permute_at_lowest_height
