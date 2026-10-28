finish:
	pushq	%rbx
	subq	$4112, %rsp
	movq	%rdi, %rbx
	movq	(%rdi), %rdi
	testq	%rdi, %rdi
	je	.LB55
	movl	$0, %eax
	.p2align 5
.LB56:
	movq	8256(%rbx,%rax,8), %rdx
	movw	%dx, 2064(%rsp,%rax,2)
	addq	$1, %rax
	cmpq	%rdi, %rax
	jne	.LB56
.LB55:
	leaq	12(%rsp), %rcx
	leaq	16(%rsp), %rdx
	leaq	2064(%rsp), %rsi
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
	addq	$4112, %rsp
	popq	%rbx
	ret
.LB57:
	movzwl	14(%rsp), %edx
	movq	56(%rbx), %rax
	movzwl	12(%rsp), %ecx
	movq	%rcx, (%rax)
	movq	56(%rbx), %rax
	movq	%rdx, 8(%rax)
	movq	$-1, %rax
	jmp	.LB54
	.size	finish, .-finish
