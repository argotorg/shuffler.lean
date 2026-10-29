permuteDestinations:
	pushq	%rbx
	subq	$4112, %rsp
	movq	%rdi, %rbx
	movq	(%rdi), %rdi
	testq	%rdi, %rdi
	je	.LB51
	movl	$0, %eax
	.p2align 5
.LB52:
	movq	72(%rbx,%rax,8), %rdx
	movw	%dx, 2064(%rsp,%rax,2)
	addq	$1, %rax
	cmpq	%rdi, %rax
	jne	.LB52
.LB51:
	leaq	12(%rsp), %rcx
	leaq	16(%rsp), %rdx
	leaq	2064(%rsp), %rsi
	call	permute
	testq	%rax, %rax
	js	.LB60
	jle	.LB56
	movq	(%rbx), %rsi
	leaq	-1(%rsi), %r10
	leaq	0(,%r10,8), %rsi
	leaq	16(%rsp), %rdx
	leaq	(%rax,%rdx), %r9
.LB55:
	movq	64(%rbx), %rcx
	movzbl	(%rdx), %edi
	movq	%r10, %rax
	subq	%rdi, %rax
	leaq	(%rcx,%rax,8), %rax
	movl	(%rax), %r11d
	movzbl	4(%rax), %r8d
	movzbl	5(%rax), %edi
	movq	(%rcx,%rsi), %rcx
	movq	%rcx, (%rax)
	movq	%rsi, %rax
	addq	64(%rbx), %rax
	movl	%r11d, (%rax)
	movb	%r8b, 4(%rax)
	movb	%dil, 5(%rax)
	movzbl	(%rdx), %ecx
	movq	16(%rbx), %rax
	leaq	(%rax,%rax,2), %rdi
	movq	48(%rbx), %rax
	leaq	(%rax,%rdi,4), %rax
	movb	$0, (%rax)
	movb	%cl, 1(%rax)
	movl	$0, 4(%rax)
	movb	$1, 8(%rax)
	movb	$5, 9(%rax)
	addq	$1, 16(%rbx)
	addq	$1, %rdx
	cmpq	%r9, %rdx
	jne	.LB55
	movl	$0, %eax
.LB50:
	addq	$4112, %rsp
	popq	%rbx
	ret
.LB60:
	movq	56(%rbx), %rax
	movzwl	12(%rsp), %edx
	movq	%rdx, (%rax)
	movq	56(%rbx), %rax
	movzwl	14(%rsp), %edx
	movq	%rdx, 8(%rax)
	movq	$-1, %rax
	jmp	.LB50
.LB56:
	movl	$0, %eax
	jmp	.LB50
	.size	permuteDestinations, .-permuteDestinations
