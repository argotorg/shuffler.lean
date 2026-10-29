_ZN12_GLOBAL__N_18Emission19permuteDestinationsEv:
	pushq	%rbp
	pushq	%rbx
	subq	$4120, %rsp
	movq	%rdi, %rbx
	movq	32(%rdi), %rdi
	testq	%rdi, %rdi
	je	.LB35
	movl	$0, %eax
.LB37:
	movq	56(%rbx,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB41
	movw	%dx, 2064(%rsp,%rax,2)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB37
.LB35:
	leaq	12(%rsp), %rcx
	leaq	16(%rsp), %rdx
	leaq	2064(%rsp), %rsi
	call	permute
	testq	%rax, %rax
	js	.LB38
	leaq	16(%rsp), %rcx
	leaq	(%rax,%rcx), %r9
	movl	$0, %eax
	jle	.LB34
.LB40:
	movzbl	(%rcx), %eax
	movq	32(%rbx), %rsi
	leaq	-1(%rsi), %r8
	movq	24(%rbx), %rdi
	movq	%r8, %rdx
	subq	%rax, %rdx
	leaq	(%rdi,%rdx,8), %rdx
	movl	(%rdx), %ebp
	movzbl	4(%rdx), %r11d
	movzbl	5(%rdx), %r10d
	movq	(%rdi,%r8,8), %rdi
	movq	%rdi, (%rdx)
	movq	32(%rbx), %rdi
	movq	24(%rbx), %rdx
	leaq	-8(%rdx,%rdi,8), %rdx
	movl	%ebp, (%rdx)
	movb	%r11b, 4(%rdx)
	movb	%r10b, 5(%rdx)
	addq	32(%rbx), %rax
	subq	%rsi, %rax
	movq	%rax, %rdx
	movq	48(%rbx), %rax
	leaq	1(%rax), %rsi
	movq	%rsi, 48(%rbx)
	leaq	(%rax,%rax,2), %rax
	salq	$2, %rax
	addq	40(%rbx), %rax
	movb	$0, (%rax)
	movb	%dl, 1(%rax)
	movl	$0, 4(%rax)
	movb	$1, 8(%rax)
	movb	$5, 9(%rax)
	addq	$1, %rcx
	cmpq	%r9, %rcx
	jne	.LB40
	movl	$0, %eax
	jmp	.LB34
.LB38:
	movzwl	14(%rsp), %eax
	movzwl	12(%rsp), %edx
	movq	%rdx, 16448(%rbx)
	movq	%rax, 16456(%rbx)
	movl	$1, %eax
	jmp	.LB34
.LB41:
	movl	$2, %eax
.LB34:
	addq	$4120, %rsp
	popq	%rbx
	popq	%rbp
	ret
	.size	_ZN12_GLOBAL__N_18Emission19permuteDestinationsEv, .-_ZN12_GLOBAL__N_18Emission19permuteDestinationsEv
