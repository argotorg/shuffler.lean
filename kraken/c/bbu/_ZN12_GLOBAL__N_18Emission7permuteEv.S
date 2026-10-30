_ZN12_GLOBAL__N_18Emission7permuteEv:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$16408, %rsp
	movq	32(%rdi), %rbx
	movl	$0, %eax
	testq	%rbx, %rbx
	je	.LB54
	movq	%rdi, %r15
	movl	$0, %eax
.LB57:
	movq	56(%r15,%rax,8), %rdx
	cmpq	$-1, %rdx
	jne	.LB56
	movl	$2, %eax
.LB54:
	addq	$16408, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB56:
	movq	%rdx, 8208(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rbx
	jne	.LB57
	leaq	16(%rsp), %rax
	leaq	(%rax,%rbx,8), %rdx
	.p2align 4
.LB58:
	movq	$-1, (%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB58
	movq	$8, 8(%rsp)
	movq	$1, (%rsp)
	movl	$0, %ebp
	leaq	16(%rsp), %r12
	jmp	.LB71
	.p2align 5
.LB61:
	addq	$8, %rax
	movq	8(%rsp), %rdi
	cmpq	%rdi, %rax
	je	.LB95
.LB62:
	movq	%r14, %rdx
	xorq	0(%r13,%rax), %rdx
	salq	$16, %rdx
	jne	.LB61
	movq	8208(%rsp,%rax), %rdx
	movq	%rbp, 16(%rsp,%rdx,8)
	jmp	.LB61
.LB95:
	movl	$0, %ecx
	movl	$0, %eax
	jmp	.LB70
.LB64:
	cmpq	%rbx, %rax
	jb	.LB68
.LB65:
	movl	$2, %eax
	jmp	.LB54
	.p2align 4
.LB66:
	addq	$1, %rax
	cmpq	%rbx, %rax
	je	.LB65
.LB68:
	cmpq	%rbp, (%r12,%rax,8)
	jne	.LB66
	movq	%r14, %rdx
	xorq	0(%r13,%rax,8), %rdx
	salq	$16, %rdx
	je	.LB66
	cmpq	%rbx, %rax
	jnb	.LB65
	movq	%rax, 8208(%rsp,%rcx,8)
	addq	$1, %rax
.LB63:
	addq	$1, %rcx
	cmpq	%rcx, (%rsp)
	je	.LB60
.LB70:
	movq	%r14, %rdx
	xorq	0(%r13,%rcx,8), %rdx
	salq	$16, %rdx
	jne	.LB63
	cmpq	%rbp, (%r12,%rcx,8)
	jne	.LB64
	movq	%rcx, 8208(%rsp,%rcx,8)
	jmp	.LB63
.LB60:
	addq	$1, %rbp
	addq	$1, (%rsp)
	addq	$8, 8(%rsp)
	cmpq	%rbp, %rbx
	je	.LB96
.LB71:
	movq	24(%r15), %r13
	movq	0(%r13,%rbp,8), %r14
	movq	%r14, %rsi
	movq	%r15, %rdi
	call	_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot
	cmpq	%rbp, %rax
	jne	.LB60
	movl	$0, %eax
	jmp	.LB62
.LB96:
	leaq	-1(%rbx), %rcx
	leaq	8208(%rsp), %rsi
	jmp	.LB84
.LB86:
	movq	%rcx, %rdx
.LB72:
	testq	%rdx, %rdx
	je	.LB97
	leaq	-1(%rdx), %rax
	cmpq	(%rsi,%rax,8), %rax
	jne	.LB74
	movq	%rax, %rdx
	jmp	.LB72
.LB97:
	movl	$0, %eax
	jmp	.LB54
.LB74:
	cmpq	%rdx, %rbx
	jne	.LB73
	movl	$0, %eax
	jmp	.LB54
.LB98:
	movq	56(%r15,%rax,8), %rdx
	movq	56(%r15,%rcx,8), %rdi
	movq	%rdi, 56(%r15,%rax,8)
	movq	%rdx, 56(%r15,%rcx,8)
	movq	56(%r15,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB78
	movq	%rax, 8248(%r15,%rdx,8)
.LB78:
	movq	56(%r15,%rcx,8), %rdx
	cmpq	$-1, %rdx
	je	.LB80
	movq	%rcx, 8248(%r15,%rdx,8)
.LB80:
	movq	8208(%rsp,%rax,8), %rdx
	movq	8208(%rsp,%rcx,8), %rdi
	movq	%rdi, 8208(%rsp,%rax,8)
	movq	%rdx, 8208(%rsp,%rcx,8)
.LB84:
	movq	8208(%rsp,%rcx,8), %rax
	cmpq	%rcx, %rax
	je	.LB86
.LB73:
	movq	24(%r15), %rdx
	movq	32(%r15), %rdi
	leaq	-8(%rdx,%rdi,8), %r9
	leaq	(%rdx,%rax,8), %r8
	movq	(%r8), %rdx
	xorq	(%r9), %rdx
	salq	$16, %rdx
	je	.LB98
	subq	%rax, %rdi
	leaq	-1(%rdi), %rdx
	cmpq	$16, %rdx
	ja	.LB99
	movl	(%r8), %r11d
	movzbl	4(%r8), %r10d
	movzbl	5(%r8), %edi
	movq	(%r9), %rdx
	movq	%rdx, (%r8)
	movq	32(%r15), %r8
	movq	24(%r15), %rdx
	leaq	-8(%rdx,%r8,8), %rdx
	movl	%r11d, (%rdx)
	movb	%r10b, 4(%rdx)
	movb	%dil, 5(%rdx)
	movq	%rax, %rdi
	notq	%rdi
	addq	32(%r15), %rdi
	movq	48(%r15), %rdx
	leaq	1(%rdx), %r8
	movq	%r8, 48(%r15)
	leaq	(%rdx,%rdx,2), %rdx
	salq	$2, %rdx
	addq	40(%r15), %rdx
	movb	$0, (%rdx)
	movb	%dil, 1(%rdx)
	movl	$0, 4(%rdx)
	movb	$1, 8(%rdx)
	movb	$5, 9(%rdx)
	movq	56(%r15,%rax,8), %rdx
	movq	56(%r15,%rcx,8), %rdi
	movq	%rdi, 56(%r15,%rax,8)
	movq	%rdx, 56(%r15,%rcx,8)
	movq	56(%r15,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB82
	movq	%rax, 8248(%r15,%rdx,8)
.LB82:
	movq	56(%r15,%rcx,8), %rdx
	cmpq	$-1, %rdx
	je	.LB80
	movq	%rcx, 8248(%r15,%rdx,8)
	jmp	.LB80
.LB99:
	movq	%rax, 16448(%r15)
	subq	$17, %rdi
	movq	%rdi, 16456(%r15)
	movl	$1, %eax
	jmp	.LB54
	.size	_ZN12_GLOBAL__N_18Emission7permuteEv, .-_ZN12_GLOBAL__N_18Emission7permuteEv
