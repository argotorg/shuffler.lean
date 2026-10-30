_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE:
	movq	32(%rdi), %rdx
	movl	$0, %eax
	testq	%rdx, %rdx
	je	.LB.Emission.permute.25
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$8216, %rsp
	movq	%rdi, %r13
	movq	%rsi, %r14
	leaq	16(%rsp), %rax
	leaq	(%rax,%rdx,8), %rdx
	.p2align 4
.LB.Emission.permute.0:
	movq	$-1, (%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB.Emission.permute.0
	movq	$8, (%rsp)
	movl	$1, %r15d
	movl	$0, %ebx
	leaq	16(%rsp), %rbp
	jmp	.LB.Emission.permute.12
	.p2align 5
.LB.Emission.permute.1:
	addq	$8, %rax
	cmpq	%rax, (%rsp)
	je	.LB.Emission.permute.3
.LB.Emission.permute.2:
	movq	8(%rsp), %rdi
	movq	%r12, %rdx
	xorq	(%rdi,%rax), %rdx
	salq	$16, %rdx
	jne	.LB.Emission.permute.1
	movq	(%r14,%rax), %rdx
	movq	%rbx, 16(%rsp,%rdx,8)
	jmp	.LB.Emission.permute.1
.LB.Emission.permute.3:
	movl	$0, %ecx
	movl	$0, %eax
	jmp	.LB.Emission.permute.10
.LB.Emission.permute.4:
	movq	32(%r13), %rsi
	cmpq	%rsi, %rax
	jb	.LB.Emission.permute.8
.LB.Emission.permute.5:
	movl	$2, %eax
.LB.Emission.permute.6:
	addq	$8216, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
	.p2align 4
.LB.Emission.permute.7:
	addq	$1, %rax
	cmpq	%rax, %rsi
	je	.LB.Emission.permute.5
.LB.Emission.permute.8:
	cmpq	0(%rbp,%rax,8), %rbx
	jne	.LB.Emission.permute.7
	movq	%r12, %rdx
	xorq	(%rdi,%rax,8), %rdx
	salq	$16, %rdx
	je	.LB.Emission.permute.7
	cmpq	%rsi, %rax
	jnb	.LB.Emission.permute.5
	movq	%rax, (%r14,%rcx,8)
	addq	$1, %rax
.LB.Emission.permute.9:
	addq	$1, %rcx
	cmpq	%rcx, %r15
	je	.LB.Emission.permute.11
.LB.Emission.permute.10:
	movq	24(%r13), %rdi
	movq	%r12, %rdx
	xorq	(%rdi,%rcx,8), %rdx
	salq	$16, %rdx
	jne	.LB.Emission.permute.9
	cmpq	0(%rbp,%rcx,8), %rbx
	jne	.LB.Emission.permute.4
	movq	%rcx, (%r14,%rcx,8)
	jmp	.LB.Emission.permute.9
.LB.Emission.permute.11:
	movq	32(%r13), %rcx
	addq	$1, %rbx
	addq	$1, %r15
	addq	$8, (%rsp)
	cmpq	%rcx, %rbx
	jnb	.LB.Emission.permute.13
.LB.Emission.permute.12:
	movq	24(%r13), %rax
	movq	%rax, 8(%rsp)
	movq	(%rax,%rbx,8), %r12
	movq	%r12, %rsi
	movq	%r13, %rdi
	call	_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot
	cmpq	%rbx, %rax
	jne	.LB.Emission.permute.11
	movl	$0, %eax
	jmp	.LB.Emission.permute.2
.LB.Emission.permute.13:
	leaq	-1(%rcx), %rsi
	jmp	.LB.Emission.permute.21
.LB.Emission.permute.14:
	movq	%rsi, %rdx
.LB.Emission.permute.15:
	testq	%rdx, %rdx
	je	.LB.Emission.permute.16
	leaq	-1(%rdx), %rax
	cmpq	(%r14,%rax,8), %rax
	jne	.LB.Emission.permute.17
	movq	%rax, %rdx
	jmp	.LB.Emission.permute.15
.LB.Emission.permute.16:
	movl	$0, %eax
	jmp	.LB.Emission.permute.6
.LB.Emission.permute.17:
	cmpq	%rcx, %rdx
	jne	.LB.Emission.permute.22
	movl	$0, %eax
	jmp	.LB.Emission.permute.6
.LB.Emission.permute.18:
	movq	56(%r13,%rax,8), %rdx
	movq	56(%r13,%rsi,8), %rdi
	movq	%rdi, 56(%r13,%rax,8)
	movq	%rdx, 56(%r13,%rsi,8)
	movq	56(%r13,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB.Emission.permute.19
	movq	%rax, 8248(%r13,%rdx,8)
.LB.Emission.permute.19:
	movq	56(%r13,%rsi,8), %rdx
	cmpq	$-1, %rdx
	je	.LB.Emission.permute.20
	movq	%rsi, 8248(%r13,%rdx,8)
.LB.Emission.permute.20:
	movq	(%r14,%rax,8), %rdx
	movq	(%r14,%rsi,8), %rdi
	movq	%rdi, (%r14,%rax,8)
	movq	%rdx, (%r14,%rsi,8)
.LB.Emission.permute.21:
	movq	(%r14,%rsi,8), %rax
	cmpq	%rsi, %rax
	je	.LB.Emission.permute.14
.LB.Emission.permute.22:
	movq	24(%r13), %rdx
	movq	32(%r13), %rdi
	leaq	-8(%rdx,%rdi,8), %r9
	leaq	(%rdx,%rax,8), %r8
	movq	(%r8), %rdx
	xorq	(%r9), %rdx
	salq	$16, %rdx
	je	.LB.Emission.permute.18
	subq	%rax, %rdi
	leaq	-1(%rdi), %rdx
	cmpq	$16, %rdx
	ja	.LB.Emission.permute.24
	movl	(%r8), %r11d
	movzbl	4(%r8), %r10d
	movzbl	5(%r8), %edi
	movq	(%r9), %rdx
	movq	%rdx, (%r8)
	movq	32(%r13), %r8
	movq	24(%r13), %rdx
	leaq	-8(%rdx,%r8,8), %rdx
	movl	%r11d, (%rdx)
	movb	%r10b, 4(%rdx)
	movb	%dil, 5(%rdx)
	movq	%rax, %rdi
	notq	%rdi
	addq	32(%r13), %rdi
	movq	48(%r13), %rdx
	leaq	1(%rdx), %r8
	movq	%r8, 48(%r13)
	leaq	(%rdx,%rdx,2), %rdx
	salq	$2, %rdx
	addq	40(%r13), %rdx
	movb	$0, (%rdx)
	movb	%dil, 1(%rdx)
	movl	$0, 4(%rdx)
	movb	$1, 8(%rdx)
	movb	$5, 9(%rdx)
	movq	56(%r13,%rax,8), %rdx
	movq	56(%r13,%rsi,8), %rdi
	movq	%rdi, 56(%r13,%rax,8)
	movq	%rdx, 56(%r13,%rsi,8)
	movq	56(%r13,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB.Emission.permute.23
	movq	%rax, 8248(%r13,%rdx,8)
.LB.Emission.permute.23:
	movq	56(%r13,%rsi,8), %rdx
	cmpq	$-1, %rdx
	je	.LB.Emission.permute.20
	movq	%rsi, 8248(%r13,%rdx,8)
	jmp	.LB.Emission.permute.20
.LB.Emission.permute.24:
	movq	%rax, 16448(%r13)
	subq	$17, %rdi
	movq	%rdi, 16456(%r13)
	movl	$1, %eax
	jmp	.LB.Emission.permute.6
.LB.Emission.permute.25:
	ret
	.size	_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE, .-_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE
