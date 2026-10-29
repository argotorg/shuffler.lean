_ZN12_GLOBAL__N_18Emission8generateE11StackOffset:
	movl	$2, %eax
	cmpq	8(%rdi), %rsi
	jnb	.LB60
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movq	%rsi, %rbx
	call	_ZN12_GLOBAL__N_18Emission7produceE11StackOffset
	testb	%al, %al
	jne	.LB53
	movq	32(%rbp), %rdx
	leaq	1(%rbx), %rcx
	cmpq	%rdx, %rcx
	jnb	.LB53
	cmpq	%rbx, 56(%rbp,%rbx,8)
	je	.LB53
	movq	24(%rbp), %rdi
	leaq	-1(%rdx), %rsi
	movq	(%rdi,%rsi,8), %rcx
	xorq	(%rdi,%rbx,8), %rcx
	salq	$16, %rcx
	je	.LB63
	subq	%rbx, %rdx
	subq	$1, %rdx
	cmpq	$16, %rdx
	jbe	.LB64
.LB53:
	popq	%rbx
	popq	%rbp
	ret
.LB63:
	movq	56(%rbp,%rbx,8), %rdx
	movq	56(%rbp,%rsi,8), %rcx
	movq	%rcx, 56(%rbp,%rbx,8)
	movq	%rdx, 56(%rbp,%rsi,8)
	movq	56(%rbp,%rbx,8), %rdx
	cmpq	$-1, %rdx
	je	.LB56
	movq	%rbx, 8248(%rbp,%rdx,8)
.LB56:
	movq	56(%rbp,%rsi,8), %rdx
	cmpq	$-1, %rdx
	je	.LB53
	movq	%rsi, 8248(%rbp,%rdx,8)
	jmp	.LB53
.LB64:
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	jmp	.LB53
.LB60:
	ret
	.size	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset, .-_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
