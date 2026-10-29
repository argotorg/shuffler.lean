push:
	movq	%rdi, %rax
	movq	%rsi, %rcx
	cmpq	$-1, 8264(%rdi,%rdx,8)
	jne	.LB22
	movq	(%rdi), %rsi
	movq	%rdx, 72(%rdi,%rsi,8)
	movq	%rsi, 8264(%rdi,%rdx,8)
	movq	%rcx, %rsi
	shrq	$32, %rsi
	movq	%rcx, %rdx
	shrq	$40, %rdx
	cmpb	$1, %dl
	movl	$3, %edx
	sbbb	$-1, %dl
	testb	%sil, %sil
	movl	$3, %esi
	cmovne	%esi, %edx
	movq	16(%rdi), %rsi
	leaq	(%rsi,%rsi,2), %rdi
	movq	48(%rax), %rsi
	leaq	(%rsi,%rdi,4), %rsi
	movb	%dl, (%rsi)
	movb	$0, 1(%rsi)
	movq	%rcx, 4(%rsi)
	addq	$1, 16(%rax)
	movq	(%rax), %rsi
	movq	64(%rax), %rdx
	movq	%rcx, (%rdx,%rsi,8)
	addq	$1, (%rax)
	movl	$0, %eax
	ret
.LB22:
	movq	$-2, %rax
	ret
	.size	push, .-push
