_ZN12_GLOBAL__N_18Emission4pushE9StackSlot11StackOffset:
	movq	%rdi, %rax
	movq	%rsi, %rcx
	movq	%rdx, %rdi
	movq	%rsi, %r9
	shrq	$32, %r9
	movq	%rsi, %r8
	shrq	$40, %r8
	movq	24(%rax), %rsi
	movq	32(%rax), %rdx
	leaq	1(%rdx), %r10
	movq	%r10, 32(%rax)
	movq	%rcx, (%rsi,%rdx,8)
	movq	48(%rax), %rdx
	leaq	1(%rdx), %rsi
	movq	%rsi, 48(%rax)
	leaq	(%rdx,%rdx,2), %rdx
	salq	$2, %rdx
	addq	40(%rax), %rdx
	testb	%r8b, %r8b
	setne	%sil
	testb	%r9b, %r9b
	sete	%r10b
	andl	%r10d, %esi
	addl	$3, %esi
	movb	%sil, (%rdx)
	movb	$0, 1(%rdx)
	movl	%ecx, 4(%rdx)
	movb	%r9b, 8(%rdx)
	movb	%r8b, 9(%rdx)
	cmpq	$-1, 8248(%rax,%rdi,8)
	je	.LB.Emission.push.0
	subq	$8, %rsp
	movl	$1, %edi
	call	exit
.LB.Emission.push.0:
	movq	32(%rax), %rcx
	leaq	-1(%rcx), %rdx
	movq	%rdi, 56(%rax,%rdx,8)
	movq	%rdx, 8248(%rax,%rdi,8)
	movl	$0, %eax
	ret
	.size	_ZN12_GLOBAL__N_18Emission4pushE9StackSlot11StackOffset, .-_ZN12_GLOBAL__N_18Emission4pushE9StackSlot11StackOffset
