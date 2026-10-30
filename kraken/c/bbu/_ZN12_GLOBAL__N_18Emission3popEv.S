_ZN12_GLOBAL__N_18Emission3popEv:
	movq	32(%rdi), %rax
	movl	$2, %edx
	testq	%rax, %rax
	je	.LB.Emission.pop.1
	leaq	-1(%rax), %rdx
	movq	%rdx, 32(%rdi)
	movq	48(%rdi), %rax
	leaq	1(%rax), %rcx
	movq	%rcx, 48(%rdi)
	leaq	(%rax,%rax,2), %rax
	salq	$2, %rax
	addq	40(%rdi), %rax
	movb	$2, (%rax)
	movb	$0, 1(%rax)
	movl	$0, 4(%rax)
	movb	$1, 8(%rax)
	movb	$5, 9(%rax)
	movq	56(%rdi,%rdx,8), %rax
	cmpq	$-1, %rax
	je	.LB.Emission.pop.0
	movq	$-1, 8248(%rdi,%rax,8)
.LB.Emission.pop.0:
	movl	$0, %edx
.LB.Emission.pop.1:
	movl	%edx, %eax
	ret
	.size	_ZN12_GLOBAL__N_18Emission3popEv, .-_ZN12_GLOBAL__N_18Emission3popEv
