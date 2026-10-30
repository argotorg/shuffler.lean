_ZN12_GLOBAL__N_18Emission21permuteAtLowestHeightEv:
	subq	$24584, %rsp
	movq	32(%rdi), %rcx
	testq	%rcx, %rcx
	je	.LB.Emission.permuteAtLowestHeight.4
	movl	$0, %eax
	movl	$0, %esi
	movl	$0, %r8d
.LB.Emission.permuteAtLowestHeight.0:
	movq	56(%rdi,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB.Emission.permuteAtLowestHeight.5
	cmpq	8(%rdi), %rax
	jnb	.LB.Emission.permuteAtLowestHeight.5
	movq	16464(%rdi), %r9
	movq	8192(%r9,%rax,8), %r9
	cmpq	%rcx, %rdx
	je	.LB.Emission.permuteAtLowestHeight.1
	jb	.LB.Emission.permuteAtLowestHeight.7
.LB.Emission.permuteAtLowestHeight.1:
	cmpq	$-1, %r9
	jne	.LB.Emission.permuteAtLowestHeight.8
	movq	%rax, 16384(%rsp,%rax,8)
.LB.Emission.permuteAtLowestHeight.2:
	addq	$1, %rax
	cmpq	%rcx, %rax
	jne	.LB.Emission.permuteAtLowestHeight.0
	movl	$2, %eax
	cmpq	%rsi, %r8
	jne	.LB.Emission.permuteAtLowestHeight.6
	testq	%rsi, %rsi
	je	.LB.Emission.permuteAtLowestHeight.4
	salq	$3, %rsi
	movl	$0, %eax
	.p2align 5
.LB.Emission.permuteAtLowestHeight.3:
	movq	(%rsp,%rax), %rdx
	movq	8192(%rsp,%rax), %rcx
	movq	%rcx, 16384(%rsp,%rdx,8)
	addq	$8, %rax
	cmpq	%rax, %rsi
	jne	.LB.Emission.permuteAtLowestHeight.3
.LB.Emission.permuteAtLowestHeight.4:
	leaq	16384(%rsp), %rsi
	call	_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE
	jmp	.LB.Emission.permuteAtLowestHeight.6
.LB.Emission.permuteAtLowestHeight.5:
	movl	$2, %eax
.LB.Emission.permuteAtLowestHeight.6:
	addq	$24584, %rsp
	ret
.LB.Emission.permuteAtLowestHeight.7:
	movq	%rdx, 16384(%rsp,%rax,8)
	cmpq	$-1, %r9
	jne	.LB.Emission.permuteAtLowestHeight.2
	movq	%rax, 8192(%rsp,%r8,8)
	leaq	1(%r8), %r8
	jmp	.LB.Emission.permuteAtLowestHeight.2
.LB.Emission.permuteAtLowestHeight.8:
	movq	%rax, (%rsp,%rsi,8)
	leaq	1(%rsi), %rsi
	jmp	.LB.Emission.permuteAtLowestHeight.2
	.size	_ZN12_GLOBAL__N_18Emission21permuteAtLowestHeightEv, .-_ZN12_GLOBAL__N_18Emission21permuteAtLowestHeightEv
