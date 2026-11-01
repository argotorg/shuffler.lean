	.file	"test_wrappers.cpp"
	.text
	.align 2
	.type	_ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot, @function
_ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot:
	movq	%rsi, %rdx
	shrq	$32, %rdx
	movl	$0, %eax
	testb	%dl, %dl
	jne	.LB.Emission.isSpilled.0
	movq	%rsi, %rdx
	shrq	$40, %rdx
	testb	%dl, %dl
	je	.LB.Emission.isSpilled.0
	movl	%esi, %esi
	movq	16(%rdi), %rax
	cmpb	$0, (%rax,%rsi)
	setne	%al
.LB.Emission.isSpilled.0:
	ret
	.size	_ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot, .-_ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot
	.align 2
	.type	_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot, @function
_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot:
	movq	32(%rdi), %rax
	.p2align 5
.LB.Emission.shallowestCopyPosition.0:
	testq	%rax, %rax
	je	.LB.Emission.shallowestCopyPosition.1
	subq	$1, %rax
	movq	24(%rdi), %rdx
	movq	%rsi, %rcx
	xorq	(%rdx,%rax,8), %rcx
	movq	%rcx, %rdx
	salq	$16, %rdx
	jne	.LB.Emission.shallowestCopyPosition.0
	ret
.LB.Emission.shallowestCopyPosition.1:
	movq	$-1, %rax
.LB.Emission.shallowestCopyPosition.2:
	ret
	.size	_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot, .-_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission4pushE9StackSlot11StackOffset, @function
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
	movl	$2, %edx
	cmpq	$-1, 8248(%rax,%rdi,8)
	jne	.LB.Emission.push.0
	movq	32(%rax), %rcx
	leaq	-1(%rcx), %rdx
	movq	%rdi, 56(%rax,%rdx,8)
	movq	%rdx, 8248(%rax,%rdi,8)
	movl	$0, %edx
.LB.Emission.push.0:
	movl	%edx, %eax
	ret
	.size	_ZN12_GLOBAL__N_18Emission4pushE9StackSlot11StackOffset, .-_ZN12_GLOBAL__N_18Emission4pushE9StackSlot11StackOffset
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission3dupE11StackOffsetS1_, @function
_ZN12_GLOBAL__N_18Emission3dupE11StackOffsetS1_:
	movq	%rdi, %rax
	movq	%rdx, %rcx
	movq	24(%rdi), %rdi
	movl	$2, %edx
	cmpb	$3, 4(%rdi,%rsi,8)
	je	.LB.Emission.dup.0
	movq	32(%rax), %rdi
	subq	%rsi, %rdi
	movq	48(%rax), %rdx
	leaq	1(%rdx), %r8
	movq	%r8, 48(%rax)
	leaq	(%rdx,%rdx,2), %rdx
	salq	$2, %rdx
	addq	40(%rax), %rdx
	movb	$1, (%rdx)
	movb	%dil, 1(%rdx)
	movl	$0, 4(%rdx)
	movb	$1, 8(%rdx)
	movb	$5, 9(%rdx)
	movq	24(%rax), %rdx
	movq	32(%rax), %rdi
	movq	(%rdx,%rsi,8), %rsi
	movq	%rsi, (%rdx,%rdi,8)
	movq	32(%rax), %rsi
	leaq	1(%rsi), %rdx
	movq	%rdx, 32(%rax)
	movl	$2, %edx
	cmpq	$-1, 8248(%rax,%rcx,8)
	jne	.LB.Emission.dup.0
	movq	%rcx, 56(%rax,%rsi,8)
	movq	%rsi, 8248(%rax,%rcx,8)
	movl	$0, %edx
.LB.Emission.dup.0:
	movl	%edx, %eax
	ret
	.size	_ZN12_GLOBAL__N_18Emission3dupE11StackOffsetS1_, .-_ZN12_GLOBAL__N_18Emission3dupE11StackOffsetS1_
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission7produceE11StackOffset, @function
_ZN12_GLOBAL__N_18Emission7produceE11StackOffset:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$8, %rsp
	movq	%rdi, %rbx
	movq	%rsi, %r12
	leaq	0(,%rsi,8), %r14
	movq	%r14, %rdx
	addq	(%rdi), %rdx
	movzbl	5(%rdx), %r15d
	movzbl	4(%rdx), %r13d
	movzbl	%r15b, %eax
	salq	$40, %rax
	movabsq	$-280375465082881, %rbp
	andq	(%rdx), %rbp
	orq	%rax, %rbp
	movq	%rbp, %rsi
	call	_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot
	movq	%rax, (%rsp)
	cmpb	$1, %r13b
	je	.LB.Emission.produce.4
	movq	(%rsp), %rax
	cmpq	$-1, %rax
	je	.LB.Emission.produce.0
	notq	%rax
	addq	32(%rbx), %rax
	cmpq	$15, %rax
	jbe	.LB.Emission.produce.5
.LB.Emission.produce.0:
	cmpb	$2, %r13b
	je	.LB.Emission.produce.1
	testb	%r15b, %r15b
	jne	.LB.Emission.produce.6
.LB.Emission.produce.1:
	movq	%r12, %rdx
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission4pushE9StackSlot11StackOffset
.LB.Emission.produce.2:
	testb	%al, %al
	jne	.LB.Emission.produce.3
	movq	32(%rbx), %rcx
	leaq	-1(%rcx), %rdx
	cmpq	%rdx, 8248(%rbx,%r14)
	jne	.LB.Emission.produce.7
	subq	$1, 16440(%rbx)
.LB.Emission.produce.3:
	addq	$8, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB.Emission.produce.4:
	movq	%r12, %rdx
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission4pushE9StackSlot11StackOffset
	jmp	.LB.Emission.produce.2
.LB.Emission.produce.5:
	movq	%r12, %rdx
	movq	(%rsp), %rsi
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission3dupE11StackOffsetS1_
	jmp	.LB.Emission.produce.2
.LB.Emission.produce.6:
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	call	_ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot
	testb	%al, %al
	jne	.LB.Emission.produce.1
	movl	$2, %eax
	cmpq	$-1, (%rsp)
	je	.LB.Emission.produce.3
	movq	$-16, %rdx
	movq	(%rsp), %rcx
	subq	%rcx, %rdx
	movl	$2, %eax
	addq	32(%rbx), %rdx
	je	.LB.Emission.produce.3
	movq	%rcx, 16448(%rbx)
	movq	%rdx, 16456(%rbx)
	movl	$1, %eax
	jmp	.LB.Emission.produce.3
.LB.Emission.produce.7:
	movl	$2, %eax
	jmp	.LB.Emission.produce.3
	.size	_ZN12_GLOBAL__N_18Emission7produceE11StackOffset, .-_ZN12_GLOBAL__N_18Emission7produceE11StackOffset
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset, @function
_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset:
	movq	%rdi, %rax
	movq	%rsi, %rdx
	movq	32(%rdi), %rsi
	movl	$2, %ecx
	cmpq	%rsi, %rdx
	jnb	.LB.Emission.swapWith.2
	leaq	0(,%rdx,8), %rdi
	cmpq	56(%rax,%rdx,8), %rdx
	je	.LB.Emission.swapWith.2
	movq	%rsi, %rcx
	subq	%rdx, %rcx
	leaq	-2(%rcx), %r8
	movl	$2, %ecx
	cmpq	$15, %r8
	ja	.LB.Emission.swapWith.2
	movq	24(%rax), %r8
	leaq	(%r8,%rdi), %rcx
	movl	(%rcx), %r10d
	movzbl	4(%rcx), %r9d
	movzbl	5(%rcx), %edi
	movq	-8(%r8,%rsi,8), %rsi
	movq	%rsi, (%rcx)
	movq	32(%rax), %rsi
	movq	24(%rax), %rcx
	leaq	-8(%rcx,%rsi,8), %rcx
	movl	%r10d, (%rcx)
	movb	%r9b, 4(%rcx)
	movb	%dil, 5(%rcx)
	movq	%rdx, %rsi
	notq	%rsi
	addq	32(%rax), %rsi
	movq	48(%rax), %rcx
	leaq	1(%rcx), %rdi
	movq	%rdi, 48(%rax)
	leaq	(%rcx,%rcx,2), %rcx
	salq	$2, %rcx
	addq	40(%rax), %rcx
	movb	$0, (%rcx)
	movb	%sil, 1(%rcx)
	movl	$0, 4(%rcx)
	movb	$1, 8(%rcx)
	movb	$5, 9(%rcx)
	movq	32(%rax), %rdi
	leaq	-1(%rdi), %rcx
	movq	56(%rax,%rdx,8), %rsi
	movq	56(%rax,%rcx,8), %rdi
	movq	%rdi, 56(%rax,%rdx,8)
	movq	%rsi, 56(%rax,%rcx,8)
	movq	56(%rax,%rdx,8), %rsi
	cmpq	$-1, %rsi
	je	.LB.Emission.swapWith.0
	movq	%rdx, 8248(%rax,%rsi,8)
.LB.Emission.swapWith.0:
	movq	56(%rax,%rcx,8), %rdx
	cmpq	$-1, %rdx
	je	.LB.Emission.swapWith.1
	movq	%rcx, 8248(%rax,%rdx,8)
.LB.Emission.swapWith.1:
	movl	$0, %ecx
.LB.Emission.swapWith.2:
	movl	%ecx, %eax
	ret
	.size	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset, .-_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset, @function
_ZN12_GLOBAL__N_18Emission8generateE11StackOffset:
	movl	$2, %eax
	cmpq	8(%rdi), %rsi
	jnb	.LB.Emission.generate.4
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movq	%rsi, %rbx
	call	_ZN12_GLOBAL__N_18Emission7produceE11StackOffset
	testb	%al, %al
	jne	.LB.Emission.generate.0
	movq	32(%rbp), %rdx
	leaq	1(%rbx), %rcx
	cmpq	%rdx, %rcx
	jnb	.LB.Emission.generate.0
	cmpq	%rbx, 56(%rbp,%rbx,8)
	je	.LB.Emission.generate.0
	movq	24(%rbp), %rdi
	leaq	-1(%rdx), %rsi
	movq	(%rdi,%rsi,8), %rcx
	xorq	(%rdi,%rbx,8), %rcx
	salq	$16, %rcx
	je	.LB.Emission.generate.1
	subq	%rbx, %rdx
	subq	$1, %rdx
	cmpq	$16, %rdx
	jbe	.LB.Emission.generate.3
.LB.Emission.generate.0:
	popq	%rbx
	popq	%rbp
	ret
.LB.Emission.generate.1:
	movq	56(%rbp,%rbx,8), %rdx
	movq	56(%rbp,%rsi,8), %rcx
	movq	%rcx, 56(%rbp,%rbx,8)
	movq	%rdx, 56(%rbp,%rsi,8)
	movq	56(%rbp,%rbx,8), %rdx
	cmpq	$-1, %rdx
	je	.LB.Emission.generate.2
	movq	%rbx, 8248(%rbp,%rdx,8)
.LB.Emission.generate.2:
	movq	56(%rbp,%rsi,8), %rdx
	cmpq	$-1, %rdx
	je	.LB.Emission.generate.0
	movq	%rsi, 8248(%rbp,%rdx,8)
	jmp	.LB.Emission.generate.0
.LB.Emission.generate.3:
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	jmp	.LB.Emission.generate.0
.LB.Emission.generate.4:
	ret
	.size	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset, .-_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE, @function
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
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv, @function
_ZN12_GLOBAL__N_18Emission13buildBottomUpEv:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$8216, %rsp
	movq	%rdi, %r12
	movq	8(%rdi), %r13
	testq	%r13, %r13
	je	.LB.Emission.buildBottomUp.31
	movl	$0, %r14d
	jmp	.LB.Emission.buildBottomUp.26
.LB.Emission.buildBottomUp.0:
	movl	$2, %eax
	cmpq	%r13, %r15
	jne	.LB.Emission.buildBottomUp.13
.LB.Emission.buildBottomUp.1:
	movq	56(%r12,%rdx,8), %rax
	cmpq	$-1, %rax
	je	.LB.Emission.buildBottomUp.2
	movq	%rax, 16(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rdx, %r13
	jne	.LB.Emission.buildBottomUp.1
	leaq	16(%rsp), %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE
	jmp	.LB.Emission.buildBottomUp.13
.LB.Emission.buildBottomUp.2:
	movl	$2, %eax
	jmp	.LB.Emission.buildBottomUp.13
.LB.Emission.buildBottomUp.3:
	movq	%rax, 16448(%r12)
	subq	$16, %rcx
	movq	%rcx, 16456(%r12)
	movl	$1, %eax
	jmp	.LB.Emission.buildBottomUp.13
	.p2align 5
.LB.Emission.buildBottomUp.4:
	addq	$1, %rbx
	cmpq	%r13, %rbx
	je	.LB.Emission.buildBottomUp.6
.LB.Emission.buildBottomUp.5:
	cmpq	$-1, 8248(%r12,%rbx,8)
	jne	.LB.Emission.buildBottomUp.4
	movq	(%r12), %rax
	leaq	(%rax,%rbx,8), %rax
	movq	(%rax), %rbp
	movzbl	4(%rax), %edx
	cmpb	$1, %dl
	je	.LB.Emission.buildBottomUp.4
	movzbl	5(%rax), %ecx
	movzbl	%dl, %eax
	salq	$32, %rax
	movabsq	$-1095216660481, %rsi
	andq	%rsi, %rbp
	orq	%rax, %rbp
	testb	%cl, %cl
	je	.LB.Emission.buildBottomUp.4
	cmpb	$2, %dl
	je	.LB.Emission.buildBottomUp.4
	movzbl	%cl, %ecx
	salq	$40, %rcx
	movabsq	$-280375465082881, %rax
	andq	%rax, %rbp
	orq	%rcx, %rbp
	movq	%rbp, %rsi
	movq	%r12, %rdi
	call	_ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot
	testb	%al, %al
	jne	.LB.Emission.buildBottomUp.4
	movq	%rbp, %rsi
	movq	%r12, %rdi
	call	_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot
	cmpq	$-1, %rax
	je	.LB.Emission.buildBottomUp.4
	movq	%r15, %rcx
	subq	%rax, %rcx
	leaq	-1(%rcx), %rdx
	cmpq	$15, %rdx
	ja	.LB.Emission.buildBottomUp.3
	cmpq	%r14, %rax
	sete	%al
	cmpq	$15, %rdx
	setne	%dl
	orb	%dl, %al
	jne	.LB.Emission.buildBottomUp.4
	movq	8(%rsp), %rax
	cmpq	$-1, %rax
	cmove	%rbx, %rax
	movq	%rax, 8(%rsp)
	jmp	.LB.Emission.buildBottomUp.4
.LB.Emission.buildBottomUp.6:
	movq	8(%rsp), %rdi
	cmpq	$-1, %rdi
	sete	%al
	cmpq	%r14, %rdi
	je	.LB.Emission.buildBottomUp.7
	testb	%al, %al
	je	.LB.Emission.buildBottomUp.14
.LB.Emission.buildBottomUp.7:
	cmpq	%r13, %r15
	setb	%cl
	cmpq	%r15, %r14
	setb	%dl
	testb	%dl, %cl
	je	.LB.Emission.buildBottomUp.8
	testb	%al, %al
	jne	.LB.Emission.buildBottomUp.15
.LB.Emission.buildBottomUp.8:
	leaq	0(,%r14,8), %rbx
	movq	8248(%r12,%rbx), %rdx
	cmpq	$-1, %rdx
	je	.LB.Emission.buildBottomUp.16
	cmpq	%r14, %rdx
	jb	.LB.Emission.buildBottomUp.28
	movq	24(%r12), %rcx
	movq	(%rcx,%rdx,8), %rsi
	movq	%rsi, %rdi
	xorq	(%rcx,%r14,8), %rdi
	movq	%r14, %rax
	salq	$16, %rdi
	jne	.LB.Emission.buildBottomUp.18
.LB.Emission.buildBottomUp.9:
	movq	%rax, %rsi
	movq	56(%r12,%rax,8), %rcx
	movq	56(%r12,%rdx,8), %rdi
	movq	%rdi, 56(%r12,%rax,8)
	movq	%rcx, 56(%r12,%rdx,8)
	movq	56(%r12,%rax,8), %rcx
	cmpq	$-1, %rcx
	je	.LB.Emission.buildBottomUp.10
	movq	%rax, 8248(%r12,%rcx,8)
.LB.Emission.buildBottomUp.10:
	movq	56(%r12,%rdx,8), %rcx
	cmpq	$-1, %rcx
	je	.LB.Emission.buildBottomUp.11
	movq	%rdx, 8248(%r12,%rcx,8)
.LB.Emission.buildBottomUp.11:
	cmpq	%rax, %r14
	je	.LB.Emission.buildBottomUp.24
	leaq	-1(%r15), %rdx
	cmpq	%rax, %rdx
	je	.LB.Emission.buildBottomUp.12
	subq	%rax, %r15
	leaq	-1(%r15), %rdx
	cmpq	$16, %rdx
	ja	.LB.Emission.buildBottomUp.22
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	testb	%al, %al
	jne	.LB.Emission.buildBottomUp.13
.LB.Emission.buildBottomUp.12:
	movq	32(%r12), %rax
	cmpq	%rax, %r14
	jnb	.LB.Emission.buildBottomUp.30
	cmpq	%r14, 56(%r12,%rbx)
	jne	.LB.Emission.buildBottomUp.17
	movl	$2, %eax
.LB.Emission.buildBottomUp.13:
	addq	$8216, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB.Emission.buildBottomUp.14:
	movq	%r15, %rax
	subq	%r14, %rax
	cmpq	$15, %rax
	ja	.LB.Emission.buildBottomUp.8
	movq	8(%rsp), %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
	testb	%al, %al
	jne	.LB.Emission.buildBottomUp.13
	subq	$1, %r14
	jmp	.LB.Emission.buildBottomUp.25
.LB.Emission.buildBottomUp.15:
	cmpq	$-1, 8248(%r12,%r15,8)
	jne	.LB.Emission.buildBottomUp.8
	movq	%r15, %rax
	subq	%r14, %rax
	cmpq	$15, %rax
	ja	.LB.Emission.buildBottomUp.8
	movq	%r15, %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
	testb	%al, %al
	jne	.LB.Emission.buildBottomUp.13
	subq	$1, %r14
	jmp	.LB.Emission.buildBottomUp.25
.LB.Emission.buildBottomUp.16:
	movq	%r14, %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
	testb	%al, %al
	jne	.LB.Emission.buildBottomUp.13
	movq	32(%r12), %rax
	cmpq	%rax, %r14
	jnb	.LB.Emission.buildBottomUp.29
	cmpq	%r14, 56(%r12,%rbx)
	je	.LB.Emission.buildBottomUp.25
.LB.Emission.buildBottomUp.17:
	leaq	-1(%rax), %rdx
	cmpq	%r14, %rdx
	je	.LB.Emission.buildBottomUp.25
	subq	%r14, %rax
	leaq	-1(%rax), %rdx
	cmpq	$16, %rdx
	ja	.LB.Emission.buildBottomUp.23
	movq	%r14, %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	testb	%al, %al
	je	.LB.Emission.buildBottomUp.25
	jmp	.LB.Emission.buildBottomUp.13
.LB.Emission.buildBottomUp.18:
	leaq	-1(%r15), %rax
	cmpq	%rax, %rdx
	jb	.LB.Emission.buildBottomUp.20
	movq	%rdx, %rax
	jmp	.LB.Emission.buildBottomUp.9
	.p2align 5
.LB.Emission.buildBottomUp.19:
	subq	$1, %rax
	cmpq	%rax, %rdx
	jnb	.LB.Emission.buildBottomUp.21
.LB.Emission.buildBottomUp.20:
	movq	%rsi, %rdi
	xorq	(%rcx,%rax,8), %rdi
	salq	$16, %rdi
	jne	.LB.Emission.buildBottomUp.19
	cmpq	%rax, 56(%r12,%rax,8)
	je	.LB.Emission.buildBottomUp.19
	xorq	(%rcx,%rax,8), %rsi
	salq	$16, %rsi
	je	.LB.Emission.buildBottomUp.9
	movl	$2, %eax
	jmp	.LB.Emission.buildBottomUp.13
.LB.Emission.buildBottomUp.21:
	movq	%rdx, %rax
	jmp	.LB.Emission.buildBottomUp.9
.LB.Emission.buildBottomUp.22:
	movq	%rax, 16448(%r12)
	subq	$17, %r15
	movq	%r15, 16456(%r12)
	movl	$1, %eax
	jmp	.LB.Emission.buildBottomUp.13
.LB.Emission.buildBottomUp.23:
	movq	%r14, 16448(%r12)
	subq	$17, %rax
	movq	%rax, 16456(%r12)
	movl	$1, %eax
	jmp	.LB.Emission.buildBottomUp.13
.LB.Emission.buildBottomUp.24:
	movq	%rax, %r14
.LB.Emission.buildBottomUp.25:
	addq	$1, %r14
	movq	8(%r12), %r13
	cmpq	%r13, %r14
	jnb	.LB.Emission.buildBottomUp.31
.LB.Emission.buildBottomUp.26:
	movq	32(%r12), %r15
	cmpq	%r15, %r14
	jnb	.LB.Emission.buildBottomUp.27
	cmpq	%r14, 56(%r12,%r14,8)
	je	.LB.Emission.buildBottomUp.25
.LB.Emission.buildBottomUp.27:
	movq	16440(%r12), %rdx
	testq	%rdx, %rdx
	je	.LB.Emission.buildBottomUp.0
	movq	%r14, %rbx
	movq	$-1, 8(%rsp)
	movl	$1, %eax
	cmpq	%r13, %r14
	jb	.LB.Emission.buildBottomUp.5
	jmp	.LB.Emission.buildBottomUp.7
.LB.Emission.buildBottomUp.28:
	movl	$2, %eax
	jmp	.LB.Emission.buildBottomUp.13
.LB.Emission.buildBottomUp.29:
	movl	$2, %eax
	jmp	.LB.Emission.buildBottomUp.13
.LB.Emission.buildBottomUp.30:
	movl	$2, %eax
	jmp	.LB.Emission.buildBottomUp.13
.LB.Emission.buildBottomUp.31:
	cmpq	%r13, 32(%r12)
	setne	%al
	addl	%eax, %eax
	jmp	.LB.Emission.buildBottomUp.13
	.size	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv, .-_ZN12_GLOBAL__N_18Emission13buildBottomUpEv
	.align 2
	.type	_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot, @function
_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot:
	movq	%rsi, %rdx
	shrq	$32, %rdx
	movl	$2, %eax
	testb	%dl, %dl
	jne	.LB.SpillSet.add.1
	movq	%rsi, %rdx
	shrq	$40, %rdx
	testb	%dl, %dl
	je	.LB.SpillSet.add.1
	movl	%esi, %esi
	addq	(%rdi), %rsi
	movzbl	(%rsi), %eax
	testb	%al, %al
	jne	.LB.SpillSet.add.0
	movb	$1, (%rsi)
	ret
.LB.SpillSet.add.0:
	movl	$2, %eax
.LB.SpillSet.add.1:
	ret
	.size	_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot, .-_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot
	.align 2
	.type	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_, @function
_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_:
	movq	32(%rdi), %rax
	movzbl	(%rax,%rsi), %eax
	testb	%al, %al
	jne	.LB.MappingBuilder.map.0
	movq	48(%rdi), %rcx
	cmpq	$-1, (%rcx,%rsi,8)
	jne	.LB.MappingBuilder.map.1
	cmpq	$-1, 8192(%rcx,%rdx,8)
	jne	.LB.MappingBuilder.map.2
	movq	%rdx, (%rcx,%rsi,8)
	movq	%rsi, 8192(%rcx,%rdx,8)
	ret
.LB.MappingBuilder.map.0:
	movl	$2, %eax
	ret
.LB.MappingBuilder.map.1:
	movl	$2, %eax
	ret
.LB.MappingBuilder.map.2:
	movl	$2, %eax
	ret
	.size	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_, .-_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
	.align 2
	.type	_ZNK12_GLOBAL__N_114MappingBuilder11closestCopyE11StackOffsetNS0_12CopyLocationE, @function
_ZNK12_GLOBAL__N_114MappingBuilder11closestCopyE11StackOffsetNS0_12CopyLocationE:
	movq	%rsi, %r10
	movq	8(%rdi), %rsi
	testq	%rsi, %rsi
	je	.LB.MappingBuilder.closestCopy.5
	pushq	%r15
	pushq	%r14
	pushq	%rbp
	pushq	%rbx
	cmpb	$1, %dl
	sete	%bpl
	movq	16(%rdi), %rbx
	movq	(%rdi), %r9
	movq	(%rbx,%r10,8), %r8
	movq	%r10, %rcx
	negq	%rcx
	movl	$0, %eax
	movq	$-1, %r11
	jmp	.LB.MappingBuilder.closestCopy.2
.LB.MappingBuilder.closestCopy.0:
	cmpb	%dl, %bpl
	je	.LB.MappingBuilder.closestCopy.3
	.p2align 5
.LB.MappingBuilder.closestCopy.1:
	addq	$1, %rax
	addq	$1, %rcx
	cmpq	%rsi, %rax
	je	.LB.MappingBuilder.closestCopy.6
.LB.MappingBuilder.closestCopy.2:
	movq	%r8, %rdx
	xorq	(%r9,%rax,8), %rdx
	salq	$16, %rdx
	jne	.LB.MappingBuilder.closestCopy.1
	movq	32(%rdi), %rdx
	cmpb	$0, (%rdx,%rax)
	jne	.LB.MappingBuilder.closestCopy.1
	movq	48(%rdi), %rdx
	cmpq	$-1, (%rdx,%rax,8)
	jne	.LB.MappingBuilder.closestCopy.1
	movl	$0, %edx
	cmpq	24(%rdi), %rax
	jnb	.LB.MappingBuilder.closestCopy.0
	cmpb	$1, 4(%rbx,%rax,8)
	sete	%dl
	jmp	.LB.MappingBuilder.closestCopy.0
.LB.MappingBuilder.closestCopy.3:
	cmpq	$-1, %r11
	je	.LB.MappingBuilder.closestCopy.4
	movq	%r10, %rdx
	subq	%rax, %rdx
	cmpq	%rax, %r10
	cmovb	%rcx, %rdx
	movq	%r11, %r14
	subq	%r10, %r14
	movq	%r10, %r15
	subq	%r11, %r15
	cmpq	%r11, %r10
	cmovnb	%r15, %r14
	cmpq	%rdx, %r14
	cmovnb	%rax, %r11
	jmp	.LB.MappingBuilder.closestCopy.1
.LB.MappingBuilder.closestCopy.4:
	movq	%rax, %r11
	jmp	.LB.MappingBuilder.closestCopy.1
.LB.MappingBuilder.closestCopy.5:
	movq	$-1, %r11
	movq	%r11, %rax
	ret
.LB.MappingBuilder.closestCopy.6:
	movq	%r11, %rax
	popq	%rbx
	popq	%rbp
	popq	%r14
	popq	%r15
	ret
	.size	_ZNK12_GLOBAL__N_114MappingBuilder11closestCopyE11StackOffsetNS0_12CopyLocationE, .-_ZNK12_GLOBAL__N_114MappingBuilder11closestCopyE11StackOffsetNS0_12CopyLocationE
	.align 2
	.type	_ZN12_GLOBAL__N_114MappingBuilder10mapInPlaceEv, @function
_ZN12_GLOBAL__N_114MappingBuilder10mapInPlaceEv:
	movq	8(%rdi), %rax
	movq	24(%rdi), %rdx
	cmpq	%rdx, %rax
	cmova	%rdx, %rax
	testq	%rax, %rax
	je	.LB.MappingBuilder.mapInPlace.4
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movl	$0, %ebx
	jmp	.LB.MappingBuilder.mapInPlace.1
	.p2align 6
.LB.MappingBuilder.mapInPlace.0:
	addq	$1, %rbx
	movq	8(%rbp), %rax
	movq	24(%rbp), %rdx
	cmpq	%rdx, %rax
	cmova	%rdx, %rax
	cmpq	%rax, %rbx
	jnb	.LB.MappingBuilder.mapInPlace.2
.LB.MappingBuilder.mapInPlace.1:
	movq	16(%rbp), %rax
	movq	0(%rbp), %rdx
	movq	(%rax,%rbx,8), %rax
	xorq	(%rdx,%rbx,8), %rax
	salq	$16, %rax
	jne	.LB.MappingBuilder.mapInPlace.0
	movq	32(%rbp), %rax
	cmpb	$0, (%rax,%rbx)
	jne	.LB.MappingBuilder.mapInPlace.0
	movq	48(%rbp), %rax
	cmpq	$-1, (%rax,%rbx,8)
	jne	.LB.MappingBuilder.mapInPlace.0
	movq	%rbx, %rdx
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
	testb	%al, %al
	je	.LB.MappingBuilder.mapInPlace.0
	jmp	.LB.MappingBuilder.mapInPlace.3
.LB.MappingBuilder.mapInPlace.2:
	movl	$0, %eax
.LB.MappingBuilder.mapInPlace.3:
	popq	%rbx
	popq	%rbp
	ret
.LB.MappingBuilder.mapInPlace.4:
	movl	$0, %eax
	ret
	.size	_ZN12_GLOBAL__N_114MappingBuilder10mapInPlaceEv, .-_ZN12_GLOBAL__N_114MappingBuilder10mapInPlaceEv
	.align 2
	.type	_ZN12_GLOBAL__N_114MappingBuilder16mapClosestCopiesEv, @function
_ZN12_GLOBAL__N_114MappingBuilder16mapClosestCopiesEv:
	cmpq	$0, 24(%rdi)
	je	.LB.MappingBuilder.mapClosestCopies.4
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movl	$0, %ebx
	jmp	.LB.MappingBuilder.mapClosestCopies.1
	.p2align 6
.LB.MappingBuilder.mapClosestCopies.0:
	addq	$1, %rbx
	cmpq	24(%rbp), %rbx
	jnb	.LB.MappingBuilder.mapClosestCopies.2
.LB.MappingBuilder.mapClosestCopies.1:
	leaq	0(,%rbx,8), %rdx
	movq	48(%rbp), %rax
	cmpq	$-1, 8192(%rax,%rbx,8)
	jne	.LB.MappingBuilder.mapClosestCopies.0
	movq	16(%rbp), %rax
	cmpb	$1, 4(%rax,%rdx)
	je	.LB.MappingBuilder.mapClosestCopies.0
	movl	$0, %edx
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	_ZNK12_GLOBAL__N_114MappingBuilder11closestCopyE11StackOffsetNS0_12CopyLocationE
	cmpq	$-1, %rax
	je	.LB.MappingBuilder.mapClosestCopies.0
	movq	%rbx, %rdx
	movq	%rax, %rsi
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
	testb	%al, %al
	je	.LB.MappingBuilder.mapClosestCopies.0
	jmp	.LB.MappingBuilder.mapClosestCopies.3
.LB.MappingBuilder.mapClosestCopies.2:
	movl	$0, %eax
.LB.MappingBuilder.mapClosestCopies.3:
	popq	%rbx
	popq	%rbp
	ret
.LB.MappingBuilder.mapClosestCopies.4:
	movl	$0, %eax
	ret
	.size	_ZN12_GLOBAL__N_114MappingBuilder16mapClosestCopiesEv, .-_ZN12_GLOBAL__N_114MappingBuilder16mapClosestCopiesEv
	.align 2
	.type	_ZN12_GLOBAL__N_114MappingBuilder21mapWildcardSlotCopiesEv, @function
_ZN12_GLOBAL__N_114MappingBuilder21mapWildcardSlotCopiesEv:
	cmpq	$0, 24(%rdi)
	je	.LB.MappingBuilder.mapWildcardSlotCopies.5
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movl	$0, %ebx
	jmp	.LB.MappingBuilder.mapWildcardSlotCopies.2
.LB.MappingBuilder.mapWildcardSlotCopies.0:
	movq	%rbx, %rdx
	movq	%rax, %rsi
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
	testb	%al, %al
	jne	.LB.MappingBuilder.mapWildcardSlotCopies.4
	.p2align 6
.LB.MappingBuilder.mapWildcardSlotCopies.1:
	addq	$1, %rbx
	cmpq	24(%rbp), %rbx
	jnb	.LB.MappingBuilder.mapWildcardSlotCopies.3
.LB.MappingBuilder.mapWildcardSlotCopies.2:
	leaq	0(,%rbx,8), %rdx
	movq	48(%rbp), %rax
	cmpq	$-1, 8192(%rax,%rbx,8)
	jne	.LB.MappingBuilder.mapWildcardSlotCopies.1
	movq	16(%rbp), %rax
	movzbl	4(%rax,%rdx), %r12d
	cmpb	$1, %r12b
	je	.LB.MappingBuilder.mapWildcardSlotCopies.1
	movl	$1, %edx
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	_ZNK12_GLOBAL__N_114MappingBuilder11closestCopyE11StackOffsetNS0_12CopyLocationE
	cmpq	$-1, %rax
	je	.LB.MappingBuilder.mapWildcardSlotCopies.1
	cmpb	$3, %r12b
	je	.LB.MappingBuilder.mapWildcardSlotCopies.0
	movb	$1, 56(%rbp)
	cmpb	$1, 40(%rbp)
	jne	.LB.MappingBuilder.mapWildcardSlotCopies.1
	movq	%rbx, %rdx
	movq	%rax, %rsi
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
	testb	%al, %al
	je	.LB.MappingBuilder.mapWildcardSlotCopies.1
	jmp	.LB.MappingBuilder.mapWildcardSlotCopies.4
.LB.MappingBuilder.mapWildcardSlotCopies.3:
	movl	$0, %eax
.LB.MappingBuilder.mapWildcardSlotCopies.4:
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	ret
.LB.MappingBuilder.mapWildcardSlotCopies.5:
	movl	$0, %eax
	ret
	.size	_ZN12_GLOBAL__N_114MappingBuilder21mapWildcardSlotCopiesEv, .-_ZN12_GLOBAL__N_114MappingBuilder21mapWildcardSlotCopiesEv
	.align 2
	.type	_ZN12_GLOBAL__N_114MappingBuilder17keepWildcardSlotsEv, @function
_ZN12_GLOBAL__N_114MappingBuilder17keepWildcardSlotsEv:
	movq	8(%rdi), %rax
	movq	24(%rdi), %rdx
	cmpq	%rdx, %rax
	cmova	%rdx, %rax
	testq	%rax, %rax
	je	.LB.MappingBuilder.keepWildcardSlots.4
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movl	$0, %ebx
	jmp	.LB.MappingBuilder.keepWildcardSlots.1
	.p2align 6
.LB.MappingBuilder.keepWildcardSlots.0:
	addq	$1, %rbx
	movq	8(%rbp), %rax
	movq	24(%rbp), %rdx
	cmpq	%rdx, %rax
	cmova	%rdx, %rax
	cmpq	%rax, %rbx
	jnb	.LB.MappingBuilder.keepWildcardSlots.2
.LB.MappingBuilder.keepWildcardSlots.1:
	leaq	0(,%rbx,8), %rdx
	movq	16(%rbp), %rax
	cmpb	$1, 4(%rax,%rbx,8)
	jne	.LB.MappingBuilder.keepWildcardSlots.0
	movq	48(%rbp), %rax
	cmpq	$-1, 8192(%rax,%rdx)
	jne	.LB.MappingBuilder.keepWildcardSlots.0
	movq	32(%rbp), %rdx
	cmpb	$0, (%rdx,%rbx)
	jne	.LB.MappingBuilder.keepWildcardSlots.0
	cmpq	$-1, (%rax,%rbx,8)
	jne	.LB.MappingBuilder.keepWildcardSlots.0
	movq	%rbx, %rdx
	movq	%rbx, %rsi
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
	testb	%al, %al
	je	.LB.MappingBuilder.keepWildcardSlots.0
	jmp	.LB.MappingBuilder.keepWildcardSlots.3
.LB.MappingBuilder.keepWildcardSlots.2:
	movl	$0, %eax
.LB.MappingBuilder.keepWildcardSlots.3:
	popq	%rbx
	popq	%rbp
	ret
.LB.MappingBuilder.keepWildcardSlots.4:
	movl	$0, %eax
	ret
	.size	_ZN12_GLOBAL__N_114MappingBuilder17keepWildcardSlotsEv, .-_ZN12_GLOBAL__N_114MappingBuilder17keepWildcardSlotsEv
	.align 2
	.type	_ZN12_GLOBAL__N_114MappingBuilder13absorbSurplusEv, @function
_ZN12_GLOBAL__N_114MappingBuilder13absorbSurplusEv:
	cmpq	$0, 24(%rdi)
	je	.LB.MappingBuilder.absorbSurplus.8
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbp
	movl	$0, %ebx
	jmp	.LB.MappingBuilder.absorbSurplus.5
.LB.MappingBuilder.absorbSurplus.0:
	movq	%rax, %rsi
	.p2align 5
.LB.MappingBuilder.absorbSurplus.1:
	addq	$1, %rax
	addq	$1, %rdx
	cmpq	%rcx, %rax
	je	.LB.MappingBuilder.absorbSurplus.3
.LB.MappingBuilder.absorbSurplus.2:
	cmpb	$0, (%rdi,%rax)
	jne	.LB.MappingBuilder.absorbSurplus.1
	cmpq	$-1, (%r8,%rax,8)
	jne	.LB.MappingBuilder.absorbSurplus.1
	cmpq	$-1, %rsi
	je	.LB.MappingBuilder.absorbSurplus.0
	movq	%rbx, %r10
	subq	%rax, %r10
	cmpq	%rax, %rbx
	cmovb	%rdx, %r10
	movq	%rsi, %r11
	subq	%rbx, %r11
	movq	%rbx, %r9
	subq	%rsi, %r9
	cmpq	%rsi, %rbx
	cmovb	%r11, %r9
	cmpq	%r9, %r10
	cmovb	%rax, %rsi
	jmp	.LB.MappingBuilder.absorbSurplus.1
.LB.MappingBuilder.absorbSurplus.3:
	cmpq	$-1, %rsi
	je	.LB.MappingBuilder.absorbSurplus.4
	movq	%rbx, %rdx
	movq	%rbp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_
	testb	%al, %al
	jne	.LB.MappingBuilder.absorbSurplus.7
	.p2align 5
.LB.MappingBuilder.absorbSurplus.4:
	addq	$1, %rbx
	cmpq	24(%rbp), %rbx
	jnb	.LB.MappingBuilder.absorbSurplus.6
.LB.MappingBuilder.absorbSurplus.5:
	leaq	0(,%rbx,8), %rdx
	movq	16(%rbp), %rax
	cmpb	$1, 4(%rax,%rbx,8)
	jne	.LB.MappingBuilder.absorbSurplus.4
	movq	48(%rbp), %r8
	movq	8192(%r8,%rdx), %rsi
	cmpq	$-1, %rsi
	jne	.LB.MappingBuilder.absorbSurplus.4
	movq	8(%rbp), %rcx
	testq	%rcx, %rcx
	je	.LB.MappingBuilder.absorbSurplus.4
	movq	32(%rbp), %rdi
	movq	%rbx, %rdx
	negq	%rdx
	movl	$0, %eax
	jmp	.LB.MappingBuilder.absorbSurplus.2
.LB.MappingBuilder.absorbSurplus.6:
	movl	$0, %eax
.LB.MappingBuilder.absorbSurplus.7:
	popq	%rbx
	popq	%rbp
	ret
.LB.MappingBuilder.absorbSurplus.8:
	movl	$0, %eax
	ret
	.size	_ZN12_GLOBAL__N_114MappingBuilder13absorbSurplusEv, .-_ZN12_GLOBAL__N_114MappingBuilder13absorbSurplusEv
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission3popEv, @function
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
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission13removeSurplusEv, @function
_ZN12_GLOBAL__N_18Emission13removeSurplusEv:
	pushq	%rbx
	movq	%rdi, %rbx
.LB.Emission.removeSurplus.0:
	movq	32(%rbx), %r8
	testq	%r8, %r8
	je	.LB.Emission.removeSurplus.9
	leaq	-1(%r8), %rdi
	movq	%rdi, %rax
	movq	$-1, %rdx
	movq	$-1, %rsi
	jmp	.LB.Emission.removeSurplus.2
	.p2align 5
.LB.Emission.removeSurplus.1:
	subq	$1, %rax
	cmpq	$-1, %rax
	je	.LB.Emission.removeSurplus.3
.LB.Emission.removeSurplus.2:
	cmpq	$-1, 56(%rbx,%rax,8)
	jne	.LB.Emission.removeSurplus.1
	cmpq	$-1, %rdx
	cmove	%rax, %rdx
	movq	%rdi, %rcx
	subq	%rax, %rcx
	cmpq	$16, %rcx
	cmovbe	%rax, %rsi
	jmp	.LB.Emission.removeSurplus.1
.LB.Emission.removeSurplus.3:
	cmpq	$-1, %rdx
	je	.LB.Emission.removeSurplus.7
	cmpq	$-1, %rsi
	je	.LB.Emission.removeSurplus.6
	cmpq	%rdx, %rdi
	je	.LB.Emission.removeSurplus.11
	leaq	0(,%rdi,8), %r8
	movq	%rdi, %rax
	.p2align 5
.LB.Emission.removeSurplus.4:
	testq	%rax, %rax
	je	.LB.Emission.removeSurplus.10
	subq	$1, %rax
	cmpq	$-1, 56(%rbx,%rax,8)
	jne	.LB.Emission.removeSurplus.4
	movq	24(%rbx), %rcx
	movq	(%rcx,%rax,8), %rdx
	xorq	(%rcx,%r8), %rdx
	salq	$16, %rdx
	jne	.LB.Emission.removeSurplus.4
	movq	56(%rbx,%rax,8), %rdx
	movq	56(%rbx,%rdi,8), %rcx
	movq	%rcx, 56(%rbx,%rax,8)
	movq	%rdx, 56(%rbx,%rdi,8)
	movq	56(%rbx,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB.Emission.removeSurplus.5
	movq	%rax, 8248(%rbx,%rdx,8)
.LB.Emission.removeSurplus.5:
	movq	56(%rbx,%rdi,8), %rax
	cmpq	$-1, %rax
	je	.LB.Emission.removeSurplus.11
	movq	%rdi, 8248(%rbx,%rax,8)
	jmp	.LB.Emission.removeSurplus.11
.LB.Emission.removeSurplus.6:
	subq	$17, %r8
	movl	$2, %eax
	subq	%rdx, %r8
	je	.LB.Emission.removeSurplus.8
	movq	%rdx, 16448(%rbx)
	movq	%r8, 16456(%rbx)
	movl	$1, %eax
	jmp	.LB.Emission.removeSurplus.8
.LB.Emission.removeSurplus.7:
	movl	$0, %eax
.LB.Emission.removeSurplus.8:
	popq	%rbx
	ret
.LB.Emission.removeSurplus.9:
	movl	$0, %eax
	jmp	.LB.Emission.removeSurplus.8
.LB.Emission.removeSurplus.10:
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	testb	%al, %al
	jne	.LB.Emission.removeSurplus.8
.LB.Emission.removeSurplus.11:
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission3popEv
	testb	%al, %al
	je	.LB.Emission.removeSurplus.0
	jmp	.LB.Emission.removeSurplus.8
	.size	_ZN12_GLOBAL__N_18Emission13removeSurplusEv, .-_ZN12_GLOBAL__N_18Emission13removeSurplusEv
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission21permuteAtLowestHeightEv, @function
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
	.align 2
	.type	_ZNK12_GLOBAL__N_18Emission11isAvailableE11StackOffset, @function
_ZNK12_GLOBAL__N_18Emission11isAvailableE11StackOffset:
	pushq	%rbp
	pushq	%rbx
	movq	(%rdi), %rax
	leaq	(%rax,%rsi,8), %rdx
	movq	(%rdx), %rbp
	movzbl	4(%rdx), %eax
	subl	$1, %eax
	cmpb	$1, %al
	setbe	%al
	cmpb	$0, 5(%rdx)
	sete	%dl
	orb	%dl, %al
	je	.LB.Emission.isAvailable.1
.LB.Emission.isAvailable.0:
	popq	%rbx
	popq	%rbp
	ret
.LB.Emission.isAvailable.1:
	movq	%rdi, %rbx
	movq	%rbp, %rsi
	call	_ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot
	testb	%al, %al
	jne	.LB.Emission.isAvailable.0
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	call	_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot
	cmpq	$-1, %rax
	setne	%al
	jmp	.LB.Emission.isAvailable.0
	.size	_ZNK12_GLOBAL__N_18Emission11isAvailableE11StackOffset, .-_ZNK12_GLOBAL__N_18Emission11isAvailableE11StackOffset
	.align 2
	.type	_ZN12_GLOBAL__N_18Emission3runEv, @function
_ZN12_GLOBAL__N_18Emission3runEv:
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	movq	%rdi, %rbx
	call	_ZN12_GLOBAL__N_18Emission13removeSurplusEv
	testb	%al, %al
	je	.LB.Emission.run.1
.LB.Emission.run.0:
	popq	%rbx
	popq	%rbp
	popq	%r12
	ret
.LB.Emission.run.1:
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission21permuteAtLowestHeightEv
	testb	%al, %al
	jne	.LB.Emission.run.0
	movq	16440(%rbx), %rcx
	movq	8(%rbx), %r12
	movq	%rcx, %rdx
	addq	32(%rbx), %rdx
	movl	$2, %eax
	cmpq	%r12, %rdx
	jne	.LB.Emission.run.0
	testq	%r12, %r12
	je	.LB.Emission.run.7
	movl	$0, %eax
	movl	$0, %edx
	jmp	.LB.Emission.run.3
	.p2align 5
.LB.Emission.run.2:
	addq	$1, %rax
	cmpq	%rax, %r12
	je	.LB.Emission.run.9
.LB.Emission.run.3:
	cmpq	$-1, 8248(%rbx,%rax,8)
	jne	.LB.Emission.run.2
	addq	$1, %rdx
	jmp	.LB.Emission.run.2
	.p2align 4
.LB.Emission.run.4:
	addq	$1, %rax
	cmpq	%rax, %r12
	je	.LB.Emission.run.8
.LB.Emission.run.5:
	cmpb	$3, 4(%rdx,%rax,8)
	jne	.LB.Emission.run.4
	cmpq	$-1, 8248(%rbx,%rax,8)
	jne	.LB.Emission.run.4
	movl	$2, %eax
	jmp	.LB.Emission.run.0
.LB.Emission.run.6:
	movl	$2, %eax
	jmp	.LB.Emission.run.0
.LB.Emission.run.7:
	movl	$2, %eax
	testq	%rcx, %rcx
	jne	.LB.Emission.run.0
.LB.Emission.run.8:
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv
	jmp	.LB.Emission.run.0
.LB.Emission.run.9:
	movl	$2, %eax
	movl	$0, %ebp
	cmpq	%rdx, %rcx
	jne	.LB.Emission.run.0
.LB.Emission.run.10:
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	call	_ZNK12_GLOBAL__N_18Emission11isAvailableE11StackOffset
	testb	%al, %al
	je	.LB.Emission.run.6
	addq	$1, %rbp
	cmpq	%rbp, %r12
	jne	.LB.Emission.run.10
	movq	(%rbx), %rdx
	movl	$0, %eax
	jmp	.LB.Emission.run.5
	.size	_ZN12_GLOBAL__N_18Emission3runEv, .-_ZN12_GLOBAL__N_18Emission3runEv
	.align 2
	.type	_ZN12_GLOBAL__N_17Planner10isRetainedERKNS_7MappingE11StackOffset, @function
_ZN12_GLOBAL__N_17Planner10isRetainedERKNS_7MappingE11StackOffset:
	cmpq	$-1, (%rdi,%rsi,8)
	setne	%al
	ret
	.size	_ZN12_GLOBAL__N_17Planner10isRetainedERKNS_7MappingE11StackOffset, .-_ZN12_GLOBAL__N_17Planner10isRetainedERKNS_7MappingE11StackOffset
	.align 2
	.type	_ZNK12_GLOBAL__N_17Planner20hasOtherRetainedCopyERKNS_7MappingERKNS_11OffsetArrayIhEE11StackOffset, @function
_ZNK12_GLOBAL__N_17Planner20hasOtherRetainedCopyERKNS_7MappingERKNS_11OffsetArrayIhEE11StackOffset:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$8, %rsp
	movq	%rdx, (%rsp)
	movq	8(%rdi), %r12
	testq	%r12, %r12
	je	.LB.Planner.hasOtherRetainedCopy.4
	movq	%rdi, %r13
	movq	%rsi, %r15
	movq	%rcx, %rbp
	leaq	0(,%rcx,8), %r14
	movl	$0, %ebx
	jmp	.LB.Planner.hasOtherRetainedCopy.1
	.p2align 4
.LB.Planner.hasOtherRetainedCopy.0:
	addq	$1, %rbx
	cmpq	%r12, %rbx
	je	.LB.Planner.hasOtherRetainedCopy.2
.LB.Planner.hasOtherRetainedCopy.1:
	cmpq	%rbp, %rbx
	je	.LB.Planner.hasOtherRetainedCopy.0
	movq	0(%r13), %rdx
	movq	(%rdx,%rbx,8), %rax
	xorq	(%rdx,%r14), %rax
	salq	$16, %rax
	jne	.LB.Planner.hasOtherRetainedCopy.0
	movq	%rbx, %rsi
	movq	%r15, %rdi
	call	_ZN12_GLOBAL__N_17Planner10isRetainedERKNS_7MappingE11StackOffset
	testb	%al, %al
	je	.LB.Planner.hasOtherRetainedCopy.0
	movq	(%rsp), %rcx
	cmpb	$0, (%rcx,%rbx)
	jne	.LB.Planner.hasOtherRetainedCopy.0
	jmp	.LB.Planner.hasOtherRetainedCopy.3
.LB.Planner.hasOtherRetainedCopy.2:
	movl	$0, %eax
.LB.Planner.hasOtherRetainedCopy.3:
	addq	$8, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB.Planner.hasOtherRetainedCopy.4:
	movl	$0, %eax
	jmp	.LB.Planner.hasOtherRetainedCopy.3
	.size	_ZNK12_GLOBAL__N_17Planner20hasOtherRetainedCopyERKNS_7MappingERKNS_11OffsetArrayIhEE11StackOffset, .-_ZNK12_GLOBAL__N_17Planner20hasOtherRetainedCopyERKNS_7MappingERKNS_11OffsetArrayIhEE11StackOffset
	.align 2
	.type	_ZNK12_GLOBAL__N_17Planner10isDemandedE9StackSlot, @function
_ZNK12_GLOBAL__N_17Planner10isDemandedE9StackSlot:
	movq	24(%rdi), %r8
	testq	%r8, %r8
	je	.LB.Planner.isDemanded.3
	movq	16(%rdi), %rcx
	movl	$0, %eax
	jmp	.LB.Planner.isDemanded.1
	.p2align 4
.LB.Planner.isDemanded.0:
	addq	$1, %rax
	cmpq	%r8, %rax
	je	.LB.Planner.isDemanded.2
.LB.Planner.isDemanded.1:
	cmpb	$1, 4(%rcx,%rax,8)
	je	.LB.Planner.isDemanded.0
	movq	%rsi, %rdx
	xorq	(%rcx,%rax,8), %rdx
	salq	$16, %rdx
	jne	.LB.Planner.isDemanded.0
	movl	$1, %eax
	ret
.LB.Planner.isDemanded.2:
	movl	$0, %eax
	ret
.LB.Planner.isDemanded.3:
	movl	$0, %eax
	ret
	.size	_ZNK12_GLOBAL__N_17Planner10isDemandedE9StackSlot, .-_ZNK12_GLOBAL__N_17Planner10isDemandedE9StackSlot
	.align 2
	.type	_ZNK12_GLOBAL__N_17Planner8classifyERKNS_7MappingERKNS_11OffsetArrayIhEE11StackOffset, @function
_ZNK12_GLOBAL__N_17Planner8classifyERKNS_7MappingERKNS_11OffsetArrayIhEE11StackOffset:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$8, %rsp
	movq	%rdi, %rbx
	movq	%rdx, %r14
	movq	(%rdi), %rax
	leaq	(%rax,%rcx,8), %rax
	movq	(%rax), %rdi
	movzbl	4(%rax), %r13d
	movl	$-1, %edx
	cmpb	$3, %r13b
	je	.LB.Planner.classify.8
	movq	%rsi, %r12
	movq	%rcx, %rbp
	movq	%rdi, %r15
	cmpb	$1, %r13b
	je	.LB.Planner.classify.6
	movl	(%rax), %ecx
	movl	%ecx, 4(%rsp)
	movzbl	5(%rax), %eax
	movb	%al, 3(%rsp)
	testb	%al, %al
	je	.LB.Planner.classify.0
	cmpb	$2, %r13b
	jne	.LB.Planner.classify.4
.LB.Planner.classify.0:
	movq	(%r12,%rbp,8), %rdx
	movq	16(%rbx), %rax
	cmpb	$1, 4(%rax,%rdx,8)
	je	.LB.Planner.classify.12
.LB.Planner.classify.1:
	leal	-1(%r13), %eax
	cmpb	$1, %al
	jbe	.LB.Planner.classify.7
	cmpb	$0, 3(%rsp)
	je	.LB.Planner.classify.7
.LB.Planner.classify.2:
	testb	%r13b, %r13b
	jne	.LB.Planner.classify.5
.LB.Planner.classify.3:
	movl	4(%rsp), %eax
	movq	32(%rbx), %rcx
	movl	$2, %edx
	cmpb	$0, (%rcx,%rax)
	jne	.LB.Planner.classify.8
	movq	%rbp, %rcx
	movq	%r14, %rdx
	movq	%r12, %rsi
	movq	%rbx, %rdi
	call	_ZNK12_GLOBAL__N_17Planner20hasOtherRetainedCopyERKNS_7MappingERKNS_11OffsetArrayIhEE11StackOffset
	movl	$3, %edx
	testb	%al, %al
	jne	.LB.Planner.classify.8
	cmpb	$1, 40(%rbx)
	sbbl	%edx, %edx
	orl	$4, %edx
	jmp	.LB.Planner.classify.8
.LB.Planner.classify.4:
	testb	%r13b, %r13b
	jne	.LB.Planner.classify.10
	movl	%ecx, %eax
	movq	32(%rbx), %rdx
	cmpb	$0, (%rdx,%rax)
	jne	.LB.Planner.classify.9
	movq	(%rsi,%rbp,8), %rdx
	movq	16(%rbx), %rax
	cmpb	$1, 4(%rax,%rdx,8)
	je	.LB.Planner.classify.11
	jmp	.LB.Planner.classify.3
.LB.Planner.classify.5:
	movq	%rbp, %rcx
	movq	%r14, %rdx
	movq	%r12, %rsi
	movq	%rbx, %rdi
	call	_ZNK12_GLOBAL__N_17Planner20hasOtherRetainedCopyERKNS_7MappingERKNS_11OffsetArrayIhEE11StackOffset
	cmpb	$1, %al
	sbbl	%edx, %edx
	orl	$3, %edx
	jmp	.LB.Planner.classify.8
.LB.Planner.classify.6:
	movq	(%rsi,%rcx,8), %rdx
	movq	16(%rbx), %rax
	cmpb	$1, 4(%rax,%rdx,8)
	je	.LB.Planner.classify.12
.LB.Planner.classify.7:
	movl	$1, %edx
.LB.Planner.classify.8:
	movl	%edx, %eax
	addq	$8, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB.Planner.classify.9:
	movq	(%rsi,%rbp,8), %rdx
	movq	16(%rbx), %rax
	cmpb	$1, 4(%rax,%rdx,8)
	jne	.LB.Planner.classify.2
	jmp	.LB.Planner.classify.12
.LB.Planner.classify.10:
	movq	(%rsi,%rbp,8), %rdx
	movq	16(%rbx), %rax
	cmpb	$1, 4(%rax,%rdx,8)
	jne	.LB.Planner.classify.5
.LB.Planner.classify.11:
	movq	%rbp, %rcx
	movq	%r14, %rdx
	movq	%r12, %rsi
	movq	%rbx, %rdi
	call	_ZNK12_GLOBAL__N_17Planner20hasOtherRetainedCopyERKNS_7MappingERKNS_11OffsetArrayIhEE11StackOffset
	testb	%al, %al
	jne	.LB.Planner.classify.12
	movl	4(%rsp), %eax
	movabsq	$-4294967296, %rsi
	andq	%r15, %rsi
	orq	%rax, %rsi
	movzbl	3(%rsp), %eax
	salq	$40, %rax
	movabsq	$-280375465082881, %rdx
	andq	%rdx, %rsi
	orq	%rax, %rsi
	movq	%rbx, %rdi
	call	_ZNK12_GLOBAL__N_17Planner10isDemandedE9StackSlot
	testb	%al, %al
	jne	.LB.Planner.classify.1
.LB.Planner.classify.12:
	movl	$0, %edx
	jmp	.LB.Planner.classify.8
	.size	_ZNK12_GLOBAL__N_17Planner8classifyERKNS_7MappingERKNS_11OffsetArrayIhEE11StackOffset, .-_ZNK12_GLOBAL__N_17Planner8classifyERKNS_7MappingERKNS_11OffsetArrayIhEE11StackOffset
	.align 2
	.type	_ZN12_GLOBAL__N_17Planner7resolveERKNS_7MappingENS_8Emission7BlockedES3_m, @function
_ZN12_GLOBAL__N_17Planner7resolveERKNS_7MappingENS_8Emission7BlockedES3_m:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$9272, %rsp
	movq	%rdi, %r14
	movq	%rsi, %r12
	movq	%rcx, 24(%rsp)
	movq	8(%rdi), %rcx
	testq	%rcx, %rcx
	je	.LB.Planner.resolve.1
	leaq	8240(%rsp), %rax
	addq	%rax, %rcx
	.p2align 4
.LB.Planner.resolve.0:
	movb	$0, (%rax)
	addq	$1, %rax
	cmpq	%rcx, %rax
	jne	.LB.Planner.resolve.0
.LB.Planner.resolve.1:
	addq	$1, %rdx
	cmpq	%r9, %rdx
	jnb	.LB.Planner.resolve.6
	movl	$0, %ebp
	jmp	.LB.Planner.resolve.5
.LB.Planner.resolve.2:
	movl	$2, %eax
.LB.Planner.resolve.3:
	addq	$9272, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
	.p2align 5
.LB.Planner.resolve.4:
	addq	$1, %rdx
	cmpq	%r9, %rdx
	jnb	.LB.Planner.resolve.7
.LB.Planner.resolve.5:
	movq	(%r8,%rdx,8), %rax
	cmpq	$-1, %rax
	je	.LB.Planner.resolve.4
	movq	8192(%r12,%rax,8), %rax
	cmpq	$-1, %rax
	je	.LB.Planner.resolve.4
	cmpq	$-1, (%r12,%rax,8)
	je	.LB.Planner.resolve.2
	movq	%rax, 48(%rsp,%rbp,8)
	leaq	1(%rbp), %rbp
	jmp	.LB.Planner.resolve.4
.LB.Planner.resolve.6:
	movl	$0, %ebp
.LB.Planner.resolve.7:
	cmpq	$0, 24(%rsp)
	je	.LB.Planner.resolve.17
	leaq	48(%rsp,%rbp,8), %r13
	movq	$0, 32(%rsp)
	movq	%rbp, 40(%rsp)
.LB.Planner.resolve.8:
	cmpq	$0, 40(%rsp)
	je	.LB.Planner.resolve.16
	leaq	48(%rsp), %rbx
	movq	$-1, %r15
	movb	$0, 23(%rsp)
	jmp	.LB.Planner.resolve.12
.LB.Planner.resolve.9:
	movq	(%r12,%rbp,8), %rax
	cmpq	%rax, (%r12,%r15,8)
	cmovb	%rbp, %r15
	movq	%r15, 8(%rsp)
	movl	%esi, %eax
.LB.Planner.resolve.10:
	movq	8(%rsp), %r15
	movb	%al, 23(%rsp)
.LB.Planner.resolve.11:
	addq	$8, %rbx
	cmpq	%r13, %rbx
	je	.LB.Planner.resolve.13
.LB.Planner.resolve.12:
	movq	(%rbx), %rbp
	movq	%rbp, 8(%rsp)
	cmpb	$0, 8240(%rsp,%rbp)
	jne	.LB.Planner.resolve.11
	movq	%rbp, %rcx
	leaq	8240(%rsp), %rdx
	movq	%r12, %rsi
	movq	%r14, %rdi
	call	_ZNK12_GLOBAL__N_17Planner8classifyERKNS_7MappingERKNS_11OffsetArrayIhEE11StackOffset
	cmpb	$-1, %al
	je	.LB.Planner.resolve.11
	movzbl	23(%rsp), %esi
	cmpb	%sil, %al
	jb	.LB.Planner.resolve.10
	cmpq	$-1, %r15
	je	.LB.Planner.resolve.10
	cmpb	%sil, %al
	je	.LB.Planner.resolve.9
	movq	%r15, 8(%rsp)
	movzbl	23(%rsp), %eax
	jmp	.LB.Planner.resolve.10
.LB.Planner.resolve.13:
	cmpq	$-1, %r15
	je	.LB.Planner.resolve.18
	cmpb	$4, 23(%rsp)
	je	.LB.Planner.resolve.15
.LB.Planner.resolve.14:
	movb	$1, 8240(%rsp,%r15)
	movq	48(%r14), %rax
	movb	$1, (%rax,%r15)
	addq	$1, 32(%rsp)
	movq	32(%rsp), %rax
	movq	24(%rsp), %rdi
	cmpq	%rdi, %rax
	jne	.LB.Planner.resolve.8
	movl	$0, %eax
	jmp	.LB.Planner.resolve.3
.LB.Planner.resolve.15:
	movq	(%r14), %rax
	movq	(%rax,%r15,8), %rsi
	leaq	32(%r14), %rdi
	call	_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot
	testb	%al, %al
	je	.LB.Planner.resolve.14
	movl	$2, %eax
	jmp	.LB.Planner.resolve.3
.LB.Planner.resolve.16:
	movl	$1, %eax
	jmp	.LB.Planner.resolve.3
.LB.Planner.resolve.17:
	movl	$0, %eax
	jmp	.LB.Planner.resolve.3
.LB.Planner.resolve.18:
	movl	$1, %eax
	jmp	.LB.Planner.resolve.3
	.size	_ZN12_GLOBAL__N_17Planner7resolveERKNS_7MappingENS_8Emission7BlockedES3_m, .-_ZN12_GLOBAL__N_17Planner7resolveERKNS_7MappingENS_8Emission7BlockedES3_m
	.align 2
	.type	_ZN12_GLOBAL__N_17Planner3runENS_14MappingBuilder21WildcardSlotsStrategyEP9StackSlotP9ShuffleOpPNS_8OptionalI11StackOffsetEERm, @function
_ZN12_GLOBAL__N_17Planner3runENS_14MappingBuilder21WildcardSlotsStrategyEP9StackSlotP9ShuffleOpPNS_8OptionalI11StackOffsetEERm:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$32968, %rsp
	movq	%rdi, %rbx
	movq	%rdx, %r12
	movq	%rcx, %r15
	movq	%r8, 16(%rsp)
	movq	%r9, %rbp
	movl	%esi, %r14d
	movb	$0, 56(%rdi)
	movq	24(%rdi), %r11
	testq	%r11, %r11
	je	.LB.Planner.run.4
	movq	16(%rdi), %r10
	movl	$0, %ecx
	jmp	.LB.Planner.run.1
	.p2align 5
.LB.Planner.run.0:
	addq	$1, %rcx
	cmpq	%r11, %rcx
	je	.LB.Planner.run.4
.LB.Planner.run.1:
	movzbl	4(%r10,%rcx,8), %esi
	cmpb	$1, %sil
	je	.LB.Planner.run.0
	cmpb	$0, 5(%r10,%rcx,8)
	je	.LB.Planner.run.0
	cmpb	$2, %sil
	je	.LB.Planner.run.0
	movq	8(%rbx), %rdi
	testq	%rdi, %rdi
	je	.LB.Planner.run.3
	movq	(%rbx), %r9
	movq	(%r10,%rcx,8), %r8
	movl	$0, %eax
	.p2align 5
.LB.Planner.run.2:
	movq	%r8, %rdx
	xorq	(%r9,%rax,8), %rdx
	salq	$16, %rdx
	je	.LB.Planner.run.0
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB.Planner.run.2
.LB.Planner.run.3:
	testb	%sil, %sil
	jne	.LB.Planner.run.25
	movl	(%r10,%rcx,8), %eax
	movq	32(%rbx), %rdx
	cmpb	$0, (%rdx,%rax)
	jne	.LB.Planner.run.0
	movl	$2, %eax
	jmp	.LB.Planner.run.26
.LB.Planner.run.4:
	leaq	32(%rsp), %r13
	movq	%rbp, 24(%rsp)
.LB.Planner.run.5:
	movq	8(%rbx), %rdx
	movq	24(%rbx), %rsi
	testq	%rdx, %rdx
	je	.LB.Planner.run.7
	movl	$0, %eax
	.p2align 5
.LB.Planner.run.6:
	movq	$-1, 96(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdx
	jne	.LB.Planner.run.6
.LB.Planner.run.7:
	testq	%rsi, %rsi
	je	.LB.Planner.run.9
	leaq	96(%rsp), %rax
	leaq	(%rax,%rsi,8), %rcx
	.p2align 5
.LB.Planner.run.8:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rcx, %rax
	jne	.LB.Planner.run.8
.LB.Planner.run.9:
	movq	(%rbx), %rdi
	movq	16(%rbx), %rcx
	movq	48(%rbx), %rax
	movq	%rdi, 32(%rsp)
	movq	%rdx, 40(%rsp)
	movq	%rcx, 48(%rsp)
	movq	%rsi, 56(%rsp)
	movq	%rax, 64(%rsp)
	movb	%r14b, 72(%rsp)
	leaq	96(%rsp), %rax
	movq	%rax, 80(%rsp)
	movb	$0, 88(%rsp)
	movq	%r13, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder10mapInPlaceEv
	testb	%al, %al
	jne	.LB.Planner.run.19
	movq	%r13, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder16mapClosestCopiesEv
	testb	%al, %al
	jne	.LB.Planner.run.20
	movq	%r13, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder21mapWildcardSlotCopiesEv
	testb	%al, %al
	jne	.LB.Planner.run.21
	movq	%r13, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder17keepWildcardSlotsEv
	testb	%al, %al
	jne	.LB.Planner.run.22
	movq	%r13, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder13absorbSurplusEv
	testb	%al, %al
	jne	.LB.Planner.run.23
	movzbl	56(%rbx), %eax
	testb	%al, %al
	movzbl	88(%rsp), %edx
	cmove	%edx, %eax
	movb	%al, 56(%rbx)
	cmpq	$0, 8(%rbx)
	je	.LB.Planner.run.32
	movl	$0, %eax
	.p2align 5
.LB.Planner.run.10:
	movq	(%rbx), %rdx
	movq	(%rdx,%rax,8), %rdx
	movq	%rdx, (%r12,%rax,8)
	addq	$1, %rax
	movq	8(%rbx), %rdx
	cmpq	%rdx, %rax
	jb	.LB.Planner.run.10
	movq	16(%rbx), %rsi
	movq	24(%rbx), %rcx
	movq	32(%rbx), %rax
	movq	%rsi, 16480(%rsp)
	movq	%rcx, 16488(%rsp)
	movq	%rax, 16496(%rsp)
	movq	%r12, 16504(%rsp)
	movq	%rdx, 16512(%rsp)
	movq	%r15, 16520(%rsp)
	movq	$0, 16528(%rsp)
	testq	%rdx, %rdx
	je	.LB.Planner.run.12
	movl	$0, %eax
	.p2align 5
.LB.Planner.run.11:
	movq	96(%rsp,%rax,8), %rsi
	movq	%rsi, 16536(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdx
	jne	.LB.Planner.run.11
.LB.Planner.run.12:
	testq	%rcx, %rcx
	je	.LB.Planner.run.27
	leaq	0(,%rcx,8), %rdx
	movl	$0, %eax
	leaq	24728(%rsp), %rdi
	leaq	8288(%rsp), %rsi
	.p2align 5
.LB.Planner.run.13:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB.Planner.run.13
	movq	$0, 32920(%rsp)
	leaq	96(%rsp), %rax
	movq	%rax, 32944(%rsp)
	leaq	16480(%rsp), %rax
	addq	%rax, %rdx
	jmp	.LB.Planner.run.15
	.p2align 5
.LB.Planner.run.14:
	addq	$8, %rax
	cmpq	%rax, %rdx
	je	.LB.Planner.run.28
.LB.Planner.run.15:
	cmpq	$-1, 8248(%rax)
	jne	.LB.Planner.run.14
	addq	$1, 32920(%rsp)
	jmp	.LB.Planner.run.14
.LB.Planner.run.16:
	movq	24(%rsp), %rbp
	testb	%al, %al
	jne	.LB.Planner.run.26
	cmpq	$0, 24(%rbx)
	je	.LB.Planner.run.18
	movl	$0, %edx
.LB.Planner.run.17:
	movq	8288(%rsp,%rdx,8), %rcx
	movq	16(%rsp), %rdi
	movq	%rcx, (%rdi,%rdx,8)
	addq	$1, %rdx
	cmpq	24(%rbx), %rdx
	jb	.LB.Planner.run.17
.LB.Planner.run.18:
	movq	16528(%rsp), %rdx
	movq	%rdx, 0(%rbp)
	jmp	.LB.Planner.run.26
.LB.Planner.run.19:
	movl	$2, %eax
	jmp	.LB.Planner.run.26
.LB.Planner.run.20:
	movl	$2, %eax
	jmp	.LB.Planner.run.26
.LB.Planner.run.21:
	movl	$2, %eax
	jmp	.LB.Planner.run.26
.LB.Planner.run.22:
	movl	$2, %eax
	jmp	.LB.Planner.run.26
.LB.Planner.run.23:
	movl	$2, %eax
	jmp	.LB.Planner.run.26
.LB.Planner.run.24:
	movl	$2, %eax
	jmp	.LB.Planner.run.26
.LB.Planner.run.25:
	movl	$2, %eax
.LB.Planner.run.26:
	addq	$32968, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB.Planner.run.27:
	movq	$0, 32920(%rsp)
	leaq	96(%rsp), %rax
	movq	%rax, 32944(%rsp)
.LB.Planner.run.28:
	leaq	16480(%rsp), %rdi
	call	_ZN12_GLOBAL__N_18Emission3runEv
	cmpb	$1, %al
	jne	.LB.Planner.run.16
	movq	8(%rbx), %rbp
	testq	%rbp, %rbp
	je	.LB.Planner.run.30
	movq	48(%rbx), %rax
	leaq	(%rax,%rbp), %rdx
	movl	$0, %ebp
	.p2align 4
.LB.Planner.run.29:
	cmpb	$1, (%rax)
	sbbq	$-1, %rbp
	addq	$1, %rax
	cmpq	%rax, %rdx
	jne	.LB.Planner.run.29
.LB.Planner.run.30:
	movq	32928(%rsp), %rdi
	movq	%rdi, (%rsp)
	movq	(%rsp), %rsi
	movq	%rsi, %rax
	movq	32936(%rsp), %rdx
	movq	%rsi, (%rsp)
	movq	%rdx, 8(%rsp)
	leaq	96(%rsp), %rsi
	movq	16512(%rsp), %r9
	leaq	16536(%rsp), %r8
	movq	%rdx, %rcx
	movq	%rax, %rdx
	movq	%rbx, %rdi
	call	_ZN12_GLOBAL__N_17Planner7resolveERKNS_7MappingENS_8Emission7BlockedES3_m
	cmpb	$1, %al
	je	.LB.Planner.run.26
	cmpb	$2, %al
	je	.LB.Planner.run.26
	movq	8(%rbx), %rcx
	testq	%rcx, %rcx
	je	.LB.Planner.run.24
	movq	48(%rbx), %rax
	addq	%rax, %rcx
	movl	$0, %edx
	.p2align 4
.LB.Planner.run.31:
	cmpb	$1, (%rax)
	sbbq	$-1, %rdx
	addq	$1, %rax
	cmpq	%rax, %rcx
	jne	.LB.Planner.run.31
	cmpq	%rdx, %rbp
	jb	.LB.Planner.run.5
	movl	$2, %eax
	jmp	.LB.Planner.run.26
.LB.Planner.run.32:
	movq	16(%rbx), %rdx
	movq	24(%rbx), %rcx
	movq	32(%rbx), %rax
	movq	%rdx, 16480(%rsp)
	movq	%rcx, 16488(%rsp)
	movq	%rax, 16496(%rsp)
	movq	%r12, 16504(%rsp)
	movq	$0, 16512(%rsp)
	movq	%r15, 16520(%rsp)
	movq	$0, 16528(%rsp)
	jmp	.LB.Planner.run.12
	.size	_ZN12_GLOBAL__N_17Planner3runENS_14MappingBuilder21WildcardSlotsStrategyEP9StackSlotP9ShuffleOpPNS_8OptionalI11StackOffsetEERm, .-_ZN12_GLOBAL__N_17Planner3runENS_14MappingBuilder21WildcardSlotsStrategyEP9StackSlotP9ShuffleOpPNS_8OptionalI11StackOffsetEERm
	.globl	build_bottom_up
	.type	build_bottom_up, @function
build_bottom_up:
	cmpq	%rdi, %rsi
	jb	.LB.build_bottom_up.14
	movq	%rdx, %r10
	cmpq	$1024, %rsi
	ja	.LB.build_bottom_up.14
	subq	$32872, %rsp
	testq	%rdi, %rdi
	je	.LB.build_bottom_up.18
	movl	$0, %eax
	.p2align 5
.LB.build_bottom_up.0:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB.build_bottom_up.0
	testq	%rsi, %rsi
	je	.LB.build_bottom_up.3
.LB.build_bottom_up.1:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%rsi,8), %rdx
	.p2align 5
.LB.build_bottom_up.2:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB.build_bottom_up.2
	testq	%rdi, %rdi
	je	.LB.build_bottom_up.19
.LB.build_bottom_up.3:
	movl	$0, %eax
	jmp	.LB.build_bottom_up.5
	.p2align 5
.LB.build_bottom_up.4:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rdi
	je	.LB.build_bottom_up.6
	movq	%rdx, %rax
.LB.build_bottom_up.5:
	movq	(%r8,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB.build_bottom_up.4
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	jmp	.LB.build_bottom_up.4
.LB.build_bottom_up.6:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	%rdx, 32(%rsp)
	movq	32880(%rsp), %rdi
	movq	%rdi, 40(%rsp)
	movq	$0, 48(%rsp)
	movl	$0, %edx
	addq	$1, %rax
	.p2align 5
.LB.build_bottom_up.7:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB.build_bottom_up.7
.LB.build_bottom_up.8:
	testq	%rsi, %rsi
	je	.LB.build_bottom_up.15
	leaq	0(,%rsi,8), %rdx
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB.build_bottom_up.9:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB.build_bottom_up.9
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rdx
	jmp	.LB.build_bottom_up.11
	.p2align 5
.LB.build_bottom_up.10:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB.build_bottom_up.16
.LB.build_bottom_up.11:
	cmpq	$-1, 8248(%rax)
	jne	.LB.build_bottom_up.10
	addq	$1, 16440(%rsp)
	jmp	.LB.build_bottom_up.10
.LB.build_bottom_up.12:
	movq	32888(%rsp), %rax
	movq	$0, (%rax)
	movq	$0, 8(%rax)
	movq	48(%rsp), %rdx
	jmp	.LB.build_bottom_up.17
.LB.build_bottom_up.13:
	movq	16448(%rsp), %rax
	movq	32888(%rsp), %rsi
	movq	%rax, (%rsi)
	movq	16456(%rsp), %rax
	movq	%rax, 8(%rsi)
	movq	48(%rsp), %rdx
	jmp	.LB.build_bottom_up.17
.LB.build_bottom_up.14:
	movq	$-2, %rdx
	movq	%rdx, %rax
	ret
.LB.build_bottom_up.15:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB.build_bottom_up.16:
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv
	cmpb	$1, %al
	je	.LB.build_bottom_up.13
	movq	$-2, %rdx
	cmpb	$2, %al
	jne	.LB.build_bottom_up.12
.LB.build_bottom_up.17:
	movq	%rdx, %rax
	addq	$32872, %rsp
	ret
.LB.build_bottom_up.18:
	testq	%rsi, %rsi
	jne	.LB.build_bottom_up.1
.LB.build_bottom_up.19:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32880(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB.build_bottom_up.8
	.size	build_bottom_up, .-build_bottom_up
	.globl	emission_pop
	.type	emission_pop, @function
emission_pop:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$32872, %rsp
	movq	32928(%rsp), %r13
	movq	32952(%rsp), %r15
	cmpq	$1024, %rdi
	ja	.LB.emission_pop.12
	movq	%rdi, %rbx
	movq	%rsi, %r12
	movq	%rdx, %rsi
	cmpq	$1024, %r12
	ja	.LB.emission_pop.12
	testq	%rdi, %rdi
	je	.LB.emission_pop.23
	movl	$0, %eax
	.p2align 5
.LB.emission_pop.0:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rbx
	jne	.LB.emission_pop.0
	testq	%r12, %r12
	je	.LB.emission_pop.3
.LB.emission_pop.1:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%r12,8), %rdx
	.p2align 5
.LB.emission_pop.2:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB.emission_pop.2
	testq	%rbx, %rbx
	je	.LB.emission_pop.24
.LB.emission_pop.3:
	movl	$0, %eax
	jmp	.LB.emission_pop.5
	.p2align 5
.LB.emission_pop.4:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rbx
	je	.LB.emission_pop.6
	movq	%rdx, %rax
.LB.emission_pop.5:
	movq	(%r8,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB.emission_pop.4
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	jmp	.LB.emission_pop.4
.LB.emission_pop.6:
	movq	%rcx, (%rsp)
	movq	%r12, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%rsi, 24(%rsp)
	movq	%rdx, 32(%rsp)
	movq	32936(%rsp), %rdi
	movq	%rdi, 40(%rsp)
	movq	$0, 48(%rsp)
	movl	$0, %edx
	addq	$1, %rax
	.p2align 5
.LB.emission_pop.7:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB.emission_pop.7
.LB.emission_pop.8:
	testq	%r12, %r12
	je	.LB.emission_pop.14
	leaq	0(,%r12,8), %rdx
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB.emission_pop.9:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB.emission_pop.9
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rdx
	jmp	.LB.emission_pop.11
	.p2align 5
.LB.emission_pop.10:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB.emission_pop.15
.LB.emission_pop.11:
	cmpq	$-1, 8248(%rax)
	jne	.LB.emission_pop.10
	addq	$1, 16440(%rsp)
	jmp	.LB.emission_pop.10
.LB.emission_pop.12:
	movq	$-2, %rax
	jmp	.LB.emission_pop.22
.LB.emission_pop.13:
	movq	$-2, %rax
	jmp	.LB.emission_pop.22
.LB.emission_pop.14:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB.emission_pop.15:
	testq	%r13, %r13
	je	.LB.emission_pop.17
	movl	$0, %ebp
	movq	%rsp, %r14
.LB.emission_pop.16:
	movq	%r14, %rdi
	call	_ZN12_GLOBAL__N_18Emission3popEv
	testb	%al, %al
	jne	.LB.emission_pop.13
	addq	$1, %rbp
	cmpq	%rbp, %r13
	jne	.LB.emission_pop.16
.LB.emission_pop.17:
	cmpq	%r13, %rbx
	je	.LB.emission_pop.19
	subq	%r13, %rbx
	movl	$0, %eax
	.p2align 5
.LB.emission_pop.18:
	movq	56(%rsp,%rax,8), %rdx
	movq	32944(%rsp), %rsi
	movq	%rdx, (%rsi,%rax,8)
	addq	$1, %rax
	cmpq	%rbx, %rax
	jb	.LB.emission_pop.18
.LB.emission_pop.19:
	testq	%r12, %r12
	je	.LB.emission_pop.21
	salq	$3, %r12
	movl	$0, %eax
	leaq	8248(%rsp), %rcx
	.p2align 5
.LB.emission_pop.20:
	movq	(%rcx,%rax), %rdx
	movq	%rdx, (%r15,%rax)
	addq	$8, %rax
	cmpq	%rax, %r12
	jne	.LB.emission_pop.20
.LB.emission_pop.21:
	movq	32960(%rsp), %rax
	movq	16440(%rsp), %rdx
	movq	%rdx, (%rax)
	movq	48(%rsp), %rax
.LB.emission_pop.22:
	addq	$32872, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB.emission_pop.23:
	testq	%r12, %r12
	jne	.LB.emission_pop.1
.LB.emission_pop.24:
	movq	%rcx, (%rsp)
	movq	%r12, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%rsi, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32936(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB.emission_pop.8
	.size	emission_pop, .-emission_pop
	.globl	spill_set
	.type	spill_set, @function
spill_set:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$24, %rsp
	movq	%rsi, (%rsp)
	movq	%rdx, %rbx
	movq	%rcx, %r12
	movq	%r8, %rbp
	movq	%r9, %r13
	testq	%rcx, %rcx
	je	.LB.spill_set.14
	movl	$0, %eax
	jmp	.LB.spill_set.1
	.p2align 4
.LB.spill_set.0:
	addq	$1, %rax
	cmpq	%rax, %r12
	je	.LB.spill_set.15
.LB.spill_set.1:
	cmpb	$0, 5(%rbx,%rax,8)
	je	.LB.spill_set.0
	cmpb	$0, 4(%rbx,%rax,8)
	jne	.LB.spill_set.0
	movl	(%rbx,%rax,8), %edx
	cmpq	%rdi, %rdx
	jb	.LB.spill_set.0
	movq	$-2, %rax
	jmp	.LB.spill_set.12
	.p2align 4
.LB.spill_set.2:
	addq	$1, %rax
	cmpq	%rax, %r13
	je	.LB.spill_set.4
.LB.spill_set.3:
	cmpb	$0, 5(%rbp,%rax,8)
	je	.LB.spill_set.2
	cmpb	$0, 4(%rbp,%rax,8)
	jne	.LB.spill_set.2
	movl	0(%rbp,%rax,8), %edx
	cmpq	%rdi, %rdx
	jb	.LB.spill_set.2
	movq	$-2, %rax
	jmp	.LB.spill_set.12
.LB.spill_set.4:
	movq	(%rsp), %rax
	movq	%rax, 16(%rsp)
	testq	%r12, %r12
	je	.LB.spill_set.7
.LB.spill_set.5:
	movl	$0, %r14d
	leaq	16(%rsp), %r15
.LB.spill_set.6:
	movq	(%rbx), %rsi
	movq	%r15, %rdi
	call	_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot
	testb	%al, %al
	jne	.LB.spill_set.11
	addq	$1, %r14
	addq	$8, %rbx
	cmpq	%r12, %r14
	jb	.LB.spill_set.6
	testq	%r13, %r13
	je	.LB.spill_set.13
.LB.spill_set.7:
	movl	$0, %eax
	jmp	.LB.spill_set.9
	.p2align 6
.LB.spill_set.8:
	movq	80(%rsp), %rcx
	movb	%dl, (%rcx,%rax)
	addq	$1, %rax
	cmpq	%rax, %r13
	je	.LB.spill_set.10
.LB.spill_set.9:
	cmpb	$0, 5(%rbp,%rax,8)
	setne	%dl
	cmpb	$0, 4(%rbp,%rax,8)
	sete	%cl
	andb	%cl, %dl
	je	.LB.spill_set.8
	movl	0(%rbp,%rax,8), %edx
	movq	(%rsp), %rcx
	cmpb	$0, (%rcx,%rdx)
	setne	%dl
	jmp	.LB.spill_set.8
.LB.spill_set.10:
	movl	$0, %eax
	jmp	.LB.spill_set.12
.LB.spill_set.11:
	movq	$-2, %rax
.LB.spill_set.12:
	addq	$24, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB.spill_set.13:
	movl	$0, %eax
	jmp	.LB.spill_set.12
.LB.spill_set.14:
	movq	%rcx, %rax
	testq	%r9, %r9
	jne	.LB.spill_set.3
	movl	$0, %eax
	jmp	.LB.spill_set.12
.LB.spill_set.15:
	movl	$0, %eax
	testq	%r13, %r13
	jne	.LB.spill_set.3
	movq	(%rsp), %rax
	movq	%rax, 16(%rsp)
	jmp	.LB.spill_set.5
	.size	spill_set, .-spill_set
	.globl	remove_surplus
	.type	remove_surplus, @function
remove_surplus:
	cmpq	$1024, %rdi
	ja	.LB.remove_surplus.22
	pushq	%rbx
	subq	$32864, %rsp
	movq	%rdx, %r10
	movq	%r8, %rbx
	cmpq	$1024, %rsi
	ja	.LB.remove_surplus.13
	testq	%rdi, %rdi
	je	.LB.remove_surplus.20
	movl	$0, %eax
	.p2align 5
.LB.remove_surplus.0:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB.remove_surplus.0
	testq	%rsi, %rsi
	je	.LB.remove_surplus.3
.LB.remove_surplus.1:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%rsi,8), %rdx
	.p2align 5
.LB.remove_surplus.2:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB.remove_surplus.2
	testq	%rdi, %rdi
	je	.LB.remove_surplus.21
.LB.remove_surplus.3:
	movl	$0, %eax
	jmp	.LB.remove_surplus.5
	.p2align 5
.LB.remove_surplus.4:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rdi
	je	.LB.remove_surplus.6
	movq	%rdx, %rax
.LB.remove_surplus.5:
	movq	(%rbx,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB.remove_surplus.4
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	jmp	.LB.remove_surplus.4
.LB.remove_surplus.6:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	%rdx, 32(%rsp)
	movq	32888(%rsp), %rdi
	movq	%rdi, 40(%rsp)
	movq	$0, 48(%rsp)
	movl	$0, %edx
	addq	$1, %rax
	.p2align 5
.LB.remove_surplus.7:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB.remove_surplus.7
.LB.remove_surplus.8:
	testq	%rsi, %rsi
	je	.LB.remove_surplus.14
	leaq	0(,%rsi,8), %rdx
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB.remove_surplus.9:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB.remove_surplus.9
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rdx
	jmp	.LB.remove_surplus.11
	.p2align 5
.LB.remove_surplus.10:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB.remove_surplus.15
.LB.remove_surplus.11:
	cmpq	$-1, 8248(%rax)
	jne	.LB.remove_surplus.10
	addq	$1, 16440(%rsp)
	jmp	.LB.remove_surplus.10
.LB.remove_surplus.12:
	movq	16448(%rsp), %rax
	movq	32896(%rsp), %rsi
	movq	%rax, (%rsi)
	movq	16456(%rsp), %rax
	movq	%rax, 8(%rsi)
	jmp	.LB.remove_surplus.16
.LB.remove_surplus.13:
	movq	$-2, %rdx
	jmp	.LB.remove_surplus.19
.LB.remove_surplus.14:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB.remove_surplus.15:
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission13removeSurplusEv
	cmpb	$1, %al
	je	.LB.remove_surplus.12
	movq	$-2, %rdx
	cmpb	$2, %al
	je	.LB.remove_surplus.19
	testb	%al, %al
	jne	.LB.remove_surplus.16
	movq	32896(%rsp), %rax
	movq	$0, (%rax)
	movq	$0, 8(%rax)
.LB.remove_surplus.16:
	movq	32(%rsp), %rcx
	movq	32904(%rsp), %rax
	movq	%rcx, (%rax)
	testq	%rcx, %rcx
	je	.LB.remove_surplus.18
	salq	$3, %rcx
	movl	$0, %eax
	leaq	56(%rsp), %rsi
	.p2align 5
.LB.remove_surplus.17:
	movq	(%rsi,%rax), %rdx
	movq	%rdx, (%rbx,%rax)
	addq	$8, %rax
	cmpq	%rax, %rcx
	jne	.LB.remove_surplus.17
.LB.remove_surplus.18:
	movq	48(%rsp), %rdx
.LB.remove_surplus.19:
	movq	%rdx, %rax
	addq	$32864, %rsp
	popq	%rbx
	ret
.LB.remove_surplus.20:
	testq	%rsi, %rsi
	jne	.LB.remove_surplus.1
.LB.remove_surplus.21:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32888(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB.remove_surplus.8
.LB.remove_surplus.22:
	movq	$-2, %rdx
	movq	%rdx, %rax
	ret
	.size	remove_surplus, .-remove_surplus
	.globl	permute
	.type	permute, @function
permute:
	pushq	%r14
	pushq	%rbp
	pushq	%rbx
	subq	$49248, %rsp
	movq	%rdi, %rbx
	cmpq	$1024, %rdi
	ja	.LB.permute.15
	movq	%rsi, %rdi
	movq	%rdx, %r10
	movq	%rcx, %r11
	movq	%r8, %r14
	movq	%r9, %rbp
	testq	%rbx, %rbx
	je	.LB.permute.16
	leaq	16480(%rsp), %rax
	leaq	0(,%rbx,8), %rcx
	leaq	(%rax,%rcx), %rsi
	movq	%rax, %rdx
	.p2align 4
.LB.permute.0:
	movq	$-1, (%rdx)
	addq	$8, %rdx
	cmpq	%rsi, %rdx
	jne	.LB.permute.0
	.p2align 5
.LB.permute.1:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rsi, %rax
	jne	.LB.permute.1
	movl	$0, %eax
	.p2align 6
.LB.permute.2:
	movq	(%r10,%rax,8), %rdx
	movq	%rdx, 41056(%rsp,%rax,8)
	movq	(%rdi,%rax,8), %rsi
	movq	%rsi, 32864(%rsp,%rdx,8)
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	addq	$1, %rax
	cmpq	%rax, %rbx
	jne	.LB.permute.2
	leaq	32864(%rsp), %rdx
	movq	%rdx, (%rsp)
	movq	%rax, 8(%rsp)
	movq	$0, 16(%rsp)
	movq	%rdi, 24(%rsp)
	movq	%rax, 32(%rsp)
	movq	%r11, 40(%rsp)
	movq	$0, 48(%rsp)
	movl	$0, %eax
	leaq	56(%rsp), %rsi
	.p2align 5
.LB.permute.3:
	movq	16480(%rsp,%rax), %rdx
	movq	%rdx, (%rsi,%rax)
	addq	$8, %rax
	cmpq	%rcx, %rax
	jne	.LB.permute.3
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB.permute.4:
	movq	(%rsi,%rax), %rdx
	movq	%rdx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rcx, %rax
	jne	.LB.permute.4
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rcx
	jmp	.LB.permute.6
	.p2align 5
.LB.permute.5:
	addq	$8, %rax
	cmpq	%rcx, %rax
	je	.LB.permute.7
.LB.permute.6:
	cmpq	$-1, 8248(%rax)
	jne	.LB.permute.5
	addq	$1, 16440(%rsp)
	jmp	.LB.permute.5
.LB.permute.7:
	leaq	41056(%rsp), %rsi
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE
	cmpb	$1, %al
	je	.LB.permute.14
	movq	$-2, %rdx
	cmpb	$2, %al
	je	.LB.permute.13
	testb	%al, %al
	jne	.LB.permute.10
.LB.permute.8:
	movl	$0, %edx
	movl	$0, %eax
.LB.permute.9:
	movq	%rdx, (%r14)
	movq	%rax, 8(%r14)
	testq	%rbx, %rbx
	je	.LB.permute.12
.LB.permute.10:
	salq	$3, %rbx
	movl	$0, %eax
	leaq	56(%rsp), %rcx
	.p2align 5
.LB.permute.11:
	movq	(%rcx,%rax), %rdx
	movq	%rdx, 0(%rbp,%rax)
	addq	$8, %rax
	cmpq	%rax, %rbx
	jne	.LB.permute.11
.LB.permute.12:
	movq	48(%rsp), %rdx
.LB.permute.13:
	movq	%rdx, %rax
	addq	$49248, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r14
	ret
.LB.permute.14:
	movq	16448(%rsp), %rdx
	movq	16456(%rsp), %rax
	jmp	.LB.permute.9
.LB.permute.15:
	movq	$-2, %rdx
	jmp	.LB.permute.13
.LB.permute.16:
	leaq	32864(%rsp), %rax
	movq	%rax, (%rsp)
	movq	%rbx, 8(%rsp)
	movq	$0, 16(%rsp)
	movq	%rsi, 24(%rsp)
	movq	%rbx, 32(%rsp)
	movq	%rcx, 40(%rsp)
	movq	$0, 48(%rsp)
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	leaq	41056(%rsp), %rsi
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE
	cmpb	$1, %al
	je	.LB.permute.14
	movq	$-2, %rdx
	cmpb	$2, %al
	je	.LB.permute.13
	testb	%al, %al
	je	.LB.permute.8
	jmp	.LB.permute.12
	.size	permute, .-permute
	.globl	permute_at_lowest_height
	.type	permute_at_lowest_height, @function
permute_at_lowest_height:
	pushq	%rbp
	pushq	%rbx
	subq	$32872, %rsp
	movq	%rdi, %rbx
	cmpq	$1024, %rdi
	ja	.LB.permute_at_lowest_height.13
	movq	%rdx, %rdi
	movq	%r8, %rbp
	cmpq	$1024, %rsi
	ja	.LB.permute_at_lowest_height.13
	testq	%rbx, %rbx
	je	.LB.permute_at_lowest_height.20
	movl	$0, %eax
	.p2align 5
.LB.permute_at_lowest_height.0:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rbx
	jne	.LB.permute_at_lowest_height.0
	testq	%rsi, %rsi
	je	.LB.permute_at_lowest_height.3
.LB.permute_at_lowest_height.1:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%rsi,8), %rdx
	.p2align 5
.LB.permute_at_lowest_height.2:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB.permute_at_lowest_height.2
	testq	%rbx, %rbx
	je	.LB.permute_at_lowest_height.21
.LB.permute_at_lowest_height.3:
	movl	$0, %eax
	jmp	.LB.permute_at_lowest_height.5
	.p2align 5
.LB.permute_at_lowest_height.4:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rbx
	je	.LB.permute_at_lowest_height.6
	movq	%rdx, %rax
.LB.permute_at_lowest_height.5:
	movq	0(%rbp,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB.permute_at_lowest_height.4
	movq	%rdx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rdx,8)
	jmp	.LB.permute_at_lowest_height.4
.LB.permute_at_lowest_height.6:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%rdi, 24(%rsp)
	movq	%rdx, 32(%rsp)
	movq	32904(%rsp), %rdi
	movq	%rdi, 40(%rsp)
	movq	$0, 48(%rsp)
	movl	$0, %edx
	addq	$1, %rax
	.p2align 5
.LB.permute_at_lowest_height.7:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB.permute_at_lowest_height.7
.LB.permute_at_lowest_height.8:
	testq	%rsi, %rsi
	je	.LB.permute_at_lowest_height.14
	leaq	0(,%rsi,8), %rdx
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rsi
	.p2align 5
.LB.permute_at_lowest_height.9:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB.permute_at_lowest_height.9
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rdx
	jmp	.LB.permute_at_lowest_height.11
	.p2align 5
.LB.permute_at_lowest_height.10:
	addq	$8, %rax
	cmpq	%rdx, %rax
	je	.LB.permute_at_lowest_height.15
.LB.permute_at_lowest_height.11:
	cmpq	$-1, 8248(%rax)
	jne	.LB.permute_at_lowest_height.10
	addq	$1, 16440(%rsp)
	jmp	.LB.permute_at_lowest_height.10
.LB.permute_at_lowest_height.12:
	movq	16448(%rsp), %rax
	movq	32912(%rsp), %rdi
	movq	%rax, (%rdi)
	movq	16456(%rsp), %rax
	movq	%rax, 8(%rdi)
	jmp	.LB.permute_at_lowest_height.16
.LB.permute_at_lowest_height.13:
	movq	$-2, %rdx
	jmp	.LB.permute_at_lowest_height.19
.LB.permute_at_lowest_height.14:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB.permute_at_lowest_height.15:
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission21permuteAtLowestHeightEv
	cmpb	$1, %al
	je	.LB.permute_at_lowest_height.12
	movq	$-2, %rdx
	cmpb	$2, %al
	je	.LB.permute_at_lowest_height.19
	testb	%al, %al
	jne	.LB.permute_at_lowest_height.16
	movq	32912(%rsp), %rax
	movq	$0, (%rax)
	movq	$0, 8(%rax)
.LB.permute_at_lowest_height.16:
	leaq	0(,%rbx,8), %rsi
	movl	$0, %eax
	leaq	56(%rsp), %rcx
	testq	%rbx, %rbx
	je	.LB.permute_at_lowest_height.18
	.p2align 5
.LB.permute_at_lowest_height.17:
	movq	(%rcx,%rax), %rdx
	movq	%rdx, 0(%rbp,%rax)
	addq	$8, %rax
	cmpq	%rsi, %rax
	jne	.LB.permute_at_lowest_height.17
.LB.permute_at_lowest_height.18:
	movq	48(%rsp), %rdx
.LB.permute_at_lowest_height.19:
	movq	%rdx, %rax
	addq	$32872, %rsp
	popq	%rbx
	popq	%rbp
	ret
.LB.permute_at_lowest_height.20:
	testq	%rsi, %rsi
	jne	.LB.permute_at_lowest_height.1
.LB.permute_at_lowest_height.21:
	movq	%rcx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%rdi, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32904(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB.permute_at_lowest_height.8
	.size	permute_at_lowest_height, .-permute_at_lowest_height
	.globl	build_mapping
	.type	build_mapping, @function
build_mapping:
	pushq	%rbp
	pushq	%rbx
	subq	$16456, %rsp
	movq	%rsi, %rbx
	movq	%rdx, %rsi
	movq	16480(%rsp), %rbp
	cmpq	$1024, %rbx
	seta	%al
	cmpb	$1, %r9b
	seta	%dl
	orb	%dl, %al
	jne	.LB.build_mapping.7
	cmpq	$1024, %rdi
	ja	.LB.build_mapping.7
	testq	%rdi, %rdi
	je	.LB.build_mapping.1
	movl	$0, %eax
	.p2align 5
.LB.build_mapping.0:
	movq	$-1, 64(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB.build_mapping.0
.LB.build_mapping.1:
	testq	%rbx, %rbx
	je	.LB.build_mapping.3
	leaq	64(%rsp), %rax
	leaq	(%rax,%rbx,8), %rdx
	.p2align 5
.LB.build_mapping.2:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB.build_mapping.2
.LB.build_mapping.3:
	movq	%rsi, (%rsp)
	movq	%rdi, 8(%rsp)
	movq	%rcx, 16(%rsp)
	movq	%rbx, 24(%rsp)
	movq	%r8, 32(%rsp)
	movb	%r9b, 40(%rsp)
	leaq	64(%rsp), %rax
	movq	%rax, 48(%rsp)
	movb	$0, 56(%rsp)
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder10mapInPlaceEv
	testb	%al, %al
	jne	.LB.build_mapping.8
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder16mapClosestCopiesEv
	testb	%al, %al
	jne	.LB.build_mapping.9
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder21mapWildcardSlotCopiesEv
	testb	%al, %al
	jne	.LB.build_mapping.10
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder17keepWildcardSlotsEv
	testb	%al, %al
	jne	.LB.build_mapping.11
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder13absorbSurplusEv
	testb	%al, %al
	jne	.LB.build_mapping.12
	testq	%rbx, %rbx
	je	.LB.build_mapping.5
	leaq	0(,%rbx,8), %rdx
	movl	$0, %eax
	leaq	8256(%rsp), %rsi
	.p2align 5
.LB.build_mapping.4:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, 0(%rbp,%rax)
	addq	$8, %rax
	cmpq	%rax, %rdx
	jne	.LB.build_mapping.4
.LB.build_mapping.5:
	movq	16488(%rsp), %rax
	movzbl	56(%rsp), %edx
	movb	%dl, (%rax)
	movl	$0, %eax
.LB.build_mapping.6:
	addq	$16456, %rsp
	popq	%rbx
	popq	%rbp
	ret
.LB.build_mapping.7:
	movq	$-2, %rax
	jmp	.LB.build_mapping.6
.LB.build_mapping.8:
	movq	$-2, %rax
	jmp	.LB.build_mapping.6
.LB.build_mapping.9:
	movq	$-2, %rax
	jmp	.LB.build_mapping.6
.LB.build_mapping.10:
	movq	$-2, %rax
	jmp	.LB.build_mapping.6
.LB.build_mapping.11:
	movq	$-2, %rax
	jmp	.LB.build_mapping.6
.LB.build_mapping.12:
	movq	$-2, %rax
	jmp	.LB.build_mapping.6
	.size	build_mapping, .-build_mapping
	.globl	resolve
	.type	resolve, @function
resolve:
	pushq	%rbp
	pushq	%rbx
	subq	$32840, %rsp
	movq	%r8, %rbx
	movq	32864(%rsp), %r11
	movq	32896(%rsp), %rbp
	movl	32904(%rsp), %r8d
	cmpq	$1024, %rdi
	ja	.LB.resolve.13
	movq	%rsi, %r10
	movq	%rdx, %rsi
	cmpq	$1024, %r10
	ja	.LB.resolve.13
	cmpq	$1024, %r9
	seta	%al
	cmpq	%r9, 32872(%rsp)
	setnb	%dl
	orb	%dl, %al
	jne	.LB.resolve.14
	cmpb	$1, %r8b
	ja	.LB.resolve.14
	testq	%rdi, %rdi
	je	.LB.resolve.15
	movl	$0, %eax
	jmp	.LB.resolve.1
	.p2align 5
.LB.resolve.0:
	leaq	1(%rax), %rdx
	cmpq	%rdx, %rdi
	je	.LB.resolve.2
	movq	%rdx, %rax
.LB.resolve.1:
	cmpb	$0, 5(%rsi,%rax,8)
	je	.LB.resolve.0
	cmpb	$0, 4(%rsi,%rax,8)
	jne	.LB.resolve.0
	movl	(%rsi,%rax,8), %edx
	cmpq	%rbp, %rdx
	jb	.LB.resolve.0
	movq	$-2, %rdx
	jmp	.LB.resolve.12
.LB.resolve.2:
	movl	$0, %edx
	addq	$1, %rax
	.p2align 5
.LB.resolve.3:
	movq	$-1, 16448(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB.resolve.3
	testq	%r10, %r10
	je	.LB.resolve.6
.LB.resolve.4:
	movl	$0, %eax
	.p2align 5
.LB.resolve.5:
	movq	$-1, 24640(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%r10, %rax
	jb	.LB.resolve.5
	testq	%rdi, %rdi
	je	.LB.resolve.16
.LB.resolve.6:
	movl	$0, %eax
	jmp	.LB.resolve.8
	.p2align 5
.LB.resolve.7:
	addq	$1, %rax
	cmpq	%rax, %rdi
	je	.LB.resolve.16
.LB.resolve.8:
	movq	(%rbx,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB.resolve.7
	movq	%rdx, 16448(%rsp,%rax,8)
	movq	%rax, 24640(%rsp,%rdx,8)
	jmp	.LB.resolve.7
	.p2align 5
.LB.resolve.9:
	addq	$1, %rax
	cmpq	%r9, %rax
	jnb	.LB.resolve.11
.LB.resolve.10:
	movq	(%r11,%rax,8), %rdx
	cmpq	$-1, %rdx
	je	.LB.resolve.9
	movq	%rdx, 64(%rsp,%rax,8)
	movq	%rax, 8256(%rsp,%rdx,8)
	jmp	.LB.resolve.9
.LB.resolve.11:
	movq	%rsi, (%rsp)
	movq	%rdi, 8(%rsp)
	movq	%rcx, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	32888(%rsp), %rax
	movq	%rax, 32(%rsp)
	cmpb	$1, %r8b
	sete	40(%rsp)
	movq	32912(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	32872(%rsp), %rax
	movq	32880(%rsp), %rdx
	leaq	16448(%rsp), %rsi
	movq	%rsp, %rdi
	leaq	64(%rsp), %r8
	movq	%rdx, %rcx
	movq	%rax, %rdx
	call	_ZN12_GLOBAL__N_17Planner7resolveERKNS_7MappingENS_8Emission7BlockedES3_m
	movq	$-1, %rdx
	cmpb	$1, %al
	je	.LB.resolve.12
	cmpb	$2, %al
	setne	%dl
	movzbl	%dl, %edx
	leaq	-2(%rdx,%rdx), %rdx
.LB.resolve.12:
	movq	%rdx, %rax
	addq	$32840, %rsp
	popq	%rbx
	popq	%rbp
	ret
.LB.resolve.13:
	movq	$-2, %rdx
	jmp	.LB.resolve.12
.LB.resolve.14:
	movq	$-2, %rdx
	jmp	.LB.resolve.12
.LB.resolve.15:
	testq	%r10, %r10
	jne	.LB.resolve.4
.LB.resolve.16:
	movl	$0, %eax
	.p2align 5
.LB.resolve.17:
	movq	$-1, 64(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%r9, %rax
	jb	.LB.resolve.17
	testq	%r10, %r10
	je	.LB.resolve.19
	leaq	64(%rsp), %rax
	leaq	(%rax,%r10,8), %rdx
	.p2align 5
.LB.resolve.18:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rax, %rdx
	jne	.LB.resolve.18
.LB.resolve.19:
	movl	$0, %eax
	jmp	.LB.resolve.10
	.size	resolve, .-resolve
	.globl	emit
	.type	emit, @function
emit:
	pushq	%rbx
	subq	$32864, %rsp
	movq	%r8, %rbx
	movq	32880(%rsp), %r8
	cmpq	$1024, %rdi
	ja	.LB.emit.16
	movq	%rdx, %r10
	movq	%rcx, %rdx
	cmpq	$1024, %rsi
	ja	.LB.emit.16
	testq	%rsi, %rsi
	je	.LB.emit.2
	movl	$0, %eax
	jmp	.LB.emit.1
	.p2align 4
.LB.emit.0:
	addq	$1, %rax
	cmpq	%rax, %rsi
	je	.LB.emit.2
.LB.emit.1:
	cmpb	$0, 4(%rdx,%rax,8)
	jne	.LB.emit.0
	cmpb	$0, 5(%rdx,%rax,8)
	je	.LB.emit.0
	movl	(%rdx,%rax,8), %ecx
	cmpq	%r8, %rcx
	jb	.LB.emit.0
	movq	$-2, %rdx
	jmp	.LB.emit.22
.LB.emit.2:
	testq	%rdi, %rdi
	je	.LB.emit.23
	movl	$0, %eax
	.p2align 5
.LB.emit.3:
	movq	$-1, 16480(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB.emit.3
	testq	%rsi, %rsi
	je	.LB.emit.6
.LB.emit.4:
	leaq	16480(%rsp), %rax
	leaq	(%rax,%rsi,8), %rcx
	.p2align 5
.LB.emit.5:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rcx, %rax
	jne	.LB.emit.5
	testq	%rdi, %rdi
	je	.LB.emit.24
.LB.emit.6:
	movl	$0, %eax
	jmp	.LB.emit.8
	.p2align 5
.LB.emit.7:
	leaq	1(%rax), %rcx
	cmpq	%rcx, %rdi
	je	.LB.emit.9
	movq	%rcx, %rax
.LB.emit.8:
	movq	(%rbx,%rax,8), %rcx
	cmpq	$-1, %rcx
	je	.LB.emit.7
	movq	%rcx, 16480(%rsp,%rax,8)
	movq	%rax, 24672(%rsp,%rcx,8)
	jmp	.LB.emit.7
.LB.emit.9:
	movq	%rdx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	%rcx, 32(%rsp)
	movq	32888(%rsp), %rdi
	movq	%rdi, 40(%rsp)
	movq	$0, 48(%rsp)
	movl	$0, %edx
	movq	%rcx, %rax
	.p2align 5
.LB.emit.10:
	movq	16480(%rsp,%rdx,8), %rcx
	movq	%rcx, 56(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rax, %rdx
	jne	.LB.emit.10
.LB.emit.11:
	testq	%rsi, %rsi
	je	.LB.emit.17
	salq	$3, %rsi
	movl	$0, %eax
	leaq	8248(%rsp), %rdi
	leaq	24672(%rsp), %rcx
	.p2align 5
.LB.emit.12:
	movq	(%rcx,%rax), %rdx
	movq	%rdx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rsi, %rax
	jne	.LB.emit.12
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
	movq	%rsp, %rax
	addq	%rsp, %rsi
	jmp	.LB.emit.14
	.p2align 5
.LB.emit.13:
	addq	$8, %rax
	cmpq	%rsi, %rax
	je	.LB.emit.18
.LB.emit.14:
	cmpq	$-1, 8248(%rax)
	jne	.LB.emit.13
	addq	$1, 16440(%rsp)
	jmp	.LB.emit.13
.LB.emit.15:
	movq	16448(%rsp), %rax
	movq	32896(%rsp), %rdi
	movq	%rax, (%rdi)
	movq	16456(%rsp), %rax
	movq	%rax, 8(%rdi)
	jmp	.LB.emit.19
.LB.emit.16:
	movq	$-2, %rdx
	jmp	.LB.emit.22
.LB.emit.17:
	movq	$0, 16440(%rsp)
	leaq	16480(%rsp), %rax
	movq	%rax, 16464(%rsp)
.LB.emit.18:
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_18Emission3runEv
	cmpb	$1, %al
	je	.LB.emit.15
	movq	$-2, %rdx
	cmpb	$2, %al
	je	.LB.emit.22
	testb	%al, %al
	jne	.LB.emit.19
	movq	32896(%rsp), %rax
	movq	$0, (%rax)
	movq	$0, 8(%rax)
.LB.emit.19:
	movq	32(%rsp), %rcx
	movq	32904(%rsp), %rax
	movq	%rcx, (%rax)
	testq	%rcx, %rcx
	je	.LB.emit.21
	salq	$3, %rcx
	movl	$0, %eax
	leaq	56(%rsp), %rsi
	.p2align 5
.LB.emit.20:
	movq	(%rsi,%rax), %rdx
	movq	%rdx, (%rbx,%rax)
	addq	$8, %rax
	cmpq	%rax, %rcx
	jne	.LB.emit.20
.LB.emit.21:
	movq	48(%rsp), %rdx
.LB.emit.22:
	movq	%rdx, %rax
	addq	$32864, %rsp
	popq	%rbx
	ret
.LB.emit.23:
	testq	%rsi, %rsi
	jne	.LB.emit.4
.LB.emit.24:
	movq	%rdx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	32888(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 48(%rsp)
	jmp	.LB.emit.11
	.size	emit, .-emit
	.globl	plan
	.type	plan, @function
plan:
	pushq	%rbx
	subq	$80, %rsp
	movl	96(%rsp), %ebx
	movl	104(%rsp), %eax
	cmpq	$1024, %rdi
	ja	.LB.plan.12
	movl	%eax, %r11d
	cmpq	$1024, %rsi
	ja	.LB.plan.12
	orl	%ebx, %eax
	cmpb	$1, %al
	ja	.LB.plan.13
	testq	%rdi, %rdi
	je	.LB.plan.14
	movl	$0, %eax
	jmp	.LB.plan.1
	.p2align 4
.LB.plan.0:
	addq	$1, %rax
	cmpq	%rax, %rdi
	je	.LB.plan.2
.LB.plan.1:
	cmpb	$0, 5(%rdx,%rax,8)
	je	.LB.plan.0
	cmpb	$0, 4(%rdx,%rax,8)
	jne	.LB.plan.0
	movl	(%rdx,%rax,8), %r10d
	cmpq	%r9, %r10
	jb	.LB.plan.0
	movq	$-2, %rdx
	jmp	.LB.plan.9
.LB.plan.2:
	testq	%rsi, %rsi
	je	.LB.plan.6
	movl	$0, %eax
	jmp	.LB.plan.4
	.p2align 4
.LB.plan.3:
	addq	$1, %rax
	cmpq	%rsi, %rax
	jnb	.LB.plan.5
.LB.plan.4:
	cmpb	$0, 5(%rcx,%rax,8)
	je	.LB.plan.3
	cmpb	$0, 4(%rcx,%rax,8)
	jne	.LB.plan.3
	movl	(%rcx,%rax,8), %r10d
	cmpq	%r9, %r10
	jb	.LB.plan.3
	movq	$-2, %rdx
	jmp	.LB.plan.9
.LB.plan.5:
	testq	%rdi, %rdi
	je	.LB.plan.8
.LB.plan.6:
	movq	112(%rsp), %rax
	movq	%rdi, %r9
	addq	%rax, %r9
	.p2align 4
.LB.plan.7:
	movb	$0, (%rax)
	addq	$1, %rax
	cmpq	%rax, %r9
	jne	.LB.plan.7
.LB.plan.8:
	movq	%rdx, 16(%rsp)
	movq	%rdi, 24(%rsp)
	movq	%rcx, 32(%rsp)
	movq	%rsi, 40(%rsp)
	movq	%r8, 48(%rsp)
	cmpb	$1, %bl
	sete	56(%rsp)
	movq	112(%rsp), %rax
	movq	%rax, 64(%rsp)
	movq	$0, 8(%rsp)
	leaq	16(%rsp), %rdi
	leaq	8(%rsp), %r9
	movq	144(%rsp), %r8
	movq	136(%rsp), %rcx
	movq	128(%rsp), %rdx
	movl	%r11d, %esi
	call	_ZN12_GLOBAL__N_17Planner3runENS_14MappingBuilder21WildcardSlotsStrategyEP9StackSlotP9ShuffleOpPNS_8OptionalI11StackOffsetEERm
	cmpb	$1, %al
	je	.LB.plan.11
	movq	$-2, %rdx
	cmpb	$2, %al
	jne	.LB.plan.10
.LB.plan.9:
	movq	%rdx, %rax
	addq	$80, %rsp
	popq	%rbx
	ret
.LB.plan.10:
	movzbl	72(%rsp), %eax
	movq	120(%rsp), %rbx
	movb	%al, (%rbx)
	movq	8(%rsp), %rdx
	jmp	.LB.plan.9
.LB.plan.11:
	movzbl	72(%rsp), %eax
	movq	120(%rsp), %rbx
	movb	%al, (%rbx)
	movq	$-1, %rdx
	jmp	.LB.plan.9
.LB.plan.12:
	movq	$-2, %rdx
	jmp	.LB.plan.9
.LB.plan.13:
	movq	$-2, %rdx
	jmp	.LB.plan.9
.LB.plan.14:
	movq	%rdi, %rax
	testq	%rsi, %rsi
	jne	.LB.plan.4
	jmp	.LB.plan.8
	.size	plan, .-plan
	.section	.note.GNU-stack,"",@progbits
