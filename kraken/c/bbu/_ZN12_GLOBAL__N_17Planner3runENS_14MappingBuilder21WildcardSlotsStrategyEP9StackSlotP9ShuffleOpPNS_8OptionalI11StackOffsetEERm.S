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
	je	.LB.Planner.run.5
	movq	16(%rdi), %r10
	movl	$0, %ecx
	jmp	.LB.Planner.run.1
	.p2align 5
.LB.Planner.run.0:
	addq	$1, %rcx
	cmpq	%r11, %rcx
	je	.LB.Planner.run.5
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
	jne	.LB.Planner.run.4
	movl	(%r10,%rcx,8), %eax
	movq	32(%rbx), %rdx
	cmpb	$0, (%rdx,%rax)
	jne	.LB.Planner.run.0
.LB.Planner.run.4:
	movl	$1, %edi
	call	exit
.LB.Planner.run.5:
	leaq	32(%rsp), %r13
	movq	%rbp, 24(%rsp)
.LB.Planner.run.6:
	movq	8(%rbx), %rdx
	movq	24(%rbx), %rsi
	testq	%rdx, %rdx
	je	.LB.Planner.run.8
	movl	$0, %eax
	.p2align 5
.LB.Planner.run.7:
	movq	$-1, 96(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdx
	jne	.LB.Planner.run.7
.LB.Planner.run.8:
	testq	%rsi, %rsi
	je	.LB.Planner.run.10
	leaq	96(%rsp), %rax
	leaq	(%rax,%rsi,8), %rcx
	.p2align 5
.LB.Planner.run.9:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rcx, %rax
	jne	.LB.Planner.run.9
.LB.Planner.run.10:
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
	jne	.LB.Planner.run.20
	movq	%r13, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder16mapClosestCopiesEv
	testb	%al, %al
	jne	.LB.Planner.run.22
	movq	%r13, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder21mapWildcardSlotCopiesEv
	testb	%al, %al
	jne	.LB.Planner.run.23
	movq	%r13, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder17keepWildcardSlotsEv
	testb	%al, %al
	jne	.LB.Planner.run.24
	movq	%r13, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder13absorbSurplusEv
	testb	%al, %al
	jne	.LB.Planner.run.25
	movzbl	56(%rbx), %eax
	testb	%al, %al
	movzbl	88(%rsp), %edx
	cmove	%edx, %eax
	movb	%al, 56(%rbx)
	cmpq	$0, 8(%rbx)
	je	.LB.Planner.run.32
	movl	$0, %eax
	.p2align 5
.LB.Planner.run.11:
	movq	(%rbx), %rdx
	movq	(%rdx,%rax,8), %rdx
	movq	%rdx, (%r12,%rax,8)
	addq	$1, %rax
	movq	8(%rbx), %rdx
	cmpq	%rdx, %rax
	jb	.LB.Planner.run.11
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
	je	.LB.Planner.run.13
	movl	$0, %eax
	.p2align 5
.LB.Planner.run.12:
	movq	96(%rsp,%rax,8), %rsi
	movq	%rsi, 16536(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdx
	jne	.LB.Planner.run.12
.LB.Planner.run.13:
	testq	%rcx, %rcx
	je	.LB.Planner.run.26
	leaq	0(,%rcx,8), %rdx
	movl	$0, %eax
	leaq	24728(%rsp), %rdi
	leaq	8288(%rsp), %rsi
	.p2align 5
.LB.Planner.run.14:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	%rax, %rdx
	jne	.LB.Planner.run.14
	movq	$0, 32920(%rsp)
	leaq	96(%rsp), %rax
	movq	%rax, 32944(%rsp)
	leaq	16480(%rsp), %rax
	addq	%rax, %rdx
	jmp	.LB.Planner.run.16
	.p2align 5
.LB.Planner.run.15:
	addq	$8, %rax
	cmpq	%rax, %rdx
	je	.LB.Planner.run.27
.LB.Planner.run.16:
	cmpq	$-1, 8248(%rax)
	jne	.LB.Planner.run.15
	addq	$1, 32920(%rsp)
	jmp	.LB.Planner.run.15
.LB.Planner.run.17:
	movq	24(%rsp), %rbp
	testb	%al, %al
	jne	.LB.Planner.run.21
	cmpq	$0, 24(%rbx)
	je	.LB.Planner.run.19
	movl	$0, %edx
.LB.Planner.run.18:
	movq	8288(%rsp,%rdx,8), %rcx
	movq	16(%rsp), %rdi
	movq	%rcx, (%rdi,%rdx,8)
	addq	$1, %rdx
	cmpq	24(%rbx), %rdx
	jb	.LB.Planner.run.18
.LB.Planner.run.19:
	movq	16528(%rsp), %rdx
	movq	%rdx, 0(%rbp)
	jmp	.LB.Planner.run.21
.LB.Planner.run.20:
	movl	$2, %eax
.LB.Planner.run.21:
	addq	$32968, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB.Planner.run.22:
	movl	$2, %eax
	jmp	.LB.Planner.run.21
.LB.Planner.run.23:
	movl	$2, %eax
	jmp	.LB.Planner.run.21
.LB.Planner.run.24:
	movl	$2, %eax
	jmp	.LB.Planner.run.21
.LB.Planner.run.25:
	movl	$2, %eax
	jmp	.LB.Planner.run.21
.LB.Planner.run.26:
	movq	$0, 32920(%rsp)
	leaq	96(%rsp), %rax
	movq	%rax, 32944(%rsp)
.LB.Planner.run.27:
	leaq	16480(%rsp), %rdi
	call	_ZN12_GLOBAL__N_18Emission3runEv
	cmpb	$1, %al
	jne	.LB.Planner.run.17
	movq	8(%rbx), %rbp
	testq	%rbp, %rbp
	je	.LB.Planner.run.29
	movq	48(%rbx), %rax
	leaq	0(%rbp,%rax), %rdx
	movl	$0, %ebp
	.p2align 4
.LB.Planner.run.28:
	cmpb	$1, (%rax)
	sbbq	$-1, %rbp
	addq	$1, %rax
	cmpq	%rdx, %rax
	jne	.LB.Planner.run.28
.LB.Planner.run.29:
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
	je	.LB.Planner.run.21
	cmpb	$2, %al
	je	.LB.Planner.run.21
	movq	8(%rbx), %rcx
	testq	%rcx, %rcx
	je	.LB.Planner.run.31
	movq	48(%rbx), %rax
	addq	%rax, %rcx
	movl	$0, %edx
	.p2align 4
.LB.Planner.run.30:
	cmpb	$1, (%rax)
	sbbq	$-1, %rdx
	addq	$1, %rax
	cmpq	%rcx, %rax
	jne	.LB.Planner.run.30
	cmpq	%rdx, %rbp
	jb	.LB.Planner.run.6
.LB.Planner.run.31:
	movl	$1, %edi
	call	exit
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
	jmp	.LB.Planner.run.13
	.size	_ZN12_GLOBAL__N_17Planner3runENS_14MappingBuilder21WildcardSlotsStrategyEP9StackSlotP9ShuffleOpPNS_8OptionalI11StackOffsetEERm, .-_ZN12_GLOBAL__N_17Planner3runENS_14MappingBuilder21WildcardSlotsStrategyEP9StackSlotP9ShuffleOpPNS_8OptionalI11StackOffsetEERm
