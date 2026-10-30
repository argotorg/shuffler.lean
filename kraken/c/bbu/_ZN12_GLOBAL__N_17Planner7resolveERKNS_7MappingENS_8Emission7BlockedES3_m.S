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
