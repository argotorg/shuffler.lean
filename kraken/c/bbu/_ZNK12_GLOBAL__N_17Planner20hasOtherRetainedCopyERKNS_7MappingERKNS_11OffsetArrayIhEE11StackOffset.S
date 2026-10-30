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
