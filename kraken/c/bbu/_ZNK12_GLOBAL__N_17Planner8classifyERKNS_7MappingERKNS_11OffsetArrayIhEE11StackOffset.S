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
