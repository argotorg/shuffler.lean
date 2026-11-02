_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot:
	subq	$8, %rsp
	movq	%rsi, %rax
	shrq	$32, %rax
	testb	%al, %al
	jne	.LB.SpillSet.add.0
	movq	%rsi, %rax
	shrq	$40, %rax
	testb	%al, %al
	je	.LB.SpillSet.add.0
	movl	%esi, %esi
	addq	(%rdi), %rsi
	cmpb	$0, (%rsi)
	jne	.LB.SpillSet.add.1
	movb	$1, (%rsi)
	movl	$0, %eax
	addq	$8, %rsp
	ret
.LB.SpillSet.add.0:
	movl	$1, %edi
	call	exit
.LB.SpillSet.add.1:
	movl	$1, %edi
	call	exit
	.size	_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot, .-_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot
