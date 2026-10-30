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
