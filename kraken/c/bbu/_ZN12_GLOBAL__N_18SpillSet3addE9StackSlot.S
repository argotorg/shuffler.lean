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
