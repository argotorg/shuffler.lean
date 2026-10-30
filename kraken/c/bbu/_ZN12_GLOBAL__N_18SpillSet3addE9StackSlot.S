_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot:
	movq	%rsi, %rdx
	shrq	$32, %rdx
	movl	$2, %eax
	testb	%dl, %dl
	jne	.LB245
	movq	%rsi, %rdx
	shrq	$40, %rdx
	testb	%dl, %dl
	je	.LB245
	movl	%esi, %esi
	addq	(%rdi), %rsi
	movzbl	(%rsi), %eax
	testb	%al, %al
	jne	.LB249
	movb	$1, (%rsi)
	ret
.LB249:
	movl	$2, %eax
.LB245:
	ret
	.size	_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot, .-_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot
