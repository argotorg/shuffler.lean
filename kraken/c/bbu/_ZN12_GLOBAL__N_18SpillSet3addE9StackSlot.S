_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot:
	movq	%rsi, %rdx
	shrq	$32, %rdx
	movl	$2, %eax
	testb	%dl, %dl
	jne	.LB239
	movq	%rsi, %rdx
	shrq	$40, %rdx
	testb	%dl, %dl
	je	.LB239
	movl	%esi, %esi
	addq	(%rdi), %rsi
	movzbl	(%rsi), %eax
	testb	%al, %al
	jne	.LB243
	movb	$1, (%rsi)
	ret
.LB243:
	movl	$2, %eax
.LB239:
	ret
	.size	_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot, .-_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot
