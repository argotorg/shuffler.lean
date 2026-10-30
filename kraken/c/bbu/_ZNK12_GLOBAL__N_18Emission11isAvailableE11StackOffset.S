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
