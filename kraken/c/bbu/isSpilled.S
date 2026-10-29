isSpilled:
	movl	$0, %eax
	cmpq	$1, %rsi
	jbe	.LB1
	testb	$1, %sil
	jne	.LB1
	subq	$2, %rsi
	shrq	%rsi
	movq	40(%rdi), %rax
	cmpb	$0, (%rax,%rsi)
	setne	%al
	movzbl	%al, %eax
.LB1:
	ret
	.size	isSpilled, .-isSpilled
