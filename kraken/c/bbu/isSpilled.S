isSpilled:
	movq	%rsi, %rdx
	shrq	$32, %rdx
	movl	$0, %eax
	testb	%dl, %dl
	jne	.LB1
	movq	%rsi, %rdx
	shrq	$40, %rdx
	testb	%dl, %dl
	je	.LB1
	movl	%esi, %esi
	movq	40(%rdi), %rax
	cmpb	$0, (%rax,%rsi)
	setne	%al
	movzbl	%al, %eax
.LB1:
	ret
	.size	isSpilled, .-isSpilled
