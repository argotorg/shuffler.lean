build_mapping:
	pushq	%rbp
	pushq	%rbx
	subq	$16456, %rsp
	movq	%rsi, %rbx
	movq	%rdx, %rsi
	movq	16480(%rsp), %rbp
	cmpq	$1024, %rbx
	seta	%al
	cmpb	$1, %r9b
	seta	%dl
	orb	%dl, %al
	jne	.LB.build_mapping.7
	cmpq	$1024, %rdi
	ja	.LB.build_mapping.7
	testq	%rdi, %rdi
	je	.LB.build_mapping.1
	movl	$0, %eax
	.p2align 5
.LB.build_mapping.0:
	movq	$-1, 64(%rsp,%rax,8)
	addq	$1, %rax
	cmpq	%rax, %rdi
	jne	.LB.build_mapping.0
.LB.build_mapping.1:
	testq	%rbx, %rbx
	je	.LB.build_mapping.3
	leaq	64(%rsp), %rax
	leaq	(%rax,%rbx,8), %rdx
	.p2align 5
.LB.build_mapping.2:
	movq	$-1, 8192(%rax)
	addq	$8, %rax
	cmpq	%rdx, %rax
	jne	.LB.build_mapping.2
.LB.build_mapping.3:
	movq	%rsi, (%rsp)
	movq	%rdi, 8(%rsp)
	movq	%rcx, 16(%rsp)
	movq	%rbx, 24(%rsp)
	movq	%r8, 32(%rsp)
	movb	%r9b, 40(%rsp)
	leaq	64(%rsp), %rax
	movq	%rax, 48(%rsp)
	movb	$0, 56(%rsp)
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder10mapInPlaceEv
	testb	%al, %al
	jne	.LB.build_mapping.8
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder16mapClosestCopiesEv
	testb	%al, %al
	jne	.LB.build_mapping.9
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder21mapWildcardSlotCopiesEv
	testb	%al, %al
	jne	.LB.build_mapping.10
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder17keepWildcardSlotsEv
	testb	%al, %al
	jne	.LB.build_mapping.11
	movq	%rsp, %rdi
	call	_ZN12_GLOBAL__N_114MappingBuilder13absorbSurplusEv
	testb	%al, %al
	jne	.LB.build_mapping.12
	testq	%rbx, %rbx
	je	.LB.build_mapping.5
	leaq	0(,%rbx,8), %rdx
	movl	$0, %eax
	leaq	8256(%rsp), %rsi
	.p2align 5
.LB.build_mapping.4:
	movq	(%rsi,%rax), %rcx
	movq	%rcx, 0(%rbp,%rax)
	addq	$8, %rax
	cmpq	%rax, %rdx
	jne	.LB.build_mapping.4
.LB.build_mapping.5:
	movq	16488(%rsp), %rax
	movzbl	56(%rsp), %edx
	movb	%dl, (%rax)
	movl	$0, %eax
.LB.build_mapping.6:
	addq	$16456, %rsp
	popq	%rbx
	popq	%rbp
	ret
.LB.build_mapping.7:
	movq	$-2, %rax
	jmp	.LB.build_mapping.6
.LB.build_mapping.8:
	movq	$-2, %rax
	jmp	.LB.build_mapping.6
.LB.build_mapping.9:
	movq	$-2, %rax
	jmp	.LB.build_mapping.6
.LB.build_mapping.10:
	movq	$-2, %rax
	jmp	.LB.build_mapping.6
.LB.build_mapping.11:
	movq	$-2, %rax
	jmp	.LB.build_mapping.6
.LB.build_mapping.12:
	movq	$-2, %rax
	jmp	.LB.build_mapping.6
	.size	build_mapping, .-build_mapping
