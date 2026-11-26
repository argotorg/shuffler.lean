	.file	"shuffler"
	.text
	.hidden	solidity_shuffler_shuffle
	.globl	solidity_shuffler_shuffle
	.type	solidity_shuffler_shuffle,@function
solidity_shuffler_shuffle:
	pushq	%rbp
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbx
	subq	$24, %rsp
	pushq	$2
	popq	%rbp
	cmpq	$1, 48(%rdi)
	jbe	.LBB0_65
	movq	%rdi, %rbx
	cmpq	$1024, 8(%rdi)
	ja	.LBB0_65
	cmpq	$1024, 24(%rbx)
	ja	.LBB0_65
	movabsq	$280375465082880, %r13
	movabsq	$1095216660480, %r15
	movq	(%rbx), %rax
	movq	40(%rbx), %r14
	leaq	357408(%r14), %rdi
	movq	%rax, 357408(%r14)
	movq	8(%rbx), %rax
	movq	%rax, 357416(%r14)
	movq	16(%rbx), %rax
	movq	%rax, 357424(%r14)
	movq	24(%rbx), %rax
	movq	%rax, 357432(%r14)
	movq	32(%rbx), %rax
	movq	%rax, 357440(%r14)
	movb	56(%rbx), %al
	andb	$1, %al
	movb	%al, 357448(%r14)
	leaq	355360(%r14), %rax
	movq	%rax, 357456(%r14)
	movb	$0, 357464(%r14)
	movq	48(%rbx), %rax
	movq	%rax, 357472(%r14)
	leaq	280608(%r14), %rax
	movq	%rax, 357480(%r14)
	movq	8(%rbx), %rax
	xorl	%ecx, %ecx
.LBB0_4:
	cmpq	%rcx, %rax
	je	.LBB0_9
	movq	(%rbx), %rdx
	movq	(%rdx,%rcx,8), %rdx
	testq	%r15, %rdx
	setne	%sil
	testq	%r13, %rdx
	sete	%r8b
	orb	%sil, %r8b
	je	.LBB0_7
	xorl	%edx, %edx
	jmp	.LBB0_8
.LBB0_7:
	movq	357440(%r14), %rsi
	movl	%edx, %edx
	cmpb	$0, (%rsi,%rdx)
	setne	%dl
.LBB0_8:
	movb	%dl, 356384(%r14,%rcx)
	incq	%rcx
	jmp	.LBB0_4
.LBB0_9:
	movq	8(%rbx), %rax
	movq	40(%rbx), %rbp
	xorl	%ecx, %ecx
.LBB0_10:
	cmpq	%rcx, %rax
	je	.LBB0_12
	movb	$0, 355360(%rbp,%rcx)
	incq	%rcx
	jmp	.LBB0_10
.LBB0_12:
	leaq	357488(%rbp), %rsi
	leaq	357608(%rbp), %rdx
	leaq	8192(%r14), %r9
	leaq	131080(%r14), %r12
	leaq	131072(%r14), %rax
	xorl	%ecx, %ecx
	movq	%r14, %r8
	pushq	%rax
	pushq	%r12
	callq	.Lshuffler.Planner.run
	popq	%rcx
	popq	%rdx
	movb	$1, %r8b
	testw	%ax, %ax
	jne	.LBB0_68
.LBB0_13:
	movq	8(%rbx), %rax
	xorl	%ecx, %ecx
.LBB0_14:
	cmpq	%rcx, %rax
	je	.LBB0_19
	movq	(%rbx), %rdx
	movq	(%rdx,%rcx,8), %rdx
	testq	%r15, %rdx
	setne	%sil
	testq	%r13, %rdx
	sete	%dil
	orb	%sil, %dil
	je	.LBB0_17
	xorl	%edx, %edx
	jmp	.LBB0_18
.LBB0_17:
	movq	357440(%r14), %rsi
	movl	%edx, %edx
	cmpb	$0, (%rsi,%rdx)
	setne	%dl
.LBB0_18:
	movb	%dl, 139272(%r14,%rcx)
	incq	%rcx
	jmp	.LBB0_14
.LBB0_19:
	andq	$0, 140296(%r14)
	movq	8(%rbx), %rax
	xorl	%ecx, %ecx
.LBB0_20:
	cmpq	%rcx, %rax
	je	.LBB0_26
	cmpb	$0, 356384(%rbp,%rcx)
	jne	.LBB0_25
	movq	(%rbx), %rdx
	movq	(%rdx,%rcx,8), %rdx
	testq	%r15, %rdx
	setne	%sil
	testq	%r13, %rdx
	sete	%dil
	orb	%sil, %dil
	jne	.LBB0_25
	movq	357440(%r14), %rsi
	movl	%edx, %edx
	cmpb	$0, (%rsi,%rdx)
	je	.LBB0_25
	movq	32(%rbx), %rsi
	movb	$0, (%rsi,%rdx)
	incq	140296(%r14)
.LBB0_25:
	incq	%rcx
	jmp	.LBB0_20
.LBB0_26:
	testb	$1, 357464(%r14)
	je	.LBB0_30
	movq	8(%rbx), %rax
	movq	40(%rbx), %r12
	xorl	%ecx, %ecx
	pushq	$2
	popq	%rbp
.LBB0_28:
	cmpq	%rcx, %rax
	je	.LBB0_36
	movb	$0, 355360(%r12,%rcx)
	incq	%rcx
	jmp	.LBB0_28
.LBB0_30:
	testb	%r8b, %r8b
	je	.LBB0_54
	movq	8(%rbx), %rax
	xorl	%ecx, %ecx
.LBB0_32:
	cmpq	%rcx, %rax
	je	.LBB0_55
	movq	(%rbx), %rdx
	movq	(%rdx,%rcx,8), %rdx
	testq	%r15, %rdx
	setne	%sil
	testq	%r13, %rdx
	sete	%dil
	orb	%sil, %dil
	jne	.LBB0_35
	movl	%edx, %edx
	movq	32(%rbx), %rsi
	movb	139272(%r14,%rcx), %dil
	movb	%dil, (%rsi,%rdx)
.LBB0_35:
	incq	%rcx
	jmp	.LBB0_32
.LBB0_36:
	movl	%r8d, 12(%rsp)
	leaq	140304(%r14), %r8
	leaq	357488(%r12), %rsi
	leaq	357608(%r12), %rdx
	leaq	148496(%r14), %r9
	leaq	271384(%r14), %rax
	leaq	271376(%r14), %r10
	pushq	$1
	popq	%rcx
	leaq	357408(%r14), %rdi
	movq	%r8, 16(%rsp)
	pushq	%r10
	pushq	%rax
	callq	.Lshuffler.Planner.run
	popq	%rcx
	popq	%rdx
	testw	%ax, %ax
	jne	.LBB0_72
	xorl	%eax, %eax
	movl	12(%rsp), %r10d
.LBB0_38:
	movq	8(%rbx), %rcx
	xorl	%edx, %edx
.LBB0_39:
	cmpq	%rdx, %rcx
	je	.LBB0_44
	movq	(%rbx), %rsi
	movq	(%rsi,%rdx,8), %rsi
	testq	%r15, %rsi
	setne	%dil
	testq	%r13, %rsi
	sete	%r8b
	orb	%dil, %r8b
	je	.LBB0_42
	xorl	%esi, %esi
	jmp	.LBB0_43
.LBB0_42:
	movq	357440(%r14), %rdi
	movl	%esi, %esi
	cmpb	$0, (%rdi,%rsi)
	setne	%sil
.LBB0_43:
	movb	%sil, 279576(%r14,%rdx)
	incq	%rdx
	jmp	.LBB0_39
.LBB0_44:
	andq	$0, 280600(%r14)
	movq	8(%rbx), %rdx
	xorl	%ecx, %ecx
	xorl	%esi, %esi
.LBB0_45:
	cmpq	%rsi, %rdx
	je	.LBB0_51
	cmpb	$0, 356384(%r12,%rsi)
	jne	.LBB0_50
	movq	(%rbx), %rdi
	movq	(%rdi,%rsi,8), %rdi
	testq	%r15, %rdi
	setne	%r8b
	testq	%r13, %rdi
	sete	%r9b
	orb	%r8b, %r9b
	jne	.LBB0_50
	movq	357440(%r14), %r8
	movl	%edi, %edi
	cmpb	$0, (%r8,%rdi)
	je	.LBB0_50
	movq	32(%rbx), %rcx
	movb	$0, (%rcx,%rdi)
	movq	280600(%r14), %rcx
	incq	%rcx
	movq	%rcx, 280600(%r14)
.LBB0_50:
	incq	%rsi
	jmp	.LBB0_45
.LBB0_51:
	movl	%r10d, %edx
	xorb	$1, %dl
	pushq	$1
	popq	%rbp
	testb	%dl, %al
	jne	.LBB0_65
	orb	%dl, %al
	cmpb	$1, %al
	jne	.LBB0_56
	testb	%r10b, %r10b
	je	.LBB0_57
	jmp	.LBB0_58
.LBB0_54:
	pushq	$1
.LBB0_70:
	popq	%rbp
	jmp	.LBB0_65
.LBB0_55:
	movq	%r14, 64(%rbx)
	leaq	8192(%r14), %rax
	movq	%rax, 72(%rbx)
	movq	131072(%r14), %rax
	movq	%rax, 80(%rbx)
	movq	%r12, 88(%rbx)
	jmp	.LBB0_64
.LBB0_56:
	cmpq	140296(%r14), %rcx
	jae	.LBB0_66
.LBB0_57:
	movq	16(%rsp), %r14
.LBB0_58:
	movq	8(%rbx), %rax
	xorl	%ecx, %ecx
.LBB0_59:
	cmpq	%rcx, %rax
	je	.LBB0_63
	movq	(%rbx), %rdx
	movq	(%rdx,%rcx,8), %rdx
	testq	%r15, %rdx
	setne	%sil
	testq	%r13, %rdx
	sete	%dil
	orb	%sil, %dil
	jne	.LBB0_62
	movl	%edx, %edx
	movq	32(%rbx), %rsi
	movb	139272(%r14,%rcx), %dil
	movb	%dil, (%rsi,%rdx)
.LBB0_62:
	incq	%rcx
	jmp	.LBB0_59
.LBB0_63:
	movq	%r14, 64(%rbx)
	leaq	8192(%r14), %rax
	movq	%rax, 72(%rbx)
	movq	131072(%r14), %rax
	movq	%rax, 80(%rbx)
	addq	$131080, %r14
	movq	%r14, 88(%rbx)
.LBB0_64:
	xorl	%ebp, %ebp
.LBB0_65:
	movl	%ebp, %eax
	addq	$24, %rsp
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	popq	%rbp
	retq
.LBB0_66:
	jne	.LBB0_58
	leaq	271376(%r14), %rax
	movq	(%rax), %rax
	leaq	131072(%r14), %rcx
	cmpq	(%rcx), %rax
	jb	.LBB0_57
	jmp	.LBB0_58
.LBB0_68:
	movzwl	%ax, %eax
	cmpl	$1, %eax
	jne	.LBB0_71
	pushq	$2
	jmp	.LBB0_70
.LBB0_71:
	xorl	%r8d, %r8d
	jmp	.LBB0_13
.LBB0_72:
	movzwl	%ax, %eax
	cmpl	$1, %eax
	movl	12(%rsp), %r10d
	je	.LBB0_65
	movb	$1, %al
	jmp	.LBB0_38
.Lfunc_end0:
	.size	solidity_shuffler_shuffle, .Lfunc_end0-solidity_shuffler_shuffle

	.hidden	solidity_shuffler_workspaceAlignment
	.globl	solidity_shuffler_workspaceAlignment
	.type	solidity_shuffler_workspaceAlignment,@function
solidity_shuffler_workspaceAlignment:
	pushq	$8
	popq	%rax
	retq
.Lfunc_end1:
	.size	solidity_shuffler_workspaceAlignment, .Lfunc_end1-solidity_shuffler_workspaceAlignment

	.type	.Lshuffler.Planner.run,@function
.Lshuffler.Planner.run:
	pushq	%rbp
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbx
	subq	$24, %rsp
	movq	%r9, 16(%rsp)
	movq	%r8, %r15
	movq	%rsi, %rbx
	movq	%rdi, %r13
	movb	$0, 56(%rdi)
	movq	24(%rdi), %rax
	xorl	%r11d, %r11d
.LBB2_1:
	cmpq	%rax, %r11
	je	.LBB2_2
	movq	16(%r13), %rsi
	movq	(%rsi,%r11,8), %rbp
	movq	%rbp, %rsi
	shrq	$32, %rsi
	movq	%rbp, %rdi
	shrq	$40, %rdi
	testb	%dil, %dil
	sete	%dil
	leal	-1(%rsi), %r8d
	cmpb	$2, %r8b
	setb	%r8b
	orb	%dil, %r8b
	jne	.LBB2_14
	movq	(%r13), %rdi
	movq	8(%r13), %r8
	xorl	%r9d, %r9d
.LBB2_10:
	cmpq	%r9, %r8
	je	.LBB2_12
	movq	(%rdi,%r9,8), %r10
	xorq	%rbp, %r10
	shlq	$16, %r10
	incq	%r9
	testq	%r10, %r10
	jne	.LBB2_10
	jmp	.LBB2_14
.LBB2_12:
	movw	$1, %r14w
	testb	%sil, %sil
	jne	.LBB2_50
	movq	32(%r13), %rsi
	movl	%ebp, %edi
	cmpb	$0, (%rsi,%rdi)
	je	.LBB2_50
.LBB2_14:
	incq	%r11
	jmp	.LBB2_1
.LBB2_2:
	movq	8(%r13), %rax
	movl	%ecx, 4(%rsp)
	movq	%rdx, 8(%rsp)
.LBB2_3:
	movq	24(%r13), %rsi
	movq	72(%r13), %rbp
	xorl	%edx, %edx
.LBB2_4:
	cmpq	%rdx, %rax
	je	.LBB2_5
	orq	$-1, (%rbp,%rdx,8)
	incq	%rdx
	jmp	.LBB2_4
.LBB2_5:
	xorl	%eax, %eax
.LBB2_6:
	cmpq	%rax, %rsi
	je	.LBB2_16
	orq	$-1, 8192(%rbp,%rax,8)
	incq	%rax
	jmp	.LBB2_6
.LBB2_16:
	movq	(%r13), %rax
	movq	8(%rsp), %r12
	movq	%rax, (%r12)
	movq	8(%r13), %rax
	movq	%rax, 8(%r12)
	movq	16(%r13), %rax
	movq	%rax, 16(%r12)
	movq	24(%r13), %rax
	movq	%rax, 24(%r12)
	movq	48(%r13), %rax
	movq	%rax, 32(%r12)
	movb	%cl, 40(%r12)
	movq	%rbp, 48(%r12)
	movb	$0, 56(%r12)
	movq	%r12, %rdi
	callq	.Lshuffler.MappingBuilder.mapInPlace
	movw	$1, %r14w
	testw	%ax, %ax
	jne	.LBB2_50
	movq	%r12, %rdi
	callq	.Lshuffler.MappingBuilder.mapClosestCopies
	testw	%ax, %ax
	jne	.LBB2_50
	movq	%r12, %rdi
	callq	.Lshuffler.MappingBuilder.mapWildcardSlotCopies
	testw	%ax, %ax
	jne	.LBB2_50
	movq	%r12, %rdi
	callq	.Lshuffler.MappingBuilder.keepWildcardSlots
	testw	%ax, %ax
	jne	.LBB2_50
	movq	%r12, %rdi
	callq	.Lshuffler.MappingBuilder.absorbSurplus
	testw	%ax, %ax
	jne	.LBB2_50
	movb	$1, %al
	cmpb	$1, 56(%r13)
	je	.LBB2_22
	movq	8(%rsp), %rax
	movb	56(%rax), %al
	andb	$1, %al
.LBB2_22:
	movb	%al, 56(%r13)
	movq	8(%r13), %rax
	xorl	%ecx, %ecx
	movq	80(%rsp), %r12
.LBB2_23:
	cmpq	%rcx, %rax
	je	.LBB2_25
	movq	(%r13), %rdx
	movq	(%rdx,%rcx,8), %rdx
	movq	%rdx, (%r15,%rcx,8)
	incq	%rcx
	jmp	.LBB2_23
.LBB2_25:
	movq	8(%r13), %rdx
	movq	16(%r13), %rsi
	movq	24(%r13), %rax
	movq	32(%r13), %rdi
	movq	64(%r13), %r8
	movq	72(%r13), %rcx
	movq	%rsi, (%rbx)
	movq	%rax, 8(%rbx)
	movq	%rdi, 16(%rbx)
	movq	%r8, 24(%rbx)
	decq	%r8
	movq	%r8, 32(%rbx)
	movq	%r15, 40(%rbx)
	movq	%rdx, 48(%rbx)
	movq	16(%rsp), %rsi
	movq	%rsi, 56(%rbx)
	andq	$0, 64(%rbx)
	leaq	16384(%rcx), %rsi
	movq	%rsi, 72(%rbx)
	movq	%rbp, 104(%rbx)
	movq	%rcx, 112(%rbx)
	xorl	%edi, %edi
.LBB2_26:
	cmpq	%rdi, %rdx
	je	.LBB2_27
	movq	(%rbp,%rdi,8), %r8
	movq	%r8, (%rsi,%rdi,8)
	incq	%rdi
	jmp	.LBB2_26
.LBB2_27:
	xorl	%edx, %edx
.LBB2_28:
	cmpq	%rdx, %rax
	je	.LBB2_30
	movq	8192(%rbp,%rdx,8), %rsi
	movq	%rsi, 24576(%rcx,%rdx,8)
	incq	%rdx
	jmp	.LBB2_28
.LBB2_30:
	andq	$0, 80(%rbx)
	xorl	%ecx, %ecx
	xorl	%edx, %edx
.LBB2_31:
	cmpq	%rdx, %rax
	je	.LBB2_35
	movq	72(%rbx), %rsi
	cmpq	$-1, 8192(%rsi,%rdx,8)
	jne	.LBB2_34
	incq	%rcx
	movq	%rcx, 80(%rbx)
.LBB2_34:
	incq	%rdx
	jmp	.LBB2_31
.LBB2_35:
	movq	%rbx, %rdi
	callq	.Lshuffler.Emission.run
	testw	%ax, %ax
	je	.LBB2_38
	movzwl	%ax, %ecx
	cmpl	$1, %ecx
	je	.LBB2_37
	movq	8(%r13), %rax
	xorl	%r12d, %r12d
	xorl	%ecx, %ecx
.LBB2_43:
	cmpq	%rcx, %rax
	je	.LBB2_45
	movq	48(%r13), %rdx
	cmpb	$1, (%rdx,%rcx)
	sbbq	$-1, %r12
	incq	%rcx
	jmp	.LBB2_43
.LBB2_45:
	movq	48(%rbx), %r8
	movq	72(%rbx), %rcx
	movq	%r13, %rdi
	movq	%rbp, %rsi
	leaq	88(%rbx), %rdx
	callq	.Lshuffler.Planner.resolve
	testw	%ax, %ax
	jne	.LBB2_37
	movq	8(%r13), %rax
	xorl	%edi, %edi
	xorl	%r8d, %r8d
	movl	4(%rsp), %ecx
.LBB2_47:
	cmpq	%r8, %rax
	je	.LBB2_49
	movq	48(%r13), %rsi
	cmpb	$1, (%rsi,%r8)
	sbbq	$-1, %rdi
	incq	%r8
	jmp	.LBB2_47
.LBB2_49:
	cmpq	%r12, %rdi
	ja	.LBB2_3
	jmp	.LBB2_50
.LBB2_38:
	movq	24(%r13), %rax
	xorl	%ecx, %ecx
	movq	88(%rsp), %rsi
.LBB2_39:
	cmpq	%rcx, %rax
	je	.LBB2_41
	movq	8192(%rbp,%rcx,8), %rdx
	movq	%rdx, (%r12,%rcx,8)
	incq	%rcx
	jmp	.LBB2_39
.LBB2_41:
	movq	64(%rbx), %rax
	movq	%rax, (%rsi)
	xorl	%r14d, %r14d
.LBB2_50:
	movl	%r14d, %eax
	addq	$24, %rsp
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	popq	%rbp
	retq
.LBB2_37:
	movl	%eax, %r14d
	jmp	.LBB2_50
.Lfunc_end2:
	.size	.Lshuffler.Planner.run, .Lfunc_end2-.Lshuffler.Planner.run

	.hidden	solidity_shuffler_workspaceSize
	.globl	solidity_shuffler_workspaceSize
	.type	solidity_shuffler_workspaceSize,@function
solidity_shuffler_workspaceSize:
	movl	$357672, %eax
	retq
.Lfunc_end3:
	.size	solidity_shuffler_workspaceSize, .Lfunc_end3-solidity_shuffler_workspaceSize

	.type	.Lshuffler.Planner.resolve,@function
.Lshuffler.Planner.resolve:
	pushq	%rbp
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbx
	subq	$56, %rsp
	movl	$65536, %r15d
	addq	72(%rdi), %r15
	movq	%rdi, 16(%rsp)
	movq	8(%rdi), %rax
	xorl	%edi, %edi
.LBB4_1:
	cmpq	%rdi, %rax
	je	.LBB4_3
	movb	$0, (%r15,%rdi)
	incq	%rdi
	jmp	.LBB4_1
.LBB4_3:
	movq	16(%rsp), %rax
	movq	72(%rax), %rbp
	movq	(%rdx), %rax
	incq	%rax
	xorl	%r12d, %r12d
.LBB4_4:
	cmpq	%rax, %r8
	je	.LBB4_12
	movq	(%rcx,%rax,8), %rdi
	cmpq	$-1, %rdi
	je	.LBB4_6
	movq	8192(%rsi,%rdi,8), %rdi
	cmpq	$-1, %rdi
	je	.LBB4_6
	cmpq	$-1, (%rsi,%rdi,8)
	je	.LBB4_9
	movq	%rdi, 66560(%rbp,%r12,8)
	incq	%r12
.LBB4_6:
	incq	%rax
	jmp	.LBB4_4
.LBB4_12:
	movq	8(%rdx), %rax
	movq	%rax, 40(%rsp)
	movq	16(%rsp), %rax
	addq	$32, %rax
	movq	%rax, 32(%rsp)
	xorl	%eax, %eax
	movq	%rsi, 24(%rsp)
.LBB4_13:
	cmpq	40(%rsp), %rax
	je	.LBB4_14
	movq	%rax, 48(%rsp)
	xorl	%ebx, %ebx
	pushq	$-1
	popq	%rax
	movq	%rax, 8(%rsp)
	xorl	%r14d, %r14d
.LBB4_16:
	cmpq	%r14, %r12
	je	.LBB4_20
	movq	66560(%rbp,%r14,8), %r13
	cmpb	$0, (%r15,%r13)
	jne	.LBB4_27
	movq	16(%rsp), %rdi
	movq	%r15, %rdx
	movq	%r13, %rcx
	callq	.Lshuffler.Planner.classify
	cmpb	$-1, %al
	je	.LBB4_19
	cmpq	$-1, 8(%rsp)
	sete	%cl
	cmpb	%bl, %al
	setb	%dl
	orb	%cl, %dl
	je	.LBB4_24
	movq	%r13, 8(%rsp)
	movl	%eax, %ebx
.LBB4_19:
	movq	24(%rsp), %rsi
.LBB4_27:
	incq	%r14
	jmp	.LBB4_16
.LBB4_24:
	cmpb	%bl, %al
	movq	24(%rsp), %rsi
	jne	.LBB4_27
	movq	(%rsi,%r13,8), %rcx
	movq	8(%rsp), %rdx
	cmpq	(%rsi,%rdx,8), %rcx
	jbe	.LBB4_27
	movq	%r13, 8(%rsp)
	movl	%eax, %ebx
	jmp	.LBB4_27
.LBB4_20:
	cmpq	$-1, 8(%rsp)
	je	.LBB4_21
	cmpb	$4, %bl
	jne	.LBB4_29
	movq	16(%rsp), %rax
	movq	(%rax), %rax
	movq	8(%rsp), %rcx
	movq	(%rax,%rcx,8), %rsi
	movq	32(%rsp), %rdi
	callq	.Lshuffler.SpillSet.add
	movq	24(%rsp), %rsi
	testw	%ax, %ax
	jne	.LBB4_9
.LBB4_29:
	movb	$1, %cl
	movq	8(%rsp), %rdx
	movb	%cl, (%r15,%rdx)
	movq	16(%rsp), %rax
	movq	48(%rax), %rax
	movb	%cl, (%rax,%rdx)
	movq	48(%rsp), %rax
	incq	%rax
	jmp	.LBB4_13
.LBB4_14:
	xorl	%eax, %eax
	jmp	.LBB4_10
.LBB4_21:
	movw	$2, %ax
.LBB4_10:
	addq	$56, %rsp
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	popq	%rbp
	retq
.LBB4_9:
	movw	$1, %ax
	jmp	.LBB4_10
.Lfunc_end4:
	.size	.Lshuffler.Planner.resolve, .Lfunc_end4-.Lshuffler.Planner.resolve

	.type	.Lshuffler.Emission.run,@function
.Lshuffler.Emission.run:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbx
	movq	%rdi, %r14
	callq	.Lshuffler.Emission.removeSurplus
	testw	%ax, %ax
	jne	.LBB5_1
	movq	%r14, %rdi
	callq	.Lshuffler.Emission.permuteAtLowestHeight
	testw	%ax, %ax
	jne	.LBB5_1
	movq	80(%r14), %rax
	movq	48(%r14), %r12
	addq	%rax, %r12
	movw	$1, %bx
	cmpq	8(%r14), %r12
	jne	.LBB5_2
	xorl	%ecx, %ecx
	xorl	%edx, %edx
.LBB5_6:
	cmpq	%rcx, %r12
	je	.LBB5_8
	movq	72(%r14), %rsi
	xorl	%edi, %edi
	cmpq	$-1, 8192(%rsi,%rcx,8)
	sete	%dil
	addq	%rdi, %rdx
	incq	%rcx
	jmp	.LBB5_6
.LBB5_8:
	cmpq	%rax, %rdx
	jne	.LBB5_2
	movq	%r12, %r13
	negq	%r13
	pushq	$-1
	popq	%r15
.LBB5_10:
	leaq	(%r15,%r13), %rax
	cmpq	$-1, %rax
	je	.LBB5_11
	incq	%r15
	movq	%r14, %rdi
	movq	%r15, %rsi
	callq	.Lshuffler.Emission.isAvailable
	testb	$1, %al
	je	.LBB5_2
	jmp	.LBB5_10
.LBB5_11:
	xorl	%eax, %eax
	movabsq	$12884901888, %rcx
.LBB5_12:
	cmpq	%rax, %r12
	je	.LBB5_17
	movq	(%r14), %rdx
	movzbl	4(%rdx,%rax,8), %edx
	shlq	$32, %rdx
	cmpq	%rcx, %rdx
	jne	.LBB5_15
	movq	72(%r14), %rdx
	cmpq	$-1, 8192(%rdx,%rax,8)
	je	.LBB5_2
.LBB5_15:
	incq	%rax
	jmp	.LBB5_12
.LBB5_17:
	movq	%r14, %rdi
	callq	.Lshuffler.Emission.buildBottomUp
.LBB5_1:
	movl	%eax, %ebx
.LBB5_2:
	movl	%ebx, %eax
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	retq
.Lfunc_end5:
	.size	.Lshuffler.Emission.run, .Lfunc_end5-.Lshuffler.Emission.run

	.type	.Lshuffler.SpillSet.add,@function
.Lshuffler.SpillSet.add:
	movq	%rsi, %rcx
	shrq	$32, %rcx
	movw	$1, %ax
	testb	%cl, %cl
	jne	.LBB6_4
	movabsq	$280375465082880, %rcx
	andq	%rsi, %rcx
	je	.LBB6_4
	movl	%esi, %ecx
	movq	(%rdi), %rdx
	cmpb	$0, (%rdx,%rcx)
	jne	.LBB6_4
	movb	$1, (%rdx,%rcx)
	xorl	%eax, %eax
.LBB6_4:
	retq
.Lfunc_end6:
	.size	.Lshuffler.SpillSet.add, .Lfunc_end6-.Lshuffler.SpillSet.add

	.type	.Lshuffler.Emission.buildBottomUp,@function
.Lshuffler.Emission.buildBottomUp:
	pushq	%rbp
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbx
	subq	$24, %rsp
	movq	%rdi, %rbx
	xorl	%r14d, %r14d
.LBB7_1:
	movq	8(%rbx), %rbp
	movq	48(%rbx), %r15
	cmpq	%rbp, %r14
	jae	.LBB7_54
	movq	%r15, %rcx
	subq	%r14, %rcx
	jbe	.LBB7_4
	movq	72(%rbx), %rax
	cmpq	%r14, (%rax,%r14,8)
	je	.LBB7_52
.LBB7_4:
	cmpq	$0, 80(%rbx)
	je	.LBB7_55
	movq	%rcx, 16(%rsp)
	movq	%r14, 8(%rsp)
	pushq	$-1
	popq	%r12
.LBB7_6:
	cmpq	%r14, %rbp
	je	.LBB7_15
	movq	72(%rbx), %rax
	cmpq	$-1, 8192(%rax,%r14,8)
	je	.LBB7_9
.LBB7_8:
	incq	%r14
	jmp	.LBB7_6
.LBB7_9:
	movq	(%rbx), %rax
	movq	(%rax,%r14,8), %r13
	movq	%r13, %rax
	shrq	$40, %rax
	testb	%al, %al
	je	.LBB7_8
	movq	%r13, %rax
	shrq	$32, %rax
	decb	%al
	cmpb	$2, %al
	jb	.LBB7_8
	movq	%rbx, %rdi
	movq	%r13, %rsi
	callq	.Lshuffler.Emission.isSpilled
	testb	$1, %al
	jne	.LBB7_8
	movq	%rbx, %rdi
	movq	%r13, %rsi
	callq	.Lshuffler.Emission.shallowestCopyPosition
	cmpq	$-1, %rax
	je	.LBB7_8
	movq	%rax, %rcx
	notq	%rcx
	addq	%r15, %rcx
	movq	32(%rbx), %rdx
	movq	%rcx, %rsi
	subq	%rdx, %rsi
	ja	.LBB7_53
	xorq	%rdx, %rcx
	cmpq	8(%rsp), %rax
	movq	%r12, %rax
	movq	%r12, %rdx
	cmovneq	%r14, %rdx
	notq	%rax
	orq	%rcx, %rax
	cmoveq	%rdx, %r12
	jmp	.LBB7_8
.LBB7_15:
	cmpq	$-1, %r12
	je	.LBB7_21
	movq	8(%rsp), %r14
	cmpq	%r14, %r12
	movabsq	$281474976710655, %r9
	je	.LBB7_25
	movq	16(%rsp), %rax
	cmpq	24(%rbx), %rax
	jae	.LBB7_25
	movq	%rbx, %rdi
	movq	%r12, %rsi
.LBB7_19:
	callq	.Lshuffler.Emission.generate
	testw	%ax, %ax
	jne	.LBB7_61
	decq	%r14
	jmp	.LBB7_52
.LBB7_21:
	movq	%r15, %rax
	movq	8(%rsp), %r14
	subq	%r14, %rax
	seta	%cl
	cmpq	%rbp, %r15
	setb	%dl
	testb	%dl, %cl
	movabsq	$281474976710655, %r9
	je	.LBB7_25
	movq	72(%rbx), %rcx
	cmpq	$-1, 8192(%rcx,%r15,8)
	jne	.LBB7_25
	cmpq	24(%rbx), %rax
	jae	.LBB7_25
	movq	%rbx, %rdi
	movq	%r15, %rsi
	jmp	.LBB7_19
.LBB7_25:
	movq	72(%rbx), %rax
	movq	8192(%rax,%r14,8), %rcx
	cmpq	$-1, %rcx
	je	.LBB7_33
	movw	$1, %r12w
	cmpq	%r14, %rcx
	jb	.LBB7_65
	movq	40(%rbx), %rdx
	movq	(%rdx,%rcx,8), %rdi
	movq	(%rdx,%r14,8), %r8
	xorq	%rdi, %r8
	movq	%r14, %rsi
	testq	%r9, %r8
	je	.LBB7_36
	decq	%r15
	movq	%r15, %rsi
.LBB7_29:
	cmpq	%rcx, %rsi
	jbe	.LBB7_37
	movq	(%rdx,%rsi,8), %r8
	xorq	%rdi, %r8
	testq	%r9, %r8
	jne	.LBB7_32
	cmpq	(%rax,%rsi,8), %rsi
	jne	.LBB7_36
.LBB7_32:
	decq	%rsi
	jmp	.LBB7_29
.LBB7_33:
	movq	%rbx, %rdi
	movq	%r14, %rsi
	callq	.Lshuffler.Emission.generate
	testw	%ax, %ax
	jne	.LBB7_61
	movq	48(%rbx), %rax
	cmpq	%rax, %r14
	jae	.LBB7_66
	movq	72(%rbx), %rcx
	cmpq	%r14, (%rcx,%r14,8)
	jne	.LBB7_47
	jmp	.LBB7_52
.LBB7_36:
	testq	%r9, %r8
	jne	.LBB7_65
	jmp	.LBB7_38
.LBB7_37:
	movq	%rcx, %rsi
.LBB7_38:
	movq	(%rax,%rsi,8), %rdx
	movq	(%rax,%rcx,8), %rdi
	movq	%rdi, (%rax,%rsi,8)
	movq	%rdx, (%rax,%rcx,8)
	movq	(%rax,%rsi,8), %rdi
	cmpq	$-1, %rdi
	je	.LBB7_40
	movq	%rsi, 8192(%rax,%rdi,8)
	movq	(%rax,%rcx,8), %rdx
.LBB7_40:
	cmpq	$-1, %rdx
	je	.LBB7_42
	movq	%rcx, 8192(%rax,%rdx,8)
.LBB7_42:
	cmpq	%r14, %rsi
	je	.LBB7_52
	movq	48(%rbx), %rax
	leaq	-1(%rax), %rcx
	subq	%rsi, %rcx
	je	.LBB7_47
	subq	24(%rbx), %rcx
	ja	.LBB7_63
	movq	%rbx, %rdi
	callq	.Lshuffler.Emission.swapWith
	testw	%ax, %ax
	jne	.LBB7_65
	movq	48(%rbx), %rax
.LBB7_47:
	movw	$1, %r12w
	cmpq	%rax, %r14
	jae	.LBB7_65
	movq	72(%rbx), %rcx
	cmpq	%r14, (%rcx,%r14,8)
	je	.LBB7_65
	decq	%rax
	subq	%r14, %rax
	je	.LBB7_52
	subq	24(%rbx), %rax
	ja	.LBB7_62
	movq	%rbx, %rdi
	movq	%r14, %rsi
	callq	.Lshuffler.Emission.swapWith
	testw	%ax, %ax
	jne	.LBB7_65
.LBB7_52:
	incq	%r14
	jmp	.LBB7_1
.LBB7_53:
	movq	%rax, 88(%rbx)
	movq	%rsi, 96(%rbx)
.LBB7_64:
	movw	$2, %r12w
	jmp	.LBB7_65
.LBB7_54:
	xorl	%r12d, %r12d
	cmpq	%rbp, %r15
	setne	%r12b
	jmp	.LBB7_65
.LBB7_55:
	movw	$1, %r12w
	cmpq	%rbp, %r15
	jne	.LBB7_65
	movl	$32768, %esi
	addq	112(%rbx), %rsi
	xorl	%eax, %eax
.LBB7_57:
	cmpq	%rax, %rbp
	je	.LBB7_60
	movq	72(%rbx), %rcx
	movq	(%rcx,%rax,8), %rcx
	cmpq	$-1, %rcx
	je	.LBB7_65
	movq	%rcx, (%rsi,%rax,8)
	incq	%rax
	jmp	.LBB7_57
.LBB7_60:
	movq	%rbx, %rdi
	callq	.Lshuffler.Emission.permute
.LBB7_61:
	movl	%eax, %r12d
.LBB7_65:
	movl	%r12d, %eax
	addq	$24, %rsp
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	popq	%rbp
	retq
.LBB7_62:
	movq	%r14, 88(%rbx)
	movq	%rax, 96(%rbx)
	jmp	.LBB7_64
.LBB7_63:
	movq	%rsi, 88(%rbx)
	movq	%rcx, 96(%rbx)
	jmp	.LBB7_64
.LBB7_66:
	movw	$1, %r12w
	jmp	.LBB7_65
.Lfunc_end7:
	.size	.Lshuffler.Emission.buildBottomUp, .Lfunc_end7-.Lshuffler.Emission.buildBottomUp

	.type	.Lshuffler.Emission.isAvailable,@function
.Lshuffler.Emission.isAvailable:
	pushq	%r15
	pushq	%r14
	pushq	%rbx
	movq	(%rdi), %rax
	movq	(%rax,%rsi,8), %r15
	movq	%r15, %rax
	shrq	$40, %rax
	movb	$1, %bl
	testb	%al, %al
	je	.LBB8_4
	movq	%r15, %rax
	shrq	$32, %rax
	decb	%al
	cmpb	$2, %al
	jb	.LBB8_4
	movq	%rdi, %r14
	movq	%r15, %rsi
	callq	.Lshuffler.Emission.isSpilled
	testb	$1, %al
	jne	.LBB8_4
	movq	%r14, %rdi
	movq	%r15, %rsi
	callq	.Lshuffler.Emission.shallowestCopyPosition
	cmpq	$-1, %rax
	setne	%bl
.LBB8_4:
	movl	%ebx, %eax
	popq	%rbx
	popq	%r14
	popq	%r15
	retq
.Lfunc_end8:
	.size	.Lshuffler.Emission.isAvailable, .Lfunc_end8-.Lshuffler.Emission.isAvailable

	.type	.Lshuffler.Emission.swapWith,@function
.Lshuffler.Emission.swapWith:
	movq	48(%rdi), %rdx
	movw	$1, %ax
	cmpq	%rdx, %rsi
	jae	.LBB9_9
	movq	72(%rdi), %rcx
	cmpq	%rsi, (%rcx,%rsi,8)
	je	.LBB9_9
	movq	%rsi, %rcx
	notq	%rcx
	movq	%rdx, %r8
	addq	%rcx, %r8
	je	.LBB9_9
	cmpq	24(%rdi), %r8
	ja	.LBB9_9
	movq	40(%rdi), %r8
	movq	(%r8,%rsi,8), %r9
	movq	-8(%r8,%rdx,8), %rdx
	movq	%rdx, (%r8,%rsi,8)
	movq	40(%rdi), %rdx
	movq	48(%rdi), %r8
	movq	%r9, -8(%rdx,%r8,8)
	movq	64(%rdi), %rdx
	cmpq	$10239, %rdx
	ja	.LBB9_9
	addl	48(%rdi), %ecx
	movq	56(%rdi), %rax
	imulq	$12, %rdx, %rdx
	movb	$0, (%rax,%rdx)
	movb	%cl, 1(%rax,%rdx)
	movabsq	$5501853106176, %rcx
	movq	%rcx, 4(%rax,%rdx)
	incq	64(%rdi)
	movq	48(%rdi), %rax
	movq	72(%rdi), %rcx
	movq	(%rcx,%rsi,8), %rdx
	movq	-8(%rcx,%rax,8), %rdi
	movq	%rdi, (%rcx,%rsi,8)
	movq	%rdx, -8(%rcx,%rax,8)
	movq	(%rcx,%rsi,8), %rdi
	cmpq	$-1, %rdi
	je	.LBB9_6
	movq	%rsi, 8192(%rcx,%rdi,8)
	movq	-8(%rcx,%rax,8), %rdx
.LBB9_6:
	cmpq	$-1, %rdx
	je	.LBB9_8
	decq	%rax
	movq	%rax, 8192(%rcx,%rdx,8)
.LBB9_8:
	xorl	%eax, %eax
.LBB9_9:
	retq
.Lfunc_end9:
	.size	.Lshuffler.Emission.swapWith, .Lfunc_end9-.Lshuffler.Emission.swapWith

	.type	.Lshuffler.Emission.generate,@function
.Lshuffler.Emission.generate:
	cmpq	8(%rdi), %rsi
	jae	.LBB10_13
	pushq	%r14
	pushq	%rbx
	pushq	%rax
	movq	%rsi, %rbx
	movq	%rdi, %r14
	callq	.Lshuffler.Emission.produce
	testw	%ax, %ax
	jne	.LBB10_12
	leaq	1(%rbx), %rax
	movq	48(%r14), %rsi
	cmpq	%rsi, %rax
	jae	.LBB10_11
	movq	72(%r14), %rax
	movq	(%rax,%rbx,8), %rdx
	cmpq	%rbx, %rdx
	je	.LBB10_11
	movq	40(%r14), %rdi
	leaq	-1(%rsi), %rcx
	movq	-8(%rdi,%rsi,8), %r8
	xorq	(%rdi,%rbx,8), %r8
	shlq	$16, %r8
	je	.LBB10_7
	subq	%rbx, %rcx
	cmpq	24(%r14), %rcx
	ja	.LBB10_11
	movq	%r14, %rdi
	movq	%rbx, %rsi
	callq	.Lshuffler.Emission.swapWith
	jmp	.LBB10_12
.LBB10_7:
	movq	-8(%rax,%rsi,8), %rdi
	movq	%rdi, (%rax,%rbx,8)
	movq	%rdx, -8(%rax,%rsi,8)
	movq	(%rax,%rbx,8), %rdi
	cmpq	$-1, %rdi
	je	.LBB10_9
	movq	%rbx, 8192(%rax,%rdi,8)
	movq	-8(%rax,%rsi,8), %rdx
.LBB10_9:
	cmpq	$-1, %rdx
	je	.LBB10_11
	movq	%rcx, 8192(%rax,%rdx,8)
.LBB10_11:
	xorl	%eax, %eax
.LBB10_12:
	addq	$8, %rsp
	popq	%rbx
	popq	%r14
	retq
.LBB10_13:
	movw	$1, %ax
	retq
.Lfunc_end10:
	.size	.Lshuffler.Emission.generate, .Lfunc_end10-.Lshuffler.Emission.generate

	.type	.Lshuffler.Emission.shallowestCopyPosition,@function
.Lshuffler.Emission.shallowestCopyPosition:
	movq	48(%rdi), %rax
	pushq	$-1
	popq	%rcx
.LBB11_1:
	testq	%rax, %rax
	je	.LBB11_2
	movq	40(%rdi), %rdx
	movq	-8(%rdx,%rax,8), %rdx
	xorq	%rsi, %rdx
	decq	%rax
	shlq	$16, %rdx
	jne	.LBB11_1
	retq
.LBB11_2:
	movq	%rcx, %rax
	retq
.Lfunc_end11:
	.size	.Lshuffler.Emission.shallowestCopyPosition, .Lfunc_end11-.Lshuffler.Emission.shallowestCopyPosition

	.type	.Lshuffler.Emission.produce,@function
.Lshuffler.Emission.produce:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbx
	movq	%rsi, %r14
	movq	%rdi, %rbx
	movq	(%rdi), %rax
	movq	(%rax,%rsi,8), %r12
	movq	%r12, %rsi
	callq	.Lshuffler.Emission.shallowestCopyPosition
	movq	%rax, %r15
	movq	%r12, %rax
	shrq	$32, %rax
	cmpb	$1, %al
	jne	.LBB12_8
.LBB12_1:
	movq	%rbx, %rdi
	movq	%r12, %rsi
	movq	%r14, %rdx
	callq	.Lshuffler.Emission.push
.LBB12_2:
	testw	%ax, %ax
	jne	.LBB12_4
	movq	48(%rbx), %rax
	movq	72(%rbx), %rcx
	decq	%rax
	cmpq	%rax, 8192(%rcx,%r14,8)
	jne	.LBB12_4
	decq	80(%rbx)
	xorl	%eax, %eax
.LBB12_5:
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	retq
.LBB12_8:
	movq	%r15, %r13
	notq	%r13
	cmpq	$-1, %r15
	je	.LBB12_9
	movq	48(%rbx), %rcx
	addq	%r13, %rcx
	cmpq	32(%rbx), %rcx
	jbe	.LBB12_7
.LBB12_9:
	movq	%r12, %rcx
	shrq	$40, %rcx
	testb	%cl, %cl
	je	.LBB12_1
	cmpb	$2, %al
	je	.LBB12_1
	movq	%rbx, %rdi
	movq	%r12, %rsi
	callq	.Lshuffler.Emission.isSpilled
	testb	$1, %al
	jne	.LBB12_1
	movw	$1, %ax
	cmpq	$-1, %r15
	je	.LBB12_5
	addq	48(%rbx), %r13
	subq	32(%rbx), %r13
	je	.LBB12_5
	movq	%r15, 88(%rbx)
	movq	%r13, 96(%rbx)
	movw	$2, %ax
	jmp	.LBB12_5
.LBB12_7:
	movq	%rbx, %rdi
	movq	%r15, %rsi
	movq	%r14, %rdx
	callq	.Lshuffler.Emission.dup
	jmp	.LBB12_2
.LBB12_4:
	movw	$1, %ax
	jmp	.LBB12_5
.Lfunc_end12:
	.size	.Lshuffler.Emission.produce, .Lfunc_end12-.Lshuffler.Emission.produce

	.type	.Lshuffler.Emission.isSpilled,@function
.Lshuffler.Emission.isSpilled:
	movq	%rsi, %rax
	shrq	$32, %rax
	testb	%al, %al
	sete	%al
	movq	%rsi, %rcx
	shrq	$40, %rcx
	testb	%cl, %cl
	setne	%cl
	testb	%cl, %al
	jne	.LBB13_3
	xorl	%eax, %eax
	retq
.LBB13_3:
	movq	16(%rdi), %rax
	movl	%esi, %ecx
	cmpb	$0, (%rax,%rcx)
	setne	%al
	retq
.Lfunc_end13:
	.size	.Lshuffler.Emission.isSpilled, .Lfunc_end13-.Lshuffler.Emission.isSpilled

	.type	.Lshuffler.Emission.dup,@function
.Lshuffler.Emission.dup:
	movq	40(%rdi), %rax
	movzbl	4(%rax,%rsi,8), %ecx
	shlq	$32, %rcx
	movabsq	$12884901888, %r8
	movw	$1, %ax
	cmpq	%r8, %rcx
	je	.LBB14_5
	movq	48(%rdi), %rcx
	cmpq	$1024, %rcx
	jae	.LBB14_5
	movq	64(%rdi), %r8
	cmpq	$10239, %r8
	ja	.LBB14_5
	subl	%esi, %ecx
	movq	56(%rdi), %r9
	imulq	$12, %r8, %r8
	movb	$1, (%r9,%r8)
	movb	%cl, 1(%r9,%r8)
	movabsq	$5501853106176, %rcx
	movq	%rcx, 4(%r9,%r8)
	incq	64(%rdi)
	movq	40(%rdi), %rcx
	movq	48(%rdi), %r8
	movq	(%rcx,%rsi,8), %rsi
	movq	%rsi, (%rcx,%r8,8)
	movq	48(%rdi), %rcx
	movq	72(%rdi), %rsi
	leaq	1(%rcx), %r8
	movq	%r8, 48(%rdi)
	cmpq	$-1, 8192(%rsi,%rdx,8)
	jne	.LBB14_5
	movq	%rdx, (%rsi,%rcx,8)
	movq	%rcx, 8192(%rsi,%rdx,8)
	xorl	%eax, %eax
.LBB14_5:
	retq
.Lfunc_end14:
	.size	.Lshuffler.Emission.dup, .Lfunc_end14-.Lshuffler.Emission.dup

	.type	.Lshuffler.Emission.push,@function
.Lshuffler.Emission.push:
	movq	48(%rdi), %rcx
	movw	$1, %ax
	cmpq	$1023, %rcx
	ja	.LBB15_4
	movq	40(%rdi), %r8
	movq	%rsi, (%r8,%rcx,8)
	incq	48(%rdi)
	movq	64(%rdi), %rcx
	cmpq	$10239, %rcx
	ja	.LBB15_4
	movq	%rsi, %r8
	shrq	$32, %r8
	movabsq	$280375465082880, %r9
	andq	%rsi, %r9
	cmpq	$1, %r9
	movb	$4, %r9b
	sbbb	$0, %r9b
	testb	%r8b, %r8b
	movzbl	%r9b, %r8d
	pushq	$3
	popq	%r9
	cmovel	%r8d, %r9d
	movq	56(%rdi), %r8
	imulq	$12, %rcx, %rcx
	movb	%r9b, (%r8,%rcx)
	movb	$0, 1(%r8,%rcx)
	movq	%rsi, 4(%r8,%rcx)
	incq	64(%rdi)
	movq	72(%rdi), %rcx
	cmpq	$-1, 8192(%rcx,%rdx,8)
	jne	.LBB15_4
	movq	48(%rdi), %rax
	movq	%rdx, -8(%rcx,%rax,8)
	decq	%rax
	movq	%rax, 8192(%rcx,%rdx,8)
	xorl	%eax, %eax
.LBB15_4:
	retq
.Lfunc_end15:
	.size	.Lshuffler.Emission.push, .Lfunc_end15-.Lshuffler.Emission.push

	.type	.Lshuffler.Emission.permute,@function
.Lshuffler.Emission.permute:
	movq	48(%rdi), %rax
	testq	%rax, %rax
	je	.LBB16_26
	pushq	%rbp
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbx
	pushq	%rax
	movq	%rsi, %r14
	movq	%rdi, %rbx
	movq	112(%rdi), %r13
	xorl	%ecx, %ecx
.LBB16_2:
	cmpq	%rcx, %rax
	je	.LBB16_4
	orq	$-1, 57344(%r13,%rcx,8)
	incq	%rcx
	jmp	.LBB16_2
.LBB16_4:
	movabsq	$281474976710655, %r12
	movq	48(%rbx), %rax
	xorl	%ebp, %ebp
	movq	%rax, (%rsp)
.LBB16_5:
	cmpq	%rax, %rbp
	je	.LBB16_28
	movq	40(%rbx), %rax
	movq	(%rax,%rbp,8), %r15
	movq	%rbx, %rdi
	movq	%r15, %rsi
	callq	.Lshuffler.Emission.shallowestCopyPosition
	cmpq	%rbp, %rax
	jne	.LBB16_25
	xorl	%eax, %eax
.LBB16_8:
	cmpq	%rbp, %rax
	ja	.LBB16_12
	movq	40(%rbx), %rcx
	movq	(%rcx,%rax,8), %rcx
	xorq	%r15, %rcx
	testq	%r12, %rcx
	jne	.LBB16_11
	movq	(%r14,%rax,8), %rcx
	movq	%rbp, 57344(%r13,%rcx,8)
.LBB16_11:
	incq	%rax
	jmp	.LBB16_8
.LBB16_12:
	xorl	%ecx, %ecx
	xorl	%edx, %edx
.LBB16_13:
	cmpq	%rbp, %rdx
	ja	.LBB16_25
	movq	40(%rbx), %rsi
	movq	(%rsi,%rdx,8), %rax
	xorq	%r15, %rax
	testq	%r12, %rax
	jne	.LBB16_24
	cmpq	%rbp, 57344(%r13,%rdx,8)
	jne	.LBB16_17
	movq	%rdx, (%r14,%rdx,8)
	jmp	.LBB16_24
.LBB16_17:
	movq	48(%rbx), %rdi
.LBB16_18:
	movw	$1, %ax
	cmpq	%rdi, %rcx
	jae	.LBB16_45
	cmpq	%rbp, 57344(%r13,%rcx,8)
	jne	.LBB16_21
	movq	(%rsi,%rcx,8), %r8
	xorq	%r15, %r8
	testq	%r12, %r8
	jne	.LBB16_22
.LBB16_21:
	incq	%rcx
	jmp	.LBB16_18
.LBB16_22:
	cmpq	%rdi, %rcx
	jae	.LBB16_45
	movq	%rcx, (%r14,%rdx,8)
	incq	%rcx
.LBB16_24:
	incq	%rdx
	jmp	.LBB16_13
.LBB16_25:
	incq	%rbp
	movq	(%rsp), %rax
	jmp	.LBB16_5
.LBB16_26:
	xorl	%eax, %eax
	retq
.LBB16_28:
	movq	48(%rbx), %rax
	leaq	-1(%rax), %rcx
	leaq	(%r14,%rax,8), %rdx
	addq	$-16, %rdx
	movq	8(%rdx), %rdi
	movabsq	$5501853106176, %rsi
.LBB16_29:
	cmpq	%rcx, %rdi
	jne	.LBB16_35
	xorl	%r8d, %r8d
.LBB16_31:
	movq	%rcx, %rdi
	addq	%r8, %rdi
	je	.LBB16_44
	leaq	-1(%r8), %rdi
	leaq	(%rcx,%r8), %r9
	decq	%r9
	cmpq	(%rdx,%r8,8), %r9
	movq	%rdi, %r8
	je	.LBB16_31
	testq	%rdi, %rdi
	je	.LBB16_44
	addq	%rcx, %rdi
.LBB16_35:
	movq	40(%rbx), %r9
	movq	48(%rbx), %r10
	movq	(%r9,%rdi,8), %r8
	movq	-8(%r9,%r10,8), %r11
	movq	%r11, %r15
	xorq	%r8, %r15
	testq	%r12, %r15
	je	.LBB16_39
	decq	%r10
	subq	%rdi, %r10
	subq	24(%rbx), %r10
	ja	.LBB16_46
	movq	%r11, (%r9,%rdi,8)
	movq	40(%rbx), %r9
	movq	48(%rbx), %r10
	movq	%r8, -8(%r9,%r10,8)
	movq	64(%rbx), %r8
	cmpq	$10240, %r8
	jae	.LBB16_47
	movl	%edi, %r9d
	notl	%r9d
	addl	48(%rbx), %r9d
	movq	56(%rbx), %r10
	imulq	$12, %r8, %r8
	movb	$0, (%r10,%r8)
	movb	%r9b, 1(%r10,%r8)
	movq	%rsi, 4(%r10,%r8)
	incq	64(%rbx)
.LBB16_39:
	movq	72(%rbx), %r8
	movq	(%r8,%rdi,8), %r9
	movq	-8(%r8,%rax,8), %r10
	movq	%r10, (%r8,%rdi,8)
	movq	%r9, -8(%r8,%rax,8)
	movq	(%r8,%rdi,8), %r10
	cmpq	$-1, %r10
	je	.LBB16_41
	movq	%rdi, 8192(%r8,%r10,8)
	movq	-8(%r8,%rax,8), %r9
.LBB16_41:
	cmpq	$-1, %r9
	je	.LBB16_43
	movq	%rcx, 8192(%r8,%r9,8)
.LBB16_43:
	movq	(%r14,%rdi,8), %r8
	movq	-8(%r14,%rax,8), %r9
	movq	%r9, (%r14,%rdi,8)
	movq	%r8, -8(%r14,%rax,8)
	movq	%r8, %rdi
	jmp	.LBB16_29
.LBB16_44:
	xorl	%eax, %eax
.LBB16_45:
	addq	$8, %rsp
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	popq	%rbp
	retq
.LBB16_46:
	movq	%rdi, 88(%rbx)
	movq	%r10, 96(%rbx)
	movw	$2, %ax
	jmp	.LBB16_45
.LBB16_47:
	movw	$1, %ax
	jmp	.LBB16_45
.Lfunc_end16:
	.size	.Lshuffler.Emission.permute, .Lfunc_end16-.Lshuffler.Emission.permute

	.type	.Lshuffler.Emission.permuteAtLowestHeight,@function
.Lshuffler.Emission.permuteAtLowestHeight:
	pushq	%rax
	movq	48(%rdi), %r8
	movq	112(%rdi), %rcx
	leaq	32768(%rcx), %rsi
	xorl	%edx, %edx
	xorl	%r9d, %r9d
	xorl	%r10d, %r10d
.LBB17_1:
	cmpq	%r10, %r8
	je	.LBB17_7
	movq	72(%rdi), %rax
	movq	(%rax,%r10,8), %r11
	movw	$1, %ax
	cmpq	$-1, %r11
	je	.LBB17_9
	cmpq	8(%rdi), %r10
	jae	.LBB17_9
	movq	104(%rdi), %rax
	movq	8192(%rax,%r10,8), %rax
	cmpq	48(%rdi), %r11
	jae	.LBB17_5
	movq	%r11, (%rsi,%r10,8)
	cmpq	$-1, %rax
	jne	.LBB17_13
	movq	%r10, 40960(%rcx,%rdx,8)
	incq	%rdx
	jmp	.LBB17_13
.LBB17_5:
	cmpq	$-1, %rax
	je	.LBB17_6
	movq	%r10, 49152(%rcx,%r9,8)
	incq	%r9
	jmp	.LBB17_13
.LBB17_6:
	movq	%r10, (%rsi,%r10,8)
.LBB17_13:
	incq	%r10
	jmp	.LBB17_1
.LBB17_7:
	cmpq	%rdx, %r9
	jne	.LBB17_8
	xorl	%eax, %eax
.LBB17_15:
	cmpq	%rax, %rdx
	je	.LBB17_17
	movq	49152(%rcx,%rax,8), %r8
	movq	40960(%rcx,%rax,8), %r9
	movq	%r9, 32768(%rcx,%r8,8)
	incq	%rax
	jmp	.LBB17_15
.LBB17_17:
	callq	.Lshuffler.Emission.permute
.LBB17_9:
	popq	%rcx
	retq
.LBB17_8:
	movw	$1, %ax
	jmp	.LBB17_9
.Lfunc_end17:
	.size	.Lshuffler.Emission.permuteAtLowestHeight, .Lfunc_end17-.Lshuffler.Emission.permuteAtLowestHeight

	.type	.Lshuffler.Emission.removeSurplus,@function
.Lshuffler.Emission.removeSurplus:
	pushq	%r14
	pushq	%rbx
	pushq	%rax
	movq	%rdi, %rbx
	pushq	$-1
	popq	%r14
.LBB18_1:
	movq	48(%rbx), %rcx
	testq	%rcx, %rcx
	je	.LBB18_2
	movq	72(%rbx), %rax
	leaq	-1(%rcx), %rdx
	movq	%rcx, %r8
	movq	%r14, %rsi
	movq	%r14, %rdi
.LBB18_4:
	movq	%r8, %r9
.LBB18_5:
	testq	%r9, %r9
	je	.LBB18_8
	leaq	-1(%r9), %r8
	cmpq	$-1, -8(%rax,%r9,8)
	movq	%r8, %r9
	jne	.LBB18_5
	cmpq	$-1, %rdi
	cmoveq	%r8, %rdi
	movq	%rdx, %r9
	subq	%r8, %r9
	cmpq	24(%rbx), %r9
	cmovbeq	%r8, %rsi
	jmp	.LBB18_4
.LBB18_8:
	cmpq	$-1, %rdi
	je	.LBB18_2
	cmpq	$-1, %rsi
	je	.LBB18_15
	cmpq	%rdx, %rdi
	je	.LBB18_19
	leaq	-2(%rcx), %rdi
.LBB18_12:
	cmpq	$-1, %rdi
	je	.LBB18_18
	cmpq	$-1, (%rax,%rdi,8)
	jne	.LBB18_14
	movq	40(%rbx), %r8
	movq	-8(%r8,%rcx,8), %r9
	xorq	(%r8,%rdi,8), %r9
	shlq	$16, %r9
	je	.LBB18_22
.LBB18_14:
	decq	%rdi
	jmp	.LBB18_12
.LBB18_18:
	movq	%rbx, %rdi
	callq	.Lshuffler.Emission.swapWith
	testw	%ax, %ax
	jne	.LBB18_20
.LBB18_19:
	movq	%rbx, %rdi
	callq	.Lshuffler.Emission.pop
	testw	%ax, %ax
	je	.LBB18_1
	jmp	.LBB18_20
.LBB18_22:
	movq	-8(%rax,%rcx,8), %rsi
	movq	%rsi, (%rax,%rdi,8)
	orq	$-1, -8(%rax,%rcx,8)
	movq	(%rax,%rdi,8), %rsi
	cmpq	$-1, %rsi
	je	.LBB18_19
	movq	%rdi, 8192(%rax,%rsi,8)
	movq	-8(%rax,%rcx,8), %rcx
	cmpq	$-1, %rcx
	je	.LBB18_19
	movq	%rdx, 8192(%rax,%rcx,8)
	jmp	.LBB18_19
.LBB18_2:
	xorl	%eax, %eax
.LBB18_17:
	addq	$8, %rsp
	popq	%rbx
	popq	%r14
	retq
.LBB18_15:
	movq	%rdi, %rax
	notq	%rax
	addq	%rax, %rcx
	movw	$1, %ax
	subq	24(%rbx), %rcx
	je	.LBB18_17
	movq	%rdi, 88(%rbx)
	movq	%rcx, 96(%rbx)
	movw	$2, %ax
	jmp	.LBB18_17
.LBB18_20:
	movw	$1, %ax
	jmp	.LBB18_17
.Lfunc_end18:
	.size	.Lshuffler.Emission.removeSurplus, .Lfunc_end18-.Lshuffler.Emission.removeSurplus

	.type	.Lshuffler.Planner.classify,@function
.Lshuffler.Planner.classify:
	pushq	%rbp
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbx
	pushq	%rax
	movq	(%rdi), %rax
	movq	(%rax,%rcx,8), %r13
	movq	%r13, %rbp
	shrq	$32, %rbp
	movb	$-1, %al
	cmpb	$3, %bpl
	jne	.LBB19_1
.LBB19_13:
	addq	$8, %rsp
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	popq	%rbp
	retq
.LBB19_1:
	movq	%rcx, %r14
	movq	%rsi, %r12
	movq	%rdi, %rbx
	movq	%r13, %rax
	shrq	$40, %rax
	testb	%al, %al
	setne	%al
	leal	-3(%rbp), %ecx
	cmpb	$-2, %cl
	setb	%r15b
	andb	%al, %r15b
	movb	$1, %al
	cmpb	$1, %r15b
	jne	.LBB19_4
	testb	%bpl, %bpl
	je	.LBB19_3
.LBB19_14:
	movq	%rbx, %rdi
	movq	%r12, %rsi
	movq	%r14, %rcx
	movq	%rdx, (%rsp)
	callq	.Lshuffler.Planner.hasOtherRetainedCopy
	movq	(%rsp), %rdx
	jmp	.LBB19_4
.LBB19_3:
	movq	32(%rbx), %rcx
	movl	%r13d, %esi
	cmpb	$0, (%rcx,%rsi)
	je	.LBB19_14
.LBB19_4:
	movq	(%r12,%r14,8), %rcx
	movq	16(%rbx), %rsi
	movzbl	4(%rsi,%rcx,8), %ecx
	shlq	$32, %rcx
	movabsq	$4294967296, %rsi
	cmpq	%rsi, %rcx
	jne	.LBB19_8
	testb	$1, %al
	je	.LBB19_7
	xorl	%eax, %eax
	jmp	.LBB19_13
.LBB19_8:
	movb	$1, %al
	testb	%r15b, %r15b
	je	.LBB19_13
	jmp	.LBB19_9
.LBB19_7:
	movq	%rbx, %rdi
	movq	%r13, %rsi
	movq	%rdx, (%rsp)
	callq	.Lshuffler.Planner.isDemanded
	movq	(%rsp), %rdx
	andb	$1, %al
	testb	%r15b, %al
	je	.LBB19_13
.LBB19_9:
	testb	%bpl, %bpl
	je	.LBB19_10
.LBB19_11:
	movq	%rbx, %rdi
	movq	%r12, %rsi
	movq	%r14, %rcx
	callq	.Lshuffler.Planner.hasOtherRetainedCopy
	movl	%eax, %ecx
	movb	$3, %al
	testb	$1, %cl
	jne	.LBB19_13
	testb	%bpl, %bpl
	setne	%cl
	movb	40(%rbx), %al
	notb	%al
	orb	%cl, %al
	andb	$1, %al
	negb	%al
	orb	$4, %al
	jmp	.LBB19_13
.LBB19_10:
	movq	32(%rbx), %rcx
	movl	%r13d, %esi
	movb	$2, %al
	cmpb	$0, (%rcx,%rsi)
	jne	.LBB19_13
	jmp	.LBB19_11
.Lfunc_end19:
	.size	.Lshuffler.Planner.classify, .Lfunc_end19-.Lshuffler.Planner.classify

	.type	.Lshuffler.Emission.pop,@function
.Lshuffler.Emission.pop:
	movq	48(%rdi), %rcx
	movw	$1, %ax
	subq	$1, %rcx
	jb	.LBB20_5
	movq	%rcx, 48(%rdi)
	movq	64(%rdi), %rdx
	cmpq	$10240, %rdx
	jae	.LBB20_5
	movq	56(%rdi), %rax
	imulq	$12, %rdx, %rdx
	movw	$2, (%rax,%rdx)
	movabsq	$5501853106176, %rsi
	movq	%rsi, 4(%rax,%rdx)
	incq	64(%rdi)
	movq	72(%rdi), %rax
	movq	(%rax,%rcx,8), %rcx
	cmpq	$-1, %rcx
	je	.LBB20_4
	orq	$-1, 8192(%rax,%rcx,8)
.LBB20_4:
	xorl	%eax, %eax
.LBB20_5:
	retq
.Lfunc_end20:
	.size	.Lshuffler.Emission.pop, .Lfunc_end20-.Lshuffler.Emission.pop

	.type	.Lshuffler.Planner.isDemanded,@function
.Lshuffler.Planner.isDemanded:
	movq	24(%rdi), %rax
	xorl	%ecx, %ecx
	movabsq	$1095216660480, %rdx
	movabsq	$4294967296, %r8
.LBB21_1:
	cmpq	%rcx, %rax
	je	.LBB21_5
	movq	16(%rdi), %r9
	movq	(%r9,%rcx,8), %r9
	movq	%r9, %r10
	andq	%rdx, %r10
	cmpq	%r8, %r10
	je	.LBB21_4
	xorq	%rsi, %r9
	shlq	$16, %r9
	je	.LBB21_5
.LBB21_4:
	incq	%rcx
	jmp	.LBB21_1
.LBB21_5:
	cmpq	%rax, %rcx
	setb	%al
	retq
.Lfunc_end21:
	.size	.Lshuffler.Planner.isDemanded, .Lfunc_end21-.Lshuffler.Planner.isDemanded

	.type	.Lshuffler.Planner.hasOtherRetainedCopy,@function
.Lshuffler.Planner.hasOtherRetainedCopy:
	pushq	%rbp
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbx
	pushq	%rax
	movq	%rcx, %rbx
	movq	%rdx, %r14
	movq	%rsi, %r15
	movq	%rdi, %r12
	movq	8(%rdi), %rbp
	xorl	%r13d, %r13d
.LBB22_1:
	cmpq	%r13, %rbp
	je	.LBB22_7
	cmpq	%r13, %rbx
	je	.LBB22_6
	movq	(%r12), %rax
	movq	(%rax,%rbx,8), %rcx
	xorq	(%rax,%r13,8), %rcx
	shlq	$16, %rcx
	jne	.LBB22_6
	movq	%r15, %rdi
	movq	%r13, %rsi
	callq	.Lshuffler.Planner.isRetained
	testb	$1, %al
	je	.LBB22_6
	cmpb	$0, (%r14,%r13)
	je	.LBB22_7
.LBB22_6:
	incq	%r13
	jmp	.LBB22_1
.LBB22_7:
	cmpq	%rbp, %r13
	setb	%al
	addq	$8, %rsp
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	popq	%rbp
	retq
.Lfunc_end22:
	.size	.Lshuffler.Planner.hasOtherRetainedCopy, .Lfunc_end22-.Lshuffler.Planner.hasOtherRetainedCopy

	.type	.Lshuffler.MappingBuilder.absorbSurplus,@function
.Lshuffler.MappingBuilder.absorbSurplus:
	pushq	%rbp
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbx
	pushq	%rax
	movq	%rdi, %rbx
	movq	24(%rdi), %r15
	xorl	%r14d, %r14d
	movabsq	$4294967296, %r12
	pushq	$-1
	popq	%r13
	xorl	%ebp, %ebp
.LBB23_1:
	cmpq	%r15, %r14
	je	.LBB23_2
	movq	16(%rbx), %rax
	movzbl	4(%rax,%r14,8), %eax
	shlq	$32, %rax
	cmpq	%r12, %rax
	jne	.LBB23_5
	movq	48(%rbx), %rax
	cmpq	$-1, 8192(%rax,%r14,8)
	jne	.LBB23_5
	movq	8(%rbx), %rcx
	movq	%r14, %rdx
	movq	%r13, %rsi
	xorl	%edi, %edi
.LBB23_8:
	cmpq	%rdi, %rcx
	je	.LBB23_16
	movq	32(%rbx), %r8
	cmpb	$0, (%r8,%rdi)
	jne	.LBB23_10
	cmpq	$-1, (%rax,%rdi,8)
	je	.LBB23_13
.LBB23_10:
	movq	%rsi, %r8
.LBB23_11:
	incq	%rdi
	decq	%rdx
	movq	%r8, %rsi
	jmp	.LBB23_8
.LBB23_13:
	movq	%rdi, %r8
	cmpq	$-1, %rsi
	je	.LBB23_11
	leaq	(%rdi,%rbp), %r9
	cmpq	%r14, %rdi
	cmovbeq	%rdx, %r9
	movq	%r14, %r8
	subq	%rsi, %r8
	movq	%rsi, %r10
	subq	%r14, %r10
	cmovbq	%r8, %r10
	movq	%rsi, %r8
	cmpq	%r10, %r9
	jae	.LBB23_11
	movq	%rdi, %r8
	jmp	.LBB23_11
.LBB23_16:
	cmpq	$-1, %rsi
	je	.LBB23_5
	movq	%rbx, %rdi
	movq	%r14, %rdx
	callq	.Lshuffler.MappingBuilder.map
	testw	%ax, %ax
	jne	.LBB23_18
.LBB23_5:
	incq	%r14
	decq	%rbp
	jmp	.LBB23_1
.LBB23_2:
	xorl	%eax, %eax
.LBB23_3:
	addq	$8, %rsp
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	popq	%rbp
	retq
.LBB23_18:
	movw	$1, %ax
	jmp	.LBB23_3
.Lfunc_end23:
	.size	.Lshuffler.MappingBuilder.absorbSurplus, .Lfunc_end23-.Lshuffler.MappingBuilder.absorbSurplus

	.type	.Lshuffler.Planner.isRetained,@function
.Lshuffler.Planner.isRetained:
	cmpq	$-1, (%rdi,%rsi,8)
	setne	%al
	retq
.Lfunc_end24:
	.size	.Lshuffler.Planner.isRetained, .Lfunc_end24-.Lshuffler.Planner.isRetained

	.type	.Lshuffler.MappingBuilder.map,@function
.Lshuffler.MappingBuilder.map:
	movq	32(%rdi), %rcx
	movw	$1, %ax
	cmpb	$0, (%rcx,%rsi)
	jne	.LBB25_4
	movq	48(%rdi), %rcx
	cmpq	$-1, (%rcx,%rsi,8)
	jne	.LBB25_4
	cmpq	$-1, 8192(%rcx,%rdx,8)
	jne	.LBB25_4
	movq	%rdx, (%rcx,%rsi,8)
	movq	%rsi, 8192(%rcx,%rdx,8)
	xorl	%eax, %eax
.LBB25_4:
	retq
.Lfunc_end25:
	.size	.Lshuffler.MappingBuilder.map, .Lfunc_end25-.Lshuffler.MappingBuilder.map

	.type	.Lshuffler.MappingBuilder.keepWildcardSlots,@function
.Lshuffler.MappingBuilder.keepWildcardSlots:
	pushq	%r15
	pushq	%r14
	pushq	%r12
	pushq	%rbx
	pushq	%rax
	movq	%rdi, %rbx
	movq	8(%rdi), %rax
	movq	24(%rdi), %r15
	cmpq	%r15, %rax
	cmovbq	%rax, %r15
	xorl	%r14d, %r14d
	movabsq	$4294967296, %r12
.LBB26_1:
	cmpq	%r14, %r15
	je	.LBB26_2
	movq	16(%rbx), %rax
	movzbl	4(%rax,%r14,8), %eax
	shlq	$32, %rax
	cmpq	%r12, %rax
	jne	.LBB26_5
	movq	48(%rbx), %rax
	cmpq	$-1, 8192(%rax,%r14,8)
	jne	.LBB26_5
	movq	32(%rbx), %rcx
	cmpb	$0, (%rcx,%r14)
	jne	.LBB26_5
	cmpq	$-1, (%rax,%r14,8)
	jne	.LBB26_5
	movq	%rbx, %rdi
	movq	%r14, %rsi
	movq	%r14, %rdx
	callq	.Lshuffler.MappingBuilder.map
	testw	%ax, %ax
	jne	.LBB26_10
.LBB26_5:
	incq	%r14
	jmp	.LBB26_1
.LBB26_2:
	xorl	%eax, %eax
.LBB26_3:
	addq	$8, %rsp
	popq	%rbx
	popq	%r12
	popq	%r14
	popq	%r15
	retq
.LBB26_10:
	movw	$1, %ax
	jmp	.LBB26_3
.Lfunc_end26:
	.size	.Lshuffler.MappingBuilder.keepWildcardSlots, .Lfunc_end26-.Lshuffler.MappingBuilder.keepWildcardSlots

	.type	.Lshuffler.MappingBuilder.mapWildcardSlotCopies,@function
.Lshuffler.MappingBuilder.mapWildcardSlotCopies:
	pushq	%rbp
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbx
	pushq	%rax
	movq	%rdi, %rbx
	movq	24(%rdi), %r15
	xorl	%r14d, %r14d
	movabsq	$4294967296, %r12
	pushq	$1
	popq	%rbp
.LBB27_1:
	cmpq	%r14, %r15
	je	.LBB27_2
	movq	48(%rbx), %rax
	cmpq	$-1, 8192(%rax,%r14,8)
	jne	.LBB27_5
	movq	16(%rbx), %rax
	movzbl	4(%rax,%r14,8), %r13d
	shlq	$32, %r13
	cmpq	%r12, %r13
	je	.LBB27_5
	movq	%rbx, %rdi
	movq	%r14, %rsi
	movl	%ebp, %edx
	callq	.Lshuffler.MappingBuilder.closestCopy
	cmpq	$-1, %rax
	je	.LBB27_5
	movabsq	$12884901888, %rcx
	cmpq	%rcx, %r13
	je	.LBB27_9
	movb	$1, 56(%rbx)
	cmpb	$1, 40(%rbx)
	jne	.LBB27_5
.LBB27_9:
	movq	%rbx, %rdi
	movq	%rax, %rsi
	movq	%r14, %rdx
	callq	.Lshuffler.MappingBuilder.map
	testw	%ax, %ax
	jne	.LBB27_10
.LBB27_5:
	incq	%r14
	jmp	.LBB27_1
.LBB27_2:
	xorl	%eax, %eax
.LBB27_3:
	addq	$8, %rsp
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	popq	%rbp
	retq
.LBB27_10:
	movw	$1, %ax
	jmp	.LBB27_3
.Lfunc_end27:
	.size	.Lshuffler.MappingBuilder.mapWildcardSlotCopies, .Lfunc_end27-.Lshuffler.MappingBuilder.mapWildcardSlotCopies

	.type	.Lshuffler.MappingBuilder.mapClosestCopies,@function
.Lshuffler.MappingBuilder.mapClosestCopies:
	pushq	%r15
	pushq	%r14
	pushq	%r12
	pushq	%rbx
	pushq	%rax
	movq	%rdi, %rbx
	movq	24(%rdi), %r15
	xorl	%r14d, %r14d
	movabsq	$4294967296, %r12
.LBB28_1:
	cmpq	%r14, %r15
	je	.LBB28_2
	movq	48(%rbx), %rax
	cmpq	$-1, 8192(%rax,%r14,8)
	jne	.LBB28_5
	movq	16(%rbx), %rax
	movzbl	4(%rax,%r14,8), %eax
	shlq	$32, %rax
	cmpq	%r12, %rax
	je	.LBB28_5
	movq	%rbx, %rdi
	movq	%r14, %rsi
	xorl	%edx, %edx
	callq	.Lshuffler.MappingBuilder.closestCopy
	cmpq	$-1, %rax
	je	.LBB28_5
	movq	%rbx, %rdi
	movq	%rax, %rsi
	movq	%r14, %rdx
	callq	.Lshuffler.MappingBuilder.map
	testw	%ax, %ax
	jne	.LBB28_9
.LBB28_5:
	incq	%r14
	jmp	.LBB28_1
.LBB28_2:
	xorl	%eax, %eax
.LBB28_3:
	addq	$8, %rsp
	popq	%rbx
	popq	%r12
	popq	%r14
	popq	%r15
	retq
.LBB28_9:
	movw	$1, %ax
	jmp	.LBB28_3
.Lfunc_end28:
	.size	.Lshuffler.MappingBuilder.mapClosestCopies, .Lfunc_end28-.Lshuffler.MappingBuilder.mapClosestCopies

	.type	.Lshuffler.MappingBuilder.closestCopy,@function
.Lshuffler.MappingBuilder.closestCopy:
	pushq	%rbp
	pushq	%r15
	pushq	%r14
	pushq	%rbx
	movq	8(%rdi), %rcx
	movq	%rsi, %r8
	negq	%r8
	movabsq	$-1, %rax
	xorl	%r9d, %r9d
	movabsq	$4294967296, %r10
	movq	%rsi, %r11
.LBB29_1:
	cmpq	%r9, %rcx
	je	.LBB29_13
	movq	(%rdi), %r14
	movq	16(%rdi), %rbx
	movq	(%rbx,%rsi,8), %r15
	xorq	(%r14,%r9,8), %r15
	shlq	$16, %r15
	jne	.LBB29_3
	movq	32(%rdi), %r14
	cmpb	$0, (%r14,%r9)
	jne	.LBB29_3
	movq	48(%rdi), %r14
	cmpq	$-1, (%r14,%r9,8)
	je	.LBB29_7
.LBB29_3:
	movq	%rax, %rbx
.LBB29_4:
	incq	%r9
	decq	%r11
	movq	%rbx, %rax
	jmp	.LBB29_1
.LBB29_7:
	cmpq	24(%rdi), %r9
	jae	.LBB29_8
	testb	%dl, %dl
	setne	%bpl
	movzbl	4(%rbx,%r9,8), %ebx
	shlq	$32, %rbx
	cmpq	%r10, %rbx
	sete	%bl
	xorb	%bpl, %bl
	jne	.LBB29_3
	jmp	.LBB29_10
.LBB29_8:
	testb	%dl, %dl
	jne	.LBB29_3
.LBB29_10:
	movq	%r9, %rbx
	cmpq	$-1, %rax
	je	.LBB29_4
	leaq	(%r8,%r9), %r14
	cmpq	%rsi, %r9
	cmovbeq	%r11, %r14
	movq	%rsi, %rbx
	subq	%rax, %rbx
	movq	%rax, %r15
	subq	%rsi, %r15
	cmovbq	%rbx, %r15
	movq	%rax, %rbx
	cmpq	%r15, %r14
	ja	.LBB29_4
	movq	%r9, %rbx
	jmp	.LBB29_4
.LBB29_13:
	popq	%rbx
	popq	%r14
	popq	%r15
	popq	%rbp
	retq
.Lfunc_end29:
	.size	.Lshuffler.MappingBuilder.closestCopy, .Lfunc_end29-.Lshuffler.MappingBuilder.closestCopy

	.type	.Lshuffler.MappingBuilder.mapInPlace,@function
.Lshuffler.MappingBuilder.mapInPlace:
	pushq	%r15
	pushq	%r14
	pushq	%rbx
	movq	%rdi, %rbx
	movq	8(%rdi), %rax
	movq	24(%rdi), %r15
	cmpq	%r15, %rax
	cmovbq	%rax, %r15
	xorl	%r14d, %r14d
.LBB30_1:
	cmpq	%r14, %r15
	je	.LBB30_2
	movq	(%rbx), %rax
	movq	16(%rbx), %rcx
	movq	(%rcx,%r14,8), %rcx
	xorq	(%rax,%r14,8), %rcx
	shlq	$16, %rcx
	jne	.LBB30_5
	movq	32(%rbx), %rax
	cmpb	$0, (%rax,%r14)
	jne	.LBB30_5
	movq	48(%rbx), %rax
	cmpq	$-1, (%rax,%r14,8)
	jne	.LBB30_5
	movq	%rbx, %rdi
	movq	%r14, %rsi
	movq	%r14, %rdx
	callq	.Lshuffler.MappingBuilder.map
	testw	%ax, %ax
	jne	.LBB30_9
.LBB30_5:
	incq	%r14
	jmp	.LBB30_1
.LBB30_2:
	xorl	%eax, %eax
.LBB30_3:
	popq	%rbx
	popq	%r14
	popq	%r15
	retq
.LBB30_9:
	movw	$1, %ax
	jmp	.LBB30_3
.Lfunc_end30:
	.size	.Lshuffler.MappingBuilder.mapInPlace, .Lfunc_end30-.Lshuffler.MappingBuilder.mapInPlace

	.section	".note.GNU-stack","",@progbits
