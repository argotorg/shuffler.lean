_ZN12_GLOBAL__N_18Emission13buildBottomUpEv:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$24, %rsp
	movq	%rdi, %r12
	movq	8(%rdi), %r13
	testq	%r13, %r13
	je	.LB101
	movl	$0, %r14d
	jmp	.LB135
.LB104:
	movl	$2, %eax
	cmpq	%r13, %r15
	jne	.LB100
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission7permuteEv
	jmp	.LB100
.LB155:
	movq	%rax, 16448(%r12)
	subq	$16, %rcx
	movq	%rcx, 16456(%r12)
	movl	$1, %eax
	jmp	.LB100
	.p2align 5
.LB111:
	addq	$1, %rbx
	cmpq	%r13, %rbx
	je	.LB154
.LB105:
	cmpq	$-1, 8248(%r12,%rbx,8)
	jne	.LB111
	movq	(%r12), %rax
	leaq	(%rax,%rbx,8), %rax
	movq	(%rax), %rbp
	movzbl	4(%rax), %edx
	cmpb	$1, %dl
	je	.LB111
	movzbl	5(%rax), %ecx
	movzbl	%dl, %eax
	salq	$32, %rax
	movabsq	$-1095216660481, %rsi
	andq	%rsi, %rbp
	orq	%rax, %rbp
	testb	%cl, %cl
	je	.LB111
	cmpb	$2, %dl
	je	.LB111
	movzbl	%cl, %ecx
	salq	$40, %rcx
	movabsq	$-280375465082881, %rax
	andq	%rax, %rbp
	orq	%rcx, %rbp
	movq	%rbp, %rsi
	movq	%r12, %rdi
	call	_ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot
	testb	%al, %al
	jne	.LB111
	movq	%rbp, %rsi
	movq	%r12, %rdi
	call	_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot
	cmpq	$-1, %rax
	je	.LB111
	movq	%r15, %rcx
	subq	%rax, %rcx
	leaq	-1(%rcx), %rdx
	cmpq	$15, %rdx
	ja	.LB155
	cmpq	%r14, %rax
	sete	%al
	cmpq	$15, %rdx
	setne	%dl
	orb	%dl, %al
	jne	.LB111
	movq	8(%rsp), %rax
	cmpq	$-1, %rax
	cmove	%rbx, %rax
	movq	%rax, 8(%rsp)
	jmp	.LB111
.LB154:
	movq	8(%rsp), %rdi
	cmpq	$-1, %rdi
	sete	%al
	cmpq	%r14, %rdi
	je	.LB106
	testb	%al, %al
	je	.LB156
.LB106:
	cmpq	%r13, %r15
	setb	%cl
	cmpq	%r15, %r14
	setb	%dl
	testb	%dl, %cl
	je	.LB113
	testb	%al, %al
	jne	.LB157
.LB113:
	leaq	0(,%r14,8), %rbx
	movq	8248(%r12,%rbx), %rdx
	cmpq	$-1, %rdx
	je	.LB117
	cmpq	%r14, %rdx
	jb	.LB158
	movq	24(%r12), %rcx
	movq	(%rcx,%rdx,8), %rsi
	movq	%rsi, %rdi
	xorq	(%rcx,%r14,8), %rdi
	movq	%r14, %rax
	salq	$16, %rdi
	jne	.LB159
.LB125:
	movq	%rax, %rsi
	movq	56(%r12,%rax,8), %rcx
	movq	56(%r12,%rdx,8), %rdi
	movq	%rdi, 56(%r12,%rax,8)
	movq	%rcx, 56(%r12,%rdx,8)
	movq	56(%r12,%rax,8), %rcx
	cmpq	$-1, %rcx
	je	.LB126
	movq	%rax, 8248(%r12,%rcx,8)
.LB126:
	movq	56(%r12,%rdx,8), %rcx
	cmpq	$-1, %rcx
	je	.LB127
	movq	%rdx, 8248(%r12,%rcx,8)
.LB127:
	cmpq	%rax, %r14
	je	.LB142
	leaq	-1(%r15), %rdx
	cmpq	%rax, %rdx
	je	.LB128
	subq	%rax, %r15
	leaq	-1(%r15), %rdx
	cmpq	$16, %rdx
	ja	.LB160
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	testb	%al, %al
	jne	.LB100
.LB128:
	movq	32(%r12), %rax
	cmpq	%rax, %r14
	jnb	.LB144
	cmpq	%r14, 56(%r12,%rbx)
	jne	.LB130
	movl	$2, %eax
.LB100:
	addq	$24, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB156:
	movq	%r15, %rax
	subq	%r14, %rax
	cmpq	$15, %rax
	ja	.LB113
	movq	8(%rsp), %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
	testb	%al, %al
	jne	.LB100
	subq	$1, %r14
	jmp	.LB133
.LB157:
	cmpq	$-1, 8248(%r12,%r15,8)
	jne	.LB113
	movq	%r15, %rax
	subq	%r14, %rax
	cmpq	$15, %rax
	ja	.LB113
	movq	%r15, %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
	testb	%al, %al
	jne	.LB100
	subq	$1, %r14
	jmp	.LB133
.LB117:
	movq	%r14, %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
	testb	%al, %al
	jne	.LB100
	movq	32(%r12), %rax
	cmpq	%rax, %r14
	jnb	.LB143
	cmpq	%r14, 56(%r12,%rbx)
	je	.LB133
.LB130:
	leaq	-1(%rax), %rdx
	cmpq	%r14, %rdx
	je	.LB133
	subq	%r14, %rax
	leaq	-1(%rax), %rdx
	cmpq	$16, %rdx
	ja	.LB161
	movq	%r14, %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	testb	%al, %al
	je	.LB133
	jmp	.LB100
.LB159:
	leaq	-1(%r15), %rax
	cmpq	%rax, %rdx
	jb	.LB124
	movq	%rdx, %rax
	jmp	.LB125
	.p2align 5
.LB122:
	subq	$1, %rax
	cmpq	%rax, %rdx
	jnb	.LB162
.LB124:
	movq	%rsi, %rdi
	xorq	(%rcx,%rax,8), %rdi
	salq	$16, %rdi
	jne	.LB122
	cmpq	%rax, 56(%r12,%rax,8)
	je	.LB122
	xorq	(%rcx,%rax,8), %rsi
	salq	$16, %rsi
	je	.LB125
	movl	$2, %eax
	jmp	.LB100
.LB162:
	movq	%rdx, %rax
	jmp	.LB125
.LB160:
	movq	%rax, 16448(%r12)
	subq	$17, %r15
	movq	%r15, 16456(%r12)
	movl	$1, %eax
	jmp	.LB100
.LB161:
	movq	%r14, 16448(%r12)
	subq	$17, %rax
	movq	%rax, 16456(%r12)
	movl	$1, %eax
	jmp	.LB100
.LB142:
	movq	%rax, %r14
.LB133:
	addq	$1, %r14
	movq	8(%r12), %r13
	cmpq	%r13, %r14
	jnb	.LB101
.LB135:
	movq	32(%r12), %r15
	cmpq	%r15, %r14
	jnb	.LB102
	cmpq	%r14, 56(%r12,%r14,8)
	je	.LB133
.LB102:
	cmpq	$0, 16440(%r12)
	je	.LB104
	movq	%r14, %rbx
	movq	$-1, 8(%rsp)
	movl	$1, %eax
	cmpq	%r13, %r14
	jb	.LB105
	jmp	.LB106
.LB158:
	movl	$2, %eax
	jmp	.LB100
.LB143:
	movl	$2, %eax
	jmp	.LB100
.LB144:
	movl	$2, %eax
	jmp	.LB100
.LB101:
	cmpq	%r13, 32(%r12)
	setne	%al
	addl	%eax, %eax
	jmp	.LB100
	.size	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv, .-_ZN12_GLOBAL__N_18Emission13buildBottomUpEv
