_ZN12_GLOBAL__N_18Emission13buildBottomUpEv:
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbp
	pushq	%rbx
	subq	$8216, %rsp
	movq	%rdi, %r12
	movq	8(%rdi), %r13
	testq	%r13, %r13
	je	.LB101
	movl	$0, %r14d
	jmp	.LB139
.LB104:
	movl	$2, %eax
	cmpq	%r13, %r15
	jne	.LB100
.LB109:
	movq	56(%r12,%rdx,8), %rax
	cmpq	$-1, %rax
	je	.LB108
	movq	%rax, 16(%rsp,%rdx,8)
	addq	$1, %rdx
	cmpq	%rdx, %r13
	jne	.LB109
	leaq	16(%rsp), %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE
	jmp	.LB100
.LB108:
	movl	$2, %eax
	jmp	.LB100
.LB161:
	movq	%rax, 16448(%r12)
	subq	$16, %rcx
	movq	%rcx, 16456(%r12)
	movl	$1, %eax
	jmp	.LB100
	.p2align 5
.LB115:
	addq	$1, %rbx
	cmpq	%r13, %rbx
	je	.LB160
.LB105:
	cmpq	$-1, 8248(%r12,%rbx,8)
	jne	.LB115
	movq	(%r12), %rax
	leaq	(%rax,%rbx,8), %rax
	movq	(%rax), %rbp
	movzbl	4(%rax), %edx
	cmpb	$1, %dl
	je	.LB115
	movzbl	5(%rax), %ecx
	movzbl	%dl, %eax
	salq	$32, %rax
	movabsq	$-1095216660481, %rsi
	andq	%rsi, %rbp
	orq	%rax, %rbp
	testb	%cl, %cl
	je	.LB115
	cmpb	$2, %dl
	je	.LB115
	movzbl	%cl, %ecx
	salq	$40, %rcx
	movabsq	$-280375465082881, %rax
	andq	%rax, %rbp
	orq	%rcx, %rbp
	movq	%rbp, %rsi
	movq	%r12, %rdi
	call	_ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot
	testb	%al, %al
	jne	.LB115
	movq	%rbp, %rsi
	movq	%r12, %rdi
	call	_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot
	cmpq	$-1, %rax
	je	.LB115
	movq	%r15, %rcx
	subq	%rax, %rcx
	leaq	-1(%rcx), %rdx
	cmpq	$15, %rdx
	ja	.LB161
	cmpq	%r14, %rax
	sete	%al
	cmpq	$15, %rdx
	setne	%dl
	orb	%dl, %al
	jne	.LB115
	movq	8(%rsp), %rax
	cmpq	$-1, %rax
	cmove	%rbx, %rax
	movq	%rax, 8(%rsp)
	jmp	.LB115
.LB160:
	movq	8(%rsp), %rdi
	cmpq	$-1, %rdi
	sete	%al
	cmpq	%r14, %rdi
	je	.LB106
	testb	%al, %al
	je	.LB162
.LB106:
	cmpq	%r13, %r15
	setb	%cl
	cmpq	%r15, %r14
	setb	%dl
	testb	%dl, %cl
	je	.LB117
	testb	%al, %al
	jne	.LB163
.LB117:
	leaq	0(,%r14,8), %rbx
	movq	8248(%r12,%rbx), %rdx
	cmpq	$-1, %rdx
	je	.LB121
	cmpq	%r14, %rdx
	jb	.LB164
	movq	24(%r12), %rcx
	movq	(%rcx,%rdx,8), %rsi
	movq	%rsi, %rdi
	xorq	(%rcx,%r14,8), %rdi
	movq	%r14, %rax
	salq	$16, %rdi
	jne	.LB165
.LB129:
	movq	%rax, %rsi
	movq	56(%r12,%rax,8), %rcx
	movq	56(%r12,%rdx,8), %rdi
	movq	%rdi, 56(%r12,%rax,8)
	movq	%rcx, 56(%r12,%rdx,8)
	movq	56(%r12,%rax,8), %rcx
	cmpq	$-1, %rcx
	je	.LB130
	movq	%rax, 8248(%r12,%rcx,8)
.LB130:
	movq	56(%r12,%rdx,8), %rcx
	cmpq	$-1, %rcx
	je	.LB131
	movq	%rdx, 8248(%r12,%rcx,8)
.LB131:
	cmpq	%rax, %r14
	je	.LB146
	leaq	-1(%r15), %rdx
	cmpq	%rax, %rdx
	je	.LB132
	subq	%rax, %r15
	leaq	-1(%r15), %rdx
	cmpq	$16, %rdx
	ja	.LB166
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	testb	%al, %al
	jne	.LB100
.LB132:
	movq	32(%r12), %rax
	cmpq	%rax, %r14
	jnb	.LB148
	cmpq	%r14, 56(%r12,%rbx)
	jne	.LB134
	movl	$2, %eax
.LB100:
	addq	$8216, %rsp
	popq	%rbx
	popq	%rbp
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	ret
.LB162:
	movq	%r15, %rax
	subq	%r14, %rax
	cmpq	$15, %rax
	ja	.LB117
	movq	8(%rsp), %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
	testb	%al, %al
	jne	.LB100
	subq	$1, %r14
	jmp	.LB137
.LB163:
	cmpq	$-1, 8248(%r12,%r15,8)
	jne	.LB117
	movq	%r15, %rax
	subq	%r14, %rax
	cmpq	$15, %rax
	ja	.LB117
	movq	%r15, %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
	testb	%al, %al
	jne	.LB100
	subq	$1, %r14
	jmp	.LB137
.LB121:
	movq	%r14, %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8generateE11StackOffset
	testb	%al, %al
	jne	.LB100
	movq	32(%r12), %rax
	cmpq	%rax, %r14
	jnb	.LB147
	cmpq	%r14, 56(%r12,%rbx)
	je	.LB137
.LB134:
	leaq	-1(%rax), %rdx
	cmpq	%r14, %rdx
	je	.LB137
	subq	%r14, %rax
	leaq	-1(%rax), %rdx
	cmpq	$16, %rdx
	ja	.LB167
	movq	%r14, %rsi
	movq	%r12, %rdi
	call	_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset
	testb	%al, %al
	je	.LB137
	jmp	.LB100
.LB165:
	leaq	-1(%r15), %rax
	cmpq	%rax, %rdx
	jb	.LB128
	movq	%rdx, %rax
	jmp	.LB129
	.p2align 5
.LB126:
	subq	$1, %rax
	cmpq	%rax, %rdx
	jnb	.LB168
.LB128:
	movq	%rsi, %rdi
	xorq	(%rcx,%rax,8), %rdi
	salq	$16, %rdi
	jne	.LB126
	cmpq	%rax, 56(%r12,%rax,8)
	je	.LB126
	xorq	(%rcx,%rax,8), %rsi
	salq	$16, %rsi
	je	.LB129
	movl	$2, %eax
	jmp	.LB100
.LB168:
	movq	%rdx, %rax
	jmp	.LB129
.LB166:
	movq	%rax, 16448(%r12)
	subq	$17, %r15
	movq	%r15, 16456(%r12)
	movl	$1, %eax
	jmp	.LB100
.LB167:
	movq	%r14, 16448(%r12)
	subq	$17, %rax
	movq	%rax, 16456(%r12)
	movl	$1, %eax
	jmp	.LB100
.LB146:
	movq	%rax, %r14
.LB137:
	addq	$1, %r14
	movq	8(%r12), %r13
	cmpq	%r13, %r14
	jnb	.LB101
.LB139:
	movq	32(%r12), %r15
	cmpq	%r15, %r14
	jnb	.LB102
	cmpq	%r14, 56(%r12,%r14,8)
	je	.LB137
.LB102:
	movq	16440(%r12), %rdx
	testq	%rdx, %rdx
	je	.LB104
	movq	%r14, %rbx
	movq	$-1, 8(%rsp)
	movl	$1, %eax
	cmpq	%r13, %r14
	jb	.LB105
	jmp	.LB106
.LB164:
	movl	$2, %eax
	jmp	.LB100
.LB147:
	movl	$2, %eax
	jmp	.LB100
.LB148:
	movl	$2, %eax
	jmp	.LB100
.LB101:
	cmpq	%r13, 32(%r12)
	setne	%al
	addl	%eax, %eax
	jmp	.LB100
	.size	_ZN12_GLOBAL__N_18Emission13buildBottomUpEv, .-_ZN12_GLOBAL__N_18Emission13buildBottomUpEv
