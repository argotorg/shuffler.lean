	.file	"permute.c"
	.text
	.globl	permute
	.type	permute, @function
permute:
	pushq	%rbx
	movq	%rcx, %rbx
	movl	$0, %ecx
	testq	%rdi, %rdi
	je	.L1
	movq	%rsi, %r9
	movq	%rdx, %r11
	leaq	-1(%rdi), %r10
	leaq	(%rsi,%r10), %rdi
	jmp	.L7
.L13:
	cmpq	%rdx, %rsi
	je	.L1
	movq	%rsi, %rax
	.p2align 6
.L3:
	movq	%r10, %rdx
	subq	%rax, %rdx
	cmpq	$16, %rdx
	ja	.L12
	addq	$1, %rcx
	movb	%dl, -1(%r11,%rcx)
	movzbl	(%rdi), %edx
	addq	%r9, %rax
	movzbl	(%rax), %esi
	movb	%sil, (%rdi)
	movb	%dl, (%rax)
.L7:
	movzbl	(%rdi), %eax
	cmpq	%rax, %r10
	jne	.L3
	testq	%rax, %rax
	je	.L1
	movq	%rax, %rsi
	movl	$0, %edx
	.p2align 5
.L5:
	movzbl	(%r9,%rdx), %r8d
	cmpq	%rdx, %r8
	cmovne	%rdx, %rsi
	addq	$1, %rdx
	cmpq	%rdx, %rax
	jne	.L5
	jmp	.L13
.L12:
	movb	%al, (%rbx)
	subl	$16, %edx
	movb	%dl, 1(%rbx)
	movq	$-1, %rcx
.L1:
	movq	%rcx, %rax
	popq	%rbx
	ret
	.size	permute, .-permute
	.section	.note.GNU-stack,"",@progbits
