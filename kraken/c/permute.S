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
	leaq	(%rsi,%r10,2), %rdi
	jmp	.L7
.L13:
	cmpq	%rax, %rsi
	je	.L1
	movq	%rsi, %rdx
	.p2align 6
.L3:
	movq	%r10, %rax
	subq	%rdx, %rax
	cmpq	$16, %rax
	ja	.L12
	addq	$1, %rcx
	movb	%al, -1(%r11,%rcx)
	movzwl	(%rdi), %esi
	leaq	(%r9,%rdx,2), %rax
	movzwl	(%rax), %edx
	movw	%dx, (%rdi)
	movw	%si, (%rax)
.L7:
	movzwl	(%rdi), %edx
	cmpq	%rdx, %r10
	jne	.L3
	testq	%rdx, %rdx
	je	.L1
	movq	%rdx, %rsi
	movl	$0, %eax
	.p2align 5
.L5:
	movzwl	(%r9,%rax,2), %r8d
	cmpq	%rax, %r8
	cmovne	%rax, %rsi
	addq	$1, %rax
	cmpq	%rax, %rdx
	jne	.L5
	jmp	.L13
.L12:
	movw	%dx, (%rbx)
	subl	$16, %eax
	movw	%ax, 2(%rbx)
	movq	$-1, %rcx
.L1:
	movq	%rcx, %rax
	popq	%rbx
	ret
	.size	permute, .-permute
	.section	.note.GNU-stack,"",@progbits
