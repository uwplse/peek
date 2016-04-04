# File generated by CompCert 2.4
# Command line: -fno-peeps -stdlib ../../runtime -dc -dclight -dasm -S -o mandelbrot.handtuned.s mandelbrot.c
	.section	.rodata
	.align	1
__stringlit_1:
	.ascii	"P4\012%d %d\012\000"
	.type	__stringlit_1, @object
	.size	__stringlit_1, . - __stringlit_1
	.text
	.align	16
	.globl main
main:
	.cfi_startproc
	subl	$52, %esp
	.cfi_adjust_cfa_offset	52
	leal	56(%esp), %edx
	movl	%edx, 12(%esp)
	movl	%ebx, 16(%esp)
	movl	%esi, 20(%esp)
	movl	%edi, 24(%esp)
	movl	%ebp, 28(%esp)
	movl	0(%edx), %ecx
	movl	4(%edx), %eax
	xorl	%ebp, %ebp
	xorl	%ebx, %ebx
	cmpl	$2, %ecx
	jl	.L100
	movl	4(%eax), %edx
	movl	%edx, 0(%esp)
	call	atoi
	movl	%eax, %esi
	movl	%esi, %edi
	jmp	.L101
.L100:
	movl	$5000, %edi
	movl	$5000, %esi
.L101:
	leal	__stringlit_1, %edx
	movl	%edx, 0(%esp)
	movl	%esi, 4(%esp)
	movl	%edi, 8(%esp)
	call	printf
	xorpd	%xmm2, %xmm2
	movsd	%xmm2, 40(%esp)
.L102:
	cvtsi2sd %edi, %xmm4
	movsd	40(%esp), %xmm3
	comisd	%xmm3, %xmm4
	jbe	.L103
	xorpd	%xmm5, %xmm5
	movsd	%xmm5, 32(%esp)
.L104:
	cvtsi2sd %esi, %xmm1
	movsd	32(%esp), %xmm2
	comisd	%xmm2, %xmm1
	jbe	.L105
	xorpd	%xmm2, %xmm2
	movapd	%xmm2, %xmm4
	movapd	%xmm4, %xmm7
	movapd	%xmm7, %xmm5
	movsd	32(%esp), %xmm6
	addsd	%xmm6, %xmm6
	movapd	%xmm6, %xmm0
	divsd	%xmm1, %xmm0
	movsd	.L106, %xmm1 # 1.5
	subsd	%xmm1, %xmm0
	movsd	40(%esp), %xmm1
	addsd	%xmm1, %xmm1
	cvtsi2sd %edi, %xmm3
	divsd	%xmm3, %xmm1
	movsd	.L107, %xmm3 # 1
	subsd	%xmm3, %xmm1
	xorl	%eax, %eax
.L108:
	movapd	%xmm4, %xmm3
	addsd	%xmm2, %xmm3
	movsd	.L109, %xmm6 # 4
	comisd	%xmm3, %xmm6
	jb	.L110
	addsd	%xmm5, %xmm5
	mulsd	%xmm7, %xmm5
	movapd	%xmm5, %xmm7
	addsd	%xmm1, %xmm7
	subsd	%xmm2, %xmm4
	movapd	%xmm4, %xmm5
	addsd	%xmm0, %xmm5
	movapd	%xmm5, %xmm4
	mulsd	%xmm5, %xmm4
	movapd	%xmm7, %xmm2
	mulsd	%xmm7, %xmm2
	leal	1(%eax), %eax
	cmpl	$50, %eax
	jl	.L108
.L110:
	leal	0(,%ebx,2), %eax
	movsbl	%al, %ebx
	addsd	%xmm2, %xmm4
	movsd	.L111, %xmm1 # 4
	comisd	%xmm4, %xmm1
	jb	.L112
	orl	$1, %ebx
	movsbl	%bl, %ebx
.L112:
	leal	1(%ebp), %ebp
	cmpl	$8, %ebp
	je	.L113
	leal	-1(%esi), %ecx
	cvtsi2sd %ecx, %xmm5
	movsd	32(%esp), %xmm6
	comisd	%xmm5, %xmm6
	jp	.L114
	jne	.L114
	movl	$8, %edx
	movl	%esi, %eax
	testl	%eax, %eax
	leal	7(%eax), %ecx
	cmovl	%ecx, %eax
	sarl	$3, %eax
	leal	0(,%eax,8), %eax
	movl	%esi, %ecx
	subl	%eax, %ecx
	subl	%ecx, %edx
	movl	%edx, %ecx
	sall	%cl, %ebx
	movsbl	%bl, %ecx
	movl	stdout, %edx
	movl	%ecx, 0(%esp)
	movl	%edx, 4(%esp)
	call	_IO_putc
	xorl	%ebx, %ebx
	xorl	%ebp, %ebp
	jmp	.L114
.L113:
	movl	stdout, %edx
	movl	%ebx, 0(%esp)
	movl	%edx, 4(%esp)
	call	_IO_putc
	xorl	%ebx, %ebx
	xorl	%ebp, %ebp
.L114:
	movsd	.L115, %xmm2 # 1
	movsd	32(%esp), %xmm3
	addsd	%xmm2, %xmm3
	movsd	%xmm3, 32(%esp)
	jmp	.L104
.L105:
	movsd	.L116, %xmm0 # 1
	movsd	40(%esp), %xmm4
	addsd	%xmm0, %xmm4
	movsd	%xmm4, 40(%esp)
	jmp	.L102
.L103:
	xorl	%eax, %eax
	movl	16(%esp), %ebx
	movl	20(%esp), %esi
	movl	24(%esp), %edi
	movl	28(%esp), %ebp
	addl	$52, %esp
	ret
	.cfi_endproc
	.type	main, @function
	.size	main, . - main
	.section	.rodata.cst8,"aM",@progbits,8
	.align	8
.L116:	.quad	0x3ff0000000000000
.L115:	.quad	0x3ff0000000000000
.L111:	.quad	0x4010000000000000
.L109:	.quad	0x4010000000000000
.L107:	.quad	0x3ff0000000000000
.L106:	.quad	0x3ff8000000000000
