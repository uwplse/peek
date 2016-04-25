# File generated by CompCert 2.4
# Command line: -fno-peeps -stdlib ../../runtime -dc -dclight -dasm -S -o bisect.handtuned.s bisect.c
	.section	.rodata
	.align	1
__stringlit_1:
	.ascii	"Error: couldn't allocate V in allocvector.\012\000"
	.type	__stringlit_1, @object
	.size	__stringlit_1, . - __stringlit_1
	.section	.rodata
	.align	1
__stringlit_2:
	.ascii	"bisect: Couldn't allocate memory for wu\000"
	.type	__stringlit_2, @object
	.size	__stringlit_2, . - __stringlit_2
	.section	.rodata
	.align	1
__stringlit_3:
	.ascii	"%5d %.5e\012\000"
	.type	__stringlit_3, @object
	.size	__stringlit_3, . - __stringlit_3
	.section	.rodata
	.align	1
__stringlit_4:
	.ascii	"eps2 = %.5e,  k = %d\012\000"
	.type	__stringlit_4, @object
	.size	__stringlit_4, . - __stringlit_4
	.text
	.align	16
	.globl allocvector
allocvector:
	.cfi_startproc
	subl	$28, %esp
	.cfi_adjust_cfa_offset	28
	leal	32(%esp), %edx
	movl	%edx, 12(%esp)
	movl	%ebx, 16(%esp)
	movl	%esi, 20(%esp)
	movl	0(%edx), %esi
	movl	%esi, 0(%esp)
	call	malloc
	movl	%eax, %ebx
	cmpl	$0, %ebx
	jne	.L100
	movl	stderr, %edx
	leal	__stringlit_1, %ecx
	movl	%edx, 0(%esp)
	movl	%ecx, 4(%esp)
	call	fprintf
	movl	$2, %eax
	movl	%eax, 0(%esp)
	call	exit
.L100:
	xorl	%ecx, %ecx
	movl	%ebx, 0(%esp)
	movl	%ecx, 4(%esp)
	movl	%esi, 8(%esp)
	call	memset
	movl	%ebx, %eax
	movl	16(%esp), %ebx
	movl	20(%esp), %esi
	addl	$28, %esp
	ret
	.cfi_endproc
	.type	allocvector, @function
	.size	allocvector, . - allocvector
	.text
	.align	16
	.globl dallocvector
dallocvector:
	.cfi_startproc
	subl	$20, %esp
	.cfi_adjust_cfa_offset	20
	leal	24(%esp), %edx
	movl	%edx, 4(%esp)
	movl	%ebx, 8(%esp)
	movl	0(%edx), %ecx
	movl	4(%edx), %ebx
	leal	0(,%ecx,8), %eax
	movl	%eax, 0(%esp)
	call	allocvector
	movl	%eax, 0(%ebx)
	movl	8(%esp), %ebx
	addl	$20, %esp
	ret
	.cfi_endproc
	.type	dallocvector, @function
	.size	dallocvector, . - dallocvector
	.text
	.align	16
	.globl sturm
sturm:
	.cfi_startproc
	subl	$60, %esp
	.cfi_adjust_cfa_offset	60
	leal	64(%esp), %edx
	movl	%edx, 8(%esp)
	movl	%ebx, 12(%esp)
	movl	%esi, 16(%esp)
	movl	%edi, 20(%esp)
	movl	%ebp, 24(%esp)
	movl	0(%edx), %edx
	movl	%edx, 44(%esp)
	movl	8(%esp), %edx
	movl	4(%edx), %esi
	movl	8(%edx), %edx
	movl	%edx, 32(%esp)
	movl	8(%esp), %edx
	movl	12(%edx), %ebx
	movsd	16(%edx), %xmm1
	movsd	%xmm1, 36(%esp)
	xorl	%ebp, %ebp
	movsd	.L101, %xmm3 # 1
	xorl	%edi, %edi
.L102:
	cmpl	44(%esp), %edi	
	jge	.L103
        .DZ0:	.quad	0x0	
	comisd	.DZ0, %xmm3
	jp	.L104
	jne	.L104
	movl	32(%esp), %ecx
	movsd	0(%ecx,%edi,8), %xmm6
	movsd	%xmm6, 0(%esp)
	call	fabs
	fstpl	48(%esp)
	movsd	48(%esp), %xmm5
	movsd	0(%esi,%edi,8), %xmm3
	subsd	36(%esp), %xmm3		
	mulsd	.L105, %xmm5
	subsd	%xmm5, %xmm3
	jmp	.L106
.L104:
	movsd	0(%esi,%edi,8), %xmm4
	movsd	36(%esp), %xmm0
	subsd	%xmm0, %xmm4
	movsd	0(%ebx,%edi,8), %xmm2
	divsd	%xmm3, %xmm2
	movapd	%xmm4, %xmm3
	subsd	%xmm2, %xmm3
.L106:	
	comisd	.DZ0, %xmm3
	jbe	.L107
	incl	%ebp
.L107:
	incl    %edi
	jmp	.L102
.L103:
	movl	%ebp, %eax
	movl	12(%esp), %ebx
	movl	16(%esp), %esi
	movl	20(%esp), %edi
	movl	24(%esp), %ebp
	addl	$60, %esp
	ret
	.cfi_endproc
	.type	sturm, @function
	.size	sturm, . - sturm
	.section	.rodata.cst8,"aM",@progbits,8
	.align	8
.L105:	.quad	0x4330000000000000
.L101:	.quad	0x3ff0000000000000
	.text
	.align	16
	.globl dbisect
dbisect:
	.cfi_startproc
	subl	$132, %esp
	.cfi_adjust_cfa_offset	132
	leal	136(%esp), %edx
	movl	%edx, 24(%esp)
	movl	%ebx, 28(%esp)
	movl	%esi, 32(%esp)
	movl	%edi, 36(%esp)
	movl	%ebp, 40(%esp)
	movl	0(%edx), %edx
	movl	%edx, 64(%esp)
	movl	24(%esp), %edx
	movl	4(%edx), %edi
	movl	8(%edx), %edx
	movl	%edx, 112(%esp)
	movl	24(%esp), %edx
	movl	12(%edx), %ebp
	movl	16(%edx), %edx
	movl	%edx, 92(%esp)
	movl	24(%esp), %edx
	movl	20(%edx), %edx
	movl	%edx, 68(%esp)
	movl	24(%esp), %edx
	movsd	24(%edx), %xmm7
	movsd	%xmm7, 84(%esp)
	movl	32(%edx), %ebx
	movl	36(%edx), %edx
	movl	%edx, 108(%esp)
	movl	24(%esp), %edx
	movl	40(%edx), %edx
	movl	%edx, 104(%esp)
	xorpd	%xmm7, %xmm7
	movsd	%xmm7, 0(%edi)
	movl	112(%esp), %ecx
	movsd	%xmm7, 0(%ecx)
	movsd	-8(%edi,%ebp,8), %xmm5
	movsd	%xmm5, 0(%esp)
	call	fabs
	fstpl	48(%esp)
	movsd	48(%esp), %xmm6
	movl	64(%esp), %eax
	movsd	-8(%eax,%ebp,8), %xmm5
	movsd	.L108, %xmm1 # 1.01000000000000001
	mulsd	%xmm6, %xmm1
	subsd	%xmm1, %xmm5
	movsd	%xmm5, 76(%esp)
	movsd	-8(%edi,%ebp,8), %xmm1
	movsd	%xmm1, 0(%esp)
	call	fabs
	fstpl	48(%esp)
	movsd	48(%esp), %xmm7
	movl	64(%esp), %eax
	movsd	-8(%eax,%ebp,8), %xmm5
	movsd	.L109, %xmm4 # 1.01000000000000001
	mulsd	%xmm7, %xmm4
	addsd	%xmm4, %xmm5
	movsd	%xmm5, 48(%esp)
	leal	-2(%ebp), %esi
.L110:
	testl	%esi, %esi
	jl	.L111
	movsd	0(%edi,%esi,8), %xmm5
	movsd	%xmm5, 0(%esp)
	call	fabs
	fstpl	56(%esp)
	movsd	8(%edi,%esi,8), %xmm5
	movsd	%xmm5, 0(%esp)
	call	fabs
	fstpl	96(%esp)
	movsd	96(%esp), %xmm0
	movsd	.L112, %xmm3 # 1.01000000000000001
	movsd	56(%esp), %xmm7
	addsd	%xmm0, %xmm7
	mulsd	%xmm7, %xmm3
	movl	64(%esp), %edx
	movsd	0(%edx,%esi,8), %xmm2
	addsd	%xmm3, %xmm2
	movsd	48(%esp), %xmm1
	comisd	%xmm1, %xmm2
	jbe	.L113
	movsd	%xmm2, 48(%esp)
.L113:
	movl	64(%esp), %edx
	movsd	0(%edx,%esi,8), %xmm5
	subsd	%xmm3, %xmm5
	movsd	76(%esp), %xmm2
	comisd	%xmm5, %xmm2
	jbe	.L114
	movsd	%xmm5, 76(%esp)
.L114:
	leal	-1(%esi), %esi
	jmp	.L110
.L111:
	movsd	76(%esp), %xmm0
	movsd	48(%esp), %xmm3
	addsd	%xmm3, %xmm0
	xorpd	%xmm4, %xmm4
	comisd	%xmm4, %xmm0
	ja	.L115
	movsd	76(%esp), %xmm4
	xorpd	__negd_mask, %xmm4
	jmp	.L116
.L115:
	movsd	48(%esp), %xmm4
.L116:
	movsd	.L117, %xmm3 # 2.22044604925031308e-16
	mulsd	%xmm4, %xmm3
	movsd	%xmm3, 0(%ebx)
	xorpd	%xmm6, %xmm6
	movsd	84(%esp), %xmm0
	comisd	%xmm0, %xmm6
	jb	.L118
	movsd	%xmm3, 84(%esp)
.L118:
	movsd	.L119, %xmm7 # 0.5
	movsd	84(%esp), %xmm6
	mulsd	%xmm6, %xmm7
	movsd	.L120, %xmm2 # 7
	movsd	0(%ebx), %xmm3
	mulsd	%xmm3, %xmm2
	addsd	%xmm2, %xmm7
	movsd	%xmm7, 0(%ebx)
	leal	1(%ebp), %eax
	movl	$8, %edx
	movl	%eax, 0(%esp)
	movl	%edx, 4(%esp)
	call	calloc
	movl	%eax, %esi
	cmpl	$0, %esi
	jne	.L121
	leal	__stringlit_2, %ecx
	movl	stderr, %edx
	movl	%ecx, 0(%esp)
	movl	%edx, 4(%esp)
	call	fputs
	movl	$1, %eax
	movl	%eax, 0(%esp)
	call	exit
.L121:
	movsd	48(%esp), %xmm7
	movsd	%xmm7, 56(%esp)
	movl	68(%esp), %ecx
.L122:
	movl	92(%esp), %edx
	cmpl	%edx, %ecx
	jl	.L123
	movl	104(%esp), %edx
	movsd	48(%esp), %xmm3
	movsd	%xmm3, 0(%edx,%ecx,8)
	movsd	76(%esp), %xmm0
	movsd	%xmm0, 0(%esi,%ecx,8)
	leal	-1(%ecx), %ecx
	jmp	.L122
.L123:
	xorl	%ecx, %ecx
	movl	108(%esp), %eax
	movl	%ecx, 0(%eax)
	movl	68(%esp), %ebx
.L124:
	movl	92(%esp), %edx
	cmpl	%edx, %ebx
	jl	.L125
	movsd	76(%esp), %xmm4
	movsd	%xmm4, 48(%esp)
	movl	%ebx, %eax
.L126:
	movl	92(%esp), %ecx
	cmpl	%ecx, %eax
	jl	.L127
	movsd	0(%esi,%eax,8), %xmm2
	movsd	48(%esp), %xmm5
	comisd	%xmm5, %xmm2
	jbe	.L128
	movsd	%xmm2, 48(%esp)
	jmp	.L127
.L128:
	leal	-1(%eax), %eax
	jmp	.L126
.L127:
	movl	104(%esp), %ecx
	movsd	0(%ecx,%ebx,8), %xmm7
	movsd	56(%esp), %xmm5
	comisd	%xmm7, %xmm5
	jbe	.L129
	movsd	%xmm7, 56(%esp)
.L129:
	movsd	48(%esp), %xmm5
	movsd	56(%esp), %xmm4
	addsd	%xmm4, %xmm5
	movsd	.L130, %xmm6 # 0.5
	mulsd	%xmm6, %xmm5
	movsd	%xmm5, 68(%esp)
.L131:
	movsd	48(%esp), %xmm2
	movsd	%xmm2, 0(%esp)
	call	fabs
	fstpl	96(%esp)
	movsd	56(%esp), %xmm2
	movsd	%xmm2, 0(%esp)
	call	fabs
	fstpl	116(%esp)
	movsd	116(%esp), %xmm2
	movsd	56(%esp), %xmm1
	movsd	48(%esp), %xmm4
	subsd	%xmm4, %xmm1
	movsd	.L132, %xmm3 # 4.44089209850062616e-16
	movsd	96(%esp), %xmm0
	addsd	%xmm2, %xmm0
	movapd	%xmm0, %xmm4
	mulsd	%xmm0, %xmm3
	movsd	84(%esp), %xmm0
	addsd	%xmm0, %xmm3
	comisd	%xmm3, %xmm1
	jbe	.L133
	movl	108(%esp), %eax
	movl	0(%eax), %edx
	leal	1(%edx), %ecx
	movl	%ecx, 0(%eax)
	movl	%ebp, 0(%esp)
	movl	64(%esp), %edx
	movl	%edx, 4(%esp)
	movl	%edi, 8(%esp)
	movl	112(%esp), %edx
	movl	%edx, 12(%esp)
	movsd	68(%esp), %xmm1
	movsd	%xmm1, 16(%esp)
	call	sturm
	cmpl	%ebx, %eax
	jge	.L134
	movl	92(%esp), %ecx
	cmpl	%ecx, %eax
	jl	.L135
	movsd	68(%esp), %xmm6
	movsd	%xmm6, 8(%esi,%eax,8)
	movsd	%xmm6, 48(%esp)
	movl	104(%esp), %ecx
	movsd	0(%ecx,%eax,8), %xmm2
	movsd	68(%esp), %xmm6
	comisd	%xmm6, %xmm2
	jbe	.L136
	movsd	%xmm6, 0(%ecx,%eax,8)
	jmp	.L136
.L135:
	movsd	68(%esp), %xmm7
	movsd	%xmm7, 0(%esi,%ecx,8)
	movsd	%xmm7, 48(%esp)
	jmp	.L136
.L134:
	movsd	68(%esp), %xmm1
	movsd	%xmm1, 56(%esp)
.L136:
	movsd	48(%esp), %xmm0
	movsd	56(%esp), %xmm7
	addsd	%xmm7, %xmm0
	movsd	.L137, %xmm1 # 0.5
	mulsd	%xmm1, %xmm0
	movsd	%xmm0, 68(%esp)
	jmp	.L131
.L133:
	movsd	48(%esp), %xmm6
	movsd	56(%esp), %xmm1
	addsd	%xmm1, %xmm6
	movsd	.L138, %xmm4 # 0.5
	mulsd	%xmm4, %xmm6
	movl	104(%esp), %ecx
	movsd	%xmm6, 0(%ecx,%ebx,8)
	leal	-1(%ebx), %ebx
	jmp	.L124
.L125:
	movl	%esi, 0(%esp)
	call	free
	movl	28(%esp), %ebx
	movl	32(%esp), %esi
	movl	36(%esp), %edi
	movl	40(%esp), %ebp
	addl	$132, %esp
	ret
	.cfi_endproc
	.type	dbisect, @function
	.size	dbisect, . - dbisect
	.section	.rodata.cst8,"aM",@progbits,8
	.align	8
.L138:	.quad	0x3fe0000000000000
.L137:	.quad	0x3fe0000000000000
.L132:	.quad	0x3cc0000000000000
.L130:	.quad	0x3fe0000000000000
.L120:	.quad	0x401c000000000000
.L119:	.quad	0x3fe0000000000000
.L117:	.quad	0x3cb0000000000000
.L112:	.quad	0x3ff028f5c28f5c29
.L109:	.quad	0x3ff028f5c28f5c29
.L108:	.quad	0x3ff028f5c28f5c29
	.text
	.align	16
	.globl test_matrix
test_matrix:
	.cfi_startproc
	subl	$20, %esp
	.cfi_adjust_cfa_offset	20
	leal	24(%esp), %edx
	movl	%edx, 0(%esp)
	movl	%ebx, 4(%esp)
	movl	%esi, 8(%esp)
	movl	%edi, 12(%esp)
	movl	0(%edx), %edi
	movl	4(%edx), %esi
	movl	8(%edx), %ebx
	xorl	%ecx, %ecx
.L139:
	cmpl	%edi, %ecx
	jge	.L140
	cvtsi2sd %ecx, %xmm3
	movsd	%xmm3, 0(%ebx,%ecx,8)
	leal	1(%ecx), %eax
	cvtsi2sd %eax, %xmm0
	movapd	%xmm0, %xmm1
	mulsd	%xmm0, %xmm1
	movsd	%xmm1, 0(%esi,%ecx,8)
	movapd	%xmm1, %xmm2
	mulsd	%xmm1, %xmm2
	movsd	%xmm2, 0(%esi,%ecx,8)
	movl	%eax, %ecx
	jmp	.L139
.L140:
	movl	4(%esp), %ebx
	movl	8(%esp), %esi
	movl	12(%esp), %edi
	addl	$20, %esp
	ret
	.cfi_endproc
	.type	test_matrix, @function
	.size	test_matrix, . - test_matrix
	.text
	.align	16
	.globl main
main:
	.cfi_startproc
	subl	$124, %esp
	.cfi_adjust_cfa_offset	124
	leal	128(%esp), %edx
	movl	%edx, 44(%esp)
	movl	%ebx, 48(%esp)
	movl	%esi, 52(%esp)
	movl	%edi, 56(%esp)
	movl	%ebp, 60(%esp)
	movl	$500, %ecx
	movl	%ecx, 64(%esp)
	movsd	.L141, %xmm0 # 2.22044604925031308e-16
	movsd	%xmm0, 68(%esp)
	leal	100(%esp), %eax
	movl	64(%esp), %edx
	movl	%edx, 0(%esp)
	movl	%eax, 4(%esp)
	call	dallocvector
	leal	104(%esp), %ecx
	movl	64(%esp), %eax
	movl	%eax, 0(%esp)
	movl	%ecx, 4(%esp)
	call	dallocvector
	leal	88(%esp), %edx
	movl	64(%esp), %eax
	movl	%eax, 0(%esp)
	movl	%edx, 4(%esp)
	call	dallocvector
	leal	92(%esp), %ecx
	movl	64(%esp), %edx
	movl	%edx, 0(%esp)
	movl	%ecx, 4(%esp)
	call	dallocvector
	xorl	%ebx, %ebx
.L142:
	movl	100(%esp), %eax
	movl	104(%esp), %ecx
	movl	64(%esp), %edx
	movl	%edx, 0(%esp)
	movl	%eax, 4(%esp)
	movl	%ecx, 8(%esp)
	call	test_matrix
	xorl	%edx, %edx
.L143:
	movl	88(%esp), %eax
	movl	104(%esp), %ecx
	movsd	0(%ecx,%edx,8), %xmm1
	movapd	%xmm1, %xmm2
	mulsd	%xmm2, %xmm1
	movsd	%xmm1, 0(%eax,%edx,8)
	movl	92(%esp), %eax
	xorpd	%xmm3, %xmm3
	movsd	%xmm3, 0(%eax,%edx,8)
	leal	1(%edx), %edx
	cmpl	$500, %edx
	jl	.L143
	movl	88(%esp), %edx
	movsd	%xmm3, 0(%edx)
	movl	104(%esp), %eax
	movsd	%xmm3, 0(%eax)
	movl	100(%esp), %edx
	movl	104(%esp), %eax
	movl	%eax, 80(%esp)
	movl	88(%esp), %eax
	movl	$1, %edi
	leal	112(%esp), %ecx
	leal	96(%esp), %esi
	movl	%esi, 76(%esp)
	movl	92(%esp), %esi
	leal	-8(%esi), %ebp
	movl	%edx, 0(%esp)
	movl	80(%esp), %esi
	movl	%esi, 4(%esp)
	movl	%eax, 8(%esp)
	movl	64(%esp), %esi
	movl	%esi, 12(%esp)
	movl	%edi, 16(%esp)
	movl	64(%esp), %esi
	movl	%esi, 20(%esp)
	movsd	68(%esp), %xmm5
	movsd	%xmm5, 24(%esp)
	movl	%ecx, 32(%esp)
	movl	76(%esp), %esi
	movl	%esi, 36(%esp)
	movl	%ebp, 40(%esp)
	call	dbisect
	leal	1(%ebx), %ebx
	cmpl	$50, %ebx
	jl	.L142
	movl	$1, %ebx
.L144:
	leal	__stringlit_3, %ecx
	leal	1(%ebx), %esi
	movl	92(%esp), %eax
	movsd	0(%eax,%ebx,8), %xmm2
	movl	%ecx, 0(%esp)
	movl	%esi, 4(%esp)
	movsd	%xmm2, 8(%esp)
	call	printf
	leal	1(%ebx), %ebx
	cmpl	$20, %ebx
	jl	.L144
	leal	__stringlit_4, %edx
	movsd	112(%esp), %xmm6
	movl	96(%esp), %ecx
	movl	%edx, 0(%esp)
	movsd	%xmm6, 4(%esp)
	movl	%ecx, 12(%esp)
	call	printf
	xorl	%eax, %eax
	movl	48(%esp), %ebx
	movl	52(%esp), %esi
	movl	56(%esp), %edi
	movl	60(%esp), %ebp
	addl	$124, %esp
	ret
	.cfi_endproc
	.type	main, @function
	.size	main, . - main
	.section	.rodata.cst8,"aM",@progbits,8
	.align	8
.L141:	.quad	0x3cb0000000000000
	.section	.rodata
	.align	16
__negd_mask:	.quad   0x8000000000000000, 0
__absd_mask:	.quad   0x7FFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF
__negs_mask:	.long   0x80000000, 0, 0, 0
__abss_mask:	.long   0x7FFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF