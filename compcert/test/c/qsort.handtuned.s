# File generated by CompCert 2.4
# Command line: -fno-peeps -stdlib ../../runtime -dc -dclight -dasm -S -o qsort.handtuned.s qsort.c
	.section	.rodata
	.align	1
__stringlit_2:
	.ascii	"OK\012\000"
	.type	__stringlit_2, @object
	.size	__stringlit_2, . - __stringlit_2
	.section	.rodata
	.align	1
__stringlit_1:
	.ascii	"Bug!\012\000"
	.type	__stringlit_1, @object
	.size	__stringlit_1, . - __stringlit_1
	.text
	.align	16
	.globl quicksort
quicksort:
	.cfi_startproc
	subl	$44, %esp
	.cfi_adjust_cfa_offset	44
	leal	48(%esp), %edx
	movl	%edx, 12(%esp)
	movl	%ebx, 16(%esp)
	movl	%esi, 20(%esp)
	movl	%edi, 24(%esp)
	movl	%ebp, 28(%esp)
	movl	0(%edx), %eax
	movl	%eax, 32(%esp)
	movl	4(%edx), %ebx
	movl	8(%edx), %esi
	movl	32(%esp), %ecx
	cmpl	%ebx, %ecx
	jge	.L100
	movl	32(%esp), %edi
	movl	%ebx, %ecx
	movl	0(%esi,%ebx,4), %ebp
.L101:
	cmpl	%ecx, %edi
	jge	.L102
.L103:
	cmpl	%ebx, %edi
	jge	.L104
	movl	0(%esi,%edi,4), %edx
	cmpl	%ebp, %edx
	jg	.L104
	leal	1(%edi), %edi
	jmp	.L103
.L104:
	movl	32(%esp), %eax
	cmpl	%eax, %ecx
	jle	.L105
	movl	0(%esi,%ecx,4), %eax
	cmpl	%ebp, %eax
	jl	.L105
	leal	-1(%ecx), %ecx
	jmp	.L104
.L105:
	cmpl	%ecx, %edi
	jge	.L101
	movl	0(%esi,%edi,4), %edx
	movl	0(%esi,%ecx,4), %eax
	movl	%eax, 0(%esi,%edi,4)
	movl	%edx, 0(%esi,%ecx,4)
	jmp	.L101
.L102:
	movl	0(%esi,%edi,4), %edx
	movl	0(%esi,%ebx,4), %eax
	movl	%eax, 0(%esi,%edi,4)
	movl	%edx, 0(%esi,%ebx,4)
	leal	-1(%edi), %edx
	movl	32(%esp), %ecx
	movl	%ecx, 0(%esp)
	movl	%edx, 4(%esp)
	movl	%esi, 8(%esp)
	call	quicksort
	leal	1(%edi), %edx
	movl	%edx, 0(%esp)
	movl	%ebx, 4(%esp)
	movl	%esi, 8(%esp)
	call	quicksort
.L100:
	movl	16(%esp), %ebx
	movl	20(%esp), %esi
	movl	24(%esp), %edi
	movl	28(%esp), %ebp
	addl	$44, %esp
	ret
	.cfi_endproc
	.type	quicksort, @function
	.size	quicksort, . - quicksort
	.text
	.align	16
	.globl cmpint
cmpint:
	.cfi_startproc
	subl	$12, %esp
	.cfi_adjust_cfa_offset	12
	leal	16(%esp), %edx
	movl	%edx, 0(%esp)
	movl	%ebx, 4(%esp)
	movl	0(%edx), %ecx
	movl	4(%edx), %ebx
	movl	0(%ecx), %edx
	movl	0(%ebx), %eax
	cmpl	%eax, %edx
	jne	.L106
	xorl	%eax, %eax
	jmp	.L107
.L106:
	cmpl	%eax, %edx
	jge	.L108
	movl	$-1, %eax
	jmp	.L107
.L108:
	movl	$1, %eax
.L107:
	movl	4(%esp), %ebx
	addl	$12, %esp
	ret
	.cfi_endproc
	.type	cmpint, @function
	.size	cmpint, . - cmpint
	.text
	.align	16
	.globl main
main:
	.cfi_startproc
	subl	$52, %esp
	.cfi_adjust_cfa_offset	52
	leal	56(%esp), %edx
	movl	%edx, 16(%esp)
	movl	%ebx, 20(%esp)
	movl	%esi, 24(%esp)
	movl	%edi, 28(%esp)
	movl	%ebp, 32(%esp)
	movl	0(%edx), %esi
	movl	4(%edx), %eax
	xorl	%ebp, %ebp
	cmpl	$2, %esi
	jl	.L109
	movl	4(%eax), %ecx
	movl	%ecx, 0(%esp)
	call	atoi
	movl	%eax, %ebx
	jmp	.L110
.L109:
	movl	$8000000, %ebx
.L110:
	cmpl	$3, %esi
	jl	.L111
	movl	$1, %ebp
.L111:
	leal	0(,%ebx,4), %edx
	movl	%edx, 0(%esp)
	call	malloc
	movl	%eax, %esi
	leal	0(,%ebx,4), %ecx
	movl	%ecx, 0(%esp)
	call	malloc
	movl	%eax, 40(%esp)
	xorl	%edi, %edi
.L112:
	cmpl	%ebx, %edi
	jge	.L113
	call	rand
	andl	$65535, %eax
	movl	%eax, 0(%esi,%edi,4)
	movl	40(%esp), %ecx
	movl	%eax, 0(%ecx,%edi,4)
	leal	1(%edi), %edi
	jmp	.L112
.L113:
	xorl	%eax, %eax
	leal	-1(%ebx), %edx
	movl	%eax, 0(%esp)
	movl	%edx, 4(%esp)
	movl	%esi, 8(%esp)
	call	quicksort
	testl	%ebp, %ebp
	jne	.L114
	movl	$4, %eax
	leal	cmpint, %ecx
	movl	40(%esp), %edx
	movl	%edx, 0(%esp)
	movl	%ebx, 4(%esp)
	movl	%eax, 8(%esp)
	movl	%ecx, 12(%esp)
	call	qsort
	xorl	%ecx, %ecx
.L115:
	cmpl	%ebx, %ecx
	jge	.L116
	movl	0(%esi,%ecx,4), %edi
	movl	40(%esp), %eax
	movl	0(%eax,%ecx,4), %edx
	cmpl	%edx, %edi
	je	.L117
	leal	__stringlit_1, %edx
	movl	%edx, 0(%esp)
	call	printf
	movl	$2, %eax
	jmp	.L118
.L117:
	leal	1(%ecx), %ecx
	jmp	.L115
.L116:
	leal	__stringlit_2, %edx
	movl	%edx, 0(%esp)
	call	printf
.L114:
	xorl	%eax, %eax
.L118:
	movl	20(%esp), %ebx
	movl	24(%esp), %esi
	movl	28(%esp), %edi
	movl	32(%esp), %ebp
	addl	$52, %esp
	ret
	.cfi_endproc
	.type	main, @function
	.size	main, . - main
