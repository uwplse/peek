# File generated by CompCert 2.4
# Command line: -stdlib ../../runtime -dc -dclight -dasm -o siphash24.compcert siphash24.c -lm
	.section	.rodata
	.align	1
__stringlit_1:
	.ascii	"test vector failed for %d bytes\012\000"
	.type	__stringlit_1, @object
	.size	__stringlit_1, . - __stringlit_1
	.section	.rodata
	.align	1
__stringlit_2:
	.ascii	"test vectors ok\012\000"
	.type	__stringlit_2, @object
	.size	__stringlit_2, . - __stringlit_2
	.text
	.align	16
	.globl crypto_auth
crypto_auth:
	.cfi_startproc
	subl	$92, %esp
	.cfi_adjust_cfa_offset	92
	leal	96(%esp), %edx
	movl	%edx, 0(%esp)
	movl	%ebx, 4(%esp)
	movl	%esi, 8(%esp)
	movl	%edi, 12(%esp)
	movl	%ebp, 16(%esp)
	movl	0(%edx), %eax
	movl	%eax, 80(%esp)
	movl	4(%edx), %eax
	movl	%eax, 60(%esp)
	movl	8(%edx), %eax
	movl	%eax, 28(%esp)
	movl	16(%edx), %edi
	movzbl	1(%edi), %ebx
	movl	%ebx, %eax
	shrl	$24, %eax
	movzbl	2(%edi), %ecx
	movl	%ecx, %edx
	shrl	$16, %edx
	orl	%edx, %eax
	movzbl	3(%edi), %esi
	movl	%esi, %edx
	shrl	$8, %edx
	orl	%edx, %eax
	movzbl	4(%edi), %edx
	orl	%edx, %eax
	movzbl	5(%edi), %edx
	sall	$8, %edx
	orl	%edx, %eax
	movzbl	6(%edi), %edx
	sall	$16, %edx
	orl	%edx, %eax
	movzbl	7(%edi), %edx
	sall	$24, %edx
	orl	%edx, %eax
	movzbl	0(%edi), %edx
	sall	$8, %ebx
	orl	%ebx, %edx
	sall	$16, %ecx
	orl	%ecx, %edx
	sall	$24, %esi
	movl	%edx, %ecx
	orl	%esi, %ecx
	movl	%ecx, 24(%esp)
	movzbl	9(%edi), %edx
	movl	%edx, %ebp
	shrl	$24, %ebp
	movzbl	10(%edi), %esi
	movl	%esi, %ecx
	shrl	$16, %ecx
	orl	%ecx, %ebp
	movzbl	11(%edi), %ebx
	movl	%ebx, %ecx
	shrl	$8, %ecx
	orl	%ecx, %ebp
	movzbl	12(%edi), %ecx
	orl	%ecx, %ebp
	movzbl	13(%edi), %ecx
	sall	$8, %ecx
	orl	%ecx, %ebp
	movzbl	14(%edi), %ecx
	sall	$16, %ecx
	orl	%ecx, %ebp
	movzbl	15(%edi), %ecx
	sall	$24, %ecx
	orl	%ecx, %ebp
	movzbl	8(%edi), %ecx
	sall	$8, %edx
	orl	%edx, %ecx
	sall	$16, %esi
	orl	%esi, %ecx
	sall	$24, %ebx
	movl	%ecx, %edx
	orl	%ebx, %edx
	movl	%ebp, %ecx
	movl	28(%esp), %ebx
	movl	60(%esp), %esi
	leal	0(%esi,%ebx,1), %edi
	movl	%ebx, %esi
	movl	%esi, %ebx
	andl	$7, %ebx
	subl	%ebx, %edi
	movl	%edi, 76(%esp)
	movl	%ebx, 64(%esp)
	movl	%esi, %ebx
	sall	$24, %ebx
	movl	%ebx, 52(%esp)
	movl	$0, 56(%esp)
	movl	%edx, %ebx
	movl	%ecx, %edx
	xorl	$1952801890, %edx
	movl	%edx, 28(%esp)
	movl	%ebx, %edx
	xorl	$2037671283, %edx
	movl	%edx, 40(%esp)
	movl	24(%esp), %edx
	movl	%eax, %edi
	xorl	$1819895653, %edi
	movl	%edx, %esi
	xorl	$1852142177, %esi
	movl	%edi, 48(%esp)
	movl	%esi, 44(%esp)
	xorl	$1685025377, %ecx
	xorl	$1852075885, %ebx
	movl	%ebx, 32(%esp)
	xorl	$1936682341, %eax
	movl	%eax, %ebx
	movl	%edx, %eax
	xorl	$1886610805, %eax
	movl	%ebx, %edx
	movl	%edx, 36(%esp)
.L100:
	movl	60(%esp), %ebx
	movl	76(%esp), %edx
	cmpl	%edx, %ebx
	je	.L101
	movzbl	1(%ebx), %edx
	movl	%edx, 24(%esp)
	movl	24(%esp), %edx
	shrl	$24, %edx
	movl	60(%esp), %ebx
	movzbl	2(%ebx), %edi
	movl	%edi, %ebx
	shrl	$16, %ebx
	orl	%ebx, %edx
	movl	60(%esp), %ebx
	movzbl	3(%ebx), %ebp
	movl	%ebp, %ebx
	shrl	$8, %ebx
	orl	%ebx, %edx
	movl	60(%esp), %ebx
	movzbl	4(%ebx), %esi
	orl	%esi, %edx
	movzbl	5(%ebx), %ebx
	sall	$8, %ebx
	orl	%ebx, %edx
	movl	60(%esp), %ebx
	movzbl	6(%ebx), %ebx
	sall	$16, %ebx
	orl	%ebx, %edx
	movl	60(%esp), %ebx
	movzbl	7(%ebx), %ebx
	sall	$24, %ebx
	orl	%ebx, %edx
	movl	60(%esp), %ebx
	movzbl	0(%ebx), %ebx
	movl	24(%esp), %esi
	sall	$8, %esi
	orl	%esi, %ebx
	sall	$16, %edi
	orl	%edi, %ebx
	sall	$24, %ebp
	orl	%ebp, %ebx
	movl	28(%esp), %edi
	movl	40(%esp), %esi
	movl	%edx, 68(%esp)
	movl	68(%esp), %edx
	xorl	%edx, %edi
	movl	%ebx, 72(%esp)
	movl	72(%esp), %edx
	xorl	%edx, %esi
	movl	%edi, 28(%esp)
	movl	%esi, %edi
	movl	36(%esp), %edx
	movl	32(%esp), %ebx
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	32(%esp), %esi
	movl	%ecx, %ebx
	shldl	$13, %esi, %ebx
	shldl	$13, %ecx, %esi
	movl	%esi, %ecx
	xorl	%edx, %ebx
	xorl	%eax, %ecx
	movl	%ebx, %ebp
	movl	%ecx, %esi
	movl	%edx, 24(%esp)
	movl	%eax, 32(%esp)
	movl	48(%esp), %edx
	movl	44(%esp), %eax
	movl	28(%esp), %ecx
	movl	%edi, %ebx
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%edx, 36(%esp)
	movl	%eax, 40(%esp)
	movl	28(%esp), %eax
	movl	%eax, %ecx
	shldl	$16, %edi, %ecx
	shldl	$16, %eax, %edi
	movl	%edi, %ebx
	movl	36(%esp), %edx
	xorl	%edx, %ecx
	movl	40(%esp), %edx
	xorl	%edx, %ebx
	movl	32(%esp), %edx
	movl	24(%esp), %eax
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%edx, %edi
	movl	%eax, 24(%esp)
	movl	%ecx, %edx
	shldl	$21, %ebx, %edx
	shldl	$21, %ecx, %ebx
	movl	%edi, %eax
	xorl	%eax, %edx
	movl	24(%esp), %eax
	xorl	%eax, %ebx
	movl	%edx, 44(%esp)
	movl	%ebx, 48(%esp)
	movl	36(%esp), %edx
	movl	40(%esp), %eax
	movl	%ebp, %ecx
	movl	%esi, %ebx
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%ebp, %ecx
	shldl	$17, %esi, %ecx
	shldl	$17, %ebp, %esi
	movl	%esi, %ebx
	movl	%eax, %ebp
	movl	%ecx, %eax
	movl	%edx, %ecx
	xorl	%ecx, %eax
	xorl	%ebp, %ebx
	movl	%eax, %ecx
	movl	%edx, %eax
	movl	%eax, 32(%esp)
	movl	%edi, %edx
	movl	24(%esp), %eax
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%ebx, %esi
	movl	%ecx, %ebx
	shldl	$13, %esi, %ebx
	shldl	$13, %ecx, %esi
	movl	%ebx, %ecx
	movl	%ecx, %edi
	xorl	%edx, %edi
	xorl	%eax, %esi
	movl	%edx, 24(%esp)
	movl	%eax, 28(%esp)
	movl	%ebp, %edx
	movl	32(%esp), %eax
	movl	44(%esp), %ecx
	movl	48(%esp), %ebx
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%edx, 32(%esp)
	movl	%eax, 36(%esp)
	movl	44(%esp), %edx
	movl	48(%esp), %ebx
	movl	%edx, %ecx
	shldl	$16, %ebx, %ecx
	shldl	$16, %edx, %ebx
	movl	32(%esp), %edx
	xorl	%edx, %ecx
	movl	36(%esp), %eax
	xorl	%eax, %ebx
	movl	28(%esp), %edx
	movl	24(%esp), %eax
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%ecx, %ebp
	movl	%ebx, %ecx
	movl	%ebp, %ebx
	shldl	$21, %ecx, %ebx
	shldl	$21, %ebp, %ecx
	movl	%edx, %ebp
	movl	%ebx, %edx
	xorl	%ebp, %edx
	movl	%eax, 24(%esp)
	movl	24(%esp), %eax
	xorl	%eax, %ecx
	movl	%edx, 28(%esp)
	movl	%ecx, 40(%esp)
	movl	32(%esp), %edx
	movl	36(%esp), %eax
	movl	%edi, %ecx
	movl	%esi, %ebx
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%edi, %ecx
	shldl	$17, %esi, %ecx
	shldl	$17, %edi, %esi
	xorl	%edx, %ecx
	movl	%esi, %ebx
	xorl	%eax, %ebx
	movl	%ebx, 32(%esp)
	movl	%eax, 48(%esp)
	movl	%edx, 44(%esp)
	movl	%ebp, %edx
	movl	68(%esp), %eax
	xorl	%eax, %edx
	movl	24(%esp), %eax
	movl	72(%esp), %ebx
	xorl	%ebx, %eax
	movl	%edx, 36(%esp)
	movl	60(%esp), %edx
	leal	8(%edx), %edx
	movl	%edx, 60(%esp)
	jmp	.L100
.L101:
	movl	64(%esp), %edx
	cmpl	$8, %edx
	jae	.L102
	jmp	*.L103(, %edx, 4)
.L104:
	movl	52(%esp), %ebx
	movl	56(%esp), %esi
	movl	60(%esp), %edx
	movzbl	6(%edx), %edx
	sall	$16, %edx
	orl	%edx, %ebx
	movl	%ebx, 52(%esp)
	movl	%esi, 56(%esp)
.L105:
	movl	52(%esp), %ebx
	movl	56(%esp), %esi
	movl	60(%esp), %edx
	movzbl	5(%edx), %edx
	sall	$8, %edx
	orl	%edx, %ebx
	movl	%ebx, 52(%esp)
	movl	%esi, 56(%esp)
.L106:
	movl	52(%esp), %ebx
	movl	56(%esp), %esi
	movl	60(%esp), %edx
	movzbl	4(%edx), %edx
	orl	%edx, %ebx
	movl	%ebx, 52(%esp)
	movl	%esi, 56(%esp)
.L107:
	movl	52(%esp), %esi
	movl	56(%esp), %ebx
	movl	60(%esp), %edx
	movzbl	3(%edx), %edx
	movl	%edx, %edi
	shrl	$8, %edi
	orl	%edi, %esi
	sall	$24, %edx
	orl	%edx, %ebx
	movl	%esi, 52(%esp)
	movl	%ebx, 56(%esp)
.L108:
	movl	52(%esp), %ebx
	movl	56(%esp), %edx
	movl	60(%esp), %esi
	movzbl	2(%esi), %esi
	movl	%esi, %edi
	shrl	$16, %edi
	orl	%edi, %ebx
	sall	$16, %esi
	orl	%esi, %edx
	movl	%ebx, 52(%esp)
	movl	%edx, 56(%esp)
.L109:
	movl	52(%esp), %esi
	movl	56(%esp), %ebx
	movl	60(%esp), %edx
	movzbl	1(%edx), %edx
	movl	%edx, %edi
	shrl	$24, %edi
	orl	%edi, %esi
	sall	$8, %edx
	orl	%edx, %ebx
	movl	%esi, 52(%esp)
	movl	%ebx, 56(%esp)
.L110:
	movl	52(%esp), %edx
	movl	56(%esp), %esi
	movl	60(%esp), %ebx
	movzbl	0(%ebx), %ebx
	orl	%ebx, %esi
	movl	%edx, 52(%esp)
	movl	%esi, 56(%esp)
.L102:
	movl	28(%esp), %esi
	movl	40(%esp), %edi
	movl	52(%esp), %edx
	movl	56(%esp), %ebx
	movl	%edx, 56(%esp)
	movl	56(%esp), %edx
	xorl	%edx, %esi
	movl	%ebx, 52(%esp)
	movl	52(%esp), %edx
	xorl	%edx, %edi
	movl	36(%esp), %edx
	movl	32(%esp), %ebx
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	32(%esp), %ebx
	movl	%ecx, %ebp
	movl	%ebx, %ecx
	movl	%ebp, %ebx
	shldl	$13, %ecx, %ebx
	shldl	$13, %ebp, %ecx
	movl	%edx, %ebp
	movl	%ebx, %edx
	xorl	%ebp, %edx
	movl	%ecx, %ebx
	movl	%eax, %ecx
	movl	%ebx, %eax
	xorl	%ecx, %eax
	movl	%edx, 24(%esp)
	movl	%eax, 40(%esp)
	movl	%ecx, 32(%esp)
	movl	48(%esp), %edx
	movl	44(%esp), %eax
	movl	%esi, %ecx
	movl	%edi, %ebx
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%edx, 36(%esp)
	movl	%eax, 28(%esp)
	movl	%esi, %ecx
	shldl	$16, %edi, %ecx
	shldl	$16, %esi, %edi
	movl	36(%esp), %eax
	xorl	%eax, %ecx
	movl	28(%esp), %edx
	xorl	%edx, %edi
	movl	%edi, %ebx
	movl	32(%esp), %edx
	movl	%ebp, %eax
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%edx, %esi
	movl	%eax, %ebp
	movl	%ecx, %edx
	shldl	$21, %ebx, %edx
	shldl	$21, %ecx, %ebx
	movl	%esi, %eax
	xorl	%eax, %edx
	movl	%ebp, %ecx
	xorl	%ecx, %ebx
	movl	%edx, 44(%esp)
	movl	%ebx, 48(%esp)
	movl	36(%esp), %edx
	movl	28(%esp), %eax
	movl	24(%esp), %ecx
	movl	40(%esp), %ebx
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	40(%esp), %ecx
	movl	24(%esp), %edi
	movl	%edi, %ebx
	shldl	$17, %ecx, %ebx
	shldl	$17, %edi, %ecx
	movl	%edx, %edi
	movl	%ebx, %edx
	xorl	%edi, %edx
	movl	%ecx, %ebx
	xorl	%eax, %ebx
	movl	%edx, %ecx
	movl	%eax, 24(%esp)
	movl	%esi, %edx
	movl	%ebp, %eax
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%ebx, %esi
	movl	%ecx, %ebx
	shldl	$13, %esi, %ebx
	shldl	$13, %ecx, %esi
	movl	%esi, %ecx
	xorl	%edx, %ebx
	xorl	%eax, %ecx
	movl	%ebx, %ebp
	movl	%ecx, 36(%esp)
	movl	%edx, %esi
	movl	%eax, 28(%esp)
	movl	24(%esp), %edx
	movl	%edi, %eax
	movl	44(%esp), %ecx
	movl	48(%esp), %ebx
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%edx, 32(%esp)
	movl	%eax, 24(%esp)
	movl	44(%esp), %eax
	movl	48(%esp), %ebx
	movl	%eax, %ecx
	shldl	$16, %ebx, %ecx
	shldl	$16, %eax, %ebx
	movl	32(%esp), %edx
	xorl	%edx, %ecx
	movl	24(%esp), %edx
	xorl	%edx, %ebx
	movl	28(%esp), %edx
	movl	%esi, %eax
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%ecx, %esi
	movl	%esi, %ecx
	shldl	$21, %ebx, %ecx
	shldl	$21, %esi, %ebx
	movl	%eax, %esi
	movl	%edx, %edi
	xorl	%edi, %ecx
	xorl	%esi, %ebx
	movl	%ecx, 40(%esp)
	movl	%ebx, 44(%esp)
	movl	32(%esp), %edx
	movl	24(%esp), %eax
	movl	%ebp, %ecx
	movl	36(%esp), %ebx
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	36(%esp), %ecx
	movl	%ecx, %ebx
	movl	%ebp, %ecx
	shldl	$17, %ebx, %ecx
	shldl	$17, %ebp, %ebx
	movl	%eax, %ebp
	movl	%edx, %eax
	xorl	%eax, %ecx
	movl	%ebx, %edx
	xorl	%ebp, %edx
	movl	%edx, %ebx
	movl	%eax, %edx
	movl	56(%esp), %eax
	xorl	%eax, %edi
	movl	%esi, %eax
	movl	52(%esp), %esi
	xorl	%esi, %eax
	movl	%edi, %esi
	movl	%edx, %edi
	xorl	$255, %edi
	movl	%ebp, 28(%esp)
	movl	%esi, %edx
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%ecx, %esi
	movl	%ebx, %ecx
	movl	%esi, %ebx
	shldl	$13, %ecx, %ebx
	shldl	$13, %esi, %ecx
	movl	%edx, %ebp
	xorl	%ebp, %ebx
	movl	%eax, %edx
	movl	%ecx, %eax
	xorl	%edx, %eax
	movl	%ebx, %esi
	movl	%eax, 32(%esp)
	movl	%edx, 24(%esp)
	movl	28(%esp), %edx
	movl	%edi, %eax
	movl	40(%esp), %ecx
	movl	44(%esp), %ebx
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%edx, 28(%esp)
	movl	%eax, %edi
	movl	40(%esp), %edx
	movl	44(%esp), %ebx
	movl	%edx, %ecx
	shldl	$16, %ebx, %ecx
	shldl	$16, %edx, %ebx
	movl	28(%esp), %eax
	xorl	%eax, %ecx
	movl	%edi, %edx
	xorl	%edx, %ebx
	movl	24(%esp), %edx
	movl	%ebp, %eax
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%edx, %ebp
	movl	%eax, 24(%esp)
	movl	%ecx, %edx
	shldl	$21, %ebx, %edx
	shldl	$21, %ecx, %ebx
	movl	%ebp, %eax
	xorl	%eax, %edx
	movl	24(%esp), %eax
	xorl	%eax, %ebx
	movl	%edx, 40(%esp)
	movl	%ebx, 36(%esp)
	movl	28(%esp), %edx
	movl	%edi, %eax
	movl	%esi, %ecx
	movl	32(%esp), %ebx
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	32(%esp), %ecx
	movl	%esi, %ebx
	shldl	$17, %ecx, %ebx
	shldl	$17, %esi, %ecx
	movl	%edx, %edi
	movl	%ebx, %edx
	xorl	%edi, %edx
	movl	%ecx, %ebx
	xorl	%eax, %ebx
	movl	%edx, %ecx
	movl	%eax, 28(%esp)
	movl	%ebp, %edx
	movl	24(%esp), %eax
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%ebx, %esi
	movl	%ecx, %ebx
	shldl	$13, %esi, %ebx
	shldl	$13, %ecx, %esi
	movl	%esi, %ecx
	xorl	%edx, %ebx
	xorl	%eax, %ecx
	movl	%ebx, %esi
	movl	%ecx, 32(%esp)
	movl	%edx, %ebp
	movl	%eax, 24(%esp)
	movl	28(%esp), %edx
	movl	%edi, %eax
	movl	40(%esp), %ecx
	movl	36(%esp), %ebx
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%edx, %edi
	movl	%eax, 28(%esp)
	movl	40(%esp), %edx
	movl	36(%esp), %ebx
	movl	%edx, %ecx
	shldl	$16, %ebx, %ecx
	shldl	$16, %edx, %ebx
	movl	%edi, %edx
	xorl	%edx, %ecx
	movl	28(%esp), %edx
	xorl	%edx, %ebx
	movl	24(%esp), %edx
	movl	%ebp, %eax
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%edx, 24(%esp)
	movl	%eax, %ebp
	movl	%ecx, %eax
	shldl	$21, %ebx, %eax
	shldl	$21, %ecx, %ebx
	movl	24(%esp), %ecx
	xorl	%ecx, %eax
	movl	%ebp, %edx
	xorl	%edx, %ebx
	movl	%eax, 36(%esp)
	movl	%ebx, 40(%esp)
	movl	%edi, %edx
	movl	28(%esp), %eax
	movl	%esi, %ecx
	movl	32(%esp), %ebx
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	32(%esp), %ecx
	movl	%ecx, %ebx
	movl	%esi, %ecx
	shldl	$17, %ebx, %ecx
	shldl	$17, %esi, %ebx
	xorl	%edx, %ecx
	xorl	%eax, %ebx
	movl	%edx, %esi
	movl	%eax, 28(%esp)
	movl	24(%esp), %edx
	movl	%ebp, %eax
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%ecx, %edi
	shldl	$13, %ebx, %edi
	shldl	$13, %ecx, %ebx
	movl	%edi, %ecx
	xorl	%edx, %ecx
	xorl	%eax, %ebx
	movl	%ecx, %edi
	movl	%ebx, 32(%esp)
	movl	%edx, %ebp
	movl	%eax, 24(%esp)
	movl	28(%esp), %edx
	movl	%esi, %eax
	movl	36(%esp), %ecx
	movl	40(%esp), %ebx
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%edx, 28(%esp)
	movl	%eax, %esi
	movl	36(%esp), %edx
	movl	40(%esp), %ebx
	movl	%edx, %ecx
	shldl	$16, %ebx, %ecx
	shldl	$16, %edx, %ebx
	movl	28(%esp), %eax
	xorl	%eax, %ecx
	movl	%esi, %edx
	xorl	%edx, %ebx
	movl	24(%esp), %edx
	movl	%ebp, %eax
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%edx, %ebp
	movl	%eax, 24(%esp)
	movl	%ecx, %eax
	shldl	$21, %ebx, %eax
	shldl	$21, %ecx, %ebx
	movl	%ebp, %edx
	xorl	%edx, %eax
	movl	24(%esp), %ecx
	xorl	%ecx, %ebx
	movl	%eax, 44(%esp)
	movl	%ebx, 48(%esp)
	movl	28(%esp), %edx
	movl	%esi, %eax
	movl	%edi, %ecx
	movl	32(%esp), %ebx
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	32(%esp), %ecx
	movl	%edi, %ebx
	shldl	$17, %ecx, %ebx
	shldl	$17, %edi, %ecx
	movl	%edx, %esi
	movl	%ebx, %edx
	xorl	%esi, %edx
	movl	%ecx, %ebx
	xorl	%eax, %ebx
	movl	%edx, %ecx
	movl	%eax, 28(%esp)
	movl	%ebp, %edx
	movl	24(%esp), %eax
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%ecx, %edi
	shldl	$13, %ebx, %edi
	shldl	$13, %ecx, %ebx
	movl	%edi, %ecx
	movl	%ecx, %edi
	movl	%edx, %ecx
	xorl	%ecx, %edi
	movl	%eax, %edx
	movl	%ebx, %eax
	xorl	%edx, %eax
	movl	%edi, 36(%esp)
	movl	%eax, 40(%esp)
	movl	%ecx, %edi
	movl	%edx, 32(%esp)
	movl	28(%esp), %edx
	movl	%esi, %eax
	movl	44(%esp), %ecx
	movl	48(%esp), %ebx
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%edx, 24(%esp)
	movl	%eax, %ebp
	movl	44(%esp), %eax
	movl	48(%esp), %ebx
	movl	%eax, %ecx
	shldl	$16, %ebx, %ecx
	shldl	$16, %eax, %ebx
	movl	24(%esp), %edx
	xorl	%edx, %ecx
	movl	%ebp, %edx
	xorl	%edx, %ebx
	movl	32(%esp), %edx
	movl	%edi, %eax
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	%ecx, %esi
	movl	%esi, %ecx
	shldl	$21, %ebx, %ecx
	shldl	$21, %esi, %ebx
	movl	%ebx, %esi
	movl	%edx, %ebx
	movl	%eax, %edx
	movl	%ebx, %edi
	movl	%ecx, %eax
	xorl	%edi, %eax
	movl	%eax, 28(%esp)
	movl	%edx, 32(%esp)
	movl	32(%esp), %eax
	xorl	%eax, %esi
	movl	24(%esp), %edx
	movl	%ebp, %eax
	movl	36(%esp), %ecx
	movl	40(%esp), %ebx
# begin builtin __builtin_addl
	addl	%ebx, %eax
	adcl	%ecx, %edx
# end builtin __builtin_addl
	movl	36(%esp), %ecx
	movl	40(%esp), %ebx
	movl	%ecx, %ebp
	shldl	$17, %ebx, %ebp
	shldl	$17, %ecx, %ebx
	xorl	%edx, %ebp
	xorl	%eax, %ebx
	xorl	%ebp, %edi
	movl	32(%esp), %ecx
	xorl	%ebx, %ecx
	xorl	%eax, %edi
	movl	%ecx, %eax
	xorl	%edx, %eax
	movl	28(%esp), %ecx
	xorl	%ecx, %edi
	xorl	%esi, %eax
	movl	%edi, %ebx
	movl	%eax, %esi
	movl	%esi, %edx
	movl	80(%esp), %eax
	movb	%dl, 0(%eax)
	movl	%esi, %eax
	shrl	$8, %eax
	movl	80(%esp), %edx
	movb	%al, 1(%edx)
	movl	%esi, %edx
	shrl	$16, %edx
	movl	80(%esp), %eax
	movb	%dl, 2(%eax)
	shrl	$24, %esi
	movl	80(%esp), %ecx
	movl	%esi, %eax
	movb	%al, 3(%ecx)
	movl	%ebx, %edx
	movl	80(%esp), %ecx
	movb	%dl, 4(%ecx)
	movl	%ebx, %eax
	shrl	$8, %eax
	movl	80(%esp), %ecx
	movb	%al, 5(%ecx)
	movl	%ebx, %ecx
	shrl	$16, %ecx
	movl	80(%esp), %edx
	movb	%cl, 6(%edx)
	shrl	$24, %ebx
	movl	80(%esp), %edx
	movb	%bl, 7(%edx)
	xorl	%eax, %eax
	movl	4(%esp), %ebx
	movl	8(%esp), %esi
	movl	12(%esp), %edi
	movl	16(%esp), %ebp
	addl	$92, %esp
	ret
	.cfi_endproc
	.type	crypto_auth, @function
	.size	crypto_auth, . - crypto_auth
	.text
	.align	4
.L103:	.long	.L102
	.long	.L110
	.long	.L109
	.long	.L108
	.long	.L107
	.long	.L106
	.long	.L105
	.long	.L104
	.data
	.align	1
	.global	vectors
vectors:
	.byte	49
	.byte	14
	.byte	14
	.byte	221
	.byte	71
	.byte	219
	.byte	111
	.byte	114
	.byte	253
	.byte	103
	.byte	220
	.byte	147
	.byte	197
	.byte	57
	.byte	248
	.byte	116
	.byte	90
	.byte	79
	.byte	169
	.byte	217
	.byte	9
	.byte	128
	.byte	108
	.byte	13
	.byte	45
	.byte	126
	.byte	251
	.byte	215
	.byte	150
	.byte	102
	.byte	103
	.byte	133
	.byte	183
	.byte	135
	.byte	113
	.byte	39
	.byte	224
	.byte	148
	.byte	39
	.byte	207
	.byte	141
	.byte	166
	.byte	153
	.byte	205
	.byte	100
	.byte	85
	.byte	118
	.byte	24
	.byte	206
	.byte	227
	.byte	254
	.byte	88
	.byte	110
	.byte	70
	.byte	201
	.byte	203
	.byte	55
	.byte	209
	.byte	1
	.byte	139
	.byte	245
	.byte	0
	.byte	2
	.byte	171
	.byte	98
	.byte	36
	.byte	147
	.byte	154
	.byte	121
	.byte	245
	.byte	245
	.byte	147
	.byte	176
	.byte	228
	.byte	169
	.byte	11
	.byte	223
	.byte	130
	.byte	0
	.byte	158
	.byte	243
	.byte	185
	.byte	221
	.byte	148
	.byte	197
	.byte	187
	.byte	93
	.byte	122
	.byte	167
	.byte	173
	.byte	107
	.byte	34
	.byte	70
	.byte	47
	.byte	179
	.byte	244
	.byte	251
	.byte	229
	.byte	14
	.byte	134
	.byte	188
	.byte	143
	.byte	30
	.byte	117
	.byte	144
	.byte	61
	.byte	132
	.byte	192
	.byte	39
	.byte	86
	.byte	234
	.byte	20
	.byte	238
	.byte	242
	.byte	122
	.byte	142
	.byte	144
	.byte	202
	.byte	35
	.byte	247
	.byte	229
	.byte	69
	.byte	190
	.byte	73
	.byte	97
	.byte	202
	.byte	41
	.byte	161
	.byte	219
	.byte	155
	.byte	194
	.byte	87
	.byte	127
	.byte	204
	.byte	42
	.byte	63
	.byte	148
	.byte	71
	.byte	190
	.byte	44
	.byte	245
	.byte	233
	.byte	154
	.byte	105
	.byte	156
	.byte	211
	.byte	141
	.byte	150
	.byte	240
	.byte	179
	.byte	193
	.byte	75
	.byte	189
	.byte	97
	.byte	121
	.byte	167
	.byte	29
	.byte	201
	.byte	109
	.byte	187
	.byte	152
	.byte	238
	.byte	162
	.byte	26
	.byte	242
	.byte	92
	.byte	214
	.byte	190
	.byte	199
	.byte	103
	.byte	59
	.byte	46
	.byte	176
	.byte	203
	.byte	242
	.byte	208
	.byte	136
	.byte	62
	.byte	163
	.byte	227
	.byte	149
	.byte	103
	.byte	83
	.byte	147
	.byte	200
	.byte	206
	.byte	92
	.byte	205
	.byte	140
	.byte	3
	.byte	12
	.byte	168
	.byte	148
	.byte	175
	.byte	73
	.byte	246
	.byte	198
	.byte	80
	.byte	173
	.byte	184
	.byte	234
	.byte	184
	.byte	133
	.byte	138
	.byte	222
	.byte	146
	.byte	225
	.byte	188
	.byte	243
	.byte	21
	.byte	187
	.byte	91
	.byte	184
	.byte	53
	.byte	216
	.byte	23
	.byte	173
	.byte	207
	.byte	107
	.byte	7
	.byte	99
	.byte	97
	.byte	46
	.byte	47
	.byte	165
	.byte	201
	.byte	29
	.byte	167
	.byte	172
	.byte	170
	.byte	77
	.byte	222
	.byte	113
	.byte	101
	.byte	149
	.byte	135
	.byte	102
	.byte	80
	.byte	162
	.byte	166
	.byte	40
	.byte	239
	.byte	73
	.byte	92
	.byte	83
	.byte	163
	.byte	135
	.byte	173
	.byte	66
	.byte	195
	.byte	65
	.byte	216
	.byte	250
	.byte	146
	.byte	216
	.byte	50
	.byte	206
	.byte	124
	.byte	242
	.byte	114
	.byte	47
	.byte	81
	.byte	39
	.byte	113
	.byte	227
	.byte	120
	.byte	89
	.byte	249
	.byte	70
	.byte	35
	.byte	243
	.byte	167
	.byte	56
	.byte	18
	.byte	5
	.byte	187
	.byte	26
	.byte	176
	.byte	224
	.byte	18
	.byte	174
	.byte	151
	.byte	161
	.byte	15
	.byte	212
	.byte	52
	.byte	224
	.byte	21
	.byte	180
	.byte	163
	.byte	21
	.byte	8
	.byte	190
	.byte	255
	.byte	77
	.byte	49
	.byte	129
	.byte	57
	.byte	98
	.byte	41
	.byte	240
	.byte	144
	.byte	121
	.byte	2
	.byte	77
	.byte	12
	.byte	244
	.byte	158
	.byte	229
	.byte	212
	.byte	220
	.byte	202
	.byte	92
	.byte	115
	.byte	51
	.byte	106
	.byte	118
	.byte	216
	.byte	191
	.byte	154
	.byte	208
	.byte	167
	.byte	4
	.byte	83
	.byte	107
	.byte	169
	.byte	62
	.byte	14
	.byte	146
	.byte	89
	.byte	88
	.byte	252
	.byte	214
	.byte	66
	.byte	12
	.byte	173
	.byte	169
	.byte	21
	.byte	194
	.byte	155
	.byte	200
	.byte	6
	.byte	115
	.byte	24
	.byte	149
	.byte	43
	.byte	121
	.byte	243
	.byte	188
	.byte	10
	.byte	166
	.byte	212
	.byte	242
	.byte	29
	.byte	242
	.byte	228
	.byte	29
	.byte	69
	.byte	53
	.byte	249
	.byte	135
	.byte	87
	.byte	117
	.byte	25
	.byte	4
	.byte	143
	.byte	83
	.byte	169
	.byte	16
	.byte	165
	.byte	108
	.byte	245
	.byte	223
	.byte	205
	.byte	154
	.byte	219
	.byte	235
	.byte	117
	.byte	9
	.byte	92
	.byte	205
	.byte	152
	.byte	108
	.byte	208
	.byte	81
	.byte	169
	.byte	203
	.byte	158
	.byte	203
	.byte	163
	.byte	18
	.byte	230
	.byte	150
	.byte	175
	.byte	173
	.byte	252
	.byte	44
	.byte	230
	.byte	102
	.byte	199
	.byte	114
	.byte	254
	.byte	82
	.byte	151
	.byte	90
	.byte	67
	.byte	100
	.byte	238
	.byte	90
	.byte	22
	.byte	69
	.byte	178
	.byte	118
	.byte	213
	.byte	146
	.byte	161
	.byte	178
	.byte	116
	.byte	203
	.byte	142
	.byte	191
	.byte	135
	.byte	135
	.byte	10
	.byte	111
	.byte	155
	.byte	180
	.byte	32
	.byte	61
	.byte	231
	.byte	179
	.byte	129
	.byte	234
	.byte	236
	.byte	178
	.byte	163
	.byte	11
	.byte	34
	.byte	168
	.byte	127
	.byte	153
	.byte	36
	.byte	164
	.byte	60
	.byte	193
	.byte	49
	.byte	87
	.byte	36
	.byte	189
	.byte	131
	.byte	141
	.byte	58
	.byte	175
	.byte	191
	.byte	141
	.byte	183
	.byte	11
	.byte	26
	.byte	42
	.byte	50
	.byte	101
	.byte	213
	.byte	26
	.byte	234
	.byte	19
	.byte	80
	.byte	121
	.byte	163
	.byte	35
	.byte	28
	.byte	230
	.byte	96
	.byte	147
	.byte	43
	.byte	40
	.byte	70
	.byte	228
	.byte	215
	.byte	6
	.byte	102
	.byte	225
	.byte	145
	.byte	95
	.byte	92
	.byte	177
	.byte	236
	.byte	164
	.byte	108
	.byte	243
	.byte	37
	.byte	150
	.byte	92
	.byte	161
	.byte	109
	.byte	98
	.byte	159
	.byte	87
	.byte	95
	.byte	242
	.byte	142
	.byte	96
	.byte	56
	.byte	27
	.byte	229
	.byte	114
	.byte	69
	.byte	6
	.byte	235
	.byte	76
	.byte	50
	.byte	138
	.byte	149
	.type	vectors, @object
	.size	vectors, . - vectors
	.text
	.align	16
	.globl test_vectors
test_vectors:
	.cfi_startproc
	subl	$140, %esp
	.cfi_adjust_cfa_offset	140
	leal	144(%esp), %edx
	movl	%edx, 20(%esp)
	movl	%ebx, 24(%esp)
	movl	%esi, 28(%esp)
	movl	%edi, 32(%esp)
	movl	%ebp, 36(%esp)
	movl	$1, %ecx
	movl	%ecx, 40(%esp)
	xorl	%edx, %edx
.L111:
	leal	56(%esp), %eax
	movb	%dl, 0(%eax,%edx,1)
	leal	1(%edx), %edx
	cmpl	$16, %edx
	jl	.L111
	xorl	%ebx, %ebx
.L112:
	leal	72(%esp), %eax
	movb	%bl, 0(%eax,%ebx,1)
	leal	48(%esp), %eax
	leal	72(%esp), %edi
	movl	%ebx, %edx
	movl	%edx, %ebp
	sarl	$31, %ebp
	leal	56(%esp), %esi
	movl	%eax, 0(%esp)
	movl	%edi, 4(%esp)
	movl	%ebp, 12(%esp)
	movl	%edx, 8(%esp)
	movl	%esi, 16(%esp)
	call	crypto_auth
	leal	48(%esp), %esi
	leal	vectors(,%ebx,8), %ecx
	movl	$8, %eax
	movl	%esi, 0(%esp)
	movl	%ecx, 4(%esp)
	movl	%eax, 8(%esp)
	call	memcmp
	testl	%eax, %eax
	je	.L113
	leal	__stringlit_1, %eax
	movl	%eax, 0(%esp)
	movl	%ebx, 4(%esp)
	call	printf
	xorl	%eax, %eax
	movl	%eax, 40(%esp)
.L113:
	leal	1(%ebx), %ebx
	cmpl	$64, %ebx
	jl	.L112
	movl	40(%esp), %eax
	movl	24(%esp), %ebx
	movl	28(%esp), %esi
	movl	32(%esp), %edi
	movl	36(%esp), %ebp
	addl	$140, %esp
	ret
	.cfi_endproc
	.type	test_vectors, @function
	.size	test_vectors, . - test_vectors
	.data
	.align	1
	.global	testdata
testdata:
	.byte	1
	.byte	2
	.byte	3
	.byte	4
	.byte	5
	.byte	6
	.byte	7
	.byte	8
	.byte	9
	.byte	0
	.byte	12
	.byte	34
	.byte	56
	.byte	78
	.byte	90
	.space	85
	.type	testdata, @object
	.size	testdata, . - testdata
	.text
	.align	16
	.globl speed_test
speed_test:
	.cfi_startproc
	subl	$68, %esp
	.cfi_adjust_cfa_offset	68
	leal	72(%esp), %edx
	movl	%edx, 20(%esp)
	movl	%ebx, 24(%esp)
	movl	%esi, 28(%esp)
	movl	%edi, 32(%esp)
	movl	%ebp, 36(%esp)
	xorl	%edx, %edx
.L114:
	leal	48(%esp), %ecx
	movb	%dl, 0(%ecx,%edx,1)
	leal	1(%edx), %edx
	cmpl	$16, %edx
	jl	.L114
	xorl	%ebx, %ebx
.L115:
	leal	40(%esp), %esi
	leal	testdata, %eax
	movl	$100, %ecx
	xorl	%edx, %edx
	leal	48(%esp), %ebp
	movl	%esi, 0(%esp)
	movl	%eax, 4(%esp)
	movl	%edx, 12(%esp)
	movl	%ecx, 8(%esp)
	movl	%ebp, 16(%esp)
	call	crypto_auth
	leal	1(%ebx), %ebx
	cmpl	$10000000, %ebx
	jl	.L115
	movzbl	40(%esp), %eax
	movl	24(%esp), %ebx
	movl	28(%esp), %esi
	movl	32(%esp), %edi
	movl	36(%esp), %ebp
	addl	$68, %esp
	ret
	.cfi_endproc
	.type	speed_test, @function
	.size	speed_test, . - speed_test
	.text
	.align	16
	.globl main
main:
	.cfi_startproc
	subl	$12, %esp
	.cfi_adjust_cfa_offset	12
	leal	16(%esp), %edx
	movl	%edx, 4(%esp)
	call	test_vectors
	testl	%eax, %eax
	je	.L116
	leal	__stringlit_2, %eax
	movl	%eax, 0(%esp)
	call	printf
.L116:
	call	speed_test
	xorl	%eax, %eax
	addl	$12, %esp
	ret
	.cfi_endproc
	.type	main, @function
	.size	main, . - main
