# File generated by CompCert 2.4
# Command line: -fno-peeps -stdlib ../../runtime -dc -dclight -dasm -S -o perlin.handtuned.s perlin.c
	.section	.rodata
	.align	1
__stringlit_1:
	.ascii	"%.4e\012\000"
	.type	__stringlit_1, @object
	.size	__stringlit_1, . - __stringlit_1
	.local	p
	.comm	p, 2048, 4
	.data
	.align	4
permutation:
	.long	151
	.long	160
	.long	137
	.long	91
	.long	90
	.long	15
	.long	131
	.long	13
	.long	201
	.long	95
	.long	96
	.long	53
	.long	194
	.long	233
	.long	7
	.long	225
	.long	140
	.long	36
	.long	103
	.long	30
	.long	69
	.long	142
	.long	8
	.long	99
	.long	37
	.long	240
	.long	21
	.long	10
	.long	23
	.long	190
	.long	6
	.long	148
	.long	247
	.long	120
	.long	234
	.long	75
	.long	0
	.long	26
	.long	197
	.long	62
	.long	94
	.long	252
	.long	219
	.long	203
	.long	117
	.long	35
	.long	11
	.long	32
	.long	57
	.long	177
	.long	33
	.long	88
	.long	237
	.long	149
	.long	56
	.long	87
	.long	174
	.long	20
	.long	125
	.long	136
	.long	171
	.long	168
	.long	68
	.long	175
	.long	74
	.long	165
	.long	71
	.long	134
	.long	139
	.long	48
	.long	27
	.long	166
	.long	77
	.long	146
	.long	158
	.long	231
	.long	83
	.long	111
	.long	229
	.long	122
	.long	60
	.long	211
	.long	133
	.long	230
	.long	220
	.long	105
	.long	92
	.long	41
	.long	55
	.long	46
	.long	245
	.long	40
	.long	244
	.long	102
	.long	143
	.long	54
	.long	65
	.long	25
	.long	63
	.long	161
	.long	1
	.long	216
	.long	80
	.long	73
	.long	209
	.long	76
	.long	132
	.long	187
	.long	208
	.long	89
	.long	18
	.long	169
	.long	200
	.long	196
	.long	135
	.long	130
	.long	116
	.long	188
	.long	159
	.long	86
	.long	164
	.long	100
	.long	109
	.long	198
	.long	173
	.long	186
	.long	3
	.long	64
	.long	52
	.long	217
	.long	226
	.long	250
	.long	124
	.long	123
	.long	5
	.long	202
	.long	38
	.long	147
	.long	118
	.long	126
	.long	255
	.long	82
	.long	85
	.long	212
	.long	207
	.long	206
	.long	59
	.long	227
	.long	47
	.long	16
	.long	58
	.long	17
	.long	182
	.long	189
	.long	28
	.long	42
	.long	223
	.long	183
	.long	170
	.long	213
	.long	119
	.long	248
	.long	152
	.long	2
	.long	44
	.long	154
	.long	163
	.long	70
	.long	221
	.long	153
	.long	101
	.long	155
	.long	167
	.long	43
	.long	172
	.long	9
	.long	129
	.long	22
	.long	39
	.long	253
	.long	19
	.long	98
	.long	108
	.long	110
	.long	79
	.long	113
	.long	224
	.long	232
	.long	178
	.long	185
	.long	112
	.long	104
	.long	218
	.long	246
	.long	97
	.long	228
	.long	251
	.long	34
	.long	242
	.long	193
	.long	238
	.long	210
	.long	144
	.long	12
	.long	191
	.long	179
	.long	162
	.long	241
	.long	81
	.long	51
	.long	145
	.long	235
	.long	249
	.long	14
	.long	239
	.long	107
	.long	49
	.long	192
	.long	214
	.long	31
	.long	181
	.long	199
	.long	106
	.long	157
	.long	184
	.long	84
	.long	204
	.long	176
	.long	115
	.long	121
	.long	50
	.long	45
	.long	127
	.long	4
	.long	150
	.long	254
	.long	138
	.long	236
	.long	205
	.long	93
	.long	222
	.long	114
	.long	67
	.long	29
	.long	24
	.long	72
	.long	243
	.long	141
	.long	128
	.long	195
	.long	78
	.long	66
	.long	215
	.long	61
	.long	156
	.long	180
	.type	permutation, @object
	.size	permutation, . - permutation
	.text
	.align	16
fade:
	.cfi_startproc
	subl	$20, %esp
	.cfi_adjust_cfa_offset	20
	leal	24(%esp), %edx
	movl	%edx, 0(%esp)
	movsd	0(%edx), %xmm0
	movapd	%xmm0, %xmm2
	mulsd	%xmm0, %xmm2
	mulsd	%xmm0, %xmm2
	movsd	.L100, %xmm3 # 6
	movapd	%xmm0, %xmm1
	mulsd	%xmm3, %xmm1
	movsd	.L101, %xmm4 # 15
	subsd	%xmm4, %xmm1
	mulsd	%xmm1, %xmm0
	movsd	.L102, %xmm5 # 10
	addsd	%xmm5, %xmm0
	mulsd	%xmm0, %xmm2
	movsd	%xmm2, 8(%esp)
	fldl	8(%esp)
	addl	$20, %esp
	ret
	.cfi_endproc
	.type	fade, @function
	.size	fade, . - fade
	.section	.rodata.cst8,"aM",@progbits,8
	.align	8
.L102:	.quad	0x4024000000000000
.L101:	.quad	0x402e000000000000
.L100:	.quad	0x4018000000000000
	.text
	.align	16
lerp:
	.cfi_startproc
	subl	$20, %esp
	.cfi_adjust_cfa_offset	20
	leal	24(%esp), %edx
	movl	%edx, 0(%esp)
	movsd	0(%edx), %xmm2
	movsd	8(%edx), %xmm1
	movsd	16(%edx), %xmm0
	subsd	%xmm1, %xmm0
	mulsd	%xmm0, %xmm2
	addsd	%xmm2, %xmm1
	movsd	%xmm1, 8(%esp)
	fldl	8(%esp)
	addl	$20, %esp
	ret
	.cfi_endproc
	.type	lerp, @function
	.size	lerp, . - lerp
	.text
	.align	16
grad:
	.cfi_startproc
	subl	$20, %esp
	.cfi_adjust_cfa_offset	20
	leal	24(%esp), %edx
	movl	%edx, 0(%esp)
	movl	0(%edx), %eax
	movsd	4(%edx), %xmm2
	movsd	12(%edx), %xmm3
	movsd	20(%edx), %xmm0
	andl	$15, %eax
	cmpl	$8, %eax
	jl	.L103
	movapd	%xmm3, %xmm1
	jmp	.L104
.L103:
	movapd	%xmm2, %xmm1
.L104:
	cmpl	$4, %eax
	jl	.L105
	cmpl	$12, %eax
	je	.L106
	cmpl	$14, %eax
	jne	.L107
.L106:
	movapd	%xmm2, %xmm0
	jmp	.L107
.L105:
	movapd	%xmm3, %xmm0
.L107:
	testl	$1, %eax
	je	.L108
	xorpd	__negd_mask, %xmm1
.L108:
	testl	$2, %eax
	je	.L109
	xorpd	__negd_mask, %xmm0
.L109:
	addsd	%xmm0, %xmm1
	movsd	%xmm1, 8(%esp)
	fldl	8(%esp)
	addl	$20, %esp
	ret
	.cfi_endproc
	.type	grad, @function
	.size	grad, . - grad
	.text
	.align	16
noise:
	.cfi_startproc
	subl	$132, %esp
	.cfi_adjust_cfa_offset	132
	leal	136(%esp), %edx
	movl	%edx, 28(%esp)
	movl	%ebx, 32(%esp)
	movl	%esi, 36(%esp)
	movl	%edi, 40(%esp)
	movl	%ebp, 44(%esp)
	movsd	0(%edx), %xmm4
	movsd	%xmm4, 48(%esp)
	movsd	8(%edx), %xmm4
	movsd	%xmm4, 64(%esp)
	movsd	16(%edx), %xmm4
	movsd	%xmm4, 72(%esp)
	movsd	48(%esp), %xmm7
	movsd	%xmm7, 0(%esp)
	call	floor
	fstpl	56(%esp)
	movsd	56(%esp), %xmm2
	cvttsd2si %xmm2, %ebx
	andl	$255, %ebx
	movsd	64(%esp), %xmm7
	movsd	%xmm7, 0(%esp)
	call	floor
	fstpl	56(%esp)
	movsd	56(%esp), %xmm0
	cvttsd2si %xmm0, %edi
	andl	$255, %edi
	movsd	72(%esp), %xmm6
	movsd	%xmm6, 0(%esp)
	call	floor
	fstpl	56(%esp)
	movsd	56(%esp), %xmm2
	cvttsd2si %xmm2, %esi
	andl	$255, %esi
	movsd	48(%esp), %xmm2
	movsd	%xmm2, 0(%esp)
	call	floor
	fstpl	56(%esp)
	movsd	56(%esp), %xmm1
	movsd	48(%esp), %xmm4
	subsd	%xmm1, %xmm4
	movsd	%xmm4, 56(%esp)
	movsd	64(%esp), %xmm4
	movsd	%xmm4, 0(%esp)
	call	floor
	fstpl	48(%esp)
	movsd	48(%esp), %xmm4
	movsd	64(%esp), %xmm5
	subsd	%xmm4, %xmm5
	movsd	%xmm5, 64(%esp)
	movsd	72(%esp), %xmm0
	movsd	%xmm0, 0(%esp)
	call	floor
	fstpl	48(%esp)
	movsd	48(%esp), %xmm4
	movsd	72(%esp), %xmm3
	subsd	%xmm4, %xmm3
	movsd	%xmm3, 48(%esp)
	movsd	56(%esp), %xmm5
	movsd	%xmm5, 0(%esp)
	call	fade
	fstpl	76(%esp)
	movsd	64(%esp), %xmm6
	movsd	%xmm6, 0(%esp)
	call	fade
	fstpl	84(%esp)
	movsd	48(%esp), %xmm1
	movsd	%xmm1, 0(%esp)
	call	fade
	fstpl	116(%esp)
	movl	p(,%ebx,4), %ecx
	addl	%edi, %ecx
	movl	p(,%ecx,4), %edx
	addl	%esi, %edx
	movl	%edx, 72(%esp)
	movl	(p + 4)(,%ecx,4), %edx
	leal	0(%edx,%esi,1), %ebp
	movl	(p + 4)(,%ebx,4), %edx
	leal	0(%edx,%edi,1), %ecx
	movl	p(,%ecx,4), %edx
	leal	0(%edx,%esi,1), %ebx
	movl	(p + 4)(,%ecx,4), %eax
	addl	%eax, %esi
	movl	72(%esp), %eax
	movl	p(,%eax,4), %ecx
	movl	%ecx, 0(%esp)
	movsd	56(%esp), %xmm6
	movsd	%xmm6, 4(%esp)
	movsd	64(%esp), %xmm6
	movsd	%xmm6, 12(%esp)
	movsd	48(%esp), %xmm6
	movsd	%xmm6, 20(%esp)
	call	grad
	fstpl	92(%esp)
	movl	p(,%ebx,4), %ecx
	movsd	.L110, %xmm3 # 1
	movsd	56(%esp), %xmm2
	subsd	%xmm3, %xmm2
	movl	%ecx, 0(%esp)
	movsd	%xmm2, 4(%esp)
	movsd	64(%esp), %xmm1
	movsd	%xmm1, 12(%esp)
	movsd	48(%esp), %xmm1
	movsd	%xmm1, 20(%esp)
	call	grad
	fstpl	100(%esp)
	movsd	100(%esp), %xmm0
	movsd	76(%esp), %xmm6
	movsd	%xmm6, 0(%esp)
	movsd	92(%esp), %xmm6
	movsd	%xmm6, 8(%esp)
	movsd	%xmm0, 16(%esp)
	call	lerp
	fstpl	92(%esp)
	movl	p(,%ebp,4), %edx
	movsd	.L111, %xmm4 # 1
	movsd	64(%esp), %xmm1
	subsd	%xmm4, %xmm1
	movl	%edx, 0(%esp)
	movsd	56(%esp), %xmm2
	movsd	%xmm2, 4(%esp)
	movsd	%xmm1, 12(%esp)
	movsd	48(%esp), %xmm2
	movsd	%xmm2, 20(%esp)
	call	grad
	fstpl	100(%esp)
	movl	p(,%esi,4), %ecx
	movsd	.L112, %xmm0 # 1
	movsd	56(%esp), %xmm2
	subsd	%xmm0, %xmm2
	movsd	64(%esp), %xmm1
	subsd	%xmm0, %xmm1
	movl	%ecx, 0(%esp)
	movsd	%xmm2, 4(%esp)
	movsd	%xmm1, 12(%esp)
	movsd	48(%esp), %xmm3
	movsd	%xmm3, 20(%esp)
	call	grad
	fstpl	108(%esp)
	movsd	108(%esp), %xmm4
	movsd	76(%esp), %xmm5
	movsd	%xmm5, 0(%esp)
	movsd	100(%esp), %xmm5
	movsd	%xmm5, 8(%esp)
	movsd	%xmm4, 16(%esp)
	call	lerp
	fstpl	100(%esp)
	movsd	100(%esp), %xmm7
	movsd	84(%esp), %xmm3
	movsd	%xmm3, 0(%esp)
	movsd	92(%esp), %xmm3
	movsd	%xmm3, 8(%esp)
	movsd	%xmm7, 16(%esp)
	call	lerp
	fstpl	108(%esp)
	movl	72(%esp), %ecx
	movl	(p + 4)(,%ecx,4), %ecx
	movsd	.L113, %xmm5 # 1
	movsd	48(%esp), %xmm7
	subsd	%xmm5, %xmm7
	movl	%ecx, 0(%esp)
	movsd	56(%esp), %xmm0
	movsd	%xmm0, 4(%esp)
	movsd	64(%esp), %xmm0
	movsd	%xmm0, 12(%esp)
	movsd	%xmm7, 20(%esp)
	call	grad
	fstpl	92(%esp)
	movl	(p + 4)(,%ebx,4), %eax
	movsd	.L114, %xmm7 # 1
	movsd	56(%esp), %xmm6
	subsd	%xmm7, %xmm6
	movsd	48(%esp), %xmm5
	subsd	%xmm7, %xmm5
	movl	%eax, 0(%esp)
	movsd	%xmm6, 4(%esp)
	movsd	64(%esp), %xmm4
	movsd	%xmm4, 12(%esp)
	movsd	%xmm5, 20(%esp)
	call	grad
	fstpl	100(%esp)
	movsd	100(%esp), %xmm4
	movsd	76(%esp), %xmm6
	movsd	%xmm6, 0(%esp)
	movsd	92(%esp), %xmm6
	movsd	%xmm6, 8(%esp)
	movsd	%xmm4, 16(%esp)
	call	lerp
	fstpl	100(%esp)
	movl	(p + 4)(,%ebp,4), %edx
	movsd	.L115, %xmm3 # 1
	movsd	64(%esp), %xmm2
	subsd	%xmm3, %xmm2
	movsd	48(%esp), %xmm1
	subsd	%xmm3, %xmm1
	movl	%edx, 0(%esp)
	movsd	56(%esp), %xmm0
	movsd	%xmm0, 4(%esp)
	movsd	%xmm2, 12(%esp)
	movsd	%xmm1, 20(%esp)
	call	grad
	fstpl	92(%esp)
	movl	(p + 4)(,%esi,4), %edx
	movsd	.L116, %xmm6 # 1
	movsd	56(%esp), %xmm2
	subsd	%xmm6, %xmm2
	movapd	%xmm2, %xmm7
	movsd	64(%esp), %xmm3
	subsd	%xmm6, %xmm3
	movapd	%xmm3, %xmm0
	movsd	48(%esp), %xmm1
	subsd	%xmm6, %xmm1
	movl	%edx, 0(%esp)
	movsd	%xmm7, 4(%esp)
	movsd	%xmm0, 12(%esp)
	movsd	%xmm1, 20(%esp)
	call	grad
	fstpl	48(%esp)
	movsd	48(%esp), %xmm5
	movsd	76(%esp), %xmm6
	movsd	%xmm6, 0(%esp)
	movsd	92(%esp), %xmm6
	movsd	%xmm6, 8(%esp)
	movsd	%xmm5, 16(%esp)
	call	lerp
	fstpl	48(%esp)
	movsd	48(%esp), %xmm1
	movsd	84(%esp), %xmm5
	movsd	%xmm5, 0(%esp)
	movsd	100(%esp), %xmm5
	movsd	%xmm5, 8(%esp)
	movsd	%xmm1, 16(%esp)
	call	lerp
	fstpl	48(%esp)
	movsd	48(%esp), %xmm3
	movsd	116(%esp), %xmm7
	movsd	%xmm7, 0(%esp)
	movsd	108(%esp), %xmm7
	movsd	%xmm7, 8(%esp)
	movsd	%xmm3, 16(%esp)
	call	lerp
	fstpl	48(%esp)
	movsd	48(%esp), %xmm0
	movsd	%xmm0, 48(%esp)
	fldl	48(%esp)
	movl	32(%esp), %ebx
	movl	36(%esp), %esi
	movl	40(%esp), %edi
	movl	44(%esp), %ebp
	addl	$132, %esp
	ret
	.cfi_endproc
	.type	noise, @function
	.size	noise, . - noise
	.section	.rodata.cst8,"aM",@progbits,8
	.align	8
.L116:	.quad	0x3ff0000000000000
.L115:	.quad	0x3ff0000000000000
.L114:	.quad	0x3ff0000000000000
.L113:	.quad	0x3ff0000000000000
.L112:	.quad	0x3ff0000000000000
.L111:	.quad	0x3ff0000000000000
.L110:	.quad	0x3ff0000000000000
	.text
	.align	16
init:
	.cfi_startproc
	subl	$12, %esp
	.cfi_adjust_cfa_offset	12
	leal	16(%esp), %edx
	movl	%edx, 0(%esp)
	xorl	%ecx, %ecx
.L117:
	movl	permutation(,%ecx,4), %eax
	movl	%eax, p(,%ecx,4)
	movl	%eax, (p + 1024)(,%ecx,4)
	leal	1(%ecx), %ecx
	cmpl	$256, %ecx
	jl	.L117
	addl	$12, %esp
	ret
	.cfi_endproc
	.type	init, @function
	.size	init, . - init
	.text
	.align	16
	.globl main
main:
	.cfi_startproc
	subl	$76, %esp
	.cfi_adjust_cfa_offset	76
	leal	80(%esp), %edx
	movl	%edx, 24(%esp)
	call	init
	xorpd	%xmm1, %xmm1
	movsd	%xmm1, 48(%esp)
	movsd	.L118, %xmm2 # -11352.5699999999997
	movsd	%xmm2, 40(%esp)
.L119:
	movsd	.L120, %xmm4 # 23561.5699999999997
	movsd	40(%esp), %xmm1
	comisd	%xmm1, %xmm4
	jbe	.L121
	movsd	.L122, %xmm3 # -346.123499999999979
	movsd	%xmm3, 32(%esp)
.L123:
	movsd	.L124, %xmm1 # 124.123999999999995
	movsd	32(%esp), %xmm5
	comisd	%xmm5, %xmm1
	jbe	.L125
	movsd	.L126, %xmm0 # -156.235000000000014
	movsd	%xmm0, 56(%esp)
.L127:
	movsd	.L128, %xmm5 # 23.2345000000000006
	movsd	32(%esp), %xmm2
	comisd	%xmm2, %xmm5
	jbe	.L129
	movsd	40(%esp), %xmm2
	movsd	%xmm2, 0(%esp)
	movsd	32(%esp), %xmm2
	movsd	%xmm2, 8(%esp)
	movsd	56(%esp), %xmm2
	movsd	%xmm2, 16(%esp)
	call	noise
	fstpl	64(%esp)
	movsd	64(%esp), %xmm7
	movsd	48(%esp), %xmm6
	addsd	%xmm7, %xmm6
	movsd	%xmm6, 48(%esp)
	movsd	.L130, %xmm3 # 2.45000000000000018
	movsd	32(%esp), %xmm4
	addsd	%xmm3, %xmm4
	movsd	%xmm4, 32(%esp)
	jmp	.L127
.L129:
	movsd	.L131, %xmm1 # 1.43250000000000011
	movsd	32(%esp), %xmm0
	addsd	%xmm1, %xmm0
	movsd	%xmm0, 32(%esp)
	jmp	.L123
.L125:
	movsd	.L132, %xmm0 # 0.123499999999999999
	movsd	40(%esp), %xmm7
	addsd	%xmm0, %xmm7
	movsd	%xmm7, 40(%esp)
	jmp	.L119
.L121:
	leal	__stringlit_1, %eax
	movl	%eax, 0(%esp)
	movsd	48(%esp), %xmm3
	movsd	%xmm3, 4(%esp)
	call	printf
	xorl	%eax, %eax
	addl	$76, %esp
	ret
	.cfi_endproc
	.type	main, @function
	.size	main, . - main
	.section	.rodata.cst8,"aM",@progbits,8
	.align	8
.L132:	.quad	0x3fbf9db22d0e5604
.L131:	.quad	0x3ff6eb851eb851ec
.L130:	.quad	0x400399999999999a
.L128:	.quad	0x40373c083126e979
.L126:	.quad	0xc06387851eb851ec
.L124:	.quad	0x405f07ef9db22d0e
.L122:	.quad	0xc075a1f9db22d0e5
.L120:	.quad	0x40d702647ae147ae
.L118:	.quad	0xc0c62c48f5c28f5c
	.section	.rodata
	.align	16
__negd_mask:	.quad   0x8000000000000000, 0
__absd_mask:	.quad   0x7FFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF
__negs_mask:	.long   0x80000000, 0, 0, 0
__abss_mask:	.long   0x7FFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF
