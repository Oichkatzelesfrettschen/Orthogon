	.file ""
	.section .rodata.cst16,"aM",@progbits,16
	.align	16
caml_negf_mask:
	.quad	0x8000000000000000
	.quad	0
	.align	16
caml_absf_mask:
	.quad	0x7fffffffffffffff
	.quad	-1
	.data
	.globl	camlDsf_init__data_begin
camlDsf_init__data_begin:
	.text
	.globl	camlDsf_init__code_begin
camlDsf_init__code_begin:
	.data
	.align	8
	.data
	.align	8
	.quad	3063
camlDsf_init__9:
	.quad	camlDsf_init__reccall_16
	.quad	0x100000000000005
	.data
	.align	8
	.quad	4087
camlDsf_init__8:
	.quad	caml_curry3
	.quad	0x300000000000007
	.quad	camlDsf_init__def_Corelib_Lists_ListDef_repeat_4
	.data
	.align	8
	.quad	3063
camlDsf_init__7:
	.quad	camlDsf_init__def_KeenKenning_DSF_dsf_init_14
	.quad	0x100000000000005
	.data
	.align	8
	.quad	4087
camlDsf_init__10:
	.quad	caml_curry2
	.quad	0x200000000000007
	.quad	camlDsf_init__repeat_8
	.data
	.align	8
	.quad	8960
	.globl	camlDsf_init
camlDsf_init:
	.quad	1
	.quad	1
	.quad	1
	.quad	1
	.quad	1
	.quad	1
	.quad	1
	.quad	1
	.data
	.align	8
	.globl	camlDsf_init__gc_roots
camlDsf_init__gc_roots:
	.quad	camlDsf_init
	.quad	0
	.text
	.align	16
	.globl	camlDsf_init__repeat_8
camlDsf_init__repeat_8:
	.cfi_startproc
	subq	$8, %rsp
	.cfi_adjust_cfa_offset 8
.L101:
	testb	$1, %bl
	je	.L100
	movl	$1, %eax
	addq	$8, %rsp
	.cfi_adjust_cfa_offset -8
	ret
	.cfi_adjust_cfa_offset 8
	.align	4
.L100:
	movq	%rax, (%rsp)
	movq	(%rbx), %rbx
	call	camlDsf_init__repeat_8@PLT
.L102:
	subq	$24, %r15
	cmpq	(%r14), %r15
	jb	.L103
.L105:
	leaq	8(%r15), %rbx
	movq	$2048, -8(%rbx)
	movq	(%rsp), %rdi
	movq	%rdi, (%rbx)
	movq	%rax, 8(%rbx)
	movq	%rbx, %rax
	addq	$8, %rsp
	.cfi_adjust_cfa_offset -8
	ret
	.cfi_adjust_cfa_offset 8
.L103:
	call	caml_call_gc@PLT
.L104:
	jmp	.L105
	.cfi_adjust_cfa_offset -8
	.cfi_endproc
	.type camlDsf_init__repeat_8,@function
	.size camlDsf_init__repeat_8,. - camlDsf_init__repeat_8
	.text
	.align	16
	.globl	camlDsf_init__reccall_16
camlDsf_init__reccall_16:
	.cfi_startproc
.L106:
	movq	%rbx, %rax
	ret
	.cfi_endproc
	.type camlDsf_init__reccall_16,@function
	.size camlDsf_init__reccall_16,. - camlDsf_init__reccall_16
	.text
	.align	16
	.globl	camlDsf_init__def_Corelib_Lists_ListDef_repeat_4
camlDsf_init__def_Corelib_Lists_ListDef_repeat_4:
	.cfi_startproc
.L107:
	movq	%rbx, %rax
	movq	%rdi, %rbx
	jmp	camlDsf_init__repeat_8@PLT
	.cfi_endproc
	.type camlDsf_init__def_Corelib_Lists_ListDef_repeat_4,@function
	.size camlDsf_init__def_Corelib_Lists_ListDef_repeat_4,. - camlDsf_init__def_Corelib_Lists_ListDef_repeat_4
	.text
	.align	16
	.globl	camlDsf_init__def_KeenKenning_DSF_dsf_init_14
camlDsf_init__def_KeenKenning_DSF_dsf_init_14:
	.cfi_startproc
.L108:
	movq	%rax, %rdi
	movq	camlDsf_init__9@GOTPCREL(%rip), %rax
	movq	camlDsf_init__6@GOTPCREL(%rip), %rbx
	jmp	camlDsf_init__def_Corelib_Lists_ListDef_repeat_4@PLT
	.cfi_endproc
	.type camlDsf_init__def_KeenKenning_DSF_dsf_init_14,@function
	.size camlDsf_init__def_KeenKenning_DSF_dsf_init_14,. - camlDsf_init__def_KeenKenning_DSF_dsf_init_14
	.data
	.align	8
	.quad	1792
	.globl	camlDsf_init__6
camlDsf_init__6:
	.quad	camlDsf_init__5
	.data
	.align	8
	.quad	1792
	.globl	camlDsf_init__5
camlDsf_init__5:
	.quad	camlDsf_init__4
	.data
	.align	8
	.quad	1792
	.globl	camlDsf_init__4
camlDsf_init__4:
	.quad	camlDsf_init__3
	.data
	.align	8
	.quad	1792
	.globl	camlDsf_init__3
camlDsf_init__3:
	.quad	camlDsf_init__2
	.data
	.align	8
	.quad	1792
	.globl	camlDsf_init__2
camlDsf_init__2:
	.quad	camlDsf_init__1
	.data
	.align	8
	.quad	1792
	.globl	camlDsf_init__1
camlDsf_init__1:
	.quad	1
	.text
	.align	16
	.globl	camlDsf_init__entry
camlDsf_init__entry:
	.cfi_startproc
.L109:
	movq	camlDsf_init__8@GOTPCREL(%rip), %rax
	movq	camlDsf_init@GOTPCREL(%rip), %rbx
	movq	%rax, 16(%rbx)
	movq	camlDsf_init__6@GOTPCREL(%rip), %rax
	movq	%rax, 24(%rbx)
	movq	camlDsf_init__7@GOTPCREL(%rip), %rax
	movq	%rax, 32(%rbx)
	movq	32(%rbx), %rax
	movq	%rax, 40(%rbx)
	movq	%rax, 48(%rbx)
	movq	40(%rbx), %rax
	movq	%rax, 56(%rbx)
	movq	48(%rbx), %rax
	movq	%rax, (%rbx)
	movq	56(%rbx), %rax
	movq	%rax, 8(%rbx)
	movl	$1, %eax
	ret
	.cfi_endproc
	.type camlDsf_init__entry,@function
	.size camlDsf_init__entry,. - camlDsf_init__entry
	.data
	.align	8
	.text
	.globl	camlDsf_init__code_end
camlDsf_init__code_end:
	.data
				/* relocation table start */
	.align	8
				/* relocation table end */
	.data
	.quad	0
	.globl	camlDsf_init__data_end
camlDsf_init__data_end:
	.quad	0
	.align	8
	.globl	camlDsf_init__frametable
camlDsf_init__frametable:
	.quad	2
	.quad	.L104
	.word	18
	.word	2
	.word	0
	.word	1
	.byte	1
	.byte	1
	.align	8
	.quad	.L102
	.word	16
	.word	1
	.word	0
	.align	8
	.align	8
	.size camlDsf_init__frametable,. - camlDsf_init__frametable
	.section .note.GNU-stack,"",%progbits
