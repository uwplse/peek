Require Import Coqlib.
Require Import Asm.
Require Import Integers.
Require Import PeekTactics.
Require Import PeepsLib.
Require Import PregTactics.
Require Import StepIn.
Require Import AsmBits.
Require Import Values.
Require Import ValEq.
Require Import Integers.
Require Import PeepsTactics.

Print addrmode.

Definition ea : addrmode := Addrmode None None (inl Int.zero).

Definition peep_xor_vec_example :=
  Pmov_rm EAX ea ::
  Pmov_rm EAX ea ::
  Pmov_rm EAX ea ::
  Pmov_rm EAX ea ::
  Pxor_rr EAX EAX ::
  Pxor_rr EAX EAX ::
  Pmov_rm EAX ea ::
  Pmov_rm EAX ea ::
  Pxor_rr EAX EAX ::
  Pxor_rr EAX EAX ::
  Pmov_rm EAX ea ::
  Pmov_rm EAX ea ::
  Pxor_rr EAX EAX ::
  Pxor_rr EAX EAX ::
  Pmov_rm EAX ea ::
  Pmov_rm EAX ea ::
  Pxor_rr EAX EAX ::
  Pxor_rr EAX EAX ::
  Pmov_mr ea EAX ::
  Pmov_mr ea EAX ::
  nil.

Section XOR_VEC.
  (* 

	
	movl	8(%edi), %esi
	movl	12(%edi), %ebp
	movl	48(%edi), %ecx
	movl	52(%edi), %eax
	xorl	%eax, %ebp
	xorl	%ecx, %esi
	movl	88(%edi), %ecx
	movl	92(%edi), %eax
	xorl	%eax, %ebp
	xorl	%ecx, %esi
	movl	128(%edi), %eax
	movl	132(%edi), %ecx
	xorl	%ecx, %ebp
	xorl	%eax, %esi
	movl	168(%edi), %ecx
	movl	172(%edi), %eax
	xorl	%eax, %ebp
	xorl	%ecx, %esi
	movl	%esi, 48(%esp)
	movl	%ebp, 52(%esp)


  	movsd	8(%edi), %xmm0
	xorpd 	48(%edi), %xmm0
	xorpd	88(%edi), %xmm0
	xorpd 	128(%edi), %xmm0
	xorpd	168(%edi), %xmm0
	movsd	%xmm0, 48(%esp)


*)

  
  Variable concrete : code.
  Variable r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 rb : ireg.
  (* We will need to also encode:
   list_norepet (r1,r2,r3,r4)
   (r5,r6) = (r3,r4) \/ (r6,r5) = (r3,r4)
   (r7,r8) = (r3,r4) \/ (r8,r7) = (r3,r4)
   (r9,r10) = (r3,r4) \/ (r10,r9) = (r3,r4)
*)
  Variable f1 f2 : freg.

  Variable a1 a2 a3 a4 a5 : int.

  (* Proof might need more non-alias info about these addresses *)
  Definition adr (i ofs : int) : addrmode :=
    Addrmode (Some rb) None (inl (Int.add i ofs)).

  (* We're going to need to think hard about vectorizing xor, as it's an integer thing *)
  (* We have two integer values, need to load into float reg, and xor *)
  (* think about this, maybe do later *)
  
  Definition peep_xor_vec_defs : rewrite_defs :=
    {|
      fnd :=
        Pmov_rm r1 (adr a1 Int.zero) ::
                Pmov_rm r2 (adr a1 (Int.repr 4) ::
                Pmov_rm r3 (adr a2 Int.zero) ::
                Pmov_rm r4 (adr a2 (Int.repr 4) ::
                Pxor_rr r2 r4 ::
                Pxor_rr r1 r3 ::
                Pmov_rm r5 (adr a3 Int.zero) ::
                Pmov_rm r6 (adr a3 (Int.repr 4) ::
                Pxor_rr r2 r6 ::
                Pxor_rr r1 r5 ::
                Pmov_rm r7 (adr a4 Int.zero) ::
                Pmov_rm r8 (adr a4 (Int.repr 4) ::
                Pxor_rr r2 r8 ::
                Pxor_rr r1 r7 ::
                Pmov_rm r9 ea ::
                Pmov_rm r10 ea ::
                Pxor_rr r2 r10 ::
                Pxor_rr r1 r9 ::
                Pmov_mr (adr a5 Int.zero) EAX ::
                Pmov_mr (adr a5 (Int.repr 4)) EAX ::
                nil
      ; rpl :=
          Pmovsd_fm f1 (adr a1 Int.zero) ::
                    Pmovsd_fm f2 (adr a2 Int.zero) ::
                    
      ; lv_in := PC :: IR rb :: nil
      ; lv_out := PC :: IR rb :: nil
      ; clobbered := IR r2 :: nil
    |}.

    Lemma peep_xor_vec_selr :
    StepEquiv.step_through_equiv_live (fnd peep_xor_vec_defs) (rpl peep_xor_vec_defs) (lv_in peep_xor_vec_defs) (lv_out peep_xor_vec_defs).
  Proof.
    admit.
    (* prep_l. *)
    (* step_l. *)
    (* prep_r. *)
    (* step_r. *)
    (* finish_r. *)
    (* split. *)
    (*USE: Int.shl_mul_two_p.*)    
  Qed.

  Definition peep_xor_vec_proofs : rewrite_proofs :=
    {|
      defs := peep_xor_vec_defs
      ; selr := peep_xor_vec_selr
    |}.

  Definition peep_xor_vec : 
    concrete = fnd peep_xor_vec_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite peep_xor_vec_defs peep_xor_vec_proofs.
    admit.
    admit.
  Qed.

End XOR_VEC.

Definition peep_xor_vec_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_xor_vec p.
  unfold peep_xor_vec_defs in p.
  simpl in p. 
  specialize (p c).
  do 3 set_code_cons c.
  set_code_nil c.  
  set_instr_eq i 0%nat peep_xor_vec_example.
  set_instr_eq i0 1%nat peep_xor_vec_example.
  set_instr_eq i1 2%nat peep_xor_vec_example.
  set_ireg_eq rd1 rd.
  set_ireg_eq rd0 r1.
  specialize (p _ _ _ _ eq_refl). exact (Some p).
Defined.

Definition xor_vec (c : code) : list StepEquiv.rewrite :=
  collect (map peep_xor_vec_rewrite (ParamSplit.matched_pat peep_xor_vec_example c)).

                