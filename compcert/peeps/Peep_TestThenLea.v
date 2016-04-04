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

(*TODO: Replace with newer version*)
Ltac prep_r :=
  T0 _destruct state_bits;      
    NP0 app_new step_fwd_exec step_fwd; eauto;    
  repeat break_and;      
  P0 _clear step_through;
  P0 _clear step_fwd;
  P0 _clear current_fn;
  NP app_new mem_eq_match_metadata_r MemEq.mem_eq.

Ltac step_l :=
    NP1 app_new step_through_current_instr step_through;
    NP1 app_new step_through_current_fn step_through; [ | simpl; eauto ];
    (step_l_str || step_l_jmp);
    break_and; compute_skipz; P1 _simpl step_through; try break_and;
    NP1 app_new step_fwd_transf_block step_fwd.

(*
movl  %eax, %ecx
leal  -1(%ecx), %eax
testl %ecx, %ecx
=>
testl %eax, %eax
leal  -1(%eax), %eax
*)
Definition neg_one := (Int.repr (-1)).
Definition peep_test_then_lea_example :=
  Pmov_rr ECX EAX ::
  Plea EAX (Addrmode (Some ECX) None (inl neg_one)) ::
  Ptest_rr ECX ECX ::
  nil.

Section TEST_THEN_LEA.

  Variable concrete : code.
  Variable r1 r2 : ireg.
  Hypothesis r1_r2_neq : r1 <> r2.
  
  Definition peep_test_then_lea_defs : rewrite_defs :=
    {|
      fnd :=
        Pmov_rr r2 r1 ::
                Plea r1 (Addrmode (Some r2) None (inl neg_one)) ::
                Ptest_rr r2 r2 ::
                nil
      ; rpl :=
        Ptest_rr r1 r1 ::
                 Plea r1 (Addrmode (Some r1) None (inl neg_one)) ::
                 Pnop ::
                 nil
      ; lv_in := PC :: IR r1 :: nil
      ; lv_out := PC :: IR r1 :: flags
      ; clobbered := IR r2 :: nil
    |}.

    Lemma peep_test_then_lea_selr :
    StepEquiv.step_through_equiv_live (fnd peep_test_then_lea_defs) (rpl peep_test_then_lea_defs) (lv_in peep_test_then_lea_defs) (lv_out peep_test_then_lea_defs).
  Proof.
    prep_l.
    step_l.
    step_l.
    step_l.
    prep_r.
    step_r.
    step_r.
    step_r.
    finish_r.
    prep_eq.
    split.
    2: eq_mem_tac.
    intros.
    P0 _clear current_block.
    P0 _clear MemoryAxioms.match_metadata.
    P0 _clear no_ptr_mem.
    P0 _clear no_ptr_regs.
    break_or.
    repeat find_rewrite_goal.
    simpl.
    repeat (simpl_exec; try break_match; try congruence);      
            repeat (state_inv); try opt_inv; preg_simpl.
    unfold Val.add.
    simpl.
    repeat find_rewrite_goal.
    f_equal.    
    break_or.
    repeat (simpl_and_clear; try break_match; try congruence);      
            repeat (state_inv); try opt_inv; preg_simpl.
    unfold Val.add.    
    subst m0 m1 a1 a0 m.
    clear_taut.    
    subst r0.
    preg_simpl.
    unfold Val.add.
    subst.
    preg_simpl.
    break_match_sm; simpl; intros;
    try break_match; try congruence.
    f_equal.
    P0 _simpl val_eq.
    inv_vint.
    f_equal.
    P0 _simpl val_eq.
    assumption.    

    simpl_and_clear.
    
    assert (In reg flags) by (simpl; auto).    

    repeat rewrite nextinstr_flags by assumption.
    rewrite Pregmap.gso.
    repeat rewrite nextinstr_flags by assumption.
    
    eapply val_eq_compare_ints; eauto.
    eapply val_eq_and; eauto.
    3: simpl; auto.
    subst_max.
    preg_simpl.
    assumption.
    subst_max.
    preg_simpl.
    assumption.
    subst m m1 m0.
    eauto.
    simpl in *.
    repeat break_or_reg; congruence.    
  Qed.

  Definition peep_test_then_lea_proofs : rewrite_proofs :=
    {|
      defs := peep_test_then_lea_defs
      ; selr := peep_test_then_lea_selr
    |}.

  Definition peep_test_then_lea : 
    concrete = fnd peep_test_then_lea_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite peep_test_then_lea_defs peep_test_then_lea_proofs.
  Qed.

End TEST_THEN_LEA.

Definition peep_test_then_lea_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_test_then_lea p.
  unfold peep_test_then_lea_defs in p.
  simpl in p. 
  specialize (p c).
  do 3 set_code_cons c.
  set_code_nil c.  
  set_instr_eq i 0%nat peep_test_then_lea_example.
  set_instr_eq i0 1%nat peep_test_then_lea_example.
  set_instr_eq i1 2%nat peep_test_then_lea_example.  
  set_ireg_eq rd0 r1.
  set_ireg_eq r0 r2.
  set_ireg_eq r2 rd.
  set_ireg_neq r1 rd.  
  set_addrmode_eq a (Addrmode (Some rd) None (inl neg_one)).
  specialize (p _ _ n eq_refl). exact (Some p).
Defined.

Definition test_then_lea (c : code) : list StepEquiv.rewrite :=
  collect (map peep_test_then_lea_rewrite (ParamSplit.matched_pat peep_test_then_lea_example c)).
                
