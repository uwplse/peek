Require Import Coqlib.
Require Import Asm.
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

Definition aiken_5_example :=
  Psetcc Cond_g EAX :: Pdec EAX :: Pand_rr EBX EAX :: nil.

Section AIKEN_5.

  Variable concrete : code.

  Variable r1 : ireg.
  Variable r2 : ireg.
  Variable END : label.
  Hypothesis r1_r2_neq: r1 <> r2.

  Definition aiken_5_defs : rewrite_defs :=
    {|
      fnd :=        
        (* setg %al  *)
        (* movzbl %al, %eax  *) (*move byte to long zero exteneded*)
        (* dec %eax *)
        (* and %eax, %esi *)
        Psetcc Cond_g r1 ::
               Pdec r1 ::
               Pand_rr r2 r1 ::
               nil
      ; rpl :=
          (* mov $0, EAX *)
          (* cmovg %eax, %esi *)
          Pmov_ri r1 zero ::
                  Pcmov Cond_g r2 r1 ::
                  Pnop ::
                  nil
      ; lv_in := PC :: IR r2 :: flags
      ; lv_out := PC :: IR r2 :: nil
      ; clobbered := IR r1 :: nil
    |}.

  Lemma aiken_5_selr :
    StepEquiv.step_through_equiv_live (fnd aiken_5_defs) (rpl aiken_5_defs) (lv_in aiken_5_defs) (lv_out aiken_5_defs).    
  Proof.    
    prep_l.
    do 3 step_l.
    prep_r.
    P0 _clear current_instr.
    step_r.
    prep_exec_instr.
    unfold exec_instr_bits.
    simpl.
    repeat break_match; eauto.
    repeat break_exists.
    step_r.
    step_r.
    assert (x6 = md').
    specialize (H21 x3).
    simpl_and_clear.
    subst x6.
    finish_r.    
    P0 _clear step_through;
      P0 _clear at_code;
      P0 _clear at_code_end;
      P0 _clear not_after_label_in_code;
      P0 _clear st_rs;
      inv_state;
      P0 bump val_eq;
      P0 bump exec_instr_bits.      
    (* 2: eq_mem_tac. *)
    intros.
    unfold exec_instr_bits in *.
    remember (eval_testcond Cond_g rsl) as cond_l.    
    remember (eval_testcond Cond_g (nextinstr rsr # r1 <- (Vint zero))) as cond_r.
    specialize (H30 x3).
    repeat gentle_inv_next.
    subst a1 a0.
    subst m1 m0 m.
    clear_taut.
    unfold flags in *.
    simpl_ls_pred.
    exploit (UseBasic.eval_testcond_match rsl (nextinstr rsr # r1 <- (Vint zero)) Cond_g); eauto.
    intros.    
    destruct cond_l; try destruct b0;
    try (break_or'; try congruence; [ ]).
    - subst cond_r.
      rewrite <- H42 in H30.
      clear H42.
      collapse_match_hyp.      
      P1 _inversion Nxt.
      P0 _clear Nxt.
      split.
      intros.
      2: eq_mem_tac.
      repeat break_or_reg.
      + preg_simpl.
        repeat find_rewrite_goal.
        simpl.
        f_equal.
      + subst.
        simpl.
        preg_simpl.
        simpl.
        replace (Int.sub Int.one Int.one) with (Int.zero) by ring.
        unfold Val.and.
        break_match; simpl; intros; try congruence.
        f_equal.
        rewrite Int.and_zero.
        auto.
    - subst cond_r.
      rewrite <- H42 in H30.
      clear H42.
      collapse_match_hyp.
      P1 _inversion Nxt.
      P0 _clear Nxt.
      split.
      2: eq_mem_tac.
      intros.
      repeat break_or_reg.
      + preg_simpl.
        repeat find_rewrite_goal.
        simpl.
        f_equal.
      + subst.
        simpl.
        preg_simpl.
        simpl.
        replace (Int.sub Int.zero Int.one) with (Int.mone).
        2: unfold Int.mone; ring.
        simpl.
        unfold Val.and.
        break_match; simpl; intros; try congruence.
        P0 _simpl val_eq.
        rewrite <- H0.
        f_equal.        
        apply Int.and_mone.
        P0 _simpl val_eq.
        tauto.        
    - split.
      2: eq_mem_tac.
      intros.
      repeat break_or_reg.
      + preg_simpl.
        repeat find_rewrite_goal.
        simpl.
        repeat break_match_hyp.
        * inv_next.
          preg_simpl.
          repeat find_rewrite_goal.
          simpl. auto.
        * inv_next.
          preg_simpl.
          repeat find_rewrite_goal.
          simpl. auto.
        * inv_next.
          preg_simpl.
          repeat find_rewrite_goal.
          simpl. auto.        
      + preg_simpl.                
        repeat break_match_hyp; inv_next.
        * subst.
          preg_simpl.
          simpl.
          unfold Val.and.
          break_match; simpl; intros; congruence.
        * subst.
          preg_simpl.
          simpl.          
          unfold Val.and.
          break_match; simpl; intros; try congruence.
          P0 _simpl val_eq.
          inv_false.
        * subst.
          preg_simpl.
          simpl.          
          unfold Val.and.
          break_match; simpl; intros; try congruence.      
  Qed.

  Definition aiken_5_proofs : rewrite_proofs :=
    {|
      defs := aiken_5_defs
      ; selr := aiken_5_selr
    |}.

  Definition peep_aiken_5 : 
    concrete = fnd aiken_5_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite aiken_5_defs aiken_5_proofs.    
  Qed.

End AIKEN_5.
  
Definition aiken_5_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_aiken_5 p.
  unfold aiken_5_defs in p.
  simpl in p. 
  specialize (p c).
  do 3 (destruct c; [exact None | ]).
  destruct c; [ | exact None].

  set_instr_eq i 0%nat aiken_5_example.
  set_instr_eq i0 1%nat aiken_5_example.
  set_instr_eq i1 2%nat aiken_5_example.

  set_ireg_eq rd rd0.
  set_ireg_eq r1 rd0.

  set_testcond_eq c Cond_g.

  set_ireg_neq rd0 rd1.
  
  specialize (p rd0 rd1 n eq_refl). exact (Some p).
Defined.

Definition aiken_5 (c : code) : list StepEquiv.rewrite :=
  collect (map aiken_5_rewrite (ParamSplit.matched_pat aiken_5_example c)).
