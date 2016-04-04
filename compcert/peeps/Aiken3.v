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
Require Import StepEquiv.
Require Import Globalenvs.
Require Import Memory.
Require Import MemEq.
Require Import MemoryAxioms.
Require Import UseBasic.


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

Definition aiken_3_example :=     
            Ptest_rr ECX ECX ::
            Pjcc Cond_e xH ::
            Pmov_rr ECX EDX ::
            Plabel xH ::
            Pnop ::
            nil.

Section AIKEN_3.

  Variable concrete : code.  
  Variable r2 : ireg.
  Variable r3 : ireg.
  Variable r4 : ireg.
  Variable l : label.  
  Hypothesis r2_r3_neq : r2 <> r3.
  Hypothesis r2_r4_neq : r2 <> r4.
  Hypothesis r3_r4_neq : r3 <> r4.  

  Definition aiken_3_defs : rewrite_defs :=
    {|
      fnd :=                
        (* test %ecx, %ecx *)
        (* je .l *)
        (* mov %edx, %ebx *)
        (* .l:         *)
                Ptest_rr r3 r3 ::
                Pjcc Cond_e l ::
                Pmov_rr r2 r4 ::
                Plabel l ::
                Pnop ::
                nil
      ; rpl :=
          (* test %ecx, %ecx *)
          (* cmovne %edx, %ebx           *)
                  Ptest_rr r3 r3 ::
                  Pcmov Cond_ne r2 r4 ::
                  Pnop ::
                  Pnop ::
                  Pnop ::
                  nil
      ; lv_in := PC :: IR r2 :: IR r3 :: IR r4 :: nil
      ; lv_out := PC :: IR r4 :: IR r2 :: nil
      ; clobbered := flags
    |}.
  
  Lemma aiken_3_selr:
    StepEquiv.step_through_equiv_live (fnd aiken_3_defs) (rpl aiken_3_defs) (lv_in aiken_3_defs) (lv_out aiken_3_defs).
  Proof.    
    prep_l.
    step_l.
    step_l.
    {
      step_l.
      prep_r.
      step_r.
      prep_exec_instr.
      simpl.
      repeat break_match; eauto.
      repeat break_exists.
      step_r.
      step_r.
      step_r.
      step_r.
      assert (x6 = md').
      {
        specialize (H23 x3).
        simpl_and_clear.
      }
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
      specialize (H24 x5).      
      repeat clear_dup.      
      unfold exec_instr_bits in *.
      remember r1 as cond_l_rs.
      remember (eval_testcond Cond_e cond_l_rs) as cond_l.
      remember ((nextinstr
               (compare_ints (Val.and (rsr r3) (rsr r3)) Vzero rsr mr))) as cond_r_rs.
      remember (eval_testcond Cond_ne cond_r_rs) as cond_r.
      Ltac gentle_inv_next :=
        match goal with
          | [H: Nxt _ _ _ = Nxt _ _ _ |- _] => inversion H; clear H
        end.
      repeat gentle_inv_next.
      subst m0. subst m1.
      exploit (eval_testcond_match cond_l_rs cond_r_rs Cond_e);
        try solve [
              subst;
              subst r1;
              try eapply val_eq_nextinstr;
              try eapply val_eq_compare_ints;
              try eapply val_eq_and;
              simpl;
              try assumption;      
              try reflexivity;
              eauto 8 ].
      intro.      
      unfold jumps_to_label in *.
      rewrite H28 in H31.
      break_match_lem H31.
      break_if.
      2: inv_false.
      2: inv_false.
      clear_taut.
      subst cond_l.
      break_or'.
      congruence.
      symmetry in H11.
      eapply eval_testcond_e_neg in H11.
      Focus 2.      
      subst.
      clear -H11.
      unfold eval_testcond in *.
      simpl_match_hyp.
      inv_some.
      left.
      apply PtrEquiv.int_eq_true in H0.
      subst. unfold Vtrue.
      reflexivity.
      
      subst cond_r.
      collapse_match_hyp.
      P1 _simpl negb.
      gentle_inv_next.
      subst x4.
      unfold goto_label_bits in *.
      simpl_match_hyp.
      gentle_inv_next.
      subst m.
      P0 _clear current_instr.
      subst b0.
      subst a1.
      subst a0.

      split.
      2: eq_mem_tac.
      intros.
      repeat break_or_reg.
      + subst.
        preg_simpl.
        repeat find_rewrite_goal.
        simpl.        
        preg_simpl_hyp H41.
        preg_simpl_hyp H42.
        P0 _clear current_block.
        P0 _clear no_ptr_regs.
        simpl in *.
        rewrite H40 in H41.        
        inv_vint.
        rewrite H2 in H41.
        simpl in H41.
        inv_vint.
        f_equal.
        ring.
      + subst.
        subst r1.
        preg_simpl.
        assumption.
      + subst.
        subst r1.
        preg_simpl.
        assumption.
    }
    {
      step_l.
      step_l.
      step_l.
      prep_r.
      step_r.      
      prep_exec_instr.
      simpl.
      repeat break_match; eauto.
      repeat break_exists.
      step_r.
      step_r.
      step_r.
      step_r.      
      assert (x6 = md').
      {
        specialize (H23 x3).
        simpl_and_clear.
      }
      subst x6.
      finish_r.
      
      P0 _clear step_through;
        P0 _clear at_code;
        P0 _clear at_code_end;
        P0 _clear not_after_label_in_code;
        P0 _clear st_rs;
        P0 _clear current_block;
        P0 _clear no_ptr_regs;
        P0 _clear no_ptr_mem;
        P0 _clear match_metadata;
        P0 _clear global_perms;
        inv_state;
        P0 bump val_eq;
        P0 bump exec_instr_bits.
      specialize (H14 x5).
      repeat clear_dup.      
      unfold exec_instr_bits in *.
      remember r6 as cond_l_rs.
      remember (eval_testcond Cond_e cond_l_rs) as cond_l.
      remember ((nextinstr
               (compare_ints (Val.and (rsr r3) (rsr r3)) Vzero rsr mr))) as cond_r_rs.
      remember (eval_testcond Cond_ne cond_r_rs) as cond_r.
      repeat gentle_inv_next.      
      subst m2. subst m3. subst m0. subst m1.
      subst a3 a0 a1 a2.
      exploit (eval_testcond_match cond_l_rs cond_r_rs Cond_e);
        try solve [
              subst;
              subst r6;
              try eapply val_eq_nextinstr;
              try eapply val_eq_compare_ints;
              try eapply val_eq_and;
              simpl;
              try assumption;      
              try reflexivity;
              eauto 8 ].
      intro.
      
      unfold jumps_to_label in *.
      rewrite H28 in H31.
      assert (cond_l = Some false \/ cond_l = None).
      {
        break_match_lem H31.
        break_if.
        congruence.
        left.
        congruence.
        right.
        congruence.
      }
      clear H31.
      
      break_or'.      
      - subst cond_l.
        rewrite H21 in H5.
        gentle_inv_next.
        subst m.
        clear H10.
        break_or'.
        congruence.
        symmetry in H5.
        rewrite H21 in H5.
        eapply eval_testcond_e_neg in H5.
        Focus 2.
        subst.
        clear -H5 H0 H1 H6.
        unfold compare_ints.
        preg_simpl.
        unfold Val.cmpu.
        unfold Val.of_optbool.
        unfold eval_testcond in *.
        
        simpl_match_hyp.
        inv_some.
        preg_simpl_hyp Heqv.
        unfold Val.cmpu in *.
        unfold Val.of_optbool in *.
        break_match.
        break_if; auto.
        congruence.        
                
        subst cond_r.
        collapse_match_hyp.
        P1 _simpl negb.
        gentle_inv_next.        
        subst x4.                
        P0 _clear current_instr.
        
        split.
        2: eq_mem_tac.
        intros.
        repeat break_or_reg.
        + subst.
          preg_simpl.
          repeat find_rewrite_goal.
          simpl.
          reflexivity.
        + subst.
          subst r6.
          preg_simpl.
          assumption.
        + subst.
          subst r6.
          preg_simpl.
          assumption.
      - subst cond_l.
        rewrite H21 in H5.
        congruence.
    }      
  Qed.

  Definition aiken_3_proofs : rewrite_proofs :=
    {|
      defs := aiken_3_defs
      ; selr := aiken_3_selr
    |}.

  Definition peep_aiken_3 : 
    concrete = fnd aiken_3_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite aiken_3_defs aiken_3_proofs.
  Qed.

End AIKEN_3.
  
Definition aiken_3_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_aiken_3 p.
  unfold aiken_3_defs in p.
  simpl in p. 
  specialize (p c).
  do 5 set_code_cons c.
  set_code_nil c.
  set_instr_eq i 0%nat aiken_3_example.
  set_instr_eq i0 1%nat aiken_3_example.
  set_instr_eq i1 2%nat aiken_3_example.
  set_instr_eq i2 3%nat aiken_3_example.
  set_instr_eq i3 4%nat aiken_3_example.  
  rename_all label lb.
  rename_all ireg a.    
  set_testcond_eq c Cond_e.
  set_label_eq lb0 lb.
  set_ireg_eq a2 a1.
  set_ireg_neq a0 a.
  specialize (p a0 a1 a lb n eq_refl).
  exact (Some p).
Defined.

Definition aiken_3 (c : code) : list StepEquiv.rewrite :=
  collect (map aiken_3_rewrite (ParamSplit.matched_pat aiken_3_example c)).
