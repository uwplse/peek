Require Import Coqlib.
Require Import Asm.
Require Import PeekTactics.
Require Import PeepsLib.
Require Import PregTactics.
Require Import StepIn.
Require Import AsmBits.
Require Import Values.
Require Import ValEq.
Require Import MemEq.
Require Import Integers.
Require Import PeepsTactics.
Require Import UseBasic.
Require Import Globalenvs.
Require Import Memory.


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

Definition neg_twenty := Integers.Int.repr (-20).

Definition aiken_7_example : code :=
  Pmov_mr (Addrmode (Some EBP) None (inl neg_twenty)) EAX ::
          Pmov_rm ECX (Addrmode (Some EBP) None (inl neg_twenty)) ::
          nil.

(*
TODO: Mem facts!
Mem.valid_access_store
Mem.store_access
Mem.store_valid_access_3
 *)

Section AIKEN_7.

  Variable concrete : code.
  Variable r1 : ireg.
  Variable r2 : ireg.  
  Variable a : addrmode.

  Definition aiken_7_defs : rewrite_defs :=
    {|
      fnd :=        
        (* mov %eax, -20(%ebp) *)
        (* mov -20(%ebp), %ecx *)
        Pmov_mr a r1 ::
                Pmov_rm r2 a ::
                nil
      ; rpl :=
          (* mov %eax, -20(%ebp)  *)
          (* mov %eax, %ecx       *)        
          Pmov_mr a r1 ::
                  Pmov_rr r2 r1 ::
                  nil
      ; lv_in := (PC :: IR r1 :: (use_addr a))
      ; lv_out := (PC :: IR r1 :: IR r2 :: nil)
      ; clobbered := flags
    |}.
  
  Lemma aiken_7_selr:
    StepEquiv.step_through_equiv_live (fnd aiken_7_defs) (rpl aiken_7_defs) (lv_in aiken_7_defs) (lv_out aiken_7_defs).
  Proof.
    prep_l.
    step_l.
    assert (no_ptr_regs rsl).
    {
      unfold step_fwd in *.
      break_and.
      NP app_new step_basic_corollaries step_basic.
      repeat break_and.
      unfold no_ptr in *.
      repeat break_and.
      auto.
    }
    rename H27 into Hno_ptr_regs_rsl.
    step_l.    
    prep_r.
    P0 _clear current_instr.
    prep_exec_instr.
    instantiate (1 := mr).
    {
      simpl in *.
      simpl.
      unfold exec_store_bits in *.
      unfold storev_bits in *.
      repeat (break_match_hyp; try congruence).
      erewrite eval_addrmode_bits_transf in Heqv.
      eapply use_addr_eval_addrmode_bits in Heqv; try congruence.      
      rewrite Heqv.
      app eq_mem_store Heqo.
      break_and.
      collapse_match.
      eauto.
      assumption.
      intros.
      eauto.
    }
    repeat break_exists.
    step_r.
    step_r.
    assert (x5 = md').
    {
      specialize (H21 x3).
      simpl_and_clear.
    }
    subst x5.
    finish_r.
    specialize (H21 x3).
    simpl in H21.
    unfold exec_store_bits in H21.
    unfold storev_bits in *.
    simpl_match_hyp.
    repeat gentle_inv_next.
    subst x4.
    P0 _clear step_through;
      P0 _clear at_code;
      P0 _clear at_code_end;
      P0 _clear not_after_label_in_code;
      P0 _clear st_rs;
      inv_state;
      P0 bump val_eq;
      P0 bump exec_instr_bits.
      
    simpl_and_clear.
    unfold Memory.Mem.loadv in *.
    simpl_match_hyp.
    unfold storev_bits in *.
    simpl_match_hyp.
    subst r0.
    subst a0 m0 m2.
    clear_taut.
    bump Heqv0.
    exploit (use_addr_eval_addrmode_bits (nextinstr_nf rsl) rsl); eauto.
    intros.
    2: congruence.    
    eapply val_eq_use_addr_nextinstr_nf; eauto.        
    intros.
    assert (i1 = i2) by congruence.        
    subst i2.
    assert (b1 = b2) by congruence.
    subst b2.    
    exploit load_store_bits_same; eauto.
    intro.
    split.
    intros.
    repeat break_or_reg.
    + subst.
      preg_simpl.
      repeat find_rewrite_goal.
      simpl.
      auto.
    + subst.
      copy (preg_dec r1 r2).
      P1 _inversion r1.
      * preg_simpl.
        assumption.
      * P1 _rewrite r1.
        preg_simpl.
        congruence.      
    +  subst.       
       preg_simpl.
       auto.       
    + subst.      
      app eq_mem_store Heqo1.
      break_and.
      assert (i1 = i0 /\ b0 = b1).
      exploit (use_addr_eval_addrmode_bits rsl rsr); eauto.
      congruence.      
      erewrite eval_addrmode_bits_transf.
      instantiate (1 := (env tprog)).
      intros.      
      rewrite Heqv in H34.
      inversion H34.
      split.
      auto.
      auto.
      eauto.
      repeat break_and.
      congruence.      
  Qed.

  Definition aiken_7_proofs : rewrite_proofs :=
    {|
      defs := aiken_7_defs
      ; selr := aiken_7_selr
    |}.

  Definition peep_aiken_7 : 
    concrete = fnd aiken_7_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite aiken_7_defs aiken_7_proofs.
    apply step_through_preserved_no_touch.
    2: peep_tac_aux_proofs.    
    simpl;
      unfold no_def;
      unfold no_def_instr;
      intros;
    apply not_in_preserved;
    P0 _simpl In;
    simpl.    
    repeat break_or_reg;
    simpl in *;
    repeat break_or_reg;
    simpl;
    unfold use_addr;
    repeat break_match;
    simpl in *;
    auto 20.
    apply step_through_preserved_no_touch.
    2: peep_tac_aux_proofs.    
    simpl;
      unfold no_def;
      unfold no_def_instr;
      intros;
    apply not_in_preserved;
    P0 _simpl In;
    simpl.    
    repeat break_or_reg;
    simpl in *;
    repeat break_or_reg;
    simpl;
    unfold use_addr;
    repeat break_match;
    simpl in *;
    auto 20.
  Qed.

End AIKEN_7.

Definition aiken_7_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_aiken_7 p.
  unfold aiken_7_defs in p.
  simpl in p. 
  specialize (p c).  
  do 2 set_code_cons c.
  set_code_nil c.
  set_instr_eq i 0%nat aiken_7_example.
  set_instr_eq i0 1%nat aiken_7_example.  
  set_addrmode_eq a a0.  
  specialize (p _ _ _ eq_refl). exact (Some p).
Defined.

Definition aiken_7 (c : code) : list StepEquiv.rewrite :=
  collect (map aiken_7_rewrite (ParamSplit.matched_pat aiken_7_example c)).
