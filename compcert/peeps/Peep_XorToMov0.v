Require Import Coqlib.
Require Import Asm.
Require Import PeekTactics.
Require Import UseBasic.
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

(*from chomp*)
(*xorl  %edx, %edx*)
(*movl  %edx, 0(%ebx,%esi,4)*)
Definition example_addr : addrmode := (Addrmode None None (inl zero)).
Definition peep_xor_to_mov_0_example : code :=
Pxor_r EDX :: Pmov_mr example_addr EDX :: nil.

Section XOR_TO_MOV_0.

  Variable concrete : code.
  Variable r1 : ireg.
  Variable a1 : addrmode.
  Hypothesis a1_r1_neq : ~ (In (IR r1) (use_addr a1)).

  Definition peep_xor_to_mov_0_defs : rewrite_defs :=
    {|
      fnd :=
        Pxor_r r1 ::  
               Pmov_mr a1 r1 ::
               nil
      ; rpl :=
          Pnop ::
               Pmov_mi a1 zero ::
                  nil
      ; lv_in := (PC :: (use_addr a1))
      ; lv_out := (PC :: (use_addr a1))
      ; clobbered := IR r1 :: flags
    |}.

  Lemma peep_xor_to_mov_0_selr:
    StepEquiv.step_through_equiv_live (fnd peep_xor_to_mov_0_defs) (rpl peep_xor_to_mov_0_defs) (lv_in peep_xor_to_mov_0_defs) (lv_out peep_xor_to_mov_0_defs).
  Proof.    
    prep_l.
    step_l.
    step_l.
    prep_r.
    step_r.

    simpl in H33.
    unfold exec_store_bits in *.
    unfold storev_bits in *.
    repeat (break_match_hyp; try congruence).      
    (* prep_exec_instr. *)
    assert (exists
     (rs' : regset) (m' : Memory.Mem.mem) (md'0 : MemoryAxioms.allocator_metadata),
     (forall fn : function,
     exec_instr_bits (env tprog) md' fn (Pmov_mi a1 zero) b
                     (nextinstr rsr) mr = Nxt rs' m' md'0) /\
     (MemBits.store_bits AST.Mint32 mr b0 (Int.unsigned i0) (Vint zero) = Some m') /\
     eval_addrmode_bits (env tprog) md' a1 (nextinstr rsr) = Vptr b0 i0).
    {                         
      simpl.
      unfold storev_bits in *.
      erewrite eval_addrmode_bits_transf in Heqv.
      2: eauto.
      eapply use_addr_eval_addrmode_bits in Heqv; try congruence.
      simpl_and_clear.
      subst a0.
      rewrite Heqv.      
      app MemEq.eq_mem_store Heqo.
      break_and.
      rewrite H34.
      do 3 eexists; split; eauto.      
      inv_state.
      eauto.
      subst.
      preg_simpl.
      auto.
      repeat gentle_inv_next.
      subst a0 m1.
      simpl_and_clear.
      subst m0 a.
      intros.      
      destruct (preg_eq p r1); try congruence.      
      unfold use_addr in H21.
      repeat break_match_hyp; simpl in H21; repeat break_or_reg; try inv_false; preg_simpl;
      apply H13; simpl; auto.
    }    
    repeat break_exists.
    repeat break_and.
    rename H38 into Hstr.
    rename H39 into Haddr.
    step_r.
    assert (x5 = md').
    specialize (H21 x3).
    simpl_and_clear.
    subst x5.
    finish_r.
    split.
    intros.
    specialize (H21 x3).
    simpl_and_clear.
    unfold storev_bits in *.
    simpl_match_hyp.
    inv_state.
    repeat break_or_reg.
    - preg_simpl.      
      repeat find_rewrite_goal.
      simpl.
      reflexivity.
    - simpl_and_clear.
      repeat gentle_inv_next.
      apply val_eq_nextinstr_nf.
      intros.
      bump H13.
      bump a1_r1_neq.
      copy H21.
      unfold use_addr in H21.
      unfold use_addr in H13.
      repeat break_match;
      simpl in H21;
      simpl in H13;
      repeat break_or_reg;
      preg_simpl;
      apply H33;
      simpl;
      auto.
    - specialize (H21 x3).
      simpl_and_clear.
      unfold storev_bits in *.
      simpl_match_hyp.
      inv_state.      
      preg_simpl_hyp Heqo.
      eapply MemEq.eq_mem_store in Heqo; eauto.
      repeat break_exists.
      break_and.
      2: simpl; reflexivity.      
      gentle_inv_next.
      subst.
      P0 bump MemBits.store_bits.
      inv Haddr.
      replace (Vzero) with (Vint zero) in *.
      rewrite H38 in H34.
      inv_some.
      auto.      
      auto.
  Qed.

  Definition peep_xor_to_mov_0_proofs : rewrite_proofs :=
    {|
      defs := peep_xor_to_mov_0_defs
      ; selr := peep_xor_to_mov_0_selr
    |}.

  Definition peep_peep_xor_to_mov_0 : 
    concrete = fnd peep_xor_to_mov_0_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite peep_xor_to_mov_0_defs peep_xor_to_mov_0_proofs.
    peep_tac_pres;
    try solve [
          right;
          apply in_or_app; right;
          apply in_cons;
          apply in_or_app; right;
          simpl; auto 20
        ].
    peep_tac_pres;
    try solve [
          right;
          apply in_or_app; right;
          apply in_cons;
          apply in_or_app; right;
          simpl; auto 20
        ].
  Qed.

End XOR_TO_MOV_0.

Definition peep_xor_to_mov_0_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_peep_xor_to_mov_0 p.
  unfold peep_xor_to_mov_0_defs in p.
  simpl in p. 
  specialize (p c).
  do 2 set_code_cons c.
  set_code_nil c. 
  set_instr_eq i 0%nat peep_xor_to_mov_0_example.
  set_instr_eq i0 1%nat peep_xor_to_mov_0_example.
  set_ireg_eq rd rs.  
  Lemma preg_dec':
    forall p q : preg, {p = q} + {p <> q}.
  Proof.
    intros.
    copy (preg_dec p q).
    auto.
  Qed.
  copy (in_dec preg_dec' rs (use_addr a)).
  inversion H.
  exact None.

  specialize (p _ _ H0 eq_refl). exact (Some p).
Defined.

Definition xor_to_mov_0 (c : code) : list StepEquiv.rewrite :=
  collect (map peep_xor_to_mov_0_rewrite (ParamSplit.matched_pat peep_xor_to_mov_0_example c)).
