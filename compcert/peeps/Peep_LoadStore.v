Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Import Stacklayout.
Require Import Conventions.
Require Import Asm.
Require Import AsmBits.
Require Import AsmCallingConv.
Require Import MemoryAxioms.
Require Import PeekLib.
Require Import PeekTactics.
Require Import FindInstrLib.
Require Import PregTactics.
Require Import ForwardJumps.
Require Import StepIn.
Require Import StepEquiv.
Require Import ProgPropDec.
Require Import Union.
Require Import UseBasic.
Require Import PeepholeLib.
Require Import MemEq.
Require Import ValEq.
Require Import ParamSplit.
Require Import AddrmodeEq.
Require Import PeepsLib.
Require Import PeepsTactics.

Module Imp.

Definition example_addr : addrmode := (Addrmode None None (inl Int.zero)).
Definition peep_store_load_example : code :=
  Pmov_mr example_addr EAX :: Pmov_rm EAX example_addr :: nil.

Section STORE_LOAD.

  Variable concrete : code.

  Variable r : ireg.
  Variable a : addrmode.

  Definition peep_store_load_defs : rewrite_defs :=
    {|
      fnd :=
        Pmov_mr a r :: 
                Pmov_rm r a :: nil
      ; rpl :=
          Pmov_mr a r :: Pnop :: nil
      ; lv_in := PC :: IR r :: (use_addr a)
      ; lv_out := PC :: IR r ::  nil
      ; clobbered := nil
    |}.

  Lemma peep_store_load_selr :
    StepEquiv.step_through_equiv_live (fnd peep_store_load_defs) (rpl peep_store_load_defs) (lv_in peep_store_load_defs) (lv_out peep_store_load_defs).
  Proof.
    prep_l.
    step_l.
    step_l.
    prep_r.
    (* step_r can't handle building loads or stores well *)
    prep_exec_instr.

    (* manually solve subgoal *)
    instantiate (1 := mr). (* kinda annoying *)
    simpl. simpl in H33.
    unfold exec_store_bits in H33.
    break_match_hyp; try congruence.
    inv H30. inv H33.
    unfold exec_store_bits.
    unfold storev_bits in *.
    break_match_hyp; try congruence.
    erewrite eval_addrmode_bits_transf;
      try solve [intros; rewrite Hsym; auto].
    erewrite use_addr_eval_addrmode_bits; eauto; try congruence.
    simpl.
    NP _app eq_mem_store MemBits.store_bits.
    break_and.
    collapse_match.
    eauto.

    repeat break_exists.

    step_r.
    step_r.
    eexists; eexists; split.

    (* prove mem eq *)
    assert (x5 = md').
    {
      simpl in H4. unfold exec_store_bits in H4.
      specialize (H4 x3).
      break_match_hyp; try congruence.
    } idtac.
    subst.
    eapply H22.
    prep_eq.

    simpl in *.
    repeat (break_match_hyp; try congruence); subst.
    repeat opt_inv; subst. clear H19. clear H20.
    assert (m0 = m). {
      unfold exec_load_bits in H13.
      break_match_hyp; try congruence.
    } idtac.
    subst.
    split. Focus 2.
    specialize (H22 x3).
    unfold exec_store_bits in *.
    repeat break_match_hyp; try congruence.

    inv H14. inv H22.
    eapply eq_mem_storev_bits; try eassumption.
    right. 
    erewrite eval_addrmode_bits_transf;
      try solve [intros; rewrite Hsym; auto].
    symmetry.
    erewrite use_addr_eval_addrmode_bits; try apply H5; eauto; try congruence.
    erewrite eval_addrmode_bits_transf;
      try solve [intros; rewrite Hsym; auto].
    unfold storev_bits in Heqo7.
    break_match_hyp; try congruence.


    (* Prove reg eq *)
    specialize (H22 x3).
    intros. repeat break_or; try inv_false;
    simpl in *; unfold exec_load_bits in *;
    unfold exec_store_bits in *;
    repeat (break_match_hyp; try congruence);
    repeat st_inv.
    (* PC *)
    preg_simpl. rewrite Heqv. rewrite Heqv0.
    eapply val_eq_add; try eapply val_eq_add; eauto;
    try solve [simpl; reflexivity].
    (* r *)
    preg_simpl.
    (* Here we need to appeal to loading a stored value val_eq to original result *)
    admit.
  Qed.

  Definition peep_store_load_proofs : rewrite_proofs :=
    {|
      defs := peep_store_load_defs
      ; selr := peep_store_load_selr
    |}.

  Definition peep_store_load :
    concrete = fnd peep_store_load_defs ->
    StepEquiv.rewrite.
  Proof.
    
    intros.
    
    refine (
      {|
        find := fnd peep_store_load_defs;
        repl := rpl peep_store_load_defs;
        live_in := lv_in peep_store_load_defs;
        live_out := lv_out peep_store_load_defs;
        pres := preserved peep_store_load_defs;
        not_same := _;
        PC_live_out := _;
        find_nonempty := _;
        repl_nonempty := _;
        len_same := _;
        no_trace_find := _;
        no_trace_repl := _;
        no_label_out := _;
        forward_find := _;
        steps_equiv_live := selr peep_store_load_proofs;
        steps_pres_find := _;
        steps_pres_repl := _;
        measure := measure_fun;
        measure_decr := _
      |}); admit.

  Defined.

End STORE_LOAD.


Definition peep_store_load_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_store_load p.
  unfold peep_store_load_defs in p.
  simpl in p. 
  specialize (p c).
  do 2 set_code_cons c.
  set_code_nil c.
  set_instr_eq i 0%nat peep_store_load_example.
  set_instr_eq i0 1%nat peep_store_load_example.
  set_ireg_eq rs rd.
  set_addrmode_eq a a0.
  specialize (p _ _ eq_refl). exact (Some p).
Defined.

End Imp.

Module Peep.

Definition store_load (c : code) : list StepEquiv.rewrite :=
  collect (map Imp.peep_store_load_rewrite (ParamSplit.matched_pat Imp.peep_store_load_example c)).

End Peep.