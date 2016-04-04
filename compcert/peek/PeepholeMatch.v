Require Import Coqlib.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Asm.
Require Import Integers.
Require Import Maps.
Require Import Errors.
Require Import Machregs.

Require Import ProofIrrelevance.

Require Import PeekLiveness.
Require Import SplitLib.
Require Import FindInstrLib.
Require Import StepLib.
Require Import SameBlockLib.
Require Import PeekTactics.
Require Import PregTactics.
Require Import AsmCallingConv. 
Require Import Union.
Require Import StepIn.
Require Import PeekLivenessProof.
Require Import Use.
Require Import PeekLib. 
Require Import StepEquiv. (* Where rewrite is defined *)
Require Import ProgPropDec. 
Require Import ForwardJumps. 
Require Import Zlen.

Require Import AsmBits.
Require Import MemoryAxioms.

Require Import Peephole.
Require Import PeepholeLib.
Require Import PeepholeDec.

Require Import ValEq.
Require Import MemEq.

Section PRESERVATION.


  
Variable rwr: rewrite.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSF: transf_program rwr prog = OK tprog.
Hypothesis CALLING_CONV : calling_conv_correct_bits prog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Definition outside_range := PeepholeDec.outside_range rwr prog.
Definition in_transf := PeepholeDec.in_transf rwr prog.
Definition at_entry := PeepholeDec.at_entry rwr prog.
Definition match_states := PeepholeDec.match_states rwr prog.
Definition transf_index := PeepholeLib.transf_index rwr prog.
Definition transf_idx_end := PeepholeLib.transf_idx_end rwr prog.


Lemma match_states_match_live :
  forall s1 s2,
    match_states s1 s2 ->
    outside_range s1 ->
    match_live liveness_fun_f prog s1 s2.
Proof.
  intros.
  inv H.
  * simpl. intros. split; auto.
    break_and; auto.
    split; break_and; auto.
    split; auto.
    split; auto.
    intros. apply H5. unfold ge in *.
    unify_PC. unify_psur. assumption.
  * assert (at_entry (State_bits rs m md)).
      econstructor; eauto.
      apply at_entry_not_out in H.
      apply H in H0. inv_false.
  * assert (in_transf (State_bits rsl' m' md')).
    econstructor. Focus 3. apply H4.
    Focus 3. apply H5. eauto. eauto.
    eauto. eauto.
    app outside_not_in H0.
    apply H0 in H. inv_false.
  * simpl. intros. split; auto.
    break_and; eauto.
    split; break_and; auto.
    split; auto.
    split; auto.
    intros. 
    apply H4. unfold ge in *. unify_PC. unify_psur.
    replace (Int.intval) with (Int.unsigned) in * by auto.
    rewrite Int.unsigned_zero in *. unfold ge in *.
    assumption.
Qed.


Lemma function_blocks_same :
  forall b,
    Genv.find_funct_ptr (Genv.globalenv prog) b = None ->
    Genv.find_funct_ptr (Genv.globalenv tprog) b = None.
Proof.
  intros.
  unfold transf_program in *.
  repeat break_match_hyp; try congruence.
  inversion TRANSF.
  destruct (Genv.find_funct_ptr
              (Genv.globalenv (transform_program (transf_fundef rwr) prog)) b) eqn:?; try reflexivity.

  app Genv.find_funct_ptr_rev_transf Heqo0.
  break_and. congruence.
Qed.

Lemma is_global_translated :
  forall b ofs,
    is_global (Genv.globalenv prog) b ofs <->
    is_global (Genv.globalenv tprog) b ofs.
Proof.
  intros. split; intros.
  - unfold is_global in *.
    break_or.
    * left. unfold in_code_range in *.
      break_match_hyp; try inv_false.
      app functions_translated Heqo.
      collapse_match.
      break_match_hyp. simpl.
      destruct f0. simpl.
      unfold Zlen.zlen. rewrite length_pres.
      unfold Zlen.zlen in *.
      simpl in *. omega.
      simpl. omega.
    * right.
      unfold in_var_range in *.
      break_match_hyp; try inv_false.
      erewrite varinfo_preserved; eauto.
      collapse_match. omega.
  - unfold is_global in *.
    break_or.
    * left.
      unfold in_code_range in *.
      break_match. app functions_translated Heqo.
      rewrite Heqo in H0.
      
      unfold transf_fundef in *.
      destruct f; simpl in *.
      destruct f; simpl in *.
      unfold zlen in *.
      rewrite length_pres in H0.
      assumption.
      assumption.
      
      app function_blocks_same Heqo.
      rewrite Heqo in *. inv_false.
    * right.
      unfold in_var_range in *.
      erewrite <- varinfo_preserved; eauto.
Qed.

Lemma global_perms_translated :
  forall m,
    global_perms (Genv.globalenv prog) m ->
    global_perms (Genv.globalenv tprog) m.
Proof.
  intros. unfold global_perms in *.
  intros. eapply H.
  rewrite is_global_translated. eauto.
Qed.

(* MOVE THESE TO MEMORY AXIOMS *)
Axiom md_ec'_ge :
  forall md ge1 ge2 ef vargs m t vl m',
    external_call' ef ge1 vargs m t vl m' ->
    external_call' ef ge2 vargs m t vl m' ->
    md_ec' md ef ge1 vargs m t vl m' = md_ec' md ef ge2 vargs m t vl m'.

Axiom md_ec_ge :
  forall md ge1 ge2 ef vargs m t vl m',
    external_call ef ge1 vargs m t vl m' ->
    external_call ef ge2 vargs m t vl m' ->
    md_ec md ef ge1 vargs m t vl m' = md_ec md ef ge2 vargs m t vl m'.


Lemma step_outside :
  forall st t st',
    step_bits (Genv.globalenv prog) st t st' ->
    outside_range st ->
    step_bits (Genv.globalenv tprog) st t st'.
Proof.
  intros. inv_step H.
  * subst st. subst st'.
    app functions_translated H5.
    destruct f. simpl in *.
    app instrs_translated H6.
    econstructor; eauto.
    destruct i; simpl in H7; simpl;
    try assumption;
    repeat break_match_hyp;
    try (erewrite symbol_address_pres; eauto);
    simpl; eauto;
    try find_rewrite; simpl; eauto;
    try eapply exec_load_bits_pres; eauto;
    try eapply exec_store_bits_pres; eauto;
    try eapply exec_big_load_bits_pres; eauto;
    try eapply exec_big_store_bits_pres; eauto;
    try erewrite eval_addrmode_no_ptr_pres; eauto;
    try eapply goto_label_pres; eauto;
    try find_rewrite; eauto; unfold is_label_instr in *; eauto.
    erewrite <- eval_addrmode_bits_pres in Heqo; eauto.
    rewrite Heqo. eauto. 
    erewrite <- eval_addrmode_bits_pres in Heqo; eauto.
    rewrite Heqo. eauto.
    
    app list_nth_z_in Heqo.
    find_rewrite. eauto.

    eapply global_perms_translated; eauto.
    
  * subst st. subst st'.
    app functions_translated H3.
    destruct f; simpl in *.
    app instrs_translated H4.

    erewrite md_ec'_ge.
    eapply exec_step_builtin_bits; eauto.
    inv H5.
    eapply external_call_symbols_preserved_gen in H14.
    econstructor; eauto.
    intros. unfold Senv.find_symbol.
    simpl. eapply symbols_preserved; eauto.
    intros. unfold Senv.public_symbol. simpl.
    eapply public_symbols_preserved; eauto.
    intros. unfold Senv.block_is_volatile. simpl.
    unfold Genv.block_is_volatile.
    erewrite varinfo_preserved. unfold ge.
    reflexivity. eauto.
    eapply global_perms_translated; eauto.
    assumption.
    eapply external_call_symbols_preserved'; eauto.
    intros. erewrite symbols_preserved; eauto.
    intros. erewrite public_symbols_preserved; eauto.
    intros. erewrite varinfo_preserved; eauto.
    
  * subst st. subst st'. 
    app functions_translated H5.
    destruct f; simpl in *.    
    app instrs_translated H6.
    app eval_annot_args_bits_pres H7.
    name H8 Horig_call.
    eapply external_call_symbols_preserved_gen in H8; try (intros; apply symbols_preserved).
    instantiate (1 := (Genv.globalenv tprog)) in H8.
    erewrite md_ec_ge; try instantiate (1 := (Genv.globalenv tprog)); eauto.
    eapply exec_step_annot_bits; eauto.
    eapply global_perms_translated; eauto.
    intros. unfold Senv.public_symbol. simpl.
    intros. eapply symbols_preserved; eauto.
    eapply public_symbols_preserved; eauto.
    intros. unfold Senv.block_is_volatile. simpl.
    unfold Genv.block_is_volatile.
    erewrite varinfo_preserved.
    reflexivity.
    exact TRANSF.
    
  * subst st. subst st'. 
    app functions_translated H3.
    unfold transf_fundef in H3.
    name H5 Horig_call.
    
    eapply external_call_symbols_preserved' in H5; try (intros; apply symbols_preserved).
    erewrite md_ec'_ge;
      try instantiate (1 := Genv.globalenv tprog);
      try instantiate (1 := Genv.globalenv tprog) in H5;
      eauto.
    
    eapply exec_step_external_bits; eauto.
    eapply global_perms_translated; eauto.
    intros. unfold Senv.public_symbol. simpl.
    intros. eapply symbols_preserved; eauto.
    eapply public_symbols_preserved; eauto.
    intros. erewrite varinfo_preserved.
    reflexivity. exact TRANSF.
Qed.

Lemma measure_decr_entry_in :
  forall s s' t,
    at_entry s ->
    in_transf s' ->
    step_bits (Genv.globalenv prog) s t s' ->
    (measure rwr (transf_idx_end s') s' < measure rwr (transf_idx_end s) s)%nat.
Proof.
  name (measure_decr rwr) mdr.

  intros.
  app transf_step_same_block H1.
  destruct s. destruct s'.
  inv H. inv H0. inv H1.
  inv H. inv H0.
  repeat unify_PC.
  repeat unify_psur.
  assert (at_entry (State_bits rsl m1 md)).
  econstructor; eauto.
  app transf_step_same_block H11.
  inv H11.
  inv H1. inv H6.
  
  NP _app star_step_in_same_block star. subst b1.

  repeat unify_PC. repeat unify_psur.
  eapply transf_range_unique in H10; try eapply H8; eauto.
  break_and. subst j.
  assert (in_transf (State_bits rs' m' md')).
  econstructor; eauto.
  rewrite H5. eauto.

  name (conj H1 H12) Hstin.
  rewrite <- st_in_eq in Hstin.
  app star_step_in_in' Hstin.

  unfold transf_idx_end. unfold PeepholeLib.transf_idx_end.
  repeat collapse_match.
  inv Hstin. inv H13.
  repeat unify_PC. repeat unify_psur.
  unfold fundef in *.
  inv H8. repeat break_and.
  unfold fundef in *.
  repeat collapse_match.
  
  unfold transf_code in H15.
  rewrite H8 in H15.
  app split_pat_spec H8.
  break_match_hyp.
  eapply mdr; eauto.
  split. eapply has_no_PC_overflow; eauto.
  unfold transf_program in *.
  repeat break_match_hyp; inversion TRANSF; eauto.
  app is_proper_check_sound Heqb0.
  break_and.
  unfold is_proper_rewrite_location in *.
  repeat break_and.
  unfold not_after_label. intros.
  econstructor; eauto;
  inv H46;
  inv H41;
  repeat unify_PC;
  repeat unify_psur;
  repeat unify_find_funct_ptr;
  simpl in H30;
  eapply list_eq_middle_therefore_eq in H13; eauto;
  eapply list_eq_middle_therefore_eq in H30; eauto;
  repeat break_and;
  subst;
  eauto;
  eapply list_eq_middle_therefore_eq in H30; congruence.
  
  exists 0.
  econstructor; eauto.
  omega.

  name (find_nonempty rwr) fn.
  destruct (find rwr); try congruence.
  rewrite zlen_cons. name (zlen_nonneg _ c4) zlnc. omega.


  exists ofs.
  econstructor; eauto.
  omega.


  rewrite H8 in H15.
  eapply list_neq in H15. inv_false.
  apply (not_same rwr).

Qed.

Lemma in_transf_in_code :
  forall st i j,
    in_transf st ->
    transf_index st i j ->
    in_code i (find rwr) ge st.
Proof.
  intros. inv H.
  unfold transf_index in H0.
  unfold PeepholeLib.transf_index in *.
  specialize (H0 _ _ _ eq_refl).
  name (conj H6 H5) Hstin.
  rewrite <- st_in_eq in Hstin.
  app star_step_in_in' Hstin.
  inv Hstin. inv H8.
  assert (at_entry (State_bits rsl m md)) by (econstructor; eauto).
  app transf_step_same_block H4.
  inv H4.
  inv H11. inv H12.
  repeat unify_PC.
  repeat unify_psur.
  app star_step_in_same_block H6.
  subst.
  
  specialize (H0 _ _ _ H13 H14).
  eapply transf_range_unique in H0; try apply H3.
  break_and. subst.
  rewrite <- H9.
  econstructor.
  Focus 2.
  econstructor; eauto.
  omega.
Qed.


Lemma measure_decr_rewr :
  forall s1 s1' t i,
    in_transf s1' ->
    transf_index s1' i (i + zlen (find rwr)) ->
    in_transf s1 ->
    transf_index s1 i (i + zlen (find rwr)) ->
    step_bits (Genv.globalenv prog) s1 t s1' ->
    ((measure rwr (i + zlen (find rwr))) s1' < (measure rwr (i + zlen (find rwr))) s1)%nat.
Proof.
  intros.
  eapply (measure_decr rwr); eauto.
  Focus 2. app in_transf_in_code H1.
  inv H1. eauto.
  Focus 2. app in_transf_in_code H.
  inv H. eauto.
  
  split.
  unfold transf_program in TRANSF.
  repeat break_match_hyp; inversion TRANSF.
  auto.

  unfold not_after_label.
  intros. subst.

  unfold transf_index in H2.
  unfold PeepholeLib.transf_index in H2.
  
  specialize (H2 _ _ _ eq_refl _ _ _ H5 H6).
  inv H2.
  unify_find_funct_ptr.
  break_and.
  unfold transf_code in H4.
  rewrite H2 in H4.
  app split_pat_spec H2.
  eapply list_eq_middle_therefore_eq in H2; try omega.
  break_and. subst.
  
  break_match_hyp.
  Focus 2. eapply list_neq in H4. inv_false.
  apply (not_same rwr).
  
  app is_proper_check_sound Heqb0.
  break_and.

  unfold is_proper_rewrite_location in H12.
  repeat break_and; eauto.
Qed.

Lemma in_transf_step_match :
  forall sl sl' sr,
    match_states sl sr ->
    in_transf sl ->
    in_transf sl' ->
    step_bits (Genv.globalenv prog) sl E0 sl' ->
    match_states sl' sr.
Proof.

  intros.
  name H Hmatch.
  inv H.
  * app outside_not_in H6.
    app H6 H0. inv_false.
  * assert (at_entry (State_bits rs m md)).
      econstructor; eauto.
    app at_entry_not_in H.
    app H H0. inv_false.
  * destruct sl'.

    
    
    assert (step_in (Int.unsigned i) (find rwr) (Genv.globalenv prog) (State_bits rsl' m' md') E0 (State_bits r m a)).
    {
      econstructor; eauto.
      name (conj H9 H8) Hstin.
      rewrite <- st_in_eq in Hstin.
      app star_step_in_in' Hstin.

      app transf_step_same_block H2.
      assert (Hentry : at_entry (State_bits rsl ml md)) by (econstructor; eauto).
      app transf_step_same_block H7.

      inv H8. inv H2.
      repeat match goal with
               | [ H : State_bits _ _ _ = State_bits _ _ _ |- _ ] => inv H
             end;
        repeat unify_PC;
        repeat unify_psur.
      inv H1.
      assert (Hentry2 : at_entry (State_bits rsl m md)) by (econstructor; eauto).
      name (conj H26 H25) Hstin.
      rewrite <- st_in_eq in Hstin.
      app star_step_in_in' Hstin.
      app transf_step_same_block H24.
      inv H18.
      inv H24. inv H8. inv H18.
      inv H15.
      repeat match goal with
               | [ H : State _ _ = State _ _ |- _ ] => inv H
             end;
        repeat unify_PC;
        repeat unify_psur.
      
      app star_step_in_same_block H26.
      subst b0.

      app star_step_in_same_block H9. subst b2.

      inv H7. inv H9. inv H21.
        repeat unify_PC;
        repeat unify_psur.

        eapply transf_range_unique in H23; try apply H6.
        break_and. congruence.

        right. econstructor; eauto.
      
    }
    
    eapply inside; try eapply star_right;
    try apply H9; try apply H2; try apply H7; eauto.

  * inv H0.
    app transf_step_same_block H14.
    inv H14.
    find_inversion. find_inversion.
    repeat unify_PC. repeat unify_psur.
    app star_step_in_same_block H16.
    subst b1. inv H13.
    
    unify_find_funct_ptr.

    right. econstructor; eauto.
Qed.

Lemma zlen_same :
  zlen (find rwr) = zlen (repl rwr).
Proof.
  unfold zlen. rewrite (len_same rwr).
  reflexivity.
Qed.

Lemma at_entry_match :
  forall rs m md rs' m' md',
    at_entry (State_bits rs m md) ->
    match_states (State_bits rs m md) (State_bits rs' m' md') ->
    (forall reg, In reg (live_in rwr) ->
                 val_eq (rs reg) (rs' reg)) /\ mem_eq md m m'.
Proof.
  intros.
  inv H0.
  * app at_entry_not_out H.
    app H H10. inv_false.
  * split; eauto.
    intros.
    apply H11.
    inv H10. break_and.
    unfold transf_code in H4.
    assert (c1 ++ find rwr ++ c2 <> c1 ++ repl rwr ++ c2).
    apply list_neq. apply (not_same rwr).
    repeat break_match_hyp; try congruence.
    inv H2.
    unfold is_proper_location_check in Heqb0.
    repeat break_match_hyp; try congruence.
    Focus 2.
    inv H2. app split_pat_spec Heqo.
    congruence.
    repeat break_and.
    unfold liveness_check_correct in l0.
    repeat break_and.
    app i2 H0.
    unfold liveness_fun_f.
    repeat unify_find_funct_ptr.
    rewrite p1.
    app split_pat_spec Heqo.
    rewrite Heqo. rewrite Heqo0.
    rewrite H3. eauto.
  * assert (in_transf (State_bits rs m md)).
    econstructor; try apply H11; eauto.
    app at_entry_not_in H.
    app H H0. inv_false.
  * inv H. unify_PC.
    unify_psur.
    inv H5. unify_find_funct_ptr.
Qed.

Lemma transf_did_happen :
  forall b f x y,
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    transf_range rwr prog b x y ->
    transf_code rwr (fn_code f) <> fn_code f.
Proof.
  intros. inv H0.
  unfold ge in *. unfold fundef in *.
  unify_find_funct_ptr.
  simpl. break_and.
  rewrite H1.
  app split_pat_spec H0.
  rewrite H0.
  apply list_neq.
  name (not_same rwr) ns. congruence.
Qed.

Lemma entry_or_in_range :
  forall rs m md bits b i x y,
    (at_entry (State_bits rs m md) \/ in_transf (State_bits rs m md)) ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,i) ->
    transf_range rwr prog b x y ->
    x <= Int.unsigned i < y.
Proof.
  intros. break_or.
  inv H3.
  unify_PC. unify_psur.
  eapply transf_range_unique in H2; try eapply H8.
  break_and. subst.
  inv H8. rewrite H2.
  rewrite zlen_app.
  name (zlen_find rwr) zlnf. omega.
  inv H3.
  assert (at_entry (State_bits rsl m0 md0)) by (econstructor; eauto).
  app transf_step_same_block H9.
  inv H9. inv H4. inv H5. 
  repeat unify_PC.
  repeat unify_psur.
  app star_step_in_same_block H11. subst b1.
  name (conj H4 H10) Hstin.
  rewrite <- st_in_eq in Hstin.
  app star_step_in_in' Hstin.
  inv Hstin. inv H9.
  repeat unify_PC.
  repeat unify_psur.
  eapply transf_range_unique in H8; try eapply H2.
  break_and. subst.
  inv H2. repeat unify_PC. repeat unify_psur.
  unfold ge in *.
  repeat unify_find_funct_ptr.
  rewrite zlen_app. name (zlen_find rwr) zlnf.
  
  omega.
Qed.

(* TODO: Move somewhere higher up *)
Lemma at_code_in_range :
  forall z c ofs prog rs m md bits b i,
    no_PC_overflow_prog prog ->
    at_code z c ofs (Genv.globalenv prog) (State_bits rs m md) ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,i) ->
    in_code_range (Genv.globalenv prog) b i.
Proof.
  intros. inv H0. unfold in_code_range.
  unfold fundef in *.
  unify_PC. unify_psur.
  collapse_match.
  find_rewrite.
  repeat rewrite zlen_app.
  name (zlen_nonneg _ c) zlnc.
  name (zlen_nonneg _ c1) zlnc1.
  name (zlen_nonneg _ c2) zlnc2.

  unfold no_PC_overflow_prog in H.
  assert (code_of_prog (fn_code fd) prog0).
  unfold code_of_prog. NP _app Genv.find_funct_ptr_inversion Genv.find_funct_ptr.
  destruct fd. eauto.
  NP1 _app H code_of_prog.
  unfold no_PC_overflow in *.
  

  assert (zlen c1 + ofs >= 0 /\ zlen c1 + ofs < zlen (fn_code fd)). {
    split; try omega. rewrite H15. repeat rewrite zlen_app. omega. }
                                                                    app in_range_find_instr H3.
  
  app H0 H3; omega.
Qed.    


Lemma straightlineish_single_exit :
  forall rs m md rs' m' md' instr,
    step_t (instr :: nil) ge (State_bits rs m md) E0 (State_bits rs' m' md') ->
    forall z ofs,
      at_code z (find rwr) ofs ge (State_bits rs m md) ->
      rs' PC = (nextinstr rs) PC ->
      (in_transf (State_bits rs m md) \/ at_entry (State_bits rs m md)) ->
      outside_range (State_bits rs' m' md') ->
      forall bits b i,
        rs PC = Values.Vint bits ->
        psur md bits = Some (b,i) ->
        transf_range rwr prog b z (z + zlen (find rwr)) ->
        exists bits' i',
          rs' PC = Values.Vint bits' /\
          psur md' bits' = Some (b,i') /\
          Int.unsigned i' = z + zlen (find rwr).
Proof.
  intros.
  assert (z <= Int.unsigned i < z + zlen (find rwr)).
  {
    eapply entry_or_in_range; eauto. break_or; eauto.
  }
  preg_simpl_hyp H1. rewrite H4 in H1.
  simpl in H1.

  NP _app step_t_md_extends step_t.
  NP _app step_t_md step_t; try congruence.
  NP _app step_t_gp step_t; try congruence.
  repeat break_and.
  app psur_add_one H5.

  eexists; eexists; split; eauto; split; eauto.

  name H6 Htransf_range. inv H6.
  assert (Hrange : Int.unsigned i >= 0 /\ Int.unsigned i < zlen (c1 ++ find rwr ++ c2)).
  repeat rewrite zlen_app. name (zlen_find rwr) zlnf.
  name (zlen_nonneg _ c2) zlnc. name (zlen_nonneg _ c1) zlnc1. omega.
  rewrite in_range_find_instr in Hrange.
  break_exists.
  unfold Int.add.
  rewrite Int.unsigned_one.
  
  erewrite unsigned_repr_PC; eauto.
  Focus 2. unfold transf_program in *. repeat break_match_hyp; inversion TRANSF; eauto.
  Focus 2. left. replace (Int.unsigned i + 1 - 1) with (Int.unsigned i) by omega.
  simpl. repeat break_and.
  NP _app split_pat_spec split_pat. subst c. eauto.

  
  inv H3.
  break_exists. break_and.
  repeat unify_PC.
  repeat unify_psur.
  simpl in *. unfold ge in *. unfold fundef in *.
  repeat unify_find_funct_ptr.
  destruct H17.
  Focus 2. app transf_did_happen Htransf_range.
  simpl in Htransf_range. congruence.

  repeat break_exists.
  break_and. 
  eapply transf_range_unique in H15; try eapply Htransf_range.
  break_and. subst.
  
  unfold Int.add in H17. rewrite Int.unsigned_one in H17.
  erewrite unsigned_repr_PC in H17; eauto.

  omega.

  eapply has_no_PC_overflow; eauto.

  left. replace (Int.unsigned i + 1 - 1) with (Int.unsigned i) by omega.
  simpl. break_and.
  NP _app split_pat_spec split_pat. subst c. eauto.
  

  eapply at_code_in_range; eauto.
  eapply has_no_PC_overflow; eauto.
  app step_t_to_at_code_0 H10.
  inv H10.
  repeat unify_PC. repeat unify_psur.
  eapply in_range_PC; eauto.
  eapply has_no_PC_overflow; eauto.
  rewrite H21. rewrite H28.
  rewrite find_instr_append_head by omega.
  simpl. reflexivity.
Qed.



Lemma jump_to_label_contra :
  forall rs m rs' m' instr md md',
    step_t (instr :: nil) ge (State_bits rs m md) E0 (State_bits rs' m' md') ->
    forall z ofs bits b i fd,
      at_code z (find rwr) ofs ge (State_bits rs m md) ->
      rs PC = Values.Vint bits ->
      psur md bits = Some (b,i) ->
      transf_range rwr prog b z (z + zlen (find rwr)) ->
      Genv.find_funct_ptr ge b = Some (Internal fd) ->
      (exists jmp l, goto_label_bits md fd l b rs m = Nxt rs' m' md' /\
      find_instr (Int.unsigned i) (fn_code fd) = Some jmp /\
      is_label_instr jmp l) ->
      (in_transf (State_bits rs m md) \/ at_entry (State_bits rs m md)) ->
      outside_range (State_bits rs' m' md') ->
      False.
Proof.
  intros.
  repeat break_exists.
  repeat break_and.
  unfold goto_label_bits in *.
  repeat break_match_hyp; try state_inv.

  assert (HnoPC : no_PC_overflow_prog prog) by (
  eapply has_no_PC_overflow; eauto).
  
  assert (psur md' i0 = Some (b,Int.repr z0)). {
  NP _app step_t_md step_t; try congruence.
  NP _app step_t_gp step_t; try congruence.
  repeat break_and.
  erewrite weak_valid_pointer_sur; eauto.
  split; eauto.
  NP1 _app global_perms_valid_globals global_perms.
  unfold valid_globals in *.
  eapply Memory.Mem.weak_valid_pointer_spec. right.
  NP _app label_pos_find_instr label_pos.
  erewrite unsigned_repr_PC; eauto.
  erewrite <- (unsigned_repr_PC _ _ (z0-1)); eauto.
  eapply H11.
  NP _app label_pos_find_instr label_pos.
  unfold is_global. left.
  unfold in_code_range. collapse_match.
  apex in_range_find_instr Heqo.
  erewrite unsigned_repr_PC; eauto.
  omega. 
  }


  
  assert (z <= Int.unsigned i < z + zlen (find rwr)).
  {
    inv H1.
    eapply entry_or_in_range; eauto; break_or; eauto.
  }

  name H3 Htransf.
  inv H3. repeat break_and.
  name H13 Htc.
  unfold transf_code in H13.
  rewrite H12 in H13. break_match_hyp.
  Focus 2. app transf_did_happen Htransf. simpl in Htransf. congruence.
  app is_proper_check_sound Heqb0.
  repeat break_and. unfold is_proper_rewrite_location in *.
  repeat break_and.
  unfold ge in *. unfold fundef in *.
  repeat unify_find_funct_ptr.
  simpl in *.
  app split_pat_spec H12. subst c.

  assert (z0 < zlen c1 \/ z0 >= zlen (c1 ++ find rwr)).
  {
    inv H7. preg_simpl_hyp H30. inv H30.
    break_exists. break_and.
    inv H1.
    repeat unify_PC. repeat unify_psur.
    unfold ge in *. unfold fundef in *.
    repeat unify_find_funct_ptr.

    destruct H12. Focus 2. app transf_did_happen Htransf.
    simpl in Htransf. congruence.
    repeat break_exists.
    repeat break_and.
    eapply transf_range_unique in H1; try apply Htransf.
    break_and. subst.
    assert (Int.unsigned (Int.repr z0) = z0).
    erewrite unsigned_repr_PC; eauto.
    unfold transf_program in TRANSF.
    repeat break_match_hyp; inversion TRANSF; eauto.
    app label_pos_find_instr Heqo.
    rewrite H1 in *. omega.
  }
  destruct H12.
  eapply no_labels_jump_out_contra_c1; eauto; try omega.
  eapply no_labels_jump_out_contra_c2; eauto; try omega.

Qed.

Lemma straightline_step_t_nextinstr :
  forall i ge rs m md t rs' m' md',
    straightline i ->
    step_t (i :: nil) ge (State_bits rs m md) t (State_bits rs' m' md') ->
    rs' PC = nextinstr rs PC.
Proof.
  intros.
  copy H0. inv H1.
  inv H10. inv H4.
  app straightline_step_t H0.
  break_instr_exec i;
    preg_simpl;
    try reflexivity;
    try inv_false;
    repeat break_match;
    preg_simpl;
    try congruence.
  simpl in Heqo.
  inv Heqo.
Qed.
        

Lemma single_exit :
  forall rs m rs' m' bits b i x y md md',
    (in_transf (State_bits rs m md) \/ at_entry (State_bits rs m md)) ->
    outside_range (State_bits rs' m' md') ->
    step_bits (Genv.globalenv prog) (State_bits rs m md) E0 (State_bits rs' m' md') ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,i) ->
    transf_range rwr prog b x y ->
    exists bits' i',
      rs' PC = Values.Vint bits' /\
      psur md' bits' = Some (b,i') /\
      Int.unsigned i' = y.
Proof.
  intros.
  assert (exists ofs, at_code x (find rwr) ofs ge (State_bits rs m md)).
  {
    break_or. eapply in_transf_in_code in H5.
    Focus 2. unfold transf_index. unfold PeepholeLib.transf_index.
    intros. inv H.
    repeat unify_PC. repeat unify_psur. apply H4.
    inv H5. eexists; apply H6.
    inv H5. repeat unify_PC.
    repeat unify_psur.
    eapply transf_range_unique in H4; try eapply H10.
    break_and. subst.
    inv H10. exists 0.
    rewrite H4. econstructor; eauto. omega.
    name (zlen_find rwr) zln. omega.
    simpl. break_and. app split_pat_spec H3.
  }

  assert (y = x + zlen (find rwr)).
  {
    inv H4.
    rewrite zlen_app.
    reflexivity.
  }
  subst y.
  break_exists.
  app step_at_step_t H5.
  break_and.
  rewrite find_instr_in in H7.
  break_exists.
  name (instr_class x1) ic.
  name (forward_find rwr) ff.
  unfold only_forward_jumps in ff.
  repeat break_and.
  unfold no_calls in *.
  unfold no_trace_code in *.
  destruct ic;
    try destruct H11;
    try destruct H11;
    app H9 H7;
    try app H8 H;
    try app H8 H12;
    try congruence;
    try solve [app no_trace_trace H7; try inv_false].


  
  NP _app straightlineish_single_exit outside_range; eauto.
  inv H4.
  NP _app straightline_step_t step_t.
  NP _app straightline_step_t_nextinstr step_t.

  name H6 Hat. inv H6.
  app step_t_labeled_jump H5.
  break_or.

  app jump_to_label_contra H14. inv_false.
  repeat unify_PC. repeat unify_psur. apply H4.

  app straightlineish_single_exit H6; inv H14.
  reflexivity.
  repeat unify_PC.
  eauto.
Qed.

Lemma star_step_md_extends :
  forall ge s1 s2 t,
    star step_bits ge s1 t s2 ->
    forall rs m md rs' m' md',
    s1 = State_bits rs m md ->
    s2 = State_bits rs' m' md' ->
    md_extends md md'.
Proof.
  induction 1; intros.
  subst. inv H0. econstructor; eauto.
  subst. destruct s2.
  app md_extends_step H.
  eapply ex_trans; eauto.
Qed.

Lemma step_through_transf_same_block :
  forall rs m bits b i x y rs' m' b' i' bits' md md',
    at_entry (State_bits rs m md) ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,i) ->
    transf_range rwr prog b x y ->
    step_through x (find rwr) ge (State_bits rs m md) E0 (State_bits rs' m' md') ->
    rs' PC = Values.Vint bits' ->
    psur md' bits' = Some (b',i') ->
    b = b'.
Proof.
  intros.
  inv H3.
  app transf_step_same_block H7. inv H7.
  repeat match goal with
           | [ H : State_bits _ _ _ = State_bits _ _ _ |- _ ] => inv H
         end.
  repeat unify_PC. repeat unify_psur.
  reflexivity.
  assert (t1 = E0).
  {
    destruct t1; simpl in H6. reflexivity.
    inv H6.
  }
  subst t1. simpl in H6.
  assert (t2 = E0).
  {
    destruct t2; simpl in H6. reflexivity.
    inv H6.
  }
  subst t2. simpl in H6.
  assert (t3 = E0).
  {
    destruct t3; simpl in H6. reflexivity.
    inv H6.
  }
  subst t3.  
  destruct (stB). destruct stC.
  name H2 Htransf. inv H2.
  inv H7. break_and.
  repeat unify_PC. repeat unify_psur. simpl. 
  assert (in_transf (State_bits r0 m1 a0)).
  {
    econstructor; eauto.
    rewrite H18. rewrite H2.
    replace (zlen c1 + 0) with (zlen c1) by omega.
    apply Htransf.
    name H10 Hstin.
    rewrite st_in_eq in H10. break_and.
    rewrite H18. rewrite H2.
    replace (zlen c1 + 0) with (zlen c1) by omega.
    eauto. 
    rewrite H18. rewrite H2.
    replace (zlen c1 + 0) with (zlen c1) by omega.
    rewrite st_in_eq in H10. break_and.
    eauto.
  }
  app transf_step_same_block H15.
  inv H15.
  repeat match goal with
           | [ H : State_bits _ _ _ = State_bits _ _ _ |- _ ] => inv H
         end.
  repeat unify_PC.
  repeat unify_psur.
  app transf_step_same_block H9.
  inv H9.
  repeat match goal with
           | [ H : State_bits _ _ _ = State_bits _ _ _ |- _ ] => inv H
         end.
  repeat unify_PC.
  repeat unify_psur.
  rewrite st_in_eq in H10.
  break_and.
  repeat unify_PC. repeat unify_psur.
  symmetry.

  eapply star_step_in_same_block; eauto.
  
Qed.



Lemma match_entry_match_live :
  forall rs m rs' m' bits b i md md',
    at_entry (State_bits rs m md) ->
    match_states (State_bits rs m md) (State_bits rs' m' md') ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,i) ->
    (forall r, In r (liveness_fun_f ge b (Int.unsigned i)) ->
               val_eq (rs r) (rs' r) /\ mem_eq md m m').
Proof.
  intros rs m rs' m' bits b i md md' Hat Hmatch HPC Hpsur.
  inv Hmatch; repeat unify_PC; repeat unify_psur; eauto.
  assert (in_transf (State_bits rs m md)).
  econstructor; try apply H9; try apply H7; eauto.
  
  app at_entry_not_in Hat. app Hat H. inv_false.
Qed.


Lemma match_exit :
  forall z rsl ml rsr mr ml' mr' rsl' rsr' b ofs bits mdl mdr mdl' mdr',
    match_states (State_bits rsl ml mdl) (State_bits rsr mr mdr)->
    rsl PC = Values.Vint bits ->
    psur mdl bits = Some (b,ofs) ->
    Int.unsigned ofs = z + 0 ->
    step_through z (find rwr) (Genv.globalenv prog) (State_bits rsl ml mdl) E0 (State_bits rsl' ml' mdl') ->
    step_through z (repl rwr) (Genv.globalenv tprog) (State_bits rsr mr mdr) E0 (State_bits rsr' mr' mdr') ->
    ((forall r, In r (live_out rwr) -> val_eq (rsl' r) (rsr' r)) /\ mem_eq mdl' ml' mr' /\ mdl = mdr) ->
    genv_equiv_code z (Genv.globalenv prog) (Genv.globalenv tprog) b (find rwr) (repl rwr) ->
    transf_range rwr prog b z (z + zlen (find rwr)) ->
    match_states (State_bits rsl' ml' mdl') (State_bits rsr' mr' mdr').
Proof.
  intros.
  assert (HPC : In PC (live_out rwr)) by (apply (PC_live_out rwr)).
  (* need a state right prior to rs m, in order to use single exit *)
  assert (exists rsi mi mdi, (at_entry (State_bits rsi mi mdi) \/ in_transf (State_bits rsi mi mdi)) /\
                         step_bits ge (State_bits rsi mi mdi) E0 (State_bits rsl' ml' mdl')).
  {

    inv H3. exists rsl. exists ml. exists mdl.
    split; auto. left. econstructor; eauto.
    rewrite H2. instantiate (1 := z + zlen (find rwr)).
    inv H7; econstructor; eauto. omega. 
    destruct stC. exists r. exists m. exists a.
    rewrite H8.
    destruct t1; simpl in H8; try solve [inv H8].
    destruct t2; simpl in H8; try solve [inv H8].
    destruct t3; simpl in H8; try solve [inv H8].
    simpl in H8. rewrite H8 in *.
    unfold ge. unfold fundef in *.
    split; auto.
    destruct stB.    
    right. econstructor; eauto.
    rewrite H2. instantiate (1 := z + zlen (find rwr)).
    inv H7; econstructor; eauto. omega.
    rewrite st_in_eq in H12. break_and.
    rewrite H2. replace (z + 0) with z by omega.
    assumption.
    rewrite st_in_eq in H12. break_and.
    rewrite H2. replace (z + 0) with z by omega.
    simpl.
    assumption.
  }
  break_exists. break_exists. break_and.

  app step_through_at_end H3.
  inv H3.
  destruct fd.

  repeat break_and. subst.

  
  assert (mdl' = mdr'). {
    app (steps_pres_find rwr) H10. break_and.
    app (steps_pres_repl rwr) H4. break_and.
    congruence.
    eapply no_PC_ovf_tprog; eauto.
    inv H13; eauto.
    unfold transf_program in TRANSF;
    repeat break_match_hyp;
    inversion TRANSF; eauto.
    inv H10; eauto.
  } idtac.
  subst.

  assert (at_entry (State_bits rsl ml mdr)). {
    econstructor. eauto.
    eauto. rewrite H2. replace (zlen c0 + 0) with (zlen c0) by omega.
    eassumption.
  } idtac.
  
  app step_through_transf_same_block H10. subst.

  (* Construct the match_states relation here *)
  eapply outside; eauto.

  
  * name (H5 PC HPC) Hrsr'PC.
    rewrite H14 in Hrsr'PC. simpl in Hrsr'PC. congruence.

  * econstructor; eauto.
    eexists. split. 
    eassumption. simpl.
    simpl. left. eexists; eexists.
    split; eauto. omega.

  * 

  name H7 Htransf.
  inv H7. break_and.
  name H13 Htc.
  unfold transf_code in H13.

  rewrite H7 in H13.
  break_match_hyp.
  Focus 2.
  app transf_did_happen Htransf. simpl in Htransf.
  rewrite H13 in Htransf. congruence.
  NP _app is_proper_check_sound is_proper_location_check.
  unfold is_proper_rewrite_location in *.
  repeat break_and.
  unfold liveness_check_correct in *.
  repeat break_and. 

  intro.
  unfold liveness_fun_f.
  repeat collapse_match.
  NP _app split_pat_spec split_pat.
  subst c.
  collapse_match.
  rewrite H19.
  rewrite H16.
  intros.
  
  assert (In r (live_out rwr ++ pres rwr)).
  {

    apply H34.
    rewrite zlen_app.
    assumption.
  }
  
  rewrite in_app in *. break_or.
  apply H5. auto.
  rewrite <- zlen_app in H7.
  rewrite <- H35 in H7 by auto.

  name (steps_pres_find rwr) spf.
  name (steps_pres_repl rwr) spr.

  unfold step_through_preserve in *.
  app step_through_at H4.
  app step_through_at H12.
  assert (Hnpc : no_PC_overflow_prog prog).
  {
    unfold transf_program in TRANSF;
    repeat break_match_hyp;
    inversion TRANSF; eauto.
  }
  assert (Hnpc' : no_PC_overflow_prog tprog).
  {
    eapply no_PC_ovf_tprog; eauto.
  }
  
  name (spf _ _ _ _ _ _ _ _ _ Hnpc H12 H39) spf''.
  name (spr _ _ _ _ _ _ _ _ _ Hnpc' H4 H37) spr''.
  repeat break_and. clear H43. clear H41.
  rename H42 into spf'.
  rename H40 into spr'.
  rewrite <- spf' by eauto.
  rewrite <- spr' by eauto.

  assert (Hlve : forall r0 : preg,
            In r0 (liveness_fun_f (Genv.globalenv prog) b0 (Int.unsigned ofs)) ->
            val_eq (rsl r0) (rsr r0)).
  {
    eapply match_entry_match_live; eauto.
  }
  apply Hlve. unfold liveness_fun_f.
  repeat collapse_match.
  match goal with
    | [ H : Int.unsigned ofs = _ |- _ ] => rewrite H
  end.
  replace (zlen c0 + 0) with (zlen c0) by omega.
  congruence.

  * 
  
  assert (no_ptr_regs rsr /\ no_ptr_mem mr).
  {
    inv H;break_and; split; auto;
    eapply no_ptr_mem_eq; eauto.
  }
  
  eapply no_ptr_preserved_step_through; eauto.

Qed.

Lemma step_through_match :
  forall z st st' str,
    at_entry st ->
    step_through z (find rwr) (Genv.globalenv prog) st E0 st' ->
    match_states st str ->
    exists str',
      plus step_bits (Genv.globalenv tprog) str E0 str' /\
      match_states st' str'.
Proof.
  intros.
  name (steps_equiv_live rwr) selr.
  destruct st'.  
  unfold step_through_equiv_live in selr.
  assert (at_code z (find rwr) 0 (Genv.globalenv prog) st).
  {
    inv H0; eauto.
  }

  name H2 Hat_code.
  inv H2.
  assert (genv_equiv_code (zlen c0) (Genv.globalenv prog) (Genv.globalenv tprog) b (find rwr) (repl rwr)).
  {
    econstructor; eauto;
    repeat unify_find_funct_ptr;
    simpl in *.

    erewrite functions_translated in H9; eauto.
    subst c.
    inversion H9. inversion H. inversion H16.
    subst.
    unify_PC. unify_psur. break_and.
        app split_pat_spec H2. simpl in H9.
        unify_find_funct_ptr.
    rewrite H13. rewrite H4.
    replace (zlen c0) with (zlen c2) by omega.
    rewrite nat_zlen.
    eapply pat_at_n_sane.
    inv H. inv H14.
    unify_PC. unify_psur.
    erewrite functions_translated in H9; eauto.
    repeat unify_find_funct_ptr.
    inv H15. inv H9.
    break_and.

    NP _app split_pat_spec split_pat. subst.
    unify_find_funct_ptr.
    eapply list_eq_middle_therefore_eq in H13; try omega.
    break_and. subst.
    rewrite H9.
                                        
    rewrite nat_zlen.
    repeat rewrite firstn_len.
    reflexivity.
  }


  assert (exists (s : signature) (c : code), Genv.find_funct_ptr (Genv.globalenv tprog) b = Some (Internal {| fn_sig := s; fn_code := c |})).
  {
    destruct fd.   
    eexists. eexists. erewrite functions_translated; eauto.
    simpl. reflexivity.
  }

  assert (no_PC_overflow_prog prog).
  {
    unfold transf_program in TRANSF.
    repeat break_match_hyp; inversion TRANSF; eauto.
  }

  
  name H0 Hst_thru_left.
  destruct str.
  app at_entry_match H1.
  break_and. 

  assert (t = a0). {
    simpl.
    inv H11; auto.
    assert (in_transf (State_bits rs m0 t)).
    econstructor; try apply H23; eauto.
    app at_entry_not_in H.
    app H H11. inv_false.
  } subst.

  eapply selr with (rsr := r0) in H0;
    try solve [eapply no_PC_ovf_tprog; eauto];
    eauto.

  Focus 2.
  (* clear -TRANSF H. *)
  P inv at_entry.
  P inv PeepholeLib.transf_range.
  break_and.
  unfold transf_code in *.
  NP1 app_new split_pat_spec (Some (c2, c3)).
  subst.
  assert (c2 ++ find rwr ++ c3 <> c2 ++ repl rwr ++ c3).
  eapply list_neq.  
  eapply (not_same rwr).  
  repeat (break_match_hyp; try congruence); [].
  NP app_new is_proper_check_sound is_proper_location_check.
  break_and.
  unfold is_proper_rewrite_location in *.
  repeat break_and.
  apply mk_not_after_label_in_code.
  unfold not_after_label.
  intros.
  repeat match goal with
           | [ H : State_bits _ _ _ = State_bits _ _ _ |- _ ] => inv H
           | [ H : Some _ = Some _ |- _ ] => inv H
         end.
  unify_stuff.
  inv Hat_code.
  unify_stuff.
  P1 _simpl fn_code.
  assert (zlen c0 = zlen c2) by omega.
  assert (zlen c5 = zlen c2) by omega.
  eapply list_eq_middle_therefore_eq in H4.
  repeat break_and.  
  subst c5.
  subst c6.
  split.
  assumption.
  auto.
  auto.  
  
  repeat break_exists. repeat break_and.
  
  exists (State_bits x1 x2 a).

  split.
  
  eapply step_through_plus_step; eauto.

  eapply match_exit; eauto.
  destruct fd.
  inv H. repeat unify_PC.
  repeat unify_psur.

  
  rewrite H5 in H21.
  inv H21.

  inv H. repeat unify_PC. repeat unify_psur.
  econstructor; eauto. 
  omega. rewrite zlen_app. omega.  
  inv H11; eauto.  
  intros.
  exploit symbol_address_pres; eauto.

  assert (global_perms (Genv.globalenv prog) m0).
  inv H0.
  app step_gp H14.
  tauto.
  destruct stB.
  app step_gp H16.  
  tauto.
  apply global_perms_translated.
  eapply global_perms_mem_eq; eauto.  
Qed. 


Lemma step_out :
  forall sl sl' sr t,
    match_states sl sr ->
    step_bits (Genv.globalenv prog) sl t sl' ->
    in_transf sl ->
    outside_range sl' ->
    exists sr',
      plus step_bits (Genv.globalenv tprog) sr E0 sr' /\ match_states sl' sr'.
Proof.
  intros.
  (* Here we appeal to the correctness of symbolic evaluation *)
  (* what does that look like? *)
  inv H.
  * (* contradiction *)
    eapply outside_not_in in H6; eauto.
    app H6 H1. inv_false.
  
  * (* contradiction *)
    
    assert (at_entry (State_bits rs m md)).
      econstructor; eauto.

      eapply at_entry_not_in in H; eauto.
      app H H1. inv_false.

  * (* interesting case *)
    
    name (steps_equiv_live rwr) selr.
    name (steps_pres_find rwr) spf.
    name (steps_pres_repl rwr) spr.

    assert (t = E0).
      eapply no_trace_step; eauto.
    subst.

    destruct sl'.


    assert (Hat_entry : at_entry (State_bits rsl ml md)) by (econstructor; eauto).
    
    assert (Hat_code: at_code (Int.unsigned i) (find rwr) 0 (Genv.globalenv prog) (State_bits rsl ml md)).
    {
      inv H6. rewrite H14. break_and.
      econstructor; eauto. omega.
      name (zlen_find rwr) zlnf.
      omega. simpl.
      app split_pat_spec H6.
    }

    assert (Hat_end: at_code_end (Int.unsigned i) (find rwr) (Genv.globalenv prog) (State_bits r m a)).
    {
      app transf_step_same_block H0.
      inv H0. find_inversion. find_inversion.
      app transf_step_same_block H7.
      inv H7.
      find_inversion. find_inversion.
      repeat unify_PC. repeat unify_psur.
      app star_step_in_same_block H9. subst b0.
      name H6 Htransf_range.
      inv H6. 
      rewrite H13.
      econstructor; eauto.
      rewrite <- H13.

      app single_exit H;
        repeat break_and.

      repeat unify_PC.
      repeat unify_psur.
      rewrite zlen_app in H21. omega.

      repeat break_and.
      app split_pat_spec H6.
    }

    
    assert (Hst_thru: step_through (Int.unsigned i) (find rwr) (Genv.globalenv prog) (State_bits rsl ml md) E0 (State_bits r m a)).
    {
      replace E0 with (E0 ** E0 ** E0) by (simpl; auto).
      eapply st_thru_mult_step; eauto.
      rewrite st_in_eq. split. eauto.
      eauto.
    }

    app step_through_match Hst_thru; eauto.
    eapply entry; eauto.

  * (* contradiction *)
    simpl.
    inv H1.
    app transf_step_same_block H14.
    inv H14. find_inversion. find_inversion.
    repeat unify_PC. repeat unify_psur.
    app star_step_in_same_block H16.
    subst b1.
    inv H13. unify_find_funct_ptr.
    right. econstructor; eauto.
Qed.


Lemma match_not_in :
  forall sl sl' sr sr' t,
    outside_range sl ->
    match_states sl sr ->
    step_bits (Genv.globalenv prog) sl t sl' ->
    step_bits (Genv.globalenv prog) sr t sr' ->
    outside_range sl' ->
    match_live liveness_fun_f prog sl' sr' ->
    match_states sl' sr'.
Proof.
  intros. name H Hout_start. name H3 Hout_end.
  inv H0.
  * unfold match_live in H4. destruct sl'. destruct sr'. 
    inv H3.
    specialize (H4 _ _ _ H15 H14).
    repeat break_and.
    subst a.
    eapply outside; eauto.
    
    exploit (H13 PC).
    unfold transf_program in TRANSF.
    repeat break_match_hyp; inversion TRANSF. 
    eapply PC_always_live; eauto. destruct u. eassumption.
    intros.
    rewrite H14 in H12.
    simpl in H12. congruence.
  * assert (at_entry (State_bits rs m md)).
      econstructor; eauto.
    app at_entry_not_out H0.
    app H0 H. inv_false.
  * assert (in_transf (State_bits rsl' m' md')) by (
      econstructor; try apply H5; eauto).
    app inside_not_out H0.
    app H0 H. inv_false.
  * unfold match_live in H4. destruct sl'. destruct sr'. 
    inv H3. 
    specialize (H4 _ _ _ H14 H13).
    repeat break_and.
    subst a.
    eapply outside; eauto.
    exploit (H12 PC).
    unfold transf_program in TRANSF.
    repeat break_match_hyp; inversion TRANSF. 
    eapply PC_always_live; eauto.
    destruct u. eassumption.
    intros. rewrite H13 in H11. simpl in H11. congruence.
Qed.

Lemma match_at_entry :
  forall sl sl' sr sr' t,
    outside_range sl ->
    match_states sl sr ->
    step_bits (Genv.globalenv prog) sl t sl' ->
    step_bits (Genv.globalenv prog) sr t sr' ->
    at_entry sl' ->
    match_live liveness_fun_f prog sl' sr' ->
    match_states sl' sr'.
Proof.
  intros. name H Houtside. name H3 Hat_entry.
  inv H0.
  * unfold match_live in H4. destruct sl'. destruct sr'. 
    inv H3. 
    specialize (H4 _ _ _ H15 H14).
    repeat break_and. 
    name H16 Htransf_range. inv H16.
    eapply entry; eauto. 
    exploit (H13 PC).
    unfold transf_program in TRANSF.
    repeat break_match_hyp; inversion TRANSF. 
    eapply PC_always_live; eauto. destruct u.
    eassumption.
    intros. rewrite H14 in H12. simpl in H12. congruence.
  * assert (at_entry (State_bits rs m md)) by (
      econstructor; eauto).
    app at_entry_not_out H0.
    app H0 H. inv_false.
  * assert (in_transf (State_bits rsl' m' md')) by (
      econstructor; try apply H11; try apply H9; eauto).
    app outside_not_in Houtside.
    app Houtside H0. inv_false.
  * unfold match_live in H4. destruct sl'. destruct sr'. 
    inv H3. 
    specialize (H4 _ _ _ H14 H13).
    repeat break_and. 
    
    name H15 Htransf_range. inv H15.
    eapply entry; eauto.
    exploit (H12 PC).
    unfold transf_program in TRANSF.
    repeat break_match_hyp; inversion TRANSF. 
    eapply PC_always_live; eauto.
    destruct u. eassumption.
    intros. rewrite H13 in H11. simpl in H11. congruence.
Qed.

Lemma step_out_at_entry :
  forall sl sl' sr t,
    match_states sl sr ->
    step_bits (Genv.globalenv prog) sl t sl' ->
    at_entry sl ->
    outside_range sl' ->
    exists sr',
      plus step_bits (Genv.globalenv tprog) sr E0 sr' /\ match_states sl' sr'.
Proof.
  intros.
  app at_entry_at_code H1.
  app no_trace_entry_step H0. subst t.  
  eapply step_through_match; eauto.
  econstructor; eauto.

  inv H1. destruct sl'.
  name H3 Hat_entry.
  inv H3. repeat unify_PC. repeat unify_psur.
  app single_exit H0.
  repeat break_and.
  econstructor; eauto.
  inv H14. 
  rewrite zlen_app in H16.
  omega.
Qed.

Lemma entry_step_in :
  forall s1 s2 s1',
    match_states s1 s2 ->
    at_entry s1 ->
    step_bits (Genv.globalenv prog) s1 E0 s1' ->
    in_transf s1' ->
    match_states s1' s2.
Proof.
  intros.
  inv H.
  * app at_entry_not_out H0.
    app H0 H6. inv_false.
  * app transf_step_same_block H1.
    inv H1. find_inversion.
    repeat unify_PC.
    repeat unify_psur.
    eapply inside; try apply star_refl; eauto.

    inv H2.
    assert (at_entry (State_bits rsl m md)) by (econstructor; eauto).
    app transf_step_same_block H17.
    inv H17. find_inversion. find_inversion.
    repeat unify_PC. repeat unify_psur.

    app star_step_in_same_block H19. subst b0.

    eapply transf_range_unique in H6; try apply H16.
    break_and. rewrite H6.

    name (conj H3 H18) Hstin.
    rewrite <- st_in_eq in Hstin.
    app star_step_in_in' Hstin.
    
  * assert (in_transf (State_bits rsl' m' md')) by (
    econstructor; try apply H7; eauto).
    app at_entry_not_in H0.
    app H0 H. inv_false.
  * inv H0. unify_PC. unify_psur.
    inv H13. unify_find_funct_ptr.
Qed.

End PRESERVATION.
