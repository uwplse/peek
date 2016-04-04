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
Require Import Values.

Require Import PeekLiveness.
Require Import SplitLib.
Require Import FindInstrLib.
Require Import PeekTactics.
Require Import PregTactics.
Require Import AsmCallingConv.
Require Import Union.
Require Import StepIn.
Require Import PeekLivenessProof.
Require Import Use.
Require Import PeekLib.
Require Import StepLib.
Require Import SameBlockLib.
Require Import StepEquiv. (* Where rewrite is defined *)
Require Import ProgPropDec.
Require Import ForwardJumps.
Require Import Zlen.

Require Import AsmBits.
Require Import MemoryAxioms.

Require Import Peephole.
Require Import PeepholeLib.

Section PRESERVATION.

  Variable rwr: rewrite.

  Variable prog: program.
  Variable tprog: program.
  Hypothesis TRANSF: transf_program rwr prog = OK tprog.
  Hypothesis CALLING_CONV : calling_conv_correct_bits prog.
  Let ge := Genv.globalenv prog.
  Let tge := Genv.globalenv tprog.

  Definition outside_range := PeepholeLib.outside_range rwr prog.
  Definition in_transf := PeepholeLib.in_transf rwr prog.
  Definition at_entry := PeepholeLib.at_entry rwr prog.
  Definition match_states := PeepholeLib.match_states rwr prog.
  Definition transf_range := PeepholeLib.transf_range rwr prog.

Lemma has_no_PC_overflow :
  no_PC_overflow_prog prog.
Proof.
  unfold transf_program in *.
  repeat break_match; try congruence.
  assumption.
Qed.  

Hint Resolve has_no_PC_overflow.
  
Lemma outside_not_in :
  forall s,
    outside_range s -> ~ in_transf s.
Proof.
  intros. intro.
  inv H.  inv H0.


  assert (in_code (Int.unsigned i0) (find rwr) (Genv.globalenv prog) (State_bits rs m md)).
  eapply star_step_in_in'.
  rewrite st_in_eq. split; eauto.

  
  inv H10. inv H4.
  app star_step_in_same_block H11;
    try instantiate (1 := i);
    try instantiate (1 := b). 
  subst b1.


  
  assert (b = b0).
  app start_transf_range_at_code H6.
  app only_forward_jumps_same_block H9.
  apply (forward_find rwr).

  subst b0.

  repeat break_and. unify_find_funct_ptr. destruct fd. simpl in *.
  break_or. repeat break_exists; break_and.
  eapply transf_range_unique in H12; try apply H8.
  break_and. simpl.
  subst.

  inv H. inv H17.
  name zlen_find z.
  unify_PC. unify_psur.
  unify_find_funct_ptr. simpl in H29.
  inv H8. rewrite zlen_app in H13. omega.

  inv H8. break_and. unfold ge in *.
  unify_find_funct_ptr.
  rewrite H13 in H17.
  app split_pat_spec H8.
  rewrite H8 in H17.
  name (list_neq _ _ _ _ (not_same rwr) H17) Hf. eauto.
Qed.

Lemma inside_not_out :
  forall s,
    in_transf s -> ~ outside_range s.
Proof.
  intros. intro. app outside_not_in H0.
Qed.

Lemma at_entry_not_in :
  forall s,
    at_entry s ->
    ~ in_transf s.
Proof.

  intros. intro.
  inv H. inv H0.
  name (conj H11 H10) Hc.
  rewrite <- st_in_eq in Hc.
  app star_step_in_in' Hc.
  app star_step_in_in H.
  app start_transf_range_at_code H7. instantiate (1 := m0) in H7.
  inv H10. inv H12.
  app only_forward_jumps_same_block H9.
  subst b1.
  app star_step_in_same_block H11. subst b0.
  eapply transf_range_unique in H8; try apply H3. break_and.
  subst.

  inv Hc. 
  inv H13. unify_PC. unify_psur.
  omega. apply (forward_find rwr).
Qed.

Lemma at_entry_not_out :
  forall s,
    at_entry s ->
    ~ outside_range s.
Proof.
  intros. intro.
  inv H. inv H0. unify_PC. unify_psur.
  break_exists. break_and.
  name H3 Htrange.
  inv H3. unfold ge in *. unify_find_funct_ptr. break_and.
  destruct H0. repeat break_exists. break_and.
  eapply transf_range_unique in H0; try apply Htrange.
  break_and. subst. rewrite zlen_app in H4. rewrite zlen_app in Htrange.
  name (zlen_find rwr) zl. omega.


  app split_pat_spec H2.
  rewrite H0 in H3. rewrite H2 in H3.
  name (list_neq _ _ _ _ (not_same rwr) H3) Hf. eauto.
Qed.


Lemma outside_range_match :
  forall s1 s2,
    match_states s1 s2 ->
    outside_range s1 ->
    outside_range s2.
Proof.
  intros. inv H.
  * inv H0.
    break_exists. break_and.
    unify_PC. unify_psur.
    econstructor; eauto.
  * assert (at_entry (State_bits rs m md)).
    econstructor; eauto.

    app at_entry_not_out H.
    congruence.
  * assert (in_transf (State_bits rsl' m' md')).
    econstructor; try apply H5; eauto.
    app outside_not_in H0.
    congruence.
  * inv H0.
    break_exists. break_and.
    unify_PC. unify_psur. unify_find_funct_ptr.
    econstructor; eauto.
Qed.


Lemma in_transf_dec :
  forall s1 s2,
    match_states s1 s2 ->
    in_transf s1 \/ outside_range s1 \/ at_entry s1.
Proof.
  intros.
  inversion H.
  * right. left. assumption.
  * right. right. econstructor; eauto.
  * left. econstructor. Focus 3. apply H3.
    Focus 3. eauto.
    eauto. eauto. eauto. eauto.
  * simpl. subst.
    right. left.
    econstructor; eauto.
    exists (External ef). eauto.
Qed.

Hint Resolve list_preppend_eq.
Hint Resolve list_eq_middle_therefore_eq.
Hint Resolve list_middle_eq.

Lemma split_pat_eq :
  forall a b c0 c1,
    split_pat a (c0 ++ b ++ c1) = Some (c0, c1) ->
    a = b.
Proof.
  intros.
  eapply list_middle_eq.
  eapply split_pat_spec.
  eassumption.
Qed.

Lemma transf_code_is_proper :
  forall c c0 c1,
    split_pat (find rwr) c = Some (c0, c1) ->
    transf_code rwr c = c0 ++ repl rwr ++ c1 ->
    is_proper_location_check rwr c0 (find rwr) c1 (get_labels c0 ++ get_labels c1) (repl rwr) = true.
Proof.
  intros.
  unfold transf_code in *.
  break_match.
  break_let.
  break_if.
  inv Heqo.
  inv H.
  assumption.
  subst.
  inv H.
  apply split_pat_eq in Heqo.
  name (not_same rwr) Hn.
  congruence.
  congruence.
Qed.




Ltac rwrt_p pat := P rwrt_n pat.
Ltac rwrt_p1 pat := P1 rwrt_n pat.
Ltac rwrtb_p pat := P rwrtb_n pat.
Ltac rwrtb_p1 pat := P1 rwrtb_n pat.
Ltac rwrt_pp p1 p2 := PP rwrt p1 p2.
Ltac rwrt_pp1 p1 p2 := PP1 rwrt p1 p2.
Ltac rwrtb_pp p1 p2 := PP rwrtb p1 p2.
Ltac rwrtb_pp1 p1 p2 := PP1 rwrtb p1 p2.  
Ltac erwrt_pp p1 p2 := PP erwrt p1 p2.
Ltac erwrt_pp1 p1 p2 := PP1 erwrt p1 p2.
Ltac erwrtb_pp p1 p2 := PP erwrtb p1 p2.
Ltac erwrtb_pp1 p1 p2 := PP1 erwrtb p1 p2.
Ltac erwrt_np nm pat := NP erwrt nm pat.
Ltac erwrt_np1 nm pat := NP1 erwrt nm pat.
Ltac erwrtb_np nm pat := NP erwrtb nm pat.
Ltac erwrtb_np1 nm pat := NP1 erwrtb nm pat.  
Ltac inv_p pat := P inv pat.
Ltac inv_p1 pat := P1 inv pat.
Ltac inv_p2 pat := P2 inv pat.

  Ltac ge_expand := replace ge with (Genv.globalenv prog) in * by eauto.

  Hint Resolve at_code_straightlineish_end.
  (* Hint Resolve straightlineish_exec.  *)
  
  Lemma in_rewrite_step_not_beginning_jmp :
    forall b z j l ofs_z' f,
      transf_range b z j ->
      Genv.find_funct_ptr (Genv.globalenv prog) b = Some (Internal f) ->
      label_pos l 0 (fn_code f) = Some ofs_z' ->
      Int.unsigned (Int.repr ofs_z') <> z.
  Proof.
    intros.
    inv_p transf_range.
    break_and.
    app_np transf_code_is_proper transf_code.
    app_np is_proper_check_sound is_proper_location_check.
    break_and.
    inv_p is_proper_rewrite_location.
    repeat break_and.
    exploit label_pos_find_instr; eauto; intros.
    progress unfold ends_in_not_label in *.
    assert (Int.unsigned (Int.repr ofs_z') = zlen c1 -> False); [ |omega].
    intros.
    destruct f.
    unify_stuff.
    simpl in *.
    replace (Int.unsigned (Int.repr ofs_z')) with ofs_z' in *.
    Focus 2.
    exploit unsigned_repr_PC; try left; simpl in *; eauto.
    rwrtb_pp (ofs_z' = zlen c1) (StepIn.is_any_label).
    exploit find_instr_prefix; eauto.
    instantiate (1 := ofs_z' - 1).
    exploit StepIn.find_instr_range; eauto.
    omega.
    intros.        
    rwrt_pp1 find_instr Plabel.
    erwrt_np find_instr_append_tail Plabel.
    match goal with
      | [ H : context [ Plabel ] |- _ ] =>
        instantiate (1 := nil) in H;
          rewrite app_nil_r in H;
          app_pn StepIn.is_any_label H
    end.
    rwrt_p1 (zlen c1).
    destruct c1; try congruence.
    rewrite zlen_cons.
    name (zlen_nonneg _ c1) Hz.
    omega.
  Qed.

  Lemma absurd_jmp_step :
    forall rs bits b ofs f i' i m st' l t md,
      rs PC = Values.Vint bits ->
      psur md bits = Some (b, ofs) ->
      Genv.find_funct_ptr (Genv.globalenv prog) b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) (fn_code f) = Some i' ->
      step_t (i :: nil) (Genv.globalenv prog) (State_bits rs m md) t st' ->
      labeled_jump i l ->
      ~ labeled_jump i' l ->
      False.
  Proof.
    intros.
    repeat inv_p step_t.
    inv_p at_code.
    unify_stuff.
    
    rewrite H19 in H2.
    rewrite H12 in H2.
    assert (find_instr 0 ((i :: nil) ++ c1) = Some i').
    exploit find_instr_append_head.
    instantiate (1 := 0). omega.
    intros.
    rewrite H3 in H2.
    eauto.
    simpl in *.
    inv_p (Some i).
    congruence.
  Qed.
  
  Lemma in_rewrite_step_not_beginning :
    forall z ofs rs m rs' m' bits bits' b i i' j md md',
      transf_range b z j ->
      at_code z (find rwr) ofs (Genv.globalenv prog) (State_bits rs m md) ->
      step_bits (Genv.globalenv prog) (State_bits rs m md) E0 (State_bits rs' m' md') ->
      rs PC = Values.Vint bits ->
      psur md bits = Some (b,i) ->
      rs' PC = Values.Vint bits' ->
      psur md' bits' = Some (b,i') ->
      Int.unsigned i' <> z.
  Proof.
    
    (* This is true. *)
    (* we will want a lemma like step_in_step_t', but with at_code instead of in_code *)
    (* we didn't rewrite after a call or a label *)
    (* thus we don't jump to them *)
    (* we couldn't be before it either, since already in *)
    intros.
    exploit step_at_step_t'; eauto; intros. break_exists. break_and.
    rename i into z_ofs, i' into z_ofs', x into i.
    exploit instr_class.
    instantiate (1 := i).
    intros.
    name has_no_PC_overflow Hpc.
    repeat break_or. (* case: type of instruction *)
    - repeat inv_p1 step_t.
      exploit at_code_straightline_end; eauto; intros.
      inv_p at_code_end.
      repeat inv_p1 at_code.
      unify_stuff.
      omega.
    - break_exists. rename x into l.

      invs.
      repeat inv_p1 step_t.

      (* TODO: make lemma *)
      assert (i = i0). {
        destruct f.
        ge_expand.
        simpl in *.
        unify_stuff.
        inv_p1 at_code.
        unify_stuff.
        simpl in *.
        unfold StepIn.ge in H29.
        unify_find_funct_ptr.
        simpl in H30.
        find_one_instr. reflexivity.
      } idtac.
      subst i0.

      destruct i; try inv_p labeled_jump.

      simpl in *.
      repeat break_match_hyp; try state_inv.
      simpl_exec.
      repeat break_match_hyp; try state_inv.
      inv_p (Values.Vint bits').
      unify_stuff.
      unfold goto_label_bits in *.
      repeat break_match_hyp; try congruence.
      st_inv. preg_simpl_hyp H8. find_inversion.
      erewrite weak_valid_pointer_sur in H5 by eauto. break_and.
      eapply pinj_injective_within_block in H3; try eapply Heqo0.
      subst z_ofs'.
      eapply in_rewrite_step_not_beginning_jmp; eauto.

      simpl in *.
      repeat break_match_hyp; try state_inv.
      simpl_exec.
      repeat break_match_hyp; try state_inv.
      inv_p (Values.Vint bits').
      unify_stuff.
      unfold goto_label_bits in *.
      repeat break_match_hyp; try congruence.
      st_inv. preg_simpl_hyp H8. find_inversion.
      erewrite weak_valid_pointer_sur in H5 by eauto. break_and.
      eapply pinj_injective_within_block in H3; try eapply Heqo1.
      
      subst z_ofs'.

      unify_stuff.
      eapply in_rewrite_step_not_beginning_jmp; eauto.

      (* straightline *)
      unify_stuff.
      exploit at_code_straightlineish_end.
      eauto.
      eauto.
      remember (nextinstr rs) as rs'.
      assert (rs' PC = nextinstr rs PC).
      congruence.
      eauto.
      eauto.
      eauto.
      intros.
      repeat inv_p1 at_code_end.
      repeat inv_p1 at_code.
      unify_stuff.
      omega.

      simpl in *.
      repeat break_match_hyp; try state_inv.
      simpl_exec.
      repeat break_match_hyp; try state_inv.
      inv_p (Values.Vint bits').
      unify_stuff.
      unfold goto_label_bits in *.
      repeat break_match_hyp; try congruence.
      st_inv. preg_simpl_hyp H8. find_inversion.
      erewrite weak_valid_pointer_sur in H5 by eauto. break_and.
      eapply pinj_injective_within_block in H3; try eapply Heqo2.
      subst z_ofs'.
      eapply in_rewrite_step_not_beginning_jmp; eauto.

      (* straightline *)
      unify_stuff.
      exploit at_code_straightlineish_end.
      eauto.
      eauto.
      remember (nextinstr rs) as rs'.
      assert (rs' PC = nextinstr rs PC).
      congruence.
      eauto.
      eauto.
      eauto.
      intros.
      inv_p at_code_end.
      repeat inv_p1 at_code.
      unify_stuff.
      omega.

      (* straightline *)
      unify_stuff.
      exploit at_code_straightlineish_end.
      eauto.
      eauto.
      remember (nextinstr rs) as rs'.
      assert (rs' PC = nextinstr rs PC).
      congruence.
      eauto.
      eauto.
      eauto.
      intros.
      inv_p at_code_end.
      repeat inv_p1 at_code.
      unify_stuff.
      omega.

      simpl in *.
      repeat break_match_hyp; try state_inv.
      simpl_exec.
      repeat break_match_hyp; try state_inv.
      inv_p (Values.Vint bits').
      unify_stuff.
      unfold goto_label_bits in *.
      repeat break_match_hyp; try congruence.
      st_inv. preg_simpl_hyp H9. find_inversion.
      erewrite weak_valid_pointer_sur in H5 by eauto. break_and.
      eapply pinj_injective_within_block in H3; try eapply Heqo1.
      subst z_ofs'.
      eapply in_rewrite_step_not_beginning_jmp; eauto.

      unify_stuff.
      exploit absurd_jmp_step; try eapply H2; eauto.

      unify_stuff.
      exploit absurd_jmp_step; try eapply H2; eauto.

      unify_stuff.
      repeat inv_p step_t.
      inv H11.
      unify_stuff.
      repeat ge_expand.
      unfold StepIn.ge in *.
      unfold fundef in *.
      solve [unify_find_funct_ptr].
    - name (forward_find rwr) Hr.
      inv Hr.
      break_and.
      unfold no_calls in H8.
      rewrite find_instr_in in H7.
      break_exists.
      app H8 H7.
    - name (forward_find rwr) Hr.
      inv Hr.
      break_and.
      unfold no_trace_code in H10.
      rewrite find_instr_in in H7.
      break_exists.
      app H10 H7.
      app no_trace_trace H9.
  Qed.

  Lemma in_transf_step_dec :
    forall s1 s1' t,
      in_transf s1 ->
      step_bits (Genv.globalenv prog) s1 t s1' ->
      (in_transf s1' \/ outside_range s1').
  Proof.
    intros.
    name H Hin.
    inv H.
    app no_trace_step H0. subst t.
    name H Hstep.
    app transf_step_same_block Hstep.
    inv Hstep. find_inversion.
    assert (at_entry (State_bits rsl m md)).
    econstructor; eauto.
    app transf_step_same_block H4. inv H4.
    find_inversion. find_inversion. repeat unify_PC.
    repeat unify_psur.
    app star_step_in_same_block H6. subst b0.
    assert ((Int.unsigned i' < Int.unsigned i1 \/ Int.unsigned i' >= j) \/ (Int.unsigned i' >= Int.unsigned i1 /\ Int.unsigned i' < j)) by omega.

    break_or.
    * right. inv H5. inv H13.
      unify_PC. unify_psur.
      econstructor; eauto.
      unfold fundef in *. 
      rewrite H27.
      eexists; split; eauto. simpl. destruct fd.
      left. eexists. eexists. split; eauto.
    * left. econstructor; eauto.
      eapply star_right; try apply H1; simpl; eauto.
      econstructor; try eapply H0; simpl; eauto.
      name (conj H1 H5) Hst. rewrite <- st_in_eq in Hst.
      app star_step_in_in' Hst.
      name H5 Hin_code.
      inv H5. inv H13.
      repeat unify_PC. repeat unify_psur.
      name (conj H1 Hin_code) Hstin.
      rewrite <- st_in_eq in Hstin.
      app star_step_in_in' Hstin.
      inversion Hstin.
      app in_rewrite_step_not_beginning H0.
      assert (exists x, Int.unsigned i' = zlen c0 + x /\ 0 < x < zlen (find rwr)).
      {
        inv H3. repeat break_and. rewrite zlen_app in H6.
        app split_pat_spec H18.
        unify_find_funct_ptr.
        exists (Int.unsigned i' - zlen c0).
        split; omega.
      }
      subst.
      break_exists. break_and.
      econstructor; try econstructor;
      try apply H18; eauto; try omega.
  Qed.

  (* Here's how single entry is going to go *)
  (* it'll be encapsulated as outside_step_dec *)
  (* That'll be the single_entry external interface *)
  (* however, we'll prove it another way *)
  (* * if outside and exec a non-straightline instr, then still outside *)
  (* * if outside, either straightline or not *)
  (* * if outside, straightline goes outside or to entry *)

  Lemma outside_step_straightlineish :
    forall t i rs m rs' m' md md',
      outside_range (State_bits rs m md) ->
      step_t (i :: nil) ge (State_bits rs m md) t (State_bits rs' m' md') ->
      rs' PC = (nextinstr rs) PC ->
      outside_range (State_bits rs' m' md') \/ at_entry (State_bits rs' m' md').
  Proof.
    intros.    
    P inv outside_range.
    break_exists. break_and.
    app_np straightlineish_step_fundef step_t.
    unfold ge in *. unify_find_funct_ptr.
    repeat P0 inv step_t.

    NP _app step_md step_bits.
    NP _app step_gp step_bits.
    NP _app md_extends_step step_bits.
    repeat break_and.
    eapply global_perms_valid_globals in H0.
    eapply global_perms_valid_globals in H9.
    inv H7. repeat unify_PC.
    repeat unify_psur.
    erewrite weak_valid_pointer_sur in H15; eauto.
    break_and. 
    eapply pinj_extends in H6; eauto.
    eapply pinj_add in H6. instantiate (1 := Int.one) in H6.
    assert (Memory.Mem.weak_valid_pointer m' b (Int.unsigned (Int.add i0 Int.one)) = true). {
      rewrite Memory.Mem.weak_valid_pointer_spec. right.
      unfold Int.add. rewrite Int.unsigned_one.
      erewrite unsigned_repr_PC; eauto.
      Focus 2. left. rewrite H16. rewrite H23.
      replace (zlen c0 + 0 + 1 - 1) with (zlen c0 + 0) by omega.
      rewrite find_instr_append_head by omega.
      simpl. reflexivity.
      replace (Int.unsigned i0 + 1 - 1) with (Int.unsigned i0) by omega.
      eapply H9.
      unfold is_global.
      left. unfold in_code_range.
      unfold fundef in *.
      repeat collapse_match.
      rewrite H23. rewrite H16.
      repeat rewrite zlen_app. name (zlen_nonneg) zln.
      rewrite zlen_cons. replace (zlen (@nil instruction)) with 0 by (simpl; auto).
      name (zln _ c0) zlnc0.
      name (zln _ c1) zlnc1. omega.
    } idtac.
    name (conj H6 H11) Hpsur1.
    erewrite <- weak_valid_pointer_sur in Hpsur1.

    break_match_hyp. destruct H2.
    repeat break_exists. repeat break_and.
    
    remember (Int.add i0 Int.one) as i1.
    assert (Int.unsigned i1 = x \/ (Int.unsigned i1 < x \/ Int.unsigned i1 >= x1)). {
      subst i1. inv H2. break_and.
      unfold Int.add.
      rewrite Int.unsigned_one.
      erewrite unsigned_repr_PC; try apply H; eauto.
      Focus 2. left. rewrite H16. simpl. repeat unify_find_funct_ptr.
      simpl in H23. rewrite H23.
      replace (zlen c0 + 0 + 1 - 1) with (zlen c0 + 0) by omega.
      rewrite find_instr_append_head by omega.
      simpl. reflexivity.
      rewrite zlen_app. rewrite zlen_app in H14.
      omega.
    } idtac.

    destruct H15.
    right.
    econstructor; eauto.
    rewrite H1. preg_simpl.
    rewrite H5. simpl. reflexivity.
    rewrite H15. eauto.

    left.    econstructor; eauto.
    rewrite H1. preg_simpl.
    rewrite H5. simpl. reflexivity.
    eexists. split; eauto. simpl.
    repeat unify_find_funct_ptr. left. exists x. exists x1.
    split; auto; try omega.

    left.
    econstructor; eauto.
    rewrite H1. preg_simpl.
    rewrite H5. simpl. reflexivity.
    eexists. split; eauto. simpl.
    unfold fundef in *.
    rewrite H22 in H. inversion H.
    right. eauto.
    assumption.
  Qed.


    Lemma step_t_straightline_nextinstr :
      forall ge rs m md rs' m' md' t i,
        step_t (i :: nil) ge (State_bits rs m md) t (State_bits rs' m' md') ->
        straightline i ->
        rs' PC = nextinstr rs PC.
    Proof.
      intros. inv H. inv H9.
      inv H3. invs;
        try unify_PC;
        try unify_psur;
        try unify_find_funct_ptr;
        try solve [preg_simpl; reflexivity];
        find_one_instr;
        simpl in *;
        try inv_false.
      break_instr_exec i1;
        try inv_false;
        try unfold compare_floats;
        try unfold compare_floats32;
        try solve [preg_simpl; reflexivity];
        repeat break_match;
        try solve [preg_simpl; reflexivity];
        simpl in *;
        congruence.
      Qed.
  

  Lemma outside_step_straight :
    forall st t st' i,
      outside_range st ->
      step_t (i :: nil) ge st t st' ->
      straightline i ->
      outside_range st' \/ at_entry st'.
  Proof.
    intros. destruct st. destruct st'.
    eapply outside_step_straightlineish; eauto.

    eapply step_t_straightline_nextinstr; eauto.
  Qed.

  Lemma no_trace_dec :
    forall i,
      no_trace i \/ ~ no_trace i.
  Proof.
    intros.
    destruct i; simpl in *; tauto.
  Qed.


  Lemma call_not_call_return :
    forall i,
      is_call i ->
      ~ is_call_return i ->
      False.
  Proof.
    intros. destruct i;
            simpl in *;
            inv_false.
  Qed.

  Lemma after_call_outside_range :
    forall rs m bits b ofs f i md,
      rs PC = Values.Vint bits ->
      psur md bits = Some (b,ofs) ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs - 1) (fn_code f) = Some i ->
      is_call i ->
      outside_range (State_bits rs m md).
  Proof.
    intros.
    app functions_translated H1.
    unfold transf_fundef in H1.
    destruct f.
    unfold transf_code in H1.
    repeat break_match_hyp;

      try solve [
            econstructor; eauto;
            eexists; split; try solve [eauto];
            simpl; right; unfold transf_code;
            try find_rewrite; try find_rewrite; reflexivity].

    app is_proper_check_sound Heqb0.
    break_and.
    unfold is_proper_rewrite_location in H7.
    repeat break_and.
    (* important one is ends_in_not_call *)
    assert (transf_range b (zlen c) (zlen (c ++ find rwr))).
    {
      econstructor; eauto.
      split; eauto.
      unfold transf_code.
      find_rewrite. find_rewrite. find_rewrite.
      reflexivity.
    }

    econstructor; eauto.
    eexists; split; eauto.
    simpl.
    left. eexists; eexists; split; eauto.

    name (forward_find rwr) ffr.
    unfold only_forward_jumps in ffr.
    assert (Int.unsigned ofs < zlen c \/ zlen c <= Int.unsigned ofs < zlen (c ++ find rwr) \/ Int.unsigned ofs >= zlen (c ++ find rwr)) by omega.
    repeat break_or; try omega.
    exfalso.
    assert (zlen c = Int.unsigned ofs \/ zlen c < Int.unsigned ofs < zlen (c ++ find rwr)) by omega.
    break_or.
    * rewrite <- H21 in *.
      app split_pat_spec Heqo.
      rewrite Heqo in H2.
      simpl in H2.
      unfold ends_in_not_call in H12.
      repeat break_exists.
      repeat break_and.
      rewrite H12 in H2.
      rewrite zlen_app in H2.
      rewrite zlen_cons in H2.
      simpl in H2.
      replace (zlen x0 + 1 - 1) with (zlen x0 + 0) in H2 by omega.
      rewrite app_ass in H2.
      rewrite find_instr_append_head in H2 by omega.
      simpl in H2. inv H2.
      app call_not_call_return H3.

    * repeat break_and.
      unfold no_calls in H23.
      simpl in H2.
      app split_pat_spec Heqo.
      rewrite Heqo in H2.
      replace (Int.unsigned ofs - 1) with (zlen c + (Int.unsigned ofs - 1 - zlen c)) in H2 by omega.
      rewrite find_instr_append_head in H2 by omega.
      rewrite zlen_app in H21.
      rewrite find_instr_append_tail with (c := nil) in H2 by omega.
      rewrite app_nil_r in H2.
      app H23 H2.
      app call_not_call_return H3.
  Qed.

  Lemma outside_step_external :
    forall rs m t bits b i st' ef md,
      step_bits ge (State_bits rs m md) t st' ->
      rs PC = Values.Vint bits ->
      psur md bits = Some (b,i) ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      outside_range st'.
  Proof.
    intros.
    assert (external_fun_steps_back_to_call_bits prog).
    unfold calling_conv_correct_bits in CALLING_CONV.
    intuition.
    destruct st'. unfold ge in *.
    
    unfold external_fun_steps_back_to_call_bits in H3.
    app H3 H.
    clear H3. break_and. break_and.
    repeat break_exists.
    repeat break_and.
    eapply after_call_outside_range; eauto.
    
    
    Grab Existential Variables.
    exact Pnop.
  Qed.

  Lemma find_instr_list_parts :
    forall c z i,
      find_instr z c = Some i ->
      exists c1 c2,
        c = c1 ++ (i :: nil) ++ c2 /\ z = zlen c1.
  Proof.
    induction c; intros.
    simpl in H. inv H.
    apex in_range_find_instr H.
    break_and.
    assert (z = 0 \/ z > 0) by omega.
    break_or.
    * simpl in H. inv H.
      exists nil. simpl. exists c. eauto.
    * replace z with (1 + (z - 1)) in H by omega.
      rewrite find_instr_head in H by omega.
      app IHc H. break_and.
      exists (a :: x). exists x0.
      split. rewrite H. simpl. reflexivity.
      rewrite zlen_cons. omega.
  Qed.


  Lemma find_instr_at_code :
    forall rs m bits b ofs f i md,
      rs PC = Values.Vint bits ->
      psur md bits = Some (b,ofs) ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) (fn_code f) = Some i ->
      at_code (Int.unsigned ofs) (i :: nil) 0 ge (State_bits rs m md).
  Proof.
    intros.
    app find_instr_list_parts H2.
    break_and. rewrite H4.
    econstructor; eauto. omega.
    rewrite zlen_cons. simpl. omega.
  Qed.

  Lemma step_t_or_external :
    forall st t st',
      step_bits ge st t st' ->
      (exists i, step_t (i :: nil) ge st t st') \/
      (exists rs m bits b ofs ef md,
         st = State_bits rs m md /\ rs PC = Values.Vint bits /\
         psur md bits = Some (b,ofs) /\
         Genv.find_funct_ptr ge b = Some (External ef)).
  Proof.
    intros. invs.
    left. subst.
    exists i. replace E0 with (E0 ** E0) by auto.
    app find_instr_at_code H4.
    econstructor; eauto. econstructor.
    left. subst.
    eexists. replace t with (t ** E0) by (rewrite E0_right; reflexivity).
    app find_instr_at_code H3.
    econstructor; eauto.
    rewrite E0_right.
    econstructor.
    left. subst.
    eexists. replace t with (t ** E0) by (rewrite E0_right; reflexivity).
    app find_instr_at_code H5.
    econstructor; eauto.
    rewrite E0_right.
    econstructor.
    
    right. repeat eexists; eauto.
  Qed.

  Lemma straightline_dec :
    forall x,
      straightline x \/ ~ straightline x.
  Proof.
    destruct x; unfold straightline; auto.
    destruct tbl; auto. right. congruence.
  Qed.

  Lemma outside_step_label :
    forall st t st' l,
      outside_range st ->
      step_t (Plabel l :: nil) ge st t st' ->
      outside_range st' \/ at_entry st'.
  Proof.
    intros.
    exploit outside_step_straight; eauto.
    constructor.
  Qed.
  
  Lemma get_label_guarantees :
    forall c1 c2,
      is_proper_location_check rwr c1 (find rwr) c2
                               (get_labels c1 ++ get_labels c2) (repl rwr) = true ->
      (ends_in_not_call c1 /\
       only_labels c1 (get_labels c1 ++ get_labels c2) /\
       only_labels c2 (get_labels c1 ++ get_labels c2) /\
       no_labels (find rwr) (get_labels c1 ++ get_labels c2) /\
       no_labels (repl rwr) (get_labels c1 ++ get_labels c2) /\
       ends_in_not_label c1).
  Proof.
    intros.
    app is_proper_check_sound H.
    unfold is_proper_rewrite_location in *.
    repeat break_and. intuition idtac.
  Qed.

  Lemma in_outside_labels :
    forall z fn_code l c1 c c2 lbls i,
      find_instr z fn_code = Some i ->
      is_label_instr i l ->
      fn_code = c1 ++ c ++ c2 ->
      z < zlen c1 \/ z >= zlen (c1 ++ c) ->
      lbls = get_labels c1 ++ get_labels c2 ->
      In l lbls.
  Proof.
    intros.
    subst fn_code.
    break_or.
    
    app find_instr_range H.          
    exploit (find_instr_append_tail c1 (c ++ c2) nil).
    assert (0 <= z < zlen c1) by omega.
    eauto.
    intros.
    rewrite H3 in H2.
    rewrite app_nil_r in H2.
    app get_labels_all H2.
    rewrite in_app. left. assumption.

    app find_instr_range H.       
    assert (z = zlen (c1 ++ c) + (z - zlen (c1 ++ c))) by omega.
    rewrite H3 in H2.
    remember (z - zlen (c1 ++ c)) as z'.
    exploit (find_instr_append_head (c1 ++ c) c2 z').
    omega.          
    intros.
    rewrite app_assoc in H2.
    rewrite H4 in H2.
    app get_labels_all H2.
    rewrite in_app. right. assumption.
  Qed.
  
  
  Lemma no_label_in_code :
    forall l lbls c,
      In l lbls ->
      no_labels c lbls ->
      label_pos l 0 c = None.
  Proof.
    intros.
    unfold no_labels in *.          
    assert ((exists pos, label_pos l 0 c = Some pos) -> False). {
      intros.
      break_exists.
      app label_pos_find_instr H1.
      app H0 H1.
      constructor.
    }
                                                                intros.
    destruct (label_pos l 0 c).
    assert (exists pos : Z, Some z = Some pos).
    exists z.
    reflexivity.
    congruence.
    reflexivity.
  Qed.

  Lemma range_dec :
    forall z j k,
      j <= k ->
      z <= j \/ (j < z /\ z <= k) \/ k < z.
  Proof.
    intros.
    omega.
  Qed.            

  Lemma zlen_lte_app :
    forall {A} (c1 c : list A),
      zlen c1 <= zlen (c1 ++ c).
  Proof.
    intros.
    rewrite zlen_app.
    name (zlen_nonneg A c1) Hz1.
    name (zlen_nonneg A c) Hz2.
    omega.
  Qed.

  Lemma no_label_in_range :
    forall l lbls fn_code c1 c c2 pos,
      In l lbls ->
      label_pos l 0 fn_code = Some pos ->
      fn_code = c1 ++ c ++ c2 ->
      no_labels c lbls ->
      pos <= zlen c1 \/ pos > zlen (c1 ++ c).
  Proof.
    intros.
    exploit no_label_in_code; eauto. intros. 
    app label_pos_in_range H0.
    name (range_dec pos (zlen c1) (zlen (c1 ++ c)) (zlen_lte_app c1 c)) Hr.
    repeat break_or.
    left; eauto.
    2: right; omega.                                                  
    app (label_pos_append_head c1 l pos (c ++ c2)) H4; try omega.
    rewrite zlen_app in H1.
    app (label_pos_append_tail l c c2 nil (pos - zlen c1)) H4; try omega.
    replace (c ++ nil) with c in *.
    congruence.
    rewrite app_nil_r.
    reflexivity.
  Qed.

  Lemma no_label_in_range' :
    forall l lbls fn_code c1 c c2 pos,
      In l lbls ->
      label_pos l 0 fn_code = Some pos ->
      fn_code = c1 ++ c ++ c2 ->
      no_labels c lbls ->
      ends_in_not_label c1 ->
      pos < zlen c1 \/ pos > zlen (c1 ++ c).
  Proof.
    intros.
    exploit no_label_in_range; eauto. intros.
    assert (pos = zlen c1 -> False).
    intros.
    unfold ends_in_not_label in *.
    app label_pos_find_instr H0.
    subst pos.
    rewrite H1 in H0.
    exploit (find_instr_append_tail c1 (c ++ c2) nil (zlen c1 - 1)).
    app find_instr_range H0.
    omega.
    intros.
    rewrite H5 in H0.
    rewrite app_nil_r in *.
    app H3 H0.
    simpl in *.
    eauto.
    omega.
  Qed.


  Lemma labeled_jump_same_block : 
    forall i st t st',
      (exists l, labeled_jump i l) ->
      step_t (i :: nil) ge st t st' ->
      in_same_block st st'.
  Proof.
    intros.
    repeat P inv step_t.
    destruct i; simpl in *; try solve [break_exists; inv_false].
    
    P inv at_code.
    invs; unify_stuff; try find_one_instr; unify_stuff.
    simpl in *.
    unfold goto_label_bits in *.
    repeat (break_match_hyp; try congruence); st_inv.
    app label_pos_find_instr Heqo.
    eapply global_perms_valid_globals in H20.
    unfold valid_globals in *.
    exploit (H20 b (Int.repr (z - 1))).
    unfold is_global. left. unfold in_code_range.
    unfold fundef in *. collapse_match.
    apex in_range_find_instr Heqo.
    erewrite unsigned_repr_PC; eauto. omega.
    intros.
    assert (Hvp : Memory.Mem.weak_valid_pointer m' b (Int.unsigned (Int.repr z)) = true). {
      eapply Memory.Mem.weak_valid_pointer_spec. right.
      erewrite unsigned_repr_PC; eauto. erewrite unsigned_repr_PC in H3; eauto.
    } idtac.
    name (conj Heqo0 Hvp) Hp.
    erewrite <- weak_valid_pointer_sur in Hp.
    econstructor; eauto. preg_simpl. reflexivity.
    invs; eauto.
    unify_find_funct_ptr.




    
    P inv at_code.
    invs; unify_stuff; try find_one_instr; unify_stuff.
    simpl in *.
    unfold goto_label_bits in *.
    repeat (break_match_hyp; try congruence); st_inv.
    app label_pos_find_instr Heqo0.
    eapply global_perms_valid_globals in H20.
    unfold valid_globals in *.
    exploit (H20 b (Int.repr (z - 1))).
    unfold is_global. left. unfold in_code_range.
    unfold fundef in *. collapse_match.
    apex in_range_find_instr Heqo0.
    erewrite unsigned_repr_PC; eauto. omega.
    intros.
    assert (Hvp : Memory.Mem.weak_valid_pointer m' b (Int.unsigned (Int.repr z)) = true). {
      eapply Memory.Mem.weak_valid_pointer_spec. right.
      erewrite unsigned_repr_PC; eauto. erewrite unsigned_repr_PC in H3; eauto.
    } idtac.
    name (conj Heqo1 Hvp) Hp. 
    erewrite <- weak_valid_pointer_sur in Hp.
    econstructor; eauto. preg_simpl. reflexivity.

    invs; eauto.
    app psur_add_one H11. 
    Focus 2. econstructor.
    Focus 2.
    unfold in_code_range.
    unfold fundef in *. collapse_match.
    rewrite H2.
    name (zlen_nonneg _ c1) zlnc1.
    name (zlen_nonneg _ c2) zlnc2.
    rewrite H7.
    repeat rewrite zlen_app. rewrite zlen_cons.
    omega.
    econstructor; eauto. preg_simpl. find_rewrite. simpl. reflexivity.
    eapply in_range_PC; eauto.
    rewrite H2. rewrite H7.
    rewrite find_instr_append_head by omega.
    simpl. reflexivity.
    unify_find_funct_ptr.


    P inv at_code.
    invs; unify_stuff; try find_one_instr; unify_stuff.
    simpl in *.
    unfold goto_label_bits in *.
    repeat (break_match_hyp; try congruence); st_inv.
    app label_pos_find_instr Heqo1.

    eapply global_perms_valid_globals in H20.
    unfold valid_globals in *.
    exploit (H20 b (Int.repr (z - 1))).
    unfold is_global. left. unfold in_code_range.
    unfold fundef in *. collapse_match.
    apex in_range_find_instr Heqo1.
    erewrite unsigned_repr_PC; eauto. omega.
    intros.
    assert (Hvp : Memory.Mem.weak_valid_pointer m' b (Int.unsigned (Int.repr z)) = true). {
      eapply Memory.Mem.weak_valid_pointer_spec. right.
      erewrite unsigned_repr_PC; eauto. erewrite unsigned_repr_PC in H3; eauto.
    } idtac.
    name (conj Heqo2 Hvp) Hp. 
    erewrite <- weak_valid_pointer_sur in Hp.
    econstructor; eauto. preg_simpl. reflexivity.

    invs; eauto.
    app psur_add_one H11. 
    Focus 2. econstructor.
    Focus 2.
    unfold in_code_range.
    unfold fundef in *. collapse_match.
    rewrite H2.
    name (zlen_nonneg _ c0) zlnc0.
    name (zlen_nonneg _ c3) zlnc3.
    rewrite H7.
    repeat rewrite zlen_app. rewrite zlen_cons.
    omega. 
    econstructor; eauto. preg_simpl. find_rewrite. simpl. reflexivity.
    app psur_add_one H11. 
    Focus 2. econstructor.
    Focus 2.
    unfold in_code_range.
    unfold fundef in *. collapse_match.
    rewrite H2.
    name (zlen_nonneg _ c0) zlnc0.
    name (zlen_nonneg _ c3) zlnc3.
    rewrite H7.
    repeat rewrite zlen_app. rewrite zlen_cons.
    omega.
    eapply in_range_PC; eauto.
    rewrite H2. rewrite H7.
    rewrite find_instr_append_head by omega.
    simpl. reflexivity.
    eapply in_range_PC; eauto.
    rewrite H2. rewrite H7.
    rewrite find_instr_append_head by omega.
    simpl. reflexivity.
    econstructor. reflexivity. reflexivity.
    eauto. preg_simpl. find_rewrite. simpl.
    reflexivity. eauto.
    eapply psur_add_one; eauto. econstructor.
    unfold in_code_range. unfold fundef in *.
    collapse_match. rewrite H7.
    rewrite zlen_app. rewrite zlen_cons.
    rewrite H2. name (zlen_nonneg _ c0) zlnc.
    name (zlen_nonneg _ c3) zlnc3. omega.
    eapply in_range_PC; eauto.
    rewrite H2. rewrite H7.
    rewrite find_instr_append_head by omega.
    simpl. reflexivity.
    
    unify_find_funct_ptr.


    P inv at_code.
    invs; unify_stuff; try find_one_instr; unify_stuff.
    simpl in *.
    unfold goto_label_bits in *.
    repeat (break_match_hyp; try congruence); st_inv.
    app label_pos_find_instr Heqo0.


    eapply global_perms_valid_globals in H20.
    unfold valid_globals in *.
    exploit (H20 b (Int.repr (z - 1))).
    unfold is_global. left. unfold in_code_range.
    unfold fundef in *. collapse_match.
    apex in_range_find_instr Heqo0.
    erewrite unsigned_repr_PC; eauto. omega.
    intros.
    assert (Hvp : Memory.Mem.weak_valid_pointer m' b (Int.unsigned (Int.repr z)) = true). {
      eapply Memory.Mem.weak_valid_pointer_spec. right.
      erewrite unsigned_repr_PC; eauto. erewrite unsigned_repr_PC in H3; eauto.
    } idtac.
    name (conj Heqo1 Hvp) Hp. 
    erewrite <- weak_valid_pointer_sur in Hp.
    econstructor; eauto. preg_simpl. reflexivity.

    invs; eauto.

    unify_find_funct_ptr.
  Qed.

  (* Move to StepIn *)
  Lemma step_t_fundef :
  forall ge rs m rs' m' i t bits b ofs md md',
    step_t (i :: nil) ge (State_bits rs m md) t (State_bits rs' m' md') ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,ofs) ->
    exists f,
      Genv.find_funct_ptr ge b = Some (Internal f).
Proof.
  intros. inv H.
  inv H10.
  inv H4. unify_PC. unify_psur. eauto.
Qed.  

  Lemma outside_step_labeled_jump :
    forall st t st' i,
      outside_range st ->
      step_t (i :: nil) ge st t st' ->
      (exists l, labeled_jump i l) ->
      outside_range st' \/ at_entry st'.
  Proof.
    intros.   
    name H Houtside_range.
    inv H.
    break_exists.
    break_and.
    NP _app step_t_labeled_jump_no_trace step_t. subst.
    destruct st'.
    unfold ge in *.
    NP _app step_t_fundef step_t.
    unify_find_funct_ptr.
    NP _app step_t_labeled_jump step_t.
    destruct x1.
    NP _app labeled_jump_same_block step_t.
    P inv in_same_block.
    find_inversion. find_inversion.
    repeat unify_PC. repeat unify_psur.
    destruct H4. (* transf happened or it didn't *)
    * break_or.
      - (* took the jump *)
        idtac. (* indent *)
        repeat break_exists.
        repeat break_and.
        name H2 Htransf_range.
        inv H2.
        break_and.
        app transf_code_is_proper H11.
        app get_label_guarantees H11.
        repeat break_and.
        simpl in *.
        app split_pat_spec H2.
        unfold fundef in *.
        repeat unify_find_funct_ptr.
        app in_outside_labels H5.
        unfold goto_label_bits in *.
        repeat break_match_hyp; try congruence.
        simpl in *.
        app no_label_in_range H17.
        NP _app label_pos_find_instr label_pos.
        st_inv. preg_simpl_hyp H10.
        inv H10.
        app step_t_md H6; try congruence.
        break_and.
        erewrite weak_valid_pointer_sur in H12; eauto.
        break_and.
        eapply pinj_injective_within_block in H12; try apply Heqo0.
        subst i'.
        assert (z = zlen c1 \/ (z < zlen c1 \/ z > zlen (c1 ++ find rwr))) by omega.
        break_or. right.
        econstructor. preg_simpl. reflexivity.
        erewrite weak_valid_pointer_sur; eauto.
        erewrite unsigned_repr_PC; eauto.

        left. econstructor; try solve [preg_simpl; reflexivity]; eauto.
        erewrite weak_valid_pointer_sur; eauto.
        erewrite unsigned_repr_PC; eauto.
        eexists; split; eauto. simpl.
        left. eexists; eexists; split; eauto; try omega.

      - (* nextinstr *)
        inv H4.
        eapply outside_step_straightlineish; eauto.
    * left. econstructor; eauto.
      eexists. split; eauto.
      simpl. right. eauto.
  Qed.
    
  
  (* Lemma step_t_new_bits : *)
  (*   forall i st t rs' m', *)
  (*     step_t (i :: nil) ge st t (State rs' m') -> *)
  (*     exists bits b ofs (* f z i' *), *)
  (*       rs' PC = Vint bits /\ *)
  (*       psur bits = (b, ofs)  (* /\ (* TODO *) *) *)
  (*       (* Genv.find_funct_ptr ge b = Some (Internal f) /\ *) *)
  (*       (* find_instr z (fn_code f) = Some i'. *) . *)
  (* Proof. *)
  (*   intros. *)
  (*   repeat P inv step_t. *)
  (*   P inv at_code. *)
  (*   invs. *)
  (*   - destruct i1; *)
  (*     try solve [ *)
  (*           assert (rs' PC = nextinstr rs PC); *)
  (*           simpl_exec; *)
  (*           unfold exec_big_load_bits in *; *)
  (*           unfold exec_big_store_bits in *; *)
  (*           unfold compare_floats in *; *)
  (*           unfold compare_floats32 in *; *)
  (*           repeat break_match_hyp; *)
  (*           try state_inv; *)
  (*           preg_simpl; *)
  (*           try congruence; *)
  (*           try app_np straightlineish_exec (nextinstr rs PC); *)
  (*           break_and; *)
  (*           destruct fd; *)
  (*           app step_instr H3; *)
  (*           repeat eexists; eauto *)
  (*         ]. *)

  (*     simpl_exec. *)
  (*     repeat break_match_hyp; try state_inv. *)
  (*     P inv (Vint i1 = Vint bits0). *)
  (*     app_np pinj_psur_inverse pinj. *)
  (*     unify_stuff. *)
  (*     preg_simpl. *)
  (*     repeat eexists; eauto. *)

  (*     simpl_exec. *)
  (*     assert (call_steps_to_beginning_bits prog) *)
  (*       by (unfold calling_conv_correct_bits in *; tauto). *)
  (*     unfold call_steps_to_beginning_bits in *. *)
  (*     unfold Genv.symbol_address in *. *)
  (*     destruct (Genv.find_symbol ge symb) eqn:?. *)

  (*     (* repeat break_match_hyp; state_inv. *) *)
  (*     (* destruct f; unfold ge in *.             *) *)
  (*     (* app H2 H16.     *) *)
  (*     (* break_and. *) *)
  (*     (* eexists. *) *)
  (*     (* eexists. *) *)
  (*     (* eexists. *) *)
  (*     (* eexists. *) *)
  (*     (* eexists. *) *)
  (*     (* eexists. *) *)
  (*     (* split. *) *)
  (*     (* eauto. *) *)
  (*     (* split. *) *)
  (*     (* eauto. *) *)
  (*     (* split. *) *)
  (*     (* app_np pinj_psur_inverse pinj. *) *)
  (*     (* unify_stuff. *) *)
  (*     (* remember (rs # PC <- (Vint i1)) as rs'. *) *)
  (*     (* preg_simpl. *) *)
  (*     (* assert (i1 = x). *) *)
  (*     (* rewrite Heqrs' in H8. *) *)
  (*     (* inv H8. *) *)
  (*     (* reflexivity. *) *)
  (*     (* subst i1. *) *)
  (*     (* unify_stuff. *) *)
  (*     (* repeat eexists. *) *)

  (*     repeat break_match_hyp; state_inv. *)
  (*     destruct f; unfold ge in *. *)
  (*     app H2 H16. *)
  (*     repeat break_and. *)
  (*     copy (conj H8 H9). *)
  (*     eauto. *)
  (*     unfold is_call. constructor. *)

  (*     repeat break_match_hyp; state_inv. *)
  (*     destruct f; unfold ge in *. *)
  (*     app H2 H16. *)
  (*     repeat break_and. *)
  (*     copy (conj H8 H9). *)
  (*     eauto. *)
  (*     unfold is_call. constructor. *)

  (*     simpl_exec. *)
  (*     assert (call_steps_to_beginning_bits prog) *)
  (*       by (unfold calling_conv_correct_bits in *; tauto). *)
  (*     unfold call_steps_to_beginning_bits in *. *)
  (*     repeat break_match_hyp; state_inv. *)
  (*     destruct f; unfold ge in *. *)
  (*     app H2 H16. *)
  (*     repeat break_and. *)
  (*     copy (conj H8 H9). *)
  (*     eauto. *)
  (*     unfold is_call. constructor. *)

  (*     repeat break_match_hyp; try state_inv; *)
  (*     simpl_exec; *)
  (*     repeat break_match_hyp; try state_inv; *)
  (*     unfold goto_label_bits in *; *)
  (*     repeat break_match_hyp; try state_inv. *)
  (*     P inv (Vint i1 = Vint bits0). *)
  (*     app_np pinj_psur_inverse pinj. *)
  (*     unify_stuff. *)
  (*     preg_simpl. *)
  (*     eauto. *)
  (*     exploit straightlineish_exec; eauto. intros. *)
  (*     break_exists. *)
  (*     eauto. *)

  (*     repeat break_match_hyp; try state_inv; *)
  (*     simpl_exec; *)
  (*     repeat break_match_hyp; try state_inv; *)
  (*     unfold goto_label_bits in *; *)
  (*     repeat break_match_hyp; try state_inv. *)
  (*     P inv (Vint i1 = Vint bits0). *)
  (*     app_np pinj_psur_inverse pinj. *)
  (*     unify_stuff. *)
  (*     preg_simpl. *)
  (*     eauto. *)
  (*     exploit straightlineish_exec; eauto. intros. *)
  (*     break_exists. *)
  (*     eauto. *)
  (*     exploit straightlineish_exec; eauto. intros. *)
  (*     break_exists. *)
  (*     eauto. *)

  (*     repeat break_match_hyp; try state_inv; *)
  (*     simpl_exec; *)
  (*     repeat break_match_hyp; try state_inv; *)
  (*     unfold goto_label_bits in *; *)
  (*     repeat break_match_hyp; try state_inv. *)
  (*     app_np pinj_psur_inverse pinj. *)
  (*     unify_stuff. *)
  (*     preg_simpl. *)
  (*     eauto. *)

  (*     simpl_exec. *)
  (*     assert (call_steps_to_beginning_bits prog) *)
  (*       by (unfold calling_conv_correct_bits in *; tauto). *)
  (*     unfold call_steps_to_beginning_bits in *. *)
  (*     unfold Genv.symbol_address in *. *)
  (*     destruct (Genv.find_symbol ge symb) eqn:?. *)
  (*     repeat break_match_hyp; state_inv. *)
  (*     destruct f; unfold ge in *. *)
  (*     app H2 H16. *)
  (*     repeat break_and. *)
  (*     copy (conj H8 H9). *)
  (*     eauto. *)
  (*     unfold is_call. constructor. *)
  (*     repeat break_match_hyp; state_inv. *)
  (*     destruct f; unfold ge in *. *)
  (*     app H2 H16. *)
  (*     repeat break_and. *)
  (*     copy (conj H8 H9). *)
  (*     eauto. *)
  (*     unfold is_call. constructor. *)

  (*     simpl_exec. *)
  (*     assert (call_steps_to_beginning_bits prog) *)
  (*       by (unfold calling_conv_correct_bits in *; tauto). *)
  (*     unfold call_steps_to_beginning_bits in *. *)
  (*     repeat break_match_hyp; state_inv. *)
  (*     destruct f; unfold ge in *. *)
  (*     app H2 H16. *)
  (*     repeat break_and. *)
  (*     copy (conj H8 H9). *)
  (*     eauto. *)
  (*     unfold is_call. constructor. *)
      
  (*     simpl_exec. *)
  (*     assert (return_steps_back_to_call_bits prog) *)
  (*       by (unfold calling_conv_correct_bits in *; tauto). *)
  (*     unfold return_steps_back_to_call_bits in *. *)
  (*     repeat break_match_hyp; state_inv. *)
  (*     destruct f; unfold ge in *. *)
  (*     app H2 H16. *)
  (*     repeat break_and. *)
  (*     copy (conj H8 H9). *)
  (*     eauto. *)
  (*   - unfold transf_program in *. *)
  (*     repeat break_match_hyp; try solve [inversion TRANSF]. *)
  (*     unfold no_builtin_clobber_PC_prog in *. *)
  (*     destruct f. *)
  (*     assert (code_of_prog fn_code prog). *)
  (*     unfold code_of_prog. *)
  (*     app Genv.find_funct_ptr_inversion H12. *)
  (*     eauto. *)
  (*     app n0 H2. *)
  (*     unfold no_builtin_clobber_PC in *. *)
  (*     app H2 H13. *)
  (*     break_and. *)
  (*     preg_simpl. *)
  (*     fold undef_regs. *)
  (*     rewrite set_regs_not_in by eauto. *)
  (*     rewrite undef_regs_not_in by eauto. *)
  (*     rewrite H. *)
  (*     simpl. *)
  (*     eexists. *)
  (*     eexists. *)
  (*     eexists. *)
  (*     split. *)
  (*     reflexivity. *)
  (*     eapply psur_add. *)
  (*     eauto. *)
  (*   - preg_simpl. *)
  (*     rewrite H. *)
  (*     eexists. *)
  (*     eexists. *)
  (*     eexists. *)
  (*     split. *)
  (*     reflexivity. *)
  (*     eapply psur_add. *)
  (*     eauto. *)
  (*   - unify_stuff. *)
  (*     unify_find_funct_ptr. *)
  (* Qed. *)

  Ltac from_cc := unfold calling_conv_correct_bits in *; tauto.

  Ltac inv_step_t := repeat P inv step_t; P inv at_code.
  
  Lemma rwr_not_at_start_or_end :
    forall c0 c1 lbls,
      is_proper_location_check rwr c0 (find rwr) c1 lbls (repl rwr) = true ->
      c0 <> nil /\ c1 <> nil.
  Proof.
    intros.
    unfold is_proper_location_check in *.
    repeat break_match; split; try congruence.
  Qed.

  Lemma quad_list_assoc :
    forall {A} (a b c d : list A),
      (a ++ b) ++ c ++ d = a ++ (b ++ c ++ d).
  Proof.
    intros.
    repeat rewrite app_ass; reflexivity.
  Qed.

  Lemma is_call_and_not_call_absurd:
    forall c,
      ~ is_call_return c ->
      is_call c ->
      False.
  Proof.
    intros.
    destruct c; simpl in *; tauto. 
  Qed.

  Lemma int_eq_absurd :
    forall (a b : Z),
      (a = b -> False) ->
      a <> b.
  Proof.
    intros; omega.
  Qed.

  
  Lemma outside_step_call_return :
    forall st t st' i,
      outside_range st ->
      step_t (i :: nil) ge st t st' ->
      is_call_return i ->
      outside_range st'.
  Proof.

    intros.
    app_np is_call_or_return_dec is_call_return.
    break_or.
    - assert (call_steps_to_beginning_bits prog) by from_cc.
      unfold call_steps_to_beginning_bits in *.      
      inv_step_t.
      invs.
      + unify_stuff.
        name H18 Hfind_instr.
        find_one_instr.
        destruct fd.
        app H1 H18. clear H1. repeat break_and.
        simpl in *.
        econstructor.
        eauto.
        eauto.
        eexists. split; eauto.
        break_match; trivial.
        break_match.
        subst_max.
        
        app functions_translated H9.
        simpl in *.
        unfold transf_code in H9.
        repeat break_match_hyp.
        left.
        repeat econstructor.
        eauto.
        eauto.
        unfold transf_code.
        rewrite Heqo.
        rewrite Heqb0.
        reflexivity.
        rewrite Int.unsigned_zero.
        app_np rwr_not_at_start_or_end is_proper_location_check.
        destruct c; simpl.
        break_and; congruence.
        rewrite zlen_cons.
        name (zlen_nonneg _ c) Hz.
        omega.
        
        right.
        unfold transf_code.
        rewrite Heqo.
        rewrite Heqb0.
        reflexivity.

        right.
        unfold transf_code.
        rewrite Heqo.
        reflexivity.                
      + unify_stuff.
        find_one_instr.
        inv H3.
      + unify_stuff.
        find_one_instr.
        inv H3.
      + unify_stuff.
        unfold fundef in *.
        unify_find_funct_ptr.      
    - assert (return_steps_back_to_call_bits prog) by from_cc.
      unfold return_steps_back_to_call_bits in *.
      break_exists. subst i.
      inv_step_t.
      invs; unify_stuff.
      + name H17 Hfind_instr.
        find_one_instr.
        destruct fd.
        app H1 H17. clear H1.
        repeat break_and. repeat break_exists. repeat break_and.
        unfold ge in *.
        simpl in *.        

        name functions_translated Hf.
        app Hf H8. clear Hf.        
        unfold transf_fundef in *.
        simpl.
        unfold transf_code in *.
        break_match.
        Focus 2.
        econstructor; eauto.
        eexists.
        split; eauto.
        simpl.
        right.
        unfold transf_code in *.
        rewrite Heqo.
        reflexivity.
        break_let.
        break_if.
        Focus 2.
        econstructor; eauto.
        eexists.
        split; eauto.
        simpl.
        right.
        unfold transf_code.
        rewrite Heqo.
        rewrite Heqb0.
        reflexivity.
        
        app_np is_proper_check_sound is_proper_location_check.
        subst_max.
        break_and.
        clear H19.
        assert (ends_in_not_call c) by (unfold is_proper_rewrite_location in *; tauto).
        
        (* ends not in call c *)
        unfold ends_in_not_call in *.
        repeat break_exists.
        assert (x5 = x8 -> False). {
          break_and.
          intros.
          subst x5.          
          app_np is_call_and_not_call_absurd is_call.
        }
        break_and.
        assert (Int.unsigned x1 <> zlen c). {
          apply int_eq_absurd.
          intros.
          apply H23.
          rewrite H25 in *.
          rewrite H19 in *.
          rewrite zlen_app in H25.
          rewrite zlen_cons in H25.
          rewrite zlen_app in H11.
          rewrite zlen_cons in H11.
          simpl in *.          
          replace (zlen x7 + 1 - 1) with (zlen x7) in * by omega.
          exploit find_instr_prefix.
          eapply Heqo.
          reflexivity.
          instantiate (1 := zlen x7).
          rewrite zlen_app.
          rewrite zlen_cons.
          simpl.
          name (zlen_nonneg _ x7) Hx7.
          omega.
          intros.
          rewrite H26 in H11.
          rewrite quad_list_assoc in H11.
          exploit find_instr_append_head.
          instantiate (1 := 0). omega.
          instantiate (3 := x7). 
          instantiate (1 := (x8 :: nil) ++ find rwr ++ c2). 
          intros.
          replace (zlen x7 + 0) with (zlen x7) in H27 by omega.
          simpl in *. repeat rewrite app_ass in H26. simpl in *.
          rewrite H11 in H26.
          rewrite H11 in H27. congruence.
        } idtac.
        (* clear H21. clear H9. clear H22. clear H20. clear H18.        *)
        
        (* no call in rwr *)
        remember (Int.unsigned x1 - 1) as ofs'.
        econstructor; eauto.
        eexists.
        split; eauto.
        simpl.
        unfold transf_code.
        rewrite Heqo.
        break_if.        
        2: right; reflexivity.
        left.
        eexists. eexists.
        split.
        econstructor.
        eauto.
        split.
        eauto.
        unfold transf_code.
        rewrite Heqo.
        rewrite Heqb0.
        reflexivity.
        reflexivity.
        reflexivity.
        assert ((Int.unsigned x1 <= zlen c \/ Int.unsigned x1 >= zlen (c ++ find rwr))
                  -> Int.unsigned x1 < zlen c \/ Int.unsigned x1 >= zlen (c ++ find rwr)).
        intros.
        omega.
        apply H26.
        clear H26.
        (* clear Heqb. clear H23. clear H19. clear H6. clear H. clear H11. clear H7. clear H2.
        clear H13. clear H14. *)
        name (forward_find rwr) Hfwd.
        unfold only_forward_jumps in *.
        break_and.
        clear H2.
        unfold no_calls in *.
        assert (Int.unsigned x1 <= zlen c \/ 
                (zlen c < Int.unsigned x1 /\ Int.unsigned x1 < zlen (c ++ find rwr)) \/ 
                Int.unsigned x1 >= zlen (c ++ find rwr)) by omega.
        break_or; try omega.
        break_or; try omega.
        app split_pat_spec Heqo.
        subst x4.
        rewrite zlen_app in H25. rewrite zlen_cons in H25.
        simpl in H25.
        rewrite zlen_app in H2. rewrite zlen_cons in H2.
        simpl in H2.
        repeat rewrite zlen_app.
        repeat rewrite zlen_cons.
        repeat rewrite zlen_app in H2. repeat rewrite zlen_cons in H2.
        simpl in H2.
        simpl.
          replace (Int.unsigned x1) with (zlen x7 + Int.unsigned x1 - zlen x7) in H11 by omega.
          replace (zlen x7 + Int.unsigned x1 - zlen x7 - 1)
          with (zlen x7 + (Int.unsigned x1 - zlen x7 - 1)) in H11 by omega.
          repeat rewrite app_ass in H11.
          repeat rewrite zlen_app in H2. 
          rewrite find_instr_append_head in H11 by omega.
          replace ((x8 :: nil) ++ find rwr ++ c2) with
          ((x8 :: nil) ++ (find rwr ++ c2)) in H11 by (repeat rewrite app_ass; eauto).
          replace (Int.unsigned x1 - zlen x7 - 1) with (zlen (x8 :: nil) + (Int.unsigned x1 - zlen x7 - 1 - 1)) in H11.
          rewrite find_instr_append_head in H11 by omega.
          erewrite find_instr_append_tail in H11 by omega.
          instantiate (1 := nil) in H11.
          rewrite app_nil_r in H11.
          repeat break_and.
          app H26 H11.
          app is_call_and_not_call_absurd H11. inv_false.
          rewrite zlen_cons. replace (zlen (@nil instruction)) with 0 by auto.
          omega.
      + unify_stuff.
        find_one_instr.
        (* inv H3. *)
      + unify_stuff.
        find_one_instr.
        (* inv H3. *)
      + unify_stuff.
        unfold fundef in *.
        unify_find_funct_ptr.   
  Qed.

  Lemma outside_step_trace_internal :
    forall st t st' i,
      outside_range st ->
      step_t (i :: nil) ge st t st' ->
      trace_internal i ->
      outside_range st' \/ at_entry st'.
  Proof.     
    intros.
    destruct st as (rs, m). destruct st' as (rs', m').
    assert (rs' PC = nextinstr rs PC).
    2: app outside_step_straightlineish H2.
    inv_step_t.
    invs.
    - unify_stuff.
      find_one_instr.    
      destruct i1; inv H1;
      simpl in *;
      state_inv;
      unify_stuff.
    - unify_stuff.
      P copy find_instr.
      find_one_instr.        

      (* PC clobber stuff *)      
      unfold transf_program in *.
      repeat break_match_hyp; try solve [inversion TRANSF].
      unfold no_builtin_clobber_PC_prog in *.
      destruct fd.
      assert (Hcop : code_of_prog fn_code prog). {
        unfold code_of_prog.
        app Genv.find_funct_ptr_inversion H16.
        eexists; eexists; simpl; eauto.
      }
      idtac. (* damnit indenting *)
      
      app n0 Hcop.
      unfold no_builtin_clobber_PC in *.      
      NP1 _app Hcop find_instr.
      break_and.
      preg_simpl.
      fold undef_regs.
      break_and.
      rewrite set_regs_not_in by eauto.      
      rewrite undef_regs_not_in by eauto.
      reflexivity.      
    - preg_simpl.
      reflexivity.
    - unify_stuff.
      unify_find_funct_ptr.
  Qed.

  Lemma outside_step_nonstraight :
    forall st t st' i,
      outside_range st ->
      step_t (i :: nil) ge st t st' ->
      ~ straightline i ->
      outside_range st' \/ at_entry st'.
  Proof.
    intros.
    name (instr_class i) Hinstr.
    break_or; try congruence.
    repeat break_or.
    break_exists.    
    app outside_step_labeled_jump H0.
    app outside_step_call_return H2.
    app outside_step_trace_internal H2.
  Qed.

  (* this is how we do single entry *)
  (* we never step to the inside without going through entry *)
  Lemma outside_step_dec :
    forall st t st',
      outside_range st ->
      step_bits (Genv.globalenv prog) st t st' ->
      (outside_range st' \/ at_entry st').
  Proof.
    intros.
    app step_t_or_external H0.
    break_or. break_exists.
    destruct (straightline_dec x).
    app outside_step_straight H0.
    app outside_step_nonstraight H0.
    repeat break_exists.
    repeat break_and.
    subst.
    app outside_step_external H1.
  Qed.

  Lemma no_trace_no_builtin :
    forall i,
      no_trace i ->
      ~ is_builtin i.
  Proof.
    intros.
    destruct i; simpl in *; try tauto.
  Qed.

  
  Lemma at_entry_step_dec :
    forall st st' t,
      at_entry st ->
      step_bits (Genv.globalenv prog) st t st' ->
      (in_transf st' \/ outside_range st').
  Proof.    
    intros. inv H.
    name (forward_find rwr) ffr.
    name H3 Htransf_range.
    inv H3. break_and.
    app split_pat_spec H3.
    assert (Hzlnf : zlen (find rwr) > 0).
    name (find_nonempty rwr) fnr.
    destruct (find rwr). congruence.
    rewrite zlen_cons.
    name (zlen_nonneg instruction c0) zlnc.
    omega.

    invs.

    Focus 2.
    unify_psur.
    unify_stuff.
    replace (zlen c1) with (zlen c1 + 0) in * by omega.
    rewrite H5 in *.
    simpl in *.
    rewrite find_instr_append_head in H13 by omega.
    rewrite find_instr_append_tail with (c := nil) in H13 by omega.
    rewrite app_nil_r in H13.
    unfold only_forward_jumps in *.
    repeat break_and.
    unfold no_trace_code in *.
    app H2 H13.
    inv H13.

    Focus 2.
    unify_stuff.
    rewrite H5 in *.
    replace (zlen c1) with (zlen c1 + 0) in * by omega.
    simpl in *.
    rewrite find_instr_append_head in H15 by omega.
    rewrite find_instr_append_tail with (c := nil) in H15 by omega.
    rewrite app_nil_r in H15.
    name (no_trace_find rwr) ntr. unfold no_trace_code in ntr.
    app ntr H15. simpl in H15. inv H15.

    Focus 2.    
    unify_stuff.    
    unify_find_funct_ptr.
    
    unify_stuff.
    name H15 Hfind_instr.    
    rewrite H5 in H15.
    replace (zlen c1) with (zlen c1 + 0) in * by omega.
    simpl in *.
    rewrite find_instr_append_head in H15 by omega.
    rewrite find_instr_append_tail with (c := nil) in H15 by omega.
    rewrite app_nil_r in H15.

    unfold only_forward_jumps in ffr.
    repeat break_and.     
    rename H into Hno_calls.
    rename H2 into Hno_trace.
    unfold no_calls in Hno_calls.
    unfold no_trace_code in Hno_trace.
    NP1 _app Hno_trace find_instr.
    NP1 _app Hno_calls find_instr.

    
    assert (exists i bits', rs' PC = Vint bits' /\ psur md' bits' = Some (b, i)).  {
      eapply step_PC_same_block; eauto.
      eapply no_trace_no_builtin; eauto.
    }         
    repeat break_exists.
    (* now we have just a few cases *)
    (* we case on where x is *)
    (* if outside range, easy *)
    (* if inside transf, construct step_in, easy *)
    (* if at_entry, create step_in, contra with forward jumps *)
    assert ((Int.unsigned x < zlen c1) \/ (Int.unsigned x = zlen c1) \/ (Int.unsigned x > zlen c1 /\ Int.unsigned x < zlen c1 + zlen (find rwr)) \/ (Int.unsigned x >= zlen c1 + zlen (find rwr))).
    omega.
    break_and.
    rename bits0 into bits. rename x0 into bits'. rename x into ofs'. rename i0 into instr.
    repeat break_or.

    - right. econstructor; eauto. eexists. split; eauto. simpl. 
      app transf_code_is_proper H4.
      left. eexists. eexists. split. econstructor. eauto.
      split. eauto. eauto. reflexivity. reflexivity.
      omega.
    - assert (at_code (zlen c1) (find rwr) 0 (Genv.globalenv prog) (State_bits rs m md)).
      econstructor; eauto.
      omega.
      simpl.
      reflexivity.
      assert (at_code (zlen c1) (find rwr) 0 (Genv.globalenv prog) (State_bits rs' m' md')).
      econstructor; eauto.
      omega.
      omega.
      simpl.
      reflexivity.
      exploit only_forward_PC_incr; eauto.
      apply (forward_find rwr).
      unfold transf_program in TRANSF.
      repeat break_match_hyp; inversion TRANSF; eauto.
      split; eauto.

      unfold not_after_label_in_code.
      intros.
      app transf_code_is_proper H4.
      app is_proper_check_sound H4.
      repeat break_and.
      P inv is_proper_rewrite_location.
      repeat break_and.
      inv H18.
      unify_stuff.
      app @list_eq_middle_therefore_eq H18.
      inv H18.
      eauto using mk_ends_in_not_label_from_after_code.
      intros.
      omega.
    - left. econstructor.
      3: eauto.
      2: eauto.
      eauto. eauto.
      econstructor.
      instantiate (1 := Int.unsigned ofs' - Int.unsigned i). omega.
      fold ge.
      rewrite H5. replace (zlen c1 + 0) with (zlen c1) by omega.
      econstructor; eauto.
      omega. omega. simpl. reflexivity.
      eapply star_refl.
    - right. econstructor; eauto. eexists. split; eauto. simpl.
      app transf_code_is_proper H4.
      left. eexists. eexists. split. econstructor. eauto.
      split. eauto. eauto. reflexivity. reflexivity.
      rewrite zlen_app.
      omega.
  Qed.

End PRESERVATION.
