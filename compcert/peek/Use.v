Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Axioms.
Require Import Floats.
Require Import Asm.
Require Import Values.
Require Import Memory.

Require Import PeekTactics.
Require Import PregTactics.
Require Import PeekLib.
Require Import AsmCallingConv.
Require Import AsmBits.
Require Import MemoryAxioms.
Require Import ValEq.
Require Import MemEq.
Require Import UseBasic.

Require Import NoPtr.

Require Import MemBits.
Require Import Maps.

Lemma val_eq_longofwords :
  forall v1 v2 v1' v2',
    val_eq v1 v2 ->
    val_eq v1' v2' ->
    val_eq (Val.longofwords v1 v1') (Val.longofwords v2 v2').
Proof.
  intros. unfold val_eq in *.
  repeat break_match_hyp; try inv_false; subst; simpl;
  intros; try congruence;
  unfold Val.longofwords;
  repeat break_match; try congruence.
Qed.


Lemma eval_annot_arg_rs :
  forall (prog : AST.program fundef unit) a (s1 s2 : preg -> Values.val) m b md,
    eval_annot_arg_bits md (Genv.globalenv prog) s1 (s1 (IR ESP)) m a b ->
    forall m',
    mem_eq md m m' ->
    (val_eq (s1 ESP) (s2 ESP)) ->
    (forall r, In r (get_annot_preg a) -> val_eq (s1 r) (s2 r)) ->
    exists b',
      eval_annot_arg_bits md (Genv.globalenv prog) s2 (s2 (IR ESP)) m' a b' /\ val_eq b b'.
Proof.
  
  induction 1; intros;
  try solve [  
        eexists; split; try econstructor; eauto;
        eapply H1; simpl; intuition idtac].

  
  * rewrite H in H3. simpl in H3. rewrite <- H3 in *.
    unfold Mem.loadv in *.
    simpl in *.
    app eq_mem_load H1. break_and.
    exists x.
    split; auto. econstructor; eauto.
  * app val_eq_or H0.
    break_or. 
    destruct (Val.add (s2 ESP) (Vint ofs)) eqn:?;
    exists (Val.add (s2 ESP) (Vint ofs));
    split; try econstructor; eauto;
    rewrite H3; simpl; eauto;
    try solve [intros; congruence].
           unfold Val.add in Heqv.
           break_match_hyp; try congruence.
           rewrite H3 in H2. simpl in H2.
           congruence.
    exists (Val.add (s2 ESP) (Vint ofs)).
    split. econstructor; eauto. 
    unfold Val.add.
    break_match; simpl; try rewrite <- H3; eauto;
    intros; congruence.
  * unfold Mem.loadv in *. simpl in *.
    break_match_hyp; try congruence.
    app eq_mem_load H. break_and.
    exists x.
    split; eauto.
    econstructor; eauto.
    unfold Mem.loadv.
    find_rewrite. eauto.
  * exists Vundef.
           split; simpl; eauto.
           econstructor; eauto.
           intros. congruence.
  * 
  edestruct IHeval_annot_arg_bits1; eauto.
  intros. eapply H3. simpl.
  rewrite in_app. left. eauto.
  break_and.
  edestruct IHeval_annot_arg_bits2; eauto.
  intros. eapply H3. simpl.
  rewrite in_app. right. eauto.
  break_and.
  eexists. split. econstructor; eauto.
  eapply val_eq_longofwords; eauto.

Qed.

Lemma list_forall2_annot:
  forall (prog : AST.program fundef unit) s1 s2 args vargs ef m m' md,
    list_forall2 (eval_annot_arg_bits md (Genv.globalenv prog) s1 (s1 (IR ESP)) m) args vargs ->
    (forall p, In p (use (Pannot ef args)) -> val_eq (s1 p) (s2 p)) ->
    mem_eq md m m' ->
    exists vargs',
      list_forall2 (eval_annot_arg_bits md (Genv.globalenv prog) s2 (s2 (IR ESP)) m') args vargs' /\ list_forall2 val_eq vargs vargs'.
Proof.
  intros. induction H;
    try solve [eexists; split; econstructor; eauto].
  app eval_annot_arg_rs H;
    try eapply H0;
    repeat break_and.

  Focus 2. simpl. right. left. eauto.
  Focus 2. intros. apply H0. simpl.
  right. right. rewrite in_app. left. auto.
  destruct (IHlist_forall2).
  intros. apply H0. simpl. 
  rewrite in_app. simpl in H5.
  intuition idtac.
  break_and. exists (x :: x0).
  split; econstructor; eauto.
Qed.

Ltac unify_all :=
  try unify_psur;
  simpl in *;
  try unify_find_funct_ptr;
  simpl in *;
  try unify_find_instr;
  simpl in *.

Fixpoint getres (res : list preg) (vl : list Values.val) : list preg :=
  match res with
    | nil => nil
    | f :: r =>
      match vl with
        | nil => nil
        | x :: y => f :: getres r y
      end
  end.

Lemma set_regs_gnot_in :
  forall res vl x,
    ~ (In x (getres res vl)) ->
    forall rs,
      (set_regs res vl rs) x = rs x.
Proof.
  induction res; intros.
  simpl. reflexivity.
  simpl in H. break_match_hyp; simpl in H.
  subst vl. simpl. reflexivity.
  eapply Decidable.not_or in H.
  break_and. simpl.
  rewrite IHres by eauto.
  preg_simpl. reflexivity.
Qed.
  
Lemma set_regs_gin :
  forall res vl x,
    In x (getres res vl) ->
    forall rs rs',
      (set_regs res vl rs) x = (set_regs res vl rs') x.
Proof.
  induction res; intros.
  simpl in H. inv H.
  simpl in H. break_match_hyp; simpl in H; try solve [inv H].
  destruct (in_dec preg_eq x (getres res l)).
  simpl. apply IHres. eauto.
  simpl. repeat rewrite set_regs_gnot_in by eauto.
  break_or; try congruence.
  preg_simpl. reflexivity.
Qed.

Lemma undef_regs_undef :
  forall l x rs,
    In x l ->
    undef_regs l rs x = Values.Vundef.
Proof.
  induction l; intros.
  simpl in H. inv_false.
  simpl in H.
  destruct (in_dec preg_eq x l).
  simpl. rewrite IHl; eauto.
  break_or; try congruence.
  simpl. rewrite undef_regs_not_in; eauto.
  preg_simpl. reflexivity.
Qed.

Lemma val_eq_list_lessdef :
  forall a a',
    list_forall2 val_eq a a' ->
    Val.lessdef_list a a'.
Proof.
  induction 1; intros;
  econstructor; eauto.
  eapply val_eq_lessdef; eauto.
Qed.

Lemma no_ptr_nextinstr_nf :
  forall rs,
    (forall x, ~ In x flags -> forall b i, rs x <> Vptr b i) ->
    no_ptr_regs (nextinstr_nf rs).
Proof.
  intros. unfold no_ptr_regs.
  intros. unfold nextinstr_nf.
  unfold nextinstr. simpl.
  repeat preg_case; try congruence.
  name (H PC) HPC.
  unfold Val.add. repeat break_match; try congruence.
  unfold Vone in *. congruence.
  unfold Vone in *. inv Heqv0.
  exfalso. eapply HPC. simpl. intuition idtac; try congruence.
  reflexivity. eapply H. simpl. intuition idtac.
Qed.

Lemma set_regs_either :
  forall res rs l reg,
    set_regs res l rs reg = rs reg \/
    exists v, set_regs res l rs reg = v /\ In v l.
Proof.
  induction res; intros.
  left. simpl. reflexivity.
  simpl. break_match. left. reflexivity.
  subst l. simpl.
  destruct (in_dec preg_eq reg (getres res l0)).
  erewrite set_regs_gin; eauto.
  instantiate (1 := rs).
  specialize (IHres rs l0 reg).
  destruct IHres. left. auto.
  right. break_exists. exists x. break_and. split; auto.
  rewrite set_regs_gnot_in; eauto.
  clear IHres. clear n.
  preg_case. right. eauto.
  left. eauto.
Qed.

Lemma encode_long_no_ptr :
  forall v v' x t,
    val_eq v v' ->
    In x (encode_long t v') ->
    forall b i,
      x <> Vptr b i.
Proof.
  intros. unfold encode_long in *.
  unfold val_eq in *.
  destruct v; simpl in H; try inv_false; try subst v';
  repeat break_match_hyp; simpl in *; repeat break_or; try inv_false;
  eauto; try congruence. unfold Val.hiword. break_match; try congruence.
  unfold Val.loword. break_match; try congruence.  
Qed.

Lemma global_perms_mem_eq :
  forall md m m',
    mem_eq md m m' ->
    forall ge,
      global_perms ge m ->
      global_perms ge m'.
Proof.
  intros.
  unfold global_perms in *.
  intros. app H0 H1.
  break_and.
  unfold mem_eq in *.
  repeat break_and.
  app H6 H1.
Qed.

Lemma list_forall2_inv_right :
  forall {A : Type} (P : A -> A -> Prop) (l l' : list A),
    list_forall2 P l l' ->
    forall x,
      In x l' ->
      exists y,
        In y l /\ P y x.
Proof.
  induction 1; intros.
  simpl in H. inv_false.
  simpl in H1.
  break_or. simpl. exists a1.
  split; auto.
  app IHlist_forall2 H2.
  exists x0. simpl.
  split. right. break_and. auto.
  break_and. auto.
Qed.

Lemma list_forall2_map :
  forall l (rs rs' : regset),
    (forall r, In r l -> val_eq (rs r) (rs' r)) ->
      list_forall2 val_eq (map rs l) (map rs' l).
Proof.
  induction l; intros.
  simpl. econstructor.
  simpl. econstructor. eapply H. simpl. left. auto.
  eapply IHl. intros. eapply H. simpl. right. auto.
Qed.

Lemma val_eq_hiword :
  forall v v',
    val_eq v v' ->
    val_eq (Val.hiword v) (Val.hiword v').
Proof.
  intros.
  unfold val_eq in H.
  break_match_hyp; subst; simpl; eauto;
  try congruence.
  intros. unfold Val.hiword.
  break_match; congruence.
Qed.

Lemma val_eq_loword :
  forall v v',
    val_eq v v' ->
    val_eq (Val.loword v) (Val.loword v').
Proof.
  intros.
  unfold val_eq in H.
  break_match_hyp; subst; simpl; eauto;
  try congruence.
  unfold Val.loword; break_match; congruence.
Qed.

Lemma set_regs_efres:
  forall ef p r v v' rs rs',
    In p r ->
    (forall p0, In p0 (efres ef r) -> val_eq (rs p0) (rs' p0)) ->
    val_eq v v' ->
    val_eq ((set_regs r (encode_long (sig_res (ef_sig ef)) v) rs) p) ((set_regs r (encode_long (sig_res (ef_sig ef)) v') rs') p).
Proof.
  induction r; intros.
  * simpl in H. inv H.
  * unfold efres in *; simpl in H0; repeat break_match_hyp.
    
    simpl. repeat rewrite set_regs_nil. 
    
    destruct (preg_eq p a). subst. simpl. 
    repeat rewrite set_regs_nil. repeat rewrite Pregmap.gss.
    assumption.

    simpl. repeat rewrite set_regs_nil. repeat rewrite Pregmap.gso by auto.
    apply H0. simpl in H. destruct H. congruence. assumption.

    destruct (preg_eq p a). subst. simpl. 
    repeat rewrite set_regs_nil. repeat rewrite Pregmap.gss.
    assumption.

    simpl. repeat rewrite set_regs_nil. repeat rewrite Pregmap.gso by auto.
    apply H0. simpl in H. destruct H. congruence. assumption.

    destruct (preg_eq p a). subst. simpl.
    destruct r. simpl. repeat rewrite Pregmap.gss.
    eapply val_eq_hiword; assumption.
    
    simpl. repeat rewrite set_regs_nil.
    destruct (preg_eq p a). subst. repeat rewrite Pregmap.gss.
    eapply val_eq_loword; assumption.
    rewrite Pregmap.gso by auto.
    rewrite Pregmap.gss.
    rewrite Pregmap.gso by auto.
    rewrite Pregmap.gss.

    eapply val_eq_hiword; assumption.
    
    destruct r. simpl.
    repeat rewrite Pregmap.gso by auto.
    simpl in H. destruct H. congruence. inv H.
    destruct (preg_eq p p0).
    simpl. repeat rewrite set_regs_nil.
    subst. rewrite Pregmap.gss. rewrite Pregmap.gss.

    eapply val_eq_loword; assumption.
    simpl. repeat rewrite set_regs_nil.
    repeat rewrite Pregmap.gso by auto.
    apply H0. simpl. simpl in H.
    destruct H. congruence. destruct H. congruence.
    assumption.

    destruct (preg_eq p a). subst. simpl.
    repeat rewrite set_regs_nil. repeat rewrite Pregmap.gss.
    assumption.

    simpl. repeat rewrite set_regs_nil. repeat rewrite Pregmap.gso by auto.
    apply H0. simpl in H. destruct H. congruence. assumption.

    destruct (preg_eq p a). subst. simpl.
    repeat rewrite set_regs_nil. repeat rewrite Pregmap.gss.
    assumption.
    
    simpl. repeat rewrite set_regs_nil. repeat rewrite Pregmap.gso by auto.
    apply H0. simpl in H. destruct H. congruence. assumption.

    destruct (preg_eq p a). subst. simpl.
    repeat rewrite set_regs_nil. repeat rewrite Pregmap.gss.
    assumption.
    
    simpl. repeat rewrite set_regs_nil. repeat rewrite Pregmap.gso by auto.
    apply H0. simpl in H. destruct H. congruence. assumption.

    destruct (preg_eq p a). subst. simpl.
    repeat rewrite set_regs_nil. repeat rewrite Pregmap.gss.
    assumption.

    simpl. repeat rewrite set_regs_nil. repeat rewrite Pregmap.gso by auto.
    apply H0. simpl in H. destruct H. congruence. assumption.
Qed.

Ltac invs2 :=
  match goal with
    | [ H : step_bits _ _ _ _, H2 : step_bits _ _ _ _ |- _ ] => inv_step H; inv_step H2
  end.

Lemma val_eq_set_regs :
  forall v v',
    list_forall2 val_eq v v' ->
    forall r rs rs' p,
      val_eq (rs p) (rs' p) ->
      val_eq (set_regs r v rs p)
             (set_regs r v' rs' p).
Proof.
  intros v v' H.
  induction H; intros.
  repeat rewrite set_regs_nil. eauto.
  destruct r; simpl. eauto.
  eapply IHlist_forall2; eauto.
  preg_case; try subst; eauto.
Qed.

Lemma val_eq_undef_regs :
  forall rs rs' p,
    val_eq (rs p) (rs' p) ->
    forall l,
      val_eq (undef_regs l rs p) (undef_regs l rs' p).
Proof.
  induction l; intros. simpl. eauto.
  simpl.
  destruct (in_dec preg_eq p l).
  erewrite undef_regs_in with (rs' := rs); eauto.
  erewrite undef_regs_in with (rs := rs' # a <- Values.Vundef)(rs' := rs'); eauto.
  repeat rewrite undef_regs_not_in; eauto.
  preg_case; simpl; eauto.
  congruence.
Qed.



Lemma val_eq_decode_longs :
  forall sg l l',
    list_forall2 val_eq l l' ->
    list_forall2 val_eq (decode_longs sg l)
                   (decode_longs sg l').
Proof.
  induction sg; intros; simpl; repeat break_match; subst; try solve [econstructor];
  inv H;
  try solve [
        econstructor; eauto;
        eapply IHsg; eauto].
  inv H5. inv H5.
  inv H5. econstructor.
  eapply val_eq_longofwords; eauto.
  eapply IHsg; eauto.
Qed.

Lemma use_def_spec :
  forall p s1 s1' s2 b z s c i m m0 m' t bits md md',
    s1 PC = Values.Vint bits ->
    s2 PC = Values.Vint bits ->
    no_ptr_regs s2 ->
    psur md bits = Some (b,z) ->
    @Genv.find_funct_ptr fundef unit (Genv.globalenv p) b = Some (Internal (mkfunction s c)) ->
    find_instr (Int.unsigned z) c = Some i -> 
    (forall p,
       In p (use i) -> val_eq (s1 p) (s2 p)) ->
    step_bits (Genv.globalenv p) (State_bits s1 m md) t (State_bits s1' m' md') ->
    mem_eq md m m0 ->
    no_ptr_mem m0 ->
    ~ is_call_return i ->
    (exists s2' m0',
       step_bits (Genv.globalenv p) (State_bits s2 m0 md) t (State_bits s2' m0' md') /\ (forall p, In p (def i) -> val_eq (s1' p) (s2' p)) /\ mem_eq md' m' m0'
    ).
Proof.
  intros.
  invs.
  *
    unify_all.
    
    match goal with
      | [ H : Genv.find_funct_ptr _ _ = _ |- _ ] =>
        name H Hge;
          eapply use_spec with (s1 := s1) (s2 := s2) in H; eauto
    end.

    repeat break_exists. do 2 eexists.
    split.
    eapply exec_step_internal_bits; eauto.
    unfold mem_eq in *.
    repeat break_and. assumption.
    eapply global_perms_mem_eq; eauto.
    intros. eapply use_def_exec; eauto.
      
  * app mem_eq_extcall' H20.
    repeat break_and.
    eexists. eexists.
    repeat unify_psur.
    split.
    rewrite H14. econstructor; eauto.
    eapply no_ptr_nextinstr_nf.
    intros.
    edestruct (set_regs_either res).
    rewrite H15.
    destruct (in_dec preg_eq x1 (map preg_of (Machregs.destroyed_by_builtin ef))).
    rewrite undef_regs_undef by assumption. congruence.
    rewrite undef_regs_not_in by assumption. apply H1.
    break_exists. break_and. rewrite H15.
    app (@list_forall2_inv_right val) H12.
    break_and. unfold val_eq in H21.
    break_match_hyp; try congruence.
    eapply no_ptr_mem_eq; eauto.
    unfold mem_eq in *.
    repeat break_and. assumption.
    eapply global_perms_mem_eq; eauto.

    split.
    intros.
    repeat unify_psur. repeat unify_find_funct_ptr.
    simpl in *. unify_find_instr.
    simpl in *. 
    eapply val_eq_nextinstr_nf. intros.
    rewrite in_app in H2.
    simpl in H15.
    apply Decidable.not_or in H15; break_and.
    apply Decidable.not_or in H16; break_and.
    apply Decidable.not_or in H18; break_and.
    apply Decidable.not_or in H19; break_and.
    apply Decidable.not_or in H20; break_and.

    assert (p0 = PC \/ In p0 res \/ In p0 (map preg_of (Machregs.destroyed_by_builtin ef))) by (
      repeat break_or; try congruence; try (left; reflexivity); prove_or_eq assumption; assumption). 

    clear H2.

    inv H11. inv H10.
    destruct (in_dec preg_eq p0 res).
    eapply set_regs_efres; eauto.
    intros.
    
    destruct (in_dec preg_eq p1 (map preg_of (Machregs.destroyed_by_builtin ef))).
    repeat rewrite undef_regs_undef by assumption.
    simpl. congruence.
    repeat rewrite undef_regs_not_in; eauto.
    eapply H5. right. rewrite in_app. right. eauto.

    app mem_eq_extcall H11. repeat break_and.
    eapply external_call_determ in H11; try eapply H2.
    break_and.
    specialize (H30 eq_refl). break_and.
    subst. assumption.

    eapply val_eq_decode_longs.
    eapply list_forall2_map. intros.
    eapply H5. right. rewrite in_app. left. auto.

    repeat rewrite set_regs_not_in by assumption.
    
    repeat break_or; try congruence.
    destruct (in_dec preg_eq PC (map preg_of (Machregs.destroyed_by_builtin ef))).
    repeat rewrite undef_regs_undef by assumption.
    simpl. congruence.
    repeat rewrite undef_regs_not_in; eauto.
    repeat rewrite undef_regs_undef by assumption. simpl. congruence.
    
    congruence.
    
    eapply list_forall2_map.
    intros. apply H5. repeat unify_psur.
    unify_find_funct_ptr.
    simpl in *. rewrite H4 in H19. inv H19.
    simpl. right. rewrite in_app. left. assumption.
    
  *
    unify_psur. unfold fundef in *.
    unify_find_funct_ptr. simpl in *.
    rewrite H4 in *. opt_inv. subst.

    eapply (list_forall2_annot p s1 s2) in H23;
    intros;
    try eapply H5;
    eauto.
    repeat break_exists. break_and.
    app mem_eq_extcall H24.
    
    repeat break_and. rewrite H15.

    eexists. eexists. split.
    eapply exec_step_annot_bits; eauto.
    eapply no_ptr_mem_eq; eauto.
    unfold mem_eq in *. tauto.
    eapply global_perms_mem_eq; eauto.

    split.
    intros. simpl in H16. break_or; try inv_false.
    preg_simpl. eapply val_eq_add.
    eapply H5. simpl. left. reflexivity.
    simpl. reflexivity.

    congruence.
    
  * unify_psur. unify_find_funct_ptr.

Qed.

Lemma def_spec' :
  forall prog s c z b i s1 m s1' m' t bits md md',
    s1 PC = Values.Vint bits ->
    psur md bits = Some (b,z) ->
    @Genv.find_funct_ptr fundef unit (Genv.globalenv prog) b = Some (Internal (mkfunction s c)) ->
    find_instr (Int.unsigned z) c = Some i ->
    step_bits (Genv.globalenv prog) (State_bits s1 m md) t (State_bits s1' m' md') ->
    ~ is_call_return i ->
    (forall p, (In p (def i) \/ s1 p = s1' p)).
Proof.
  intros. invs; unify_all.

  *
    eapply def_spec; eauto.


  * destruct (preg_eq PC p).
      left. left. assumption.
    destruct (in_dec preg_eq p flags).
      left. simpl. simpl in i. tauto.
    destruct (in_dec preg_eq p res).
      left. simpl. repeat right. rewrite in_app. left. assumption.
    destruct (in_dec preg_eq p (map preg_of (Machregs.destroyed_by_builtin ef))).
      left. simpl. repeat right. rewrite in_app. right. assumption.
    right. unfold nextinstr_nf. fold flags.
    unfold nextinstr. rewrite Pregmap.gso by auto.
    rewrite undef_regs_not_in by auto.
    rewrite set_regs_not_in by auto.
    rewrite undef_regs_not_in by auto.
    reflexivity.

  * destruct (preg_eq PC p).
      left. simpl. left. assumption.
    right. unfold nextinstr.
    rewrite Pregmap.gso by auto.
    reflexivity.
Qed.

Lemma val_eq_refl :
  forall v,
    (forall b ofs, v <> Vptr b ofs) ->
    val_eq v v.
Proof.
  intros. unfold val_eq.
  break_match; auto.
  congruence.
Qed.



(* Lemma use_def_exec' : *)
(*   forall prog s c i b z s1 s2 m m' s1' s2' m0 m0' t bits md md', *)
(*     s1 PC = Values.Vint bits -> *)
(*     s2 PC = Values.Vint bits -> *)
(*     psur md bits = Some (b,z) -> *)
(*     @Genv.find_funct_ptr fundef unit (Genv.globalenv prog) b = Some (Internal (mkfunction s c)) -> *)
(*     find_instr (Int.unsigned z) c = Some i -> *)
(*     step_bits (Genv.globalenv prog) (State_bits s1 m md) t (State_bits s1' m' md') -> *)
(*     step_bits (Genv.globalenv prog) (State_bits s2 m0 md) t (State_bits s2' m0' md') -> *)
(*     mem_eq md m m0 -> *)
(*     (forall p, In p (use i) -> val_eq (s1 p) (s2 p)) -> *)
(*     ~ is_call_return i -> *)
(*     (forall p, In p (def i) -> val_eq (s1' p) (s2' p)) /\ mem_eq md' m' m0'. *)
(* Proof. *)
(*   intros. invs2; repeat unify_all; try state_inv. *)

(*   * eapply use_def_exec; eauto. *)
(*   * split; intros. *)
(*     eapply val_eq_nextinstr_nf. *)
(*     intros. *)
(*     repeat break_or; try subst p; *)
(*     try solve [exfalso; apply H9; simpl; prove_or_eq reflexivity]. *)
(*     eapply val_eq_set_regs. *)
    
(*     eapply val_eq_undef_regs. *)
    
(*     eapply H7. left. eauto. *)

(*     inv H19. inv H27. *)

(*     rewrite in_app in H1. break_or. *)
(*     eapply set_regs_efres. eauto. *)
(*     intros. *)
(*     eapply val_eq_undef_regs. apply H7. *)
(*     right. rewrite in_app. right. eauto. *)

    

(*     eapply val_eq_set_regs. *)

(*     repeat rewrite undef_regs_undef by assumption. *)
(*     simpl. auto. *)
(*     congruence. *)
    
(*   * split; intros. *)
(*     break_or; try inv_false. *)
(*     eapply val_eq_nextinstr. *)
(*     eapply H7; eauto. *)
(* Qed. *)
    
