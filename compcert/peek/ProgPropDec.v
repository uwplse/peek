Require Import Coqlib.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Asm.
Require Import Integers.
Require Import Maps.
Require Import Errors.

Require Import Zlen.
Require Import SplitLib.
Require Import FindInstrLib.
Require Import PeekLib.
Require Import PeekTactics.

Definition no_PC_overflow (c : code):=
  forall z i,
    find_instr z c = Some i ->
    0 <= z < Int.max_unsigned.

Definition no_PC_overflow_dec :
  forall c,
    { no_PC_overflow c } + { ~ no_PC_overflow c }.
Proof.
  intros. 
  destruct (zlt (Int.max_unsigned) (zlen c)).
  right. unfold not. intros.
  unfold no_PC_overflow in H.
  assert (Int.max_unsigned >= 0).
    unfold Int.max_unsigned. unfold Int.modulus.
    unfold Int.wordsize. unfold Wordsize_32.wordsize.
    simpl. omega.
  assert (exists i, find_instr (Int.max_unsigned) c = Some i).
    apply in_range_find_instr. omega.
  break_exists. app H H1. omega.
  left. unfold no_PC_overflow. intros.
  assert (exists i, find_instr z c = Some i).
  eexists; eauto.
  apply in_range_find_instr in H0.
  omega.
Defined.

Definition labels_valid (c : code) :=
  forall l z, label_pos l 0 c = Some z ->
              exists i, find_instr z c = Some i.

Definition is_any_label (i : instruction) :=
  match i with
    | Plabel _ => True
    | _ => False
  end.

Definition is_any_label_dec :
  forall i,
    { l | i = Plabel l } + { ~ is_any_label i }.
Proof.
  intros. 
  destruct i eqn:?; try solve [left; eauto];
  right; unfold not; intros; inversion H.
Defined.

Definition lab (i : instruction) : label :=
  match i with
    | Plabel l => l
    | _ => xH
  end.

Fixpoint front {A : Type} (l : list A) :=
  match l with
    | nil => nil
    | a :: b :: nil => a :: nil
    | a :: b => 
      match b with
        | nil => nil
        | x :: y => a :: front b
      end
  end.

Lemma front_length :
  forall {A} (l : list A),
    l = nil \/ length l = (1 + length (front l))%nat.
Proof.
  induction l; intros.
  left. reflexivity.
  right. destruct IHl. simpl. rewrite H. reflexivity.
  unfold front. fold (@front A).
  repeat break_match; simpl; auto.
Qed.

Lemma front_back :
  forall {A} (l : list A),
    l = nil \/ ((exists x, l = (front l) ++ (x :: nil) /\ l <> nil)).
Proof.
  induction l; intros.
  left. reflexivity.
  right. destruct IHl. subst l. exists a. simpl. split. reflexivity. congruence.
  break_exists. exists x. destruct H.
  rewrite H at 1.
  simpl. repeat break_match; split; auto; try congruence.
Qed.

Lemma find_label_front :
  forall c l,
    find_instr (zlen c - 1) c = Some (Plabel l) ->
    ~ In (Plabel l) (front c) ->
    label_pos l 0 c = Some (zlen c).
Proof.
   induction c; intros.
  * simpl in H. inv H.
  * destruct (front_back (a :: c)).
    inv H1. break_exists. break_and.
    simpl in H1. destruct c. simpl in H1. inv H1.
    simpl in H. inv H.
    simpl. rewrite peq_true. f_equal.
    destruct c. simpl in H1. inv H1.
    simpl in H0. simpl.
    break_match. unfold not in H0. destruct H0. 
    left. destruct a; simpl in Heqb; inv Heqb.
    break_match_hyp; inversion H1. subst l. reflexivity.
    simpl in H. inv H. simpl. rewrite peq_true.
    f_equal.
    assert (~ In (Plabel l) (front (i :: i0 :: c))).
      assert (front (a :: i :: i0 :: c) = a :: (front (i :: i0 :: c))).
        simpl. reflexivity.
      rewrite H3 in H0. 
      assert (~ ((a = Plabel l) \/ In (Plabel l) (front (i :: i0 :: c)))).
        simpl. simpl in H0. assumption.
      unfold not in H4. unfold not. intros. apply H4. right. assumption.
    name H3 Hin.
    apply IHc in H3.
    remember (i :: i0 :: c) as c'.
    simpl in H0. rewrite Heqc' in H0. rewrite <- Heqc' in H0.
    simpl in H0. apply Decidable.not_or in H0. break_and.
    simpl. break_match. destruct a; simpl in Heqb; inv Heqb.
    break_match_hyp; inv H6; congruence.
    rewrite zlen_cons.
    replace 1 with (0 + 1) by omega.
    rewrite <- label_pos_1. assumption.
    remember (i :: i0 :: c) as c'.
    replace (zlen (a :: c') - 1) with (1 + ((zlen c') - 1)) in H.
    rewrite find_instr_head in H. assumption.
    rewrite Heqc'. repeat rewrite zlen_cons.
    name (zlen_nonneg instruction c) zlnc. omega.
    rewrite zlen_cons. omega.
Qed.

Lemma find_label_front_in :
  forall c l,
    find_instr (zlen c - 1) c = Some (Plabel l) ->
    In (Plabel l) (front c) ->
    exists z,
      label_pos l 0 c = Some z /\ 0 <= z < zlen c.
Proof.
  induction c; intros. simpl in H0. inv H0.
  simpl in H0. destruct c.
  simpl in H0. inv H0.
  destruct c. simpl in H0. 
  destruct H0. subst a. simpl.
  rewrite peq_true. exists 1. split. reflexivity.
  repeat rewrite zlen_cons. simpl. omega.
  inv H0.
  remember (i :: i0 :: c) as c'.
  simpl in H0. destruct H0.
  rewrite H0. exists 1. simpl. rewrite peq_true.
  split. reflexivity. 
  rewrite Heqc'.
  repeat rewrite zlen_cons.
  name (zlen_nonneg instruction c) zln. omega.
  app IHc H0. simpl. break_match. exists 1.
  simpl. 
  split. reflexivity. 
  rewrite Heqc'.
  repeat rewrite zlen_cons.
  name (zlen_nonneg instruction c) zln. omega.
  replace 1 with (0 + 1) by omega.
  exists (x + 1). 
  rewrite <- label_pos_1. break_and.
  split. assumption. 
  repeat rewrite zlen_cons. omega.
  rewrite zlen_cons in H.
  replace (zlen c' + 1 - 1) with (1 + (zlen c' - 1)) in H by omega.
  rewrite find_instr_head in H. assumption.
  rewrite Heqc'.
  repeat rewrite zlen_cons.
  name (zlen_nonneg instruction c) zln. omega.
Qed.  
    
Definition labels_valid_dec :
  forall c,
    { labels_valid c } + { ~ labels_valid c }.
Proof.
  intros.
  destruct (find_instr (zlen c - 1) c) eqn:?.
  destruct (is_any_label_dec i). destruct s.
  destruct (in_dec instr_eq (Plabel x) (front c)).
  left. unfold labels_valid. intros.
  destruct (peq l x). subst x.
  app find_label_front_in i0. break_and.
  rewrite H in H1. inv H1.
  apply in_range_find_instr. omega. subst i. assumption.
  apply in_range_find_instr.
  app label_pos_lt H.
  app label_pos_answer_valid H0.
  assert (z < zlen c \/ z = zlen c) by omega.
  destruct H2. omega.
  subst z. app label_pos_find_instr H1.
  subst i. rewrite H1 in Heqo. inv Heqo. congruence.
  right. subst i. app find_label_front Heqo.
  unfold labels_valid. unfold not. intros.
  app H0 Heqo. 
  assert (exists i, find_instr (zlen c) c = Some i).
    eauto.
  apply in_range_find_instr in H3. omega.
  left. unfold labels_valid. intros.
  app label_pos_find_instr H.
  apply in_range_find_instr.
  app label_pos_lt H0. 
  app label_pos_answer_valid H1.
  assert (z < zlen c \/ z = zlen c) by omega.
  destruct H3. omega. subst z.
  rewrite Heqo in H. inv H. simpl in n. 
  unfold not in n. specialize (n I). inv n.
  left. destruct c. unfold labels_valid. intros. simpl in H. inv H.
  unfold labels_valid. intros.
  assert (exists instr, find_instr (zlen (i :: c) - 1) (i :: c) = Some instr).
    apply in_range_find_instr. split; try omega.
    rewrite zlen_cons. name (zlen_nonneg instruction c) zln.
    omega.
  rewrite Heqo in H0. break_exists. inv H0.
Defined.

Definition no_builtin_clobber_PC (c : code) : Prop :=
  forall z ef args res,
    find_instr z c = Some (Pbuiltin ef args res) ->
    ~ In PC res /\ ~ In PC (map preg_of (Machregs.destroyed_by_builtin ef)).

Definition is_builtin (i : instruction) : Prop :=
  match i with
    | Pbuiltin _ _ _ => True
    | _ => False
  end.

Definition is_builtin_dec :
  forall i,
    { x | i = Pbuiltin (fst (fst x)) (snd (fst x)) (snd x) } + { ~ is_builtin i }.
Proof.
  destruct i; try solve [left; exists ((ef,args),res); simpl; auto];
  right; simpl; unfold not; intros; inv H.
Defined.

Definition no_builtin_clobber_PC_dec :
  forall c,
    { no_builtin_clobber_PC c } + { ~ no_builtin_clobber_PC c }.
Proof.
  induction c; intros.
  left. unfold no_builtin_clobber_PC. intros. simpl in H. inv H.
  destruct IHc. destruct (is_builtin_dec a).
  destruct s. destruct x. destruct p. simpl in e.
  destruct (in_dec preg_eq PC l). right. 
  unfold not. intros. unfold no_builtin_clobber_PC in H.
  specialize (H 0). simpl in H. rewrite e in H.
  specialize (H _ _ _ eq_refl). destruct H. congruence.
  destruct (in_dec preg_eq PC (map preg_of (Machregs.destroyed_by_builtin e0))).
  right. unfold not. intros. unfold no_builtin_clobber_PC in H.
  specialize (H 0). simpl in H. rewrite e in H.
  specialize (H _ _ _ eq_refl). destruct H. congruence.
  subst a. 
  left. unfold no_builtin_clobber_PC. intros.
  simpl in H. break_match_hyp. inv H. split; auto.
  unfold no_builtin_clobber_PC in n. app n H.
  left. unfold no_builtin_clobber_PC. intros.
  simpl in H. break_match_hyp. inv H. simpl in n0. auto.
  unfold no_builtin_clobber_PC in n. app n H.
  right. unfold not. intros. unfold not in n. apply n.
  clear n. unfold no_builtin_clobber_PC in *. intros.
  rewrite <- find_instr_head with (a := a) in H0. app H H0.
  assert (exists i, find_instr z c = Some i).
    eexists; eauto.
  apply in_range_find_instr in H1. omega.
Qed.

(* what it means for a piece of code to be part of a program *)
Definition code_of_prog(c : code)(p : Asm.program) : Prop :=
  exists b s,
    In (b,Gfun (Internal (mkfunction s c))) (prog_defs p).

Definition no_PC_overflow_prog (p : Asm.program) : Prop :=
  forall c,
    code_of_prog c p ->
    no_PC_overflow c.

Lemma unsigned_repr_PC :
  forall prog b z f i,
    no_PC_overflow_prog prog ->
    Genv.find_funct_ptr (Genv.globalenv prog) b = Some (Internal f) ->
    (find_instr (z - 1) (fn_code f) = Some i \/ find_instr z (fn_code f) = Some i) ->
    Int.unsigned (Int.repr z) = z.
Proof.
  intros.
  unfold no_PC_overflow_prog in *.
  destruct f.
  assert (code_of_prog fn_code prog).
  unfold code_of_prog.
  app Genv.find_funct_ptr_inversion H0.
  eauto.
  exploit Int.unsigned_repr; eauto.
  app H H2.
  unfold no_PC_overflow in H2.
  break_or;
    simpl in *;
    app H2 H4;
    omega.
Qed.

Definition labels_valid_prog (p : Asm.program) : Prop :=
  forall c,
    code_of_prog c p ->
    labels_valid c.

Definition no_builtin_clobber_PC_prog (p : Asm.program) : Prop :=
  forall c,
    code_of_prog c p ->
    no_builtin_clobber_PC c.

Lemma code_eq_dec :
  forall (c c' : code),
    { c = c' } + { c <> c' }.
Proof.
  intros. decide equality. apply instr_eq.
Defined.

Lemma prog_dec :
  forall (P : code -> Prop),
    (forall c, { P c } + { ~ P c }) ->
    (forall p, { forall c, code_of_prog c p -> P c } + { ~ forall c, code_of_prog c p -> P c }).
Proof.
  intro. intro. intro. destruct p.
  induction prog_defs. 
  * left. intros.
    unfold code_of_prog in H0. repeat break_exists.
    simpl in H0. inv H0.
  * intros.
    destruct a. destruct g. destruct f. destruct f. rename fn_code into c.
    destruct (IHprog_defs).
    destruct (H c). left. intros. unfold code_of_prog in H0.
    simpl in H0. destruct (code_eq_dec c c0). subst c0. assumption.
    break_exists. destruct H0. inv H0. congruence.
    apply p. unfold code_of_prog. simpl. eauto.
    right. unfold not. intros.
    unfold not in n. apply n. apply H0. unfold code_of_prog. simpl.
    exists i. exists fn_sig. left. reflexivity.
    unfold not in n. right. unfold not. intros. apply n. intros. apply H0.
    unfold code_of_prog. unfold code_of_prog in H1. repeat break_exists. exists x. exists x0. simpl. right. auto.
    destruct IHprog_defs. left. intros. apply p.
    unfold code_of_prog in *. repeat break_exists. simpl in H0.
    destruct H0. inv H0.
    exists x. exists x0. simpl. auto.
    right. unfold not in *. intros. apply n.
    intros. unfold code_of_prog in *. apply H0. repeat break_exists. exists x. exists x0. simpl in H1. simpl.
    right. auto.
    destruct IHprog_defs. left. intros. apply p. unfold code_of_prog in *. simpl in *.
    repeat break_exists. destruct H0. inv H0.
    exists x. exists x0. auto.
    right. unfold not in *. intros. apply n. intros.
    apply H0. unfold code_of_prog in *.
    repeat break_exists. exists x. exists x0. simpl in *. right. auto.
Defined.

Definition labels_valid_prog_dec : forall p, { labels_valid_prog p } + { ~ labels_valid_prog p}.
  intros. unfold labels_valid_prog. apply prog_dec.
  apply labels_valid_dec.
Defined.

Definition no_PC_overflow_prog_dec : forall p, { no_PC_overflow_prog p } + { ~ no_PC_overflow_prog p }.
  intros. unfold no_PC_overflow_prog. apply prog_dec.
  apply no_PC_overflow_dec.
Defined.

Definition no_builtin_clobber_PC_prog_dec : forall p, { no_builtin_clobber_PC_prog p } + { ~ no_builtin_clobber_PC_prog p }.
  intros. unfold no_builtin_clobber_PC_prog. apply prog_dec.
  apply no_builtin_clobber_PC_dec.
Defined.

Definition is_allocframe_pos (i : instruction) : Prop :=
  match i with
    | Pallocframe sz _ _ => sz > 0
    | _ => True
  end.

Definition is_allocframe_pos_dec :
  forall i,
    {is_allocframe_pos i} + {~is_allocframe_pos i}.
Proof.
  destruct i; simpl; try solve [left; auto].
  apply Z_gt_dec.
Qed.

Definition all_allocframes_positive_code (c : code) :=
  forall z sz x y,
    find_instr z c = Some (Pallocframe sz x y) ->
    sz > 0.

Definition all_allocframes_positive (p : program) :=
  forall c,
    code_of_prog c p ->
    all_allocframes_positive_code c.
    
Lemma all_allocframes_positive_code_dec :
  forall c,
    { all_allocframes_positive_code c } + { ~ all_allocframes_positive_code c }.
Proof.
  induction c; intros.
  * left. unfold all_allocframes_positive_code. intros.
    simpl in H. congruence.
  * destruct IHc. destruct (is_allocframe_pos_dec a).
    left. unfold all_allocframes_positive_code in *. intros.
    destruct (Z.eq_dec z 0). subst. simpl in H. inv H.
    unfold is_allocframe_pos in i. auto.
    apex in_range_find_instr H. break_and.
    replace z with (1 + (z -1)) in H by omega.
    rewrite find_instr_head in H; try omega.
    app a0 H.
    destruct a; simpl in n; try intuition.
    intros.
    right. intros. unfold all_allocframes_positive_code in H.
    specialize (H 0 sz ofs_ra ofs_link eq_refl). simpl in H.
    intuition.
    right. intro.
    apply n.
    clear n. unfold all_allocframes_positive_code in *.
    intros. erewrite <- find_instr_head in H0.
    eapply H. eauto.
    apex in_range_find_instr H0. omega.
Qed.

Lemma all_allocframes_positive_prog_dec :
  forall p,
    { all_allocframes_positive p } + { ~ all_allocframes_positive p }.
Proof.
  intros. destruct p.
  induction prog_defs; unfold all_allocframes_positive.
  * unfold code_of_prog. left. intros.
    repeat break_exists. simpl in H. inv H.
  * destruct IHprog_defs.
    destruct a. destruct g. destruct f.
    destruct (all_allocframes_positive_code_dec (fn_code f)).
    left. intros.
    unfold code_of_prog in H. repeat break_exists.
    simpl in H. destruct H. inv H.
    simpl in a. assumption.
    unfold all_allocframes_positive in a0.
    apply a0. unfold code_of_prog. eexists. eexists. eapply H.
    right. intro. apply n. apply H.
    unfold code_of_prog. exists i. exists (fn_sig f).
    simpl. left. destruct f. reflexivity.
    left. intros.
    unfold code_of_prog in H. repeat break_exists.
    simpl in H. destruct H. inv H. 
    unfold all_allocframes_positive in a0.
    apply a0. unfold code_of_prog. eexists. eexists. eapply H.
    left. intros.
    unfold code_of_prog in H. repeat break_exists.
    simpl in H. destruct H. inv H. 
    unfold all_allocframes_positive in a0.
    apply a0. unfold code_of_prog. eexists. eexists. eapply H.
    right. intro. apply n. clear n.
    unfold all_allocframes_positive. intros. apply H.
    unfold code_of_prog in *. 
    repeat break_exists. eexists. eexists.
    simpl. right.
    simpl in H0. eapply H0.
Qed.
