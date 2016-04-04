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
Require Import PeekTactics.
Require Import PregTactics.
(* Require Import SymbEv. *)
(* Require Import SymbEvProof. *)
Require Import AsmCallingConv.
Require Import Union.
Require Import StepIn.
Require Import PeekLivenessProof.
Require Import Use.
Require Import StepEquiv. (* Where rewrite is defined *)
Require Import ProgPropDec.
Require Import ForwardJumps.
Require Import PeekLib.
Require Import Zlen.

Require Import AsmBits.
Require Import MemoryAxioms.

(* TODO: Move to a helper lib (CompCert 2.4 doesn't have this defined for us) *)
Definition symbol_offset (ge: Genv.t fundef unit) (id: ident) (ofs: int) : Values.val :=
  match Genv.find_symbol ge id with
  | Some b => Values.Vptr b ofs
  | None => Values.Vundef
  end.

Section PEEPHOLE.

Variable rwr : rewrite.

Definition liveness_check_correct (entry exit : list preg) : Prop := 
  (forall p, In p (live_in rwr) -> In p entry) /\
  (forall p, In p exit -> In p ((live_out rwr) ++ (pres rwr))) /\
  (forall p, In p (pres rwr) -> (In p entry <-> In p exit)).

Definition is_proper_rewrite_location (c1 find c2 : code) (lm : liveness_map_t) (l : list label) (repl : code) : Prop :=
  c1 <> nil /\ c2 <> nil /\ find_liveness (c1 ++ find ++ c2) = Some lm /\ 
    liveness_check_correct (ZMap.get (zlen c1) lm) (ZMap.get (zlen (c1 ++ find)) lm) /\
  True /\ (* for hypothesis numbers later *)
  ends_in_not_call c1 /\ only_labels c1 l /\ only_labels c2 l /\ no_labels find l /\ no_labels repl l /\ ends_in_not_label c1.

Lemma and_dec :
  forall A B,
    { A } + { ~ A } ->
    { B } + { ~ B } ->
    { A /\ B } + { ~ (A /\ B) }.
Proof.
  intros. destruct H. destruct H0. left. auto.
  right. unfold not. intros. break_and. congruence.
  right. unfold not. intros. break_and. congruence.
Qed.

Definition subset_memb_eq_dec :
  forall {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (a b l : list A),
    { forall p : A, In p l -> (In p a <-> In p b) } +
    { ~ (forall p : A, In p l -> (In p a <-> In p b)) }.
Proof.
  induction l; intros.
  * left. intros. simpl in H. inv H.
  * destruct IHl. destruct (in_dec eq_dec a0 a); destruct (in_dec eq_dec a0 b).
    left. intros. simpl in H. destruct H. subst p. split; intros; auto. apply i; auto.
    right. unfold not. intros. simpl in H.
    specialize (H a0). exploit H. left. reflexivity.
    intros. app H0 i0. 
    right. unfold not. intros. simpl in H.
    specialize (H a0). exploit H. left. reflexivity.
    intros. app H0 i0. 
    left. intros. simpl in H. destruct H. subst p. split; intros; congruence.
    app i H.
    unfold not in n. right. unfold not. intros. apply n.
    intros. apply H. simpl. right. assumption.
Defined.

Definition regs_check (c1 find : code) (lm : liveness_map_t) :
  { liveness_check_correct (ZMap.get (zlen c1) lm) (ZMap.get (zlen (c1 ++ find)) lm) } +
  { ~ liveness_check_correct (ZMap.get (zlen c1) lm) (ZMap.get (zlen (c1 ++ find)) lm) }.
Proof.
  unfold liveness_check_correct. apply and_dec. apply (@subset_dec preg preg_eq).
  apply and_dec. apply (@subset_dec preg preg_eq).
  apply subset_memb_eq_dec. apply preg_eq.
Defined.

Lemma list_end_inv :
  forall {A} (l : list A),
    (l = nil \/ exists l' x, l = l' ++ x :: nil).
Proof.
  induction l; intros.
  * left. reflexivity.
  * right.
    destruct IHl. subst l.
    exists nil. exists a. simpl. reflexivity.
    repeat break_exists. subst l.
    exists (a :: x). exists x0. simpl. reflexivity.
Qed.

Lemma ends_in_not_call_dec :
  forall c,
    { ends_in_not_call c } + { ~ ends_in_not_call c }.
Proof.
  intros.
  destruct (find_instr (zlen c - 1) c) eqn:?.
  destruct (is_call_return_dec i) eqn:?.
  right. unfold not. intros.
  unfold ends_in_not_call in H. repeat break_exists.
  break_and.
  rewrite H in Heqo.
  rewrite zlen_app in Heqo. rewrite zlen_cons in Heqo. simpl in Heqo.
  replace (zlen x + 1 - 1) with (zlen x + 0) in Heqo by omega.
  rewrite find_instr_append_head in Heqo by omega.
  simpl in Heqo. inv Heqo. congruence.
  left. unfold ends_in_not_call.
  destruct (list_end_inv c). subst c. simpl in Heqo. inv Heqo.
  repeat break_exists. subst c. exists x. exists i.
  split; auto. f_equal. f_equal. rewrite zlen_app in Heqo.
  rewrite zlen_cons in Heqo. simpl in Heqo.
  replace (zlen x + 1 - 1) with (zlen x + 0) in Heqo by omega.
  rewrite find_instr_append_head in Heqo by omega.
  simpl in Heqo. inv Heqo. reflexivity.
  right. unfold not. intros.
  unfold ends_in_not_call in H.
  repeat break_exists.
  break_and. rewrite H in Heqo.
  rewrite zlen_app in Heqo.
  rewrite zlen_cons in Heqo. simpl in Heqo.
  replace (zlen x + 1 - 1) with (zlen x + 0) in Heqo by omega.
  rewrite find_instr_append_head in Heqo by omega.
  simpl in Heqo. inv Heqo.
Qed.

Lemma is_any_label_dec :
  forall i,
    { is_any_label i } + { ~ is_any_label i }.
Proof.
  intros. 
  destruct i; try solve [left; simpl; exact I];
  right; unfold not; intros; simpl in H; inversion H.
Qed.

Lemma ends_in_not_label_dec :
  forall c,
    { ends_in_not_label c } + { ~ ends_in_not_label c }.
Proof.
  intros.
  destruct (find_instr (zlen c - 1) c) eqn:?.
  destruct (is_any_label_dec i).
  right. unfold not. intros.
  unfold ends_in_not_label in H. repeat break_exists.
  app H Heqo.
  left. unfold ends_in_not_label. intros.
  rewrite H in Heqo. inv Heqo. auto.
  left.
  unfold ends_in_not_label. intros.
  rewrite H in Heqo. inv Heqo.
Qed.

Definition label_instr_dec :
  forall i,
    { l | is_label_instr i l } + { forall l, ~ is_label_instr i l }.
Proof.
  intros. destruct i; try solve [right; unfold not; intros; simpl in H; inv H];
          try solve [left; simpl; eauto].
  destruct tbl. right. intros. unfold not. intros. simpl in H. inv H.
  left. exists l. simpl. left. reflexivity.
Qed.

Lemma only_labels_cons :
  forall l c x,
    only_labels c l ->
    only_labels c (x :: l).
Proof.
  intros.
  unfold only_labels in *. intros.
   app H H0. simpl. right. assumption.
Qed.

Lemma only_labels_code_cons :
  forall l c x,
    only_labels (x :: c) l ->
    only_labels c l.
Proof.
  unfold only_labels in *.
  intros. specialize (H (1 + z) i).
  apex in_range_find_instr H0.
  rewrite find_instr_head in H by omega.
  app H H0.
Qed.

Lemma only_labels_dec :
  forall l c,
    { only_labels c l } + { ~ only_labels c l }.
Proof.
  induction l; intros.
  * induction c.
    left. unfold only_labels. intros. simpl in H. inv H.
    destruct (label_instr_dec a). right.
    unfold not. intros. unfold only_labels in H.
    specialize (H 0 a).
    simpl in H.
    specialize (H eq_refl). destruct s.
    eapply H in i. inv i.
    destruct IHc. left.
    unfold only_labels. intros.
    unfold only_labels in o.
    destruct (zeq z 0). subst z. simpl in H. inv H.
    specialize (n l). congruence.
    apex in_range_find_instr H.
    replace z with (1 + (z - 1)) in H by omega.
    rewrite find_instr_head in H by omega.
    app o H.
    right. unfold not. intros. unfold not in n0. apply n0.
    unfold only_labels in *. intros.
    specialize (H (1 + z) i).
    apex in_range_find_instr H0.
    rewrite find_instr_head in H by omega.
    app H H0.
  * induction c. 
    left. unfold only_labels. intros. simpl in H. inv H.
    destruct (IHl (a0 :: c)).
    left. apply only_labels_cons; auto.
    destruct IHc.
    destruct (@subset_dec label ident_eq (get_labels (a0 :: nil)) (a :: l)).
    left. (* prove me *) unfold only_labels. intros.
    destruct (zeq z 0). subst z. simpl in H. inv H. apply i. simpl.
    destruct i0; simpl in H0; try inversion H0;
    simpl; try solve [left; reflexivity].
    rewrite in_app. left. assumption.
    apex in_range_find_instr H.
    replace z with (1 + (z - 1)) in H by omega.
    rewrite find_instr_head in H by omega.
    unfold only_labels in o. eapply o; eauto.
    right. unfold not. intros. 
    unfold not in n0. apply n0. intros.
    unfold only_labels in H. 
    assert (find_instr 0 (a0 :: c) = Some a0).
      simpl. auto.
    app H H1. destruct a0; simpl in H0; simpl; auto;
    try (destruct H0; subst; auto; inversion H0).
    rewrite app_nil_r in H0. assumption.
    right. unfold not. intros. app only_labels_code_cons H.
Qed.

Lemma label_instr_other_dec :
  forall i l,
    { is_label_instr i l } + { ~ is_label_instr i l }.
Proof.
  intros. 
  destruct i; try solve [right; simpl; unfold not; intros; auto];
  try (destruct (ident_eq l l0)); try subst l; try solve [left; simpl; auto];
  try solve [right; congruence].
  destruct (in_dec ident_eq l tbl).
  left. simpl. auto.
  right. unfold not. intros. simpl in H.
  unfold not in n. app n H.
Qed.

Lemma find_instr_range :
  forall z c i,
    find_instr z c = Some i ->
    0 <= z < zlen c.
Proof.
  intros. assert (exists i, find_instr z c = Some i).
  eexists; eauto.
  apply in_range_find_instr in H0. omega.
Qed.

Lemma is_label_instr_code_dec :
  forall l (c : code),
    { forall z i, find_instr z c = Some i -> ~ is_label_instr i l } + 
    { exists z i, find_instr z c = Some i /\ is_label_instr i l }.
Proof.
  induction c; intros.
  left. intros. simpl in H. inv H.
  destruct IHc. destruct (label_instr_other_dec a l).
  right. exists 0. exists a. simpl. intros. auto.
  left. intros. 
  app find_instr_range H.
  destruct (zeq z 0). subst z. simpl in H0. inv H0. auto.
  replace z with (1 + (z - 1)) in H0 by omega.
  rewrite find_instr_head in H0 by omega.
  app n H0.
  destruct (label_instr_other_dec a l).
  right. repeat break_exists. exists 0. exists a.
  simpl. split; auto.
  right. repeat break_exists. break_and. exists (1 + x). exists x0.
  app find_instr_range H. split; auto.
  rewrite find_instr_head by omega. auto.
Qed.

Lemma no_labels_dec :
  forall l c,
    { no_labels c l } + { ~ no_labels c l }.
Proof.
  induction l; intros.
  * unfold no_labels. left. intros. unfold not. intros. simpl in H1. inv H1.
  * destruct (IHl c). destruct (is_label_instr_code_dec a c).
    left. unfold no_labels. intros.
    app n0 H. unfold no_labels in n. app n H1.
    destruct (peq a l0). subst a. congruence.
    simpl. unfold not. intros. destruct H3; congruence.
    right. unfold not. intros. unfold no_labels in H.
    repeat break_exists. break_and.
    app H H0. simpl in H0. unfold not in H0. apply H0.
    left. reflexivity.
    right. unfold not in *. intros. apply n.
    unfold no_labels in H. unfold no_labels. intros.
    app H H0. unfold not in H0. unfold not. intros.
    apply H0. simpl. right. assumption.
Qed.

Fixpoint ends_in_not_call_or_label_check (c : code) : bool :=
  match c with
    | nil => false
    | i :: r =>
      match r with
        | _ :: _ => ends_in_not_call_or_label_check r
        | nil => 
          if is_call_return_dec i then
            false
          else
            if is_any_label_dec i then
              false
            else
              true
      end
  end.

Lemma ends_in_not_call_check_sound :
  forall c,
    ends_in_not_call_or_label_check c = true ->
    ends_in_not_call c.
Proof.
  induction c; intros.
  simpl in H. congruence.
  simpl in H. break_match_hyp; subst.
  break_match_hyp; try congruence.
  unfold ends_in_not_call. exists nil.
  exists a. eauto.
  app IHc H. unfold ends_in_not_call in *.
  clear IHc. clear H0.
  repeat break_exists.
  break_and. exists (a :: x). exists x0.
  rewrite H. eauto.
Qed.

Lemma ends_in_not_label_check_sound :
  forall c,
    ends_in_not_call_or_label_check c = true ->
    ends_in_not_label c.
Proof.
  induction c; intros.
  simpl in H. congruence.
  simpl in H. break_match_hyp; subst.
  repeat break_match_hyp; try congruence.
  unfold ends_in_not_label. simpl.
  intros. inv H0. eauto.
  app IHc H. unfold ends_in_not_label in *.
  clear IHc. clear H0.
  intros.
  repeat rewrite zlen_cons in H0.
  replace (zlen l + 1 + 1 - 1) with (1 + zlen l) in H0 by omega.
  unfold find_instr in H0. fold find_instr in H0.
  repeat break_match_hyp. inversion H0.
  name (zlen_nonneg _ l) zlnc. omega.
  destruct l. apply H. simpl. congruence.
  clear Heqs0. rewrite zlen_cons in e.
  name (zlen_nonneg _ l) zlnc. omega.
  apply H. rewrite zlen_cons.
  replace (zlen l + 1 - 1) with (1 + (zlen l - 1)) by omega.
  rewrite find_instr_head.
  replace (1 + zlen l - 1 - 1) with (zlen l - 1) in H0 by omega.
  eauto.
  destruct l. simpl in n0. omega.
  rewrite zlen_cons. name (zlen_nonneg _ l) zlnc. omega.
Qed.

Definition get_instr_labels (i : instruction) : list label :=
  match i with
    | Pjmp_l l => l :: nil
    | Pjcc _ l => l :: nil
    | Pjcc2 _ _ l => l :: nil
    | Plabel l => l :: nil
    | Pjmptbl _ tbl => tbl
    | _ => nil
  end.

(* all of x are in y *)
Fixpoint all_in (x y : list label) : bool :=
  match x with
    | nil => true
    | f :: r => if in_dec peq f y then
                  all_in r y
                else
                  false
  end.

Lemma all_in_sound :
  forall x y,
    all_in x y = true ->
    forall elem,
      In elem x -> In elem y.
Proof.
  induction x; intros. simpl in H0. inv_false.
  simpl in H. break_match_hyp; try congruence.
  simpl in H0. break_or. eauto.
  eapply IHx; eauto.
Qed.
      
Fixpoint only_labels_check (c : code) (l : list label) : bool :=
  match c with
    | nil => true
    | f :: r => if all_in (get_instr_labels f) l then
                  only_labels_check r l
                else
                  false
  end.

Lemma get_labels_label_instr :
  forall i l,
    is_label_instr i l ->
    In l (get_instr_labels i).
Proof.
  intros.
  destruct i eqn:?; simpl in H; try inv_false;
  simpl; eauto.
Qed.

Lemma only_labels_check_sound :
  forall c l,
    only_labels_check c l = true ->
    only_labels c l.
Proof.
  induction c; intros.
  unfold only_labels. intros. simpl in H0. congruence.
  simpl in H.
  simpl in H.
  break_match_hyp; try congruence.
  name (all_in_sound _ _ Heqb) ais.
  name (IHc _ H) olc.

  clear H. clear Heqb. clear IHc.
  unfold only_labels in *.
  intros.
  destruct (zeq z 0).
  * subst z.
    simpl in H. inv H.
    eapply ais; eauto.
    eapply get_labels_label_instr; eauto.
  * apex in_range_find_instr H.
    replace z with (1 + (z - 1)) in H by omega.
    rewrite find_instr_head in H by omega.
    eapply olc; eauto.
Qed.
  
Fixpoint none_in (x y : list label) : bool :=
  match x with
    | nil => true
    | f :: r => if in_dec peq f y then
                  false
                else
                  none_in r y
  end.

Lemma none_in_sound :
  forall x y,
    none_in x y = true ->
    forall elem,
      In elem x ->
      ~ In elem y.
Proof.
  induction x; intros.
  simpl in *. inv_false.
  simpl in H. break_match_hyp; try congruence.
  simpl in H0. break_or; try assumption.
  app IHx H.
Qed.
  

Fixpoint no_labels_check (c : code) (l : list label) : bool :=
  match c with
    | nil => true
    | f :: r => if none_in (get_instr_labels f) l then
                  no_labels_check r l
                else
                  false
  end.

Lemma no_labels_check_sound :
  forall c l,
    no_labels_check c l = true ->
    no_labels c l.
Proof.
  induction c; intros.
  unfold no_labels. intros. simpl in *. congruence.
  simpl in H. break_match_hyp; try congruence.
  eapply IHc in H. name (none_in_sound _ _ Heqb) Hnin.
  clear Heqb. clear IHc.
  unfold no_labels in *. intros.
  
  destruct (zeq z 0).
  * subst z.
    simpl in H0. inv H0.
    eapply Hnin.
    eapply get_labels_label_instr; eauto.
  * apex in_range_find_instr H0.
    replace z with (1 + (z - 1)) in H0 by omega.
    rewrite find_instr_head in H0 by omega.
    eapply H; eauto.
Qed.

Definition label_check (c1 c2 find repl : code) (l : list label) : bool :=
  if ends_in_not_call_or_label_check c1 then
    if only_labels_check c1 l then
      if only_labels_check c2 l then
        if no_labels_check find l then
          if no_labels_check repl l then
            true
          else
            false
        else
          false
      else
        false
    else
      false
  else
    false.

Definition is_proper_location_check (c1 find c2 : code) (l : list label) (repl : code) : bool :=
  match c1 with
    | nil => false
    | _ :: _ =>
      match c2 with
        | nil => false
        | _ :: _ => 
          match find_liveness (c1 ++ find ++ c2) with
            | None => false
            | Some lm => 
              if regs_check c1 find lm then
                if label_check c1 c2 find repl l then
                  true
                else
                  false
              else
                false
          end
      end
  end.

Lemma is_proper_check_sound :
  forall c1 find c2 l repl,
    is_proper_location_check c1 find c2 l repl = true ->
    exists lm,
          find_liveness (c1 ++ find ++ c2) = Some lm /\
          is_proper_rewrite_location c1 find c2 lm l repl.
Proof.
  intros. unfold is_proper_location_check in H.
  repeat break_match_hyp; inv H. 
  exists l0. split; auto.
  unfold is_proper_rewrite_location.
  repeat (split; try congruence; auto);
    unfold label_check in *;
    repeat break_match_hyp; try congruence;
    try eapply ends_in_not_call_check_sound;
    try eapply only_labels_check_sound;
    try eapply no_labels_check_sound;
    try eapply ends_in_not_label_check_sound;
    eauto.
Qed.

Definition transf_code (c : code) : code :=
  match split_pat rwr.(find) c with
    | Some(c1,c2) => 
      if (is_proper_location_check c1 rwr.(find) c2 (get_labels c1 ++ get_labels c2) rwr.(repl)) then
        (c1 ++ rwr.(repl) ++ c2)
      else
        c
    | None => c
  end.

Definition transf_fundef (f : fundef) : fundef :=
  match f with
    | Internal (mkfunction s c) => Internal (mkfunction s (transf_code c))
    | External ef => External ef
  end.

Definition transf_program (p : Asm.program) : res Asm.program :=
  match (symbol_offset (Genv.globalenv p) (prog_main p) Int.zero) with  
    | Values.Vptr b _ =>
      match (Genv.find_funct_ptr (Genv.globalenv p) b) with
        | Some _ =>
          if (labels_valid_prog_dec p) then
            if (no_PC_overflow_prog_dec p) then
              if (no_builtin_clobber_PC_prog_dec p) then
                match (ensure_liveness_prog (prog_defs p)) with
                  | OK _ => OK (AST.transform_program transf_fundef p)
                  | Error x => Error x
                end
              else
                Error ((MSG "builtins clobber PC") :: nil)
            else
              Error ((MSG "PC can overflow (functions too long)") :: nil)
          else
            Error ((MSG "labels not valid") :: nil)
        | None => Error ((MSG "weirdly malformed genv") :: nil)
      end
    | _ => Error ((MSG "no main function present") :: nil)
  end.

End PEEPHOLE.

