Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Asm.
Require Import Floats.
Require Import Maps.

Require Import PeekLib.
Require Import PeekTactics.
Require Import SplitLib.
Require Import FindInstrLib.
Require Import Pred.
Require Import Use.
Require Import UseBasic.
Require Import Union.
Require Import PeekLiveness.
Require Import Zlen.

Lemma update_range :
  forall c l z,
    ((z < 0) \/ (z >= zlen c)) ->
    ZMap.get z l = ZMap.get z (update_liveness c z l).
Proof.
  intros.
  unfold update_liveness.
  destruct (find_instr z c) eqn:?. 
  assert (exists i, find_instr z c = Some i).
    exists i. assumption.
  rewrite <- in_range_find_instr in H0. destruct H0. omega.
  reflexivity.
Qed.  

Lemma update_neq:
  forall ofs z c l,
    ofs <> z ->
    ZMap.get ofs (update_liveness c z l) = ZMap.get ofs l.
Proof.
  intros.
  unfold update_liveness.
  repeat break_match;
  unfold succ; try rewrite Heqo; simpl;
  try rewrite ZMap.gso by auto; reflexivity.
Qed.

Lemma in_map_union_l_spec:
  forall {A} is l (p : A) {eq},
    In p (union_l eq (map (fun z0 => ZMap.get z0 l) is)) ->
    exists i, (In i is /\ In p (ZMap.get i l)).
Proof.
  intros. induction is.
  * simpl in H. inv H.
  * destruct (in_dec eq p (ZMap.get a l)).
    exists a. split. simpl. left. reflexivity. assumption.
    simpl in H. apply union_correct in H.
    destruct H. congruence.
    specialize (IHis H). destruct IHis. destruct H0.
    exists x. split. simpl. right. auto. auto.
Qed.

Lemma update_twice :
  forall c z l p,
    In p (ZMap.get z (update_liveness c z (update_liveness c z l))) <-> In p (ZMap.get z (update_liveness c z l)).
Proof.
  intros. unfold update_liveness.
  destruct (find_instr z c) eqn:?; 
  simpl; repeat break_match;
  try rewrite ZMap.set2;
  try reflexivity.

  destruct (in_dec Z.eq_dec z l0).

  split. intros.
  repeat rewrite ZMap.gss in *.
  unfold transfer in *.
  rewrite <- add_in_spec in H.
  destruct H. apply add_in_l. assumption.
  rewrite <- rem_in in H. destruct H.
  apply in_map_union_l_spec in H.
  destruct H. destruct H.
  destruct (zeq x z). subst x.
  rewrite ZMap.gss in H1. assumption.
  rewrite ZMap.gso in H1 by auto.
  apply add_in_r. apply rem_in. split; auto.
  eapply in_map_union_l; eauto. 

  intros. 
  repeat rewrite ZMap.gss in *.
  unfold transfer in *.
  destruct (in_dec preg_eq p (use i)).
  apply add_in_l; assumption.
  apply add_in_spec in H. destruct H. congruence.
  apply rem_in in H. destruct H.
  apply add_in_r. apply rem_in. split; auto.
  apply in_map_union_l with (i1 := z).
  intros. rewrite ZMap.gss.
  apply add_in_r. apply rem_in. split; auto. auto.

  rewrite not_in_map. reflexivity. assumption.
Qed.

Lemma update_indep :
  forall z z0 c l sl,
    z <> z0 ->
    succ z0 c = Some sl ->
    ~ In z sl ->
    (forall p, In p (ZMap.get z0 (update_liveness c z0 (update_liveness c z l))) <-> In p (ZMap.get z0 (update_liveness c z0 l))).
Proof.
  intros.
  unfold update_liveness.
  repeat break_match;
    try (assert (succ z0 c = None) by (eapply no_succ_calls; eauto); congruence);
    try congruence; try reflexivity;
    repeat rewrite ZMap.gss;
    unfold transfer; try rewrite map_get_not_in by (inv H0; auto);
    repeat rewrite ZMap.gso;
    try reflexivity; auto.
Qed.
