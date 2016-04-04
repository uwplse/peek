Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Asm.
Require Import Axioms.
Require Import Floats.

Require Import PeekLib.
Require Import SplitLib.
Require Import PeekTactics.
Require Import Zlen.

Lemma find_instr_neg:
  forall c z,
    z < 0%Z ->
    find_instr z c = None.
Proof.
  induction c.
  * intros. auto.
  * intros. unfold find_instr.
    assert (z-1 < 0). omega.
    apply (IHc (z - 1)) in H0.
    destruct (zeq z 0).
    - omega.
    - destruct c; auto.
Qed.

Lemma find_instr_overflow:
  forall c z,
    z >= zlen c ->
    find_instr z c = None.
Proof.
  induction c.
  * intros. destruct z; auto.
  * intros. unfold zlen in H. simpl in H.
    simpl.
    destruct (zeq z 0).
    - rewrite e in H.
      exfalso. auto.
    - apply IHc.
      unfold zlen.
      unfold Z_of_nat', Z.of_nat.
      break_match.
      + simpl in *. omega.
      + simpl in *.
        rewrite <- Pos.add_1_l in *.
        assert (forall x, Z.pos (1 + x) = 1 + Z.pos x).
        intros. destruct x; auto.
        rewrite H0 in H. omega.
Qed.

Lemma find_instr_head:
  forall l a z,
    z >= 0 ->
    find_instr (1 + z) (a :: l) = find_instr z l.
Proof.
  induction l; intros.
  * destruct (zeq (1+z) 0); auto. omega.
    destruct z. auto. auto. contradiction H. auto.
  * destruct z. auto. Focus 2. contradiction H. auto.
    destruct (zeq (1 + Z.pos p) 0) eqn:?. inversion e.
    unfold find_instr at 1. fold find_instr.
    rewrite Heqs. unfold find_instr at 2. fold find_instr.
    replace (1 + Z.pos p - 1) with (Z.pos p) by omega.
    auto.
Qed.

Lemma Z_nat_succ:
  forall n,
    1 + Z_of_nat' n = Z_of_nat' (S n).
Proof.
  induction n; auto.
  unfold Z_of_nat' at 2. unfold Z.of_nat.
  rewrite Zpos_P_of_succ_nat. fold Z_of_nat'.
  rewrite <- IHn. omega.
Qed. 

Lemma Z_of_nat_distr_plus:
  forall a b, Z_of_nat' (a + b) = Z_of_nat' a + Z_of_nat' b.
Proof.
  induction a; intros; unfold Z_of_nat' in *; unfold Z.of_nat in *.
  - auto.
  - repeat break_match; subst_max; auto;
        try solve_by_inversion; simpl in *; find_inversion.
    + rewrite <- plus_n_O. auto.
    + break_match; simpl; find_rewrite; auto.
    + rewrite <- plus_n_Sm. simpl.
      rewrite Pos.add_succ_l.
      specialize (IHa n0).
      repeat break_match; try solve_by_inversion; subst_max; simpl.
      * rewrite Pos.add_1_r. 
        rewrite <- plus_n_O. 
        auto.
      * repeat find_inversion.
        rewrite Pos.add_succ_r. 
        find_rewrite. auto.
Qed.

Lemma zlen_app :
  forall {A} (l l' : list A),
    zlen (l ++ l') = zlen l + zlen l'.
Proof.
  intros. unfold zlen. rewrite app_length.
  rewrite Z_of_nat_distr_plus.
  reflexivity.
Qed.

Lemma find_instr_append_head:
  forall a b i,
    i >= 0 ->
    find_instr (zlen a + i) (a ++ b) = find_instr i b.
Proof.
  induction a.
  * intros. auto.
  * intros.
    name (IHa b i) IH.
    assert (find_instr (zlen (a :: a0) + i) ((a :: a0) ++ b) = find_instr (zlen a0 + i) (a0 ++ b)).
      replace (zlen (a :: a0)) with (1 + zlen a0).
      name (zlen_nonneg instruction a0) Hnonneg.
      name (find_instr_head (a0 ++ b) a ((zlen a0) + i)) HH.
      assert (Hnn: (zlen a0) + i >= 0). omega.
      replace (1 + zlen a0 + i) with (1 + (zlen a0 + i)).
      replace ((a::a0)++b) with (a :: (a0 ++ b)).
      rewrite (HH Hnn). auto. auto. omega.
      unfold zlen. simpl length.
      rewrite Z_nat_succ. auto.
    rewrite H0. rewrite (IH H). auto.
Qed.

Lemma find_instr_append_head_0:
  forall a b,
    find_instr (zlen a) (a ++ b) = find_instr 0 b.
Proof.
  intros. replace (zlen a) with (zlen a + 0) by omega.
  eapply find_instr_append_head. omega.
Qed.

Lemma find_instr_append_tail:
  forall a b c i,
    0 <= i < zlen a ->
    find_instr i (a ++ b) = find_instr i (a ++ c).
Proof.
  induction a; 
      intros; destruct i; inversion H; unfold zlen in H1; 
      simpl in H1; try omega; auto. Focus 2. contradiction H0. auto.
  assert (0 <= Z.pos p - 1 < zlen a0).
    split. destruct p. simpl. auto. auto. omega.
    rewrite Zpos_P_of_succ_nat in H1. unfold zlen. 
    unfold Z.succ in H1. unfold Z_of_nat'. omega.
  name (IHa b c (Z.pos p - 1) H2) IH.
  assert (Z.pos p -1 >= 0). omega.
  name (find_instr_head (a0 ++ b) a (Z.pos p - 1) H3) Hb.
  name (find_instr_head (a0 ++ c) a (Z.pos p - 1) H3) Hc.
  assert (1 + (Z.pos p -1) = Z.pos p). omega.
  rewrite H4 in Hb, Hc. 
  replace ((a :: a0) ++ b) with (a :: a0 ++ b) by auto.
  replace ((a :: a0) ++ c) with (a :: a0 ++ c) by auto.
  rewrite Hb. rewrite Hc. apply IH.
Qed.
  

Lemma find_instr_prefix:
  forall c c0 c1 p1 p2 z,
    split_pat p1 c = Some(c0,c1) ->
    zlen p1 = zlen p2 ->
    0 <= z < zlen c0 ->
    find_instr z c = find_instr z (c0 ++ p2 ++ c1).
Proof.
  intros.
  apply split_pat_spec in H.
  name (find_instr_append_tail c0 (p1 ++ c1) (p2 ++ c1) z H1) f.
  rewrite <- H in f. apply f.
Qed.

Lemma find_instr_suffix:
  forall p1 c c0 c1 p2 z,
    split_pat p1 c = Some(c0,c1) ->
    zlen p1 = zlen p2 ->
    z >= zlen (c0 ++ p2) ->
    find_instr z c = find_instr z (c0 ++ p2 ++ c1).
Proof.
  intros. apply split_pat_spec in H.
  assert (z - zlen (c0 ++ p1) >= 0). 
    unfold zlen in H1. simpl in H1. unfold zlen in H0.
    rewrite app_length in H1. unfold zlen. rewrite app_length.
    rewrite Z_of_nat_distr_plus in *. omega.
  assert (z - zlen (c0 ++ p2) >= 0). omega.
  name (find_instr_append_head (c0 ++ p2) c1 (z - zlen (c0 ++ p2)) H3) Hp2.
  name (find_instr_append_head (c0 ++ p1) c1 (z - zlen (c0 ++ p1)) H2) Hp1.
  assert (zlen (c0 ++ p1) + (z - zlen (c0 ++ p1)) = z).
    omega.
  assert (zlen (c0 ++ p2) + (z - zlen (c0 ++ p2)) = z).
    omega.
  rewrite H4 in *. rewrite H5 in *.
  clear H4. clear H5.
  rewrite H.
  rewrite app_ass in Hp2. rewrite app_ass in Hp1.
  rewrite Hp2. rewrite Hp1.
  assert (zlen (c0 ++ p1) = zlen (c0 ++ p2)).
    unfold zlen. repeat rewrite app_length. repeat rewrite Z_of_nat_distr_plus.
    unfold zlen in H0. omega.
  rewrite H4. auto.
Qed.


Lemma label_pos_find_instr_k:
  forall c l k z,
    label_pos l k c = Some (z + k) ->
    find_instr (z - 1) c = Some (Plabel l).
Proof.
  induction c; intros.
  * unfold label_pos in H; inv H.
  * unfold label_pos in H.
    destruct (is_label l a) eqn:?.
    - inv H. assert (z=1). omega.
      subst z. simpl.
      destruct a; inv Heqb.
      destruct (peq l l0).
      inv e.
      reflexivity.
      discriminate.
    - fold label_pos in H.
      replace (z+k) with ((z-1)+(k+1)) in H by omega.
      apply IHc with (k:=k+1) (z:=z-1) (l:=l) in H.
      destruct (zeq (z-1) 0) eqn:?.
      + assert (z-1-1 < 0). omega.
        apply find_instr_neg with (c:=c) in H0.
        rewrite H in H0. inv H0.
      + unfold find_instr. rewrite Heqs.
        fold find_instr. assumption.
Qed.

Lemma label_pos_find_instr:
  forall c l z,
    label_pos l 0 c = Some (z) ->
    find_instr (z - 1) c = Some (Plabel l).
Proof.
  intros. apply label_pos_find_instr_k with (k:=0).
  rewrite H. f_equal. omega.
Qed.

Lemma in_range_find_instr :
  forall c z,
    ((z >= 0) /\ (z < zlen c)) <-> (exists i, find_instr z c = Some i).
Proof.
  induction c; split; intros; destruct H.
  * unfold zlen in H0. simpl in H0. omega.
  * simpl in H. inversion H.
  * destruct (Z.eq_dec z 0). exists a. rewrite e.
    simpl. reflexivity.
    assert ((z-1 >= 0) /\ (z-1) < zlen c).
      split. omega. rewrite zlen_cons in H0. omega.
    apply IHc in H1. destruct H1. exists x. simpl.
    destruct (zeq z 0). omega. apply H1.
  * destruct (zlt z 0).
    - name l l2. apply find_instr_neg with (c := c) in l.
      simpl in H.
      destruct (zeq z 0) eqn:?. 
      + simpl in H. split. omega. rewrite zlen_cons.
        name (zlen_nonneg instruction c) g. omega.
      + assert (z - 1 < 0). omega. apply find_instr_neg with (c := c) in H0.
        rewrite H in H0. inv H0.
    - split. assumption. destruct (zlt z (zlen (a :: c))).
      assumption. apply find_instr_overflow in g0. rewrite H in g0.
      inv g0.
Qed.


Lemma label_pos_1 :
  forall c k l z,
    label_pos l k c = Some z <->
    label_pos l (k + 1) c = Some (z + 1).
Proof.
  induction c; split; intros.
  * simpl in H. inv H.
  * simpl in H. inv H.
  * simpl in H. simpl.
    break_match_hyp. inv H. reflexivity.
    app IHc H.
  * simpl in H. simpl.
    break_match_hyp. inv H. f_equal. omega.
    app IHc H.
Qed.

Lemma label_pos_cons :
  forall c l k z a,
    z > k + 1 ->
    label_pos l k (a :: c) = Some z ->
    label_pos l k c = Some (z - 1).
Proof.
  intros. simpl in H0. break_match_hyp.
  inv H0. omega.
  rewrite label_pos_1. 
  replace (z - 1 + 1) with z by omega.
  assumption.
Qed.

Lemma label_pos_answer_valid :
  forall c l k z,
    label_pos l k c = Some z ->
    z >= k + 1.
Proof.
  induction c; intros.
  * simpl in H. inv H.
  * simpl in H. break_match_hyp. inv H. omega.
    app IHc H. omega.
Qed.
  
Lemma label_pos_append_head_k :
  forall c l z c' k,
    label_pos l k (c ++ c') = Some z ->
    z > zlen c + k ->
    k >= 0 ->
    label_pos l k c' = Some (z - zlen c).
Proof.
  induction c; intros.
  * simpl in H. unfold zlen. simpl.
    replace (z - 0) with z by omega.
    auto.
  * assert (z > k + 1 \/ z <= k + 1) by omega.
    destruct H2.
    replace ((a :: c) ++ c') with (a :: c ++ c') in H by auto.
    apply label_pos_cons in H; try omega.
    apply IHc in H; try omega.
    rewrite zlen_cons. rewrite H.
    f_equal. omega.
    rewrite zlen_cons in H0. omega.
    app label_pos_answer_valid H.
    rewrite zlen_cons in H0.
    name (zlen_nonneg instruction c) zlnc.
    omega.
Qed.

Lemma label_pos_append_head :
  forall c l z c',
    label_pos l 0 (c ++ c') = Some z ->
    z > zlen c ->
    label_pos l 0 c' = Some (z - zlen c).
Proof.
  intros.
  apply label_pos_append_head_k; try assumption; try omega.
Qed.

Lemma label_pos_lt :
  forall l c z,
    label_pos l 0 c = Some z ->
    z <= zlen c.
Proof.
  induction c; intros.
  * simpl in H. inv H.
  * rewrite zlen_cons.
    simpl in H. break_match_hyp. inv H.
    name (zlen_nonneg instruction c) zlnc. omega.
    replace 1 with (0 + 1) in H by omega.
    replace z with ((z - 1) + 1) in H by omega.
    rewrite <- label_pos_1 in H.
    app IHc H. omega.
Qed.

Ltac find_one_instr :=
  match goal with
    | [ H : find_instr ?X ?Y = _, H2 : ?Y = ?Z ++ _, H3 : ?X = zlen ?Z + 0 |- _ ] =>
      rewrite H2 in H; rewrite H3 in H;
      rewrite find_instr_append_head in H by omega;
      simpl in H; inv H
  end.


Ltac peel_code :=
  match goal with
    | [ H : find_instr ?X ?Y = _,
            H2 : ?X = _,
                 H3 : ?Y = _ |- _ ] =>
      rewrite H2 in H; rewrite H3 in H;
      try rewrite find_instr_append_head in H by omega;
      try erewrite find_instr_append_tail with (c := nil) in H by omega;
      try rewrite app_nil_r in H
  end.

Lemma label_pos_in_range :
  forall l c z,
    label_pos l 0 c = Some z ->
    0 < z <= zlen c.
Proof.
  intros. split. app label_pos_answer_valid H. omega.
  app label_pos_lt H.
Qed.

Lemma label_pos_append_tail_k :
  forall l c0 c1 c2 z k,
    z <= zlen c0 ->
    label_pos l k (c0 ++ c1) = Some (z + k) ->
    label_pos l k (c0 ++ c2) = Some (z + k).
Proof.
  induction c0; intros.
  app label_pos_answer_valid H0. unfold zlen in H. simpl in H.
  omega.
  destruct (instr_eq a (Plabel l)).
  subst a. simpl in H0. simpl.
  rewrite peq_true in *. assumption.
  simpl in H0. simpl. break_match_hyp. 
  unfold Asm.is_label in Heqb.
  destruct a; simpl in Heqb; inversion Heqb.
  break_match_hyp. congruence. inv H2.
  replace (z + k) with ((z-1) + (k+1)) by omega.
  eapply IHc0. rewrite zlen_cons in H. omega.
  replace (z - 1 + (k + 1)) with (z + k) by omega.
  eassumption.
Qed.

Lemma label_pos_append_tail :
  forall l c0 c1 c2 z,
    z <= zlen c0 ->
    label_pos l 0 (c0 ++ c1) = Some z ->
    label_pos l 0 (c0 ++ c2) = Some z.
Proof.
  intros. replace z with (z + 0) by omega.
  replace z with (z + 0) in H0 by omega.
  eapply label_pos_append_tail_k; eauto.
Qed.


Lemma label_pos_no_label_k :
  forall l c0 c1 z k,
    label_pos l k c1 = Some (z - zlen c0 + k) ->
    (forall z0 i, find_instr z0 c0 = Some i -> i <> Plabel l) ->
    label_pos l k (c0 ++ c1) = Some (z + k).
Proof.
  induction c0; intros.
  simpl. rewrite H. f_equal. unfold zlen. simpl. omega.
  rewrite zlen_cons in H.
  simpl. break_match. specialize (H0 0 a). simpl in H0.
  specialize (H0 eq_refl). destruct a; try congruence; simpl in Heqb; inv Heqb.
  break_match_hyp. subst l. congruence. inv H2.
  replace (z + k) with ((z - 1) + (k + 1)) by omega.
  eapply IHc0; eauto.
  replace (z - 1 - zlen c0 + (k + 1)) with ((z - zlen c0 + k - 1) + 1) by omega.
  rewrite <- label_pos_1. rewrite H. f_equal. omega.
  intros. eapply H0 with (1 + z0).
  apex in_range_find_instr H1.
  rewrite find_instr_head by omega.
  assumption.
Qed.

Lemma label_pos_no_label :
  forall l c0 c1 z,
    label_pos l 0 c1 = Some (z - zlen c0) ->
    (forall z0 i, find_instr z0 c0 = Some i -> i <> Plabel l) ->
    label_pos l 0 (c0 ++ c1) = Some z.
Proof.
  intros. 
  replace z with (z + 0) by omega.
  eapply label_pos_no_label_k; eauto.
  rewrite H. f_equal. omega.
Qed.

Lemma label_pos_append_absence_k :
  forall l c0 c1 z k,
    label_pos l k (c0 ++ c1) = Some (z + k) ->
    z > zlen c0 ->
    (forall z0 i, find_instr z0 c0 = Some i -> i <> Plabel l).
Proof.
  induction c0; intros.
  simpl in H1. inv H1.
  simpl in H. break_match_hyp. inv H. 
  assert (z = 1) by omega.
  subst z. rewrite zlen_cons in H0.
  name (zlen_nonneg instruction c0) zlnc. omega.
  replace (z + k) with ((z - 1) + (k + 1)) in H by omega.
  destruct (zeq z0 0). subst z0. simpl in H1. inv H1.
  destruct i; simpl in Heqb; try inversion Heqb; try congruence.
  break_match_hyp. inv H2. congruence.
  apex in_range_find_instr H1.
  replace z0 with (1 + (z0 - 1)) in H1 by omega.
  rewrite find_instr_head in H1 by omega.
  eapply IHc0; eauto. rewrite zlen_cons in H0. omega.
Qed.

Lemma label_pos_append_absence :
  forall l c0 c1 z,
    label_pos l 0 (c0 ++ c1) = Some z ->
    z > zlen c0 ->
    (forall z0 i, find_instr z0 c0 = Some i -> i <> Plabel l).
Proof.
  intros. replace z with (z + 0) in H by omega.
  eapply label_pos_append_absence_k; eauto.
Qed.

Lemma label_pos_replace :
  forall c0 c1 f r l z,
    label_pos l 0 (c0 ++ f ++ c1) = Some z ->
    (forall z i, find_instr z f = Some i -> i <> Plabel l ) ->
    (forall z i, find_instr z r = Some i -> i <> Plabel l ) ->
    zlen f = zlen r ->
    label_pos l 0 (c0 ++ r ++ c1) = Some z.
Proof.
  intros. 
  app label_pos_in_range H.
  repeat rewrite zlen_app in H. 
  name H3 Hlab_pos.
  assert (z <= zlen c0 \/ z > zlen c0) by omega.
  destruct H4.
  eapply label_pos_append_tail in H3; eauto.
  eapply label_pos_append_head in H3; try omega.
  assert (z - zlen c0 <= zlen f \/ z - zlen c0 > zlen f) by omega.
  destruct H5.
  eapply label_pos_append_tail with (c2 := nil) in H3; eauto.
  app label_pos_find_instr H3. rewrite app_nil_r in H3.
  app H0 H3. simpl in H3. congruence.
  name (label_pos_append_absence l c0 (f ++ c1) z Hlab_pos H4) Hc0_abs.
  apply label_pos_no_label; auto.
  apply label_pos_no_label; auto.
  eapply label_pos_append_head in H3; try omega.
  rewrite <- H2. assumption.
Qed.  
