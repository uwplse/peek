Require Import Coqlib.
Require Import Asm.
Require Import Maps.
Require Import PeekTactics.

Definition reml{A}(eq : forall (x y : A), {x = y} + {x <> y}) := list_fold_right (remove eq).
Definition add {A}(eq : forall (x y : A), {x = y} + {x <> y})(p : A)(l : list A) :=
  if In_dec eq p l then l else p :: l.
Definition addl{A}(eq : forall (x y : A), {x = y} + {x <> y}) := list_fold_right (add eq).


Fixpoint union {A : Type} (eq_dec : forall (a b:A), {a = b} + {a <> b})(x y : list A) :=
  match x with
    | nil => y
    | f :: r => if (In_dec eq_dec f y) 
                then union eq_dec r y 
                else f :: (union eq_dec r y)
  end.

Fixpoint union_l {A : Type} (eq_dec : forall (a b : A), {a = b} + {a <> b}) (l : list (list A)) :=
  match l with
    | nil => nil
    | f :: r => union eq_dec f (union_l eq_dec r)
  end.

  

Fixpoint rem1 {A : Type} (eq_dec : forall (a b : A), {a = b} + {a <> b}) (x : A) (y : list A) :=
  match y with
    | nil => nil
    | f :: r => if eq_dec f x
                then r
                else f :: (rem1 eq_dec x r)
  end.

Fixpoint list_diff {A : Type} (eq_dec : forall (a b : A), {a = b} + {a <> b}) (x y : list A) : list A :=
  match x with
    | nil => y
    | f :: r => if In_dec eq_dec f y 
                then list_diff eq_dec r (rem1 eq_dec f y)
                else f :: (list_diff eq_dec r y)
  end.

Fixpoint intersect {A : Type} (eq_dec : forall (a b : A), {a = b} + {a <> b}) (l1 l2 : list A) :=
  match l1 with
    | nil => nil
    | f :: r => if In_dec eq_dec f l2
                then f :: (intersect eq_dec r l2)
                else intersect eq_dec r l2
  end.

Lemma add_elem:
  forall {A} l (p a : A) {eq},
    (p = a \/ In p l) <-> (In p (add eq a l)).
Proof.
  induction l; split; intros.
  * simpl. destruct H. left. auto.
    right. simpl in H. auto.
  * simpl. simpl in H.
    destruct H. left. auto.
    right. auto.
  * destruct H. rewrite H.
    simpl. unfold add.
    break_match; auto.
    simpl. left. reflexivity.
    unfold add. break_match.
    auto. simpl. right.
    simpl in H. tauto.
  * simpl. unfold add in H.
    break_match_hyp. simpl in i.
    simpl in H. tauto.
    simpl in H. destruct H.
    left. auto. right. tauto.
Qed.

Lemma add_in_spec:
  forall {A} (p : A) l l2 {eq},
    (In p l \/ In p l2) <-> In p (addl eq l l2).
Proof.
  induction l; split; intros.
  * unfold addl. unfold list_fold_right. simpl.
    destruct H. simpl in H. inv H. assumption.
  * right. unfold addl in H. unfold list_fold_right in H.
    simpl in H. assumption.
  * unfold addl. 
    rewrite list_fold_right_eq.
    apply add_elem. fold (addl eq).
    rewrite <- IHl. simpl in H.
    destruct H. destruct H. left. auto.
    tauto. tauto.
  * unfold addl in H.
    rewrite list_fold_right_eq in H.
    fold (addl eq) in H. apply add_elem in H.
    simpl. destruct H. left. left. auto.
    apply IHl in H. tauto.
Qed.

Lemma add_in_l:
  forall {A} (p : A) l l2 {eq},
    In p l ->
    In p (addl eq l l2).
Proof.
  intros. assert (In p l \/ In p l2) by firstorder.
  apply add_in_spec; auto.
Qed.

Lemma add_in_r:
  forall {A} (p : A) l l2 {eq},
    In p l2 ->
    In p (addl eq l l2).
Proof.
  intros. assert (In p l \/ In p l2) by firstorder.
  apply add_in_spec; auto.
Qed.

Lemma rem_elem:
  forall {A} l (p a : A) {eq},
    (p <> a /\ In p l) <->
    In p (remove eq a l).
Proof.
  induction l; split; intros.
  * simpl. simpl in H. tauto.
  * simpl in H. tauto.
  * destruct (eq a0 a) eqn:?.
    simpl. rewrite Heqs. apply IHl.
    simpl in H. destruct H.
    split. auto.
    destruct (eq a p). congruence.
    destruct H0. congruence. auto.
    destruct H. simpl in H0.
    unfold remove. rewrite Heqs.
    fold (remove eq).
    destruct H0. simpl. left. auto.
    simpl. right. rewrite <- IHl. auto.
  * unfold remove in H. break_match_hyp.
    fold (remove eq) in H. apply IHl in H.
    simpl. split. tauto. right. tauto.
    fold (remove eq) in H. simpl in H.
    split. destruct H. destruct (eq p a0). congruence.
    auto. apply IHl in H. tauto.
    rewrite <- IHl in H. simpl. tauto.
Qed.

Lemma de_morgan:
  forall A B,
    ~ (A \/ B) <-> (~A) /\ (~B).
Proof.
  split.
  intros. unfold not in *.
  split. intros. tauto.
  intros. tauto.
  intros. unfold not in *.
  intros. destruct H.
  destruct H0; auto.
Qed.

Lemma rem_in:
  forall {A} (p : A) l l2 {eq},
    (In p l2 /\ ~ In p l) <->
    In p (reml eq l l2).
Proof.
  induction l; split; intros.
  * unfold reml. rewrite list_fold_right_eq. tauto.
  * split. unfold reml in H. rewrite list_fold_right_eq in H.
    auto. tauto.
  * unfold reml. rewrite list_fold_right_eq.
    fold (reml eq). apply rem_elem. rewrite <- IHl.
    simpl in H. destruct H. apply de_morgan in H0.
    destruct H0. split. auto. tauto.
  * unfold reml in H. rewrite list_fold_right_eq in H.
    fold (reml eq) in H. apply rem_elem in H.
    rewrite <- IHl in H. simpl. split. tauto.
    apply de_morgan. split. destruct H.
    auto. tauto.
Qed.

Lemma intersect_correct:
  forall {A} (p : A) l1 l2 {eq},
    (In p l1 /\ In p l2) <->
    In p (intersect eq l1 l2).
Proof.
  induction l1; split; intros.
  * simpl. simpl in H. destruct H. assumption.
  * simpl in H. simpl. inversion H.
  * destruct H. simpl.
    destruct (in_dec eq a l2).
    destruct (eq p a). rewrite e. simpl. left. reflexivity.
    simpl. right. simpl in H. destruct H. congruence.
    rewrite <- IHl1. split; assumption.
    destruct (eq p a). rewrite e in H0. congruence.
    simpl in H. destruct H. congruence.
    rewrite <- IHl1. split; assumption.
  * destruct (eq p a). simpl. split. left. congruence.
    simpl in H. destruct (in_dec eq a l2).
    rewrite e. assumption.
    rewrite <- IHl1 in H. destruct H. assumption.
    simpl. split. right.
    simpl in H. destruct (in_dec eq a l2).
    simpl in H. destruct H. congruence.
    rewrite <- IHl1 in H. destruct H. assumption.
    rewrite <- IHl1 in H. destruct H. assumption.
    simpl in H. destruct (in_dec eq a l2).
    simpl in H. destruct H. congruence.
    rewrite <- IHl1 in H. destruct H. assumption.
    rewrite <- IHl1 in H. destruct H. assumption.
Qed.
  

Lemma union_correct:
  forall {A} (p : A) l l2 {eq},
    (In p l \/ In p l2) <-> 
    In p (union eq l l2).
Proof.
  induction l; split; intros.
  * destruct H.
    - simpl in H. inv H.
    - unfold union. apply H.
  * simpl in H. right. assumption.
  * destruct H. destruct (eq p a).
    + simpl. destruct (in_dec eq a l2).
      - rewrite <- e in i. apply IHl. right. assumption.
      - rewrite e. simpl. left. reflexivity.
    + simpl in H. destruct H. congruence.
      assert (In p l \/ In p l2).
        left. assumption.
      rewrite IHl in H0.
      simpl. destruct (in_dec eq a l2).
      - apply H0.
      - simpl. right. assumption.
    + simpl. destruct (in_dec eq a l2).
      rewrite <- IHl. right. assumption.
      simpl. right. apply IHl. right. assumption.
  * destruct (in_dec eq p l2) eqn:?.
    - right. assumption.
    - left. simpl in H.
      destruct (in_dec eq a l2) eqn:?.
      rewrite <- IHl in H. 
      destruct H. simpl. right. assumption. congruence.
      simpl in H. destruct (eq a p). simpl. left. assumption.
      destruct H. congruence.
      rewrite <- IHl in H. simpl. right.
      destruct H. assumption. congruence.
Qed.

Lemma union_nil:
  forall {A} (l : list A) {eq},
    union eq l nil = l.
Proof.
  induction l; intros.
  * reflexivity.
  * simpl. rewrite IHl. reflexivity.
Qed.

Lemma in_union_l:
  forall {A} (p : A) l1 l2 {eq},
    In p l1 ->
    In p (union_l eq (l1 :: l2)).
Proof.
  intros. unfold union_l.
  induction l2.
  * unfold union. rewrite union_nil. assumption.
  * apply union_correct. left. assumption.
Qed.

Lemma in_union_l_spec:
  forall {A} (p : A) t h {eq},
    (In p h \/ In p (union_l eq t)) <->
    In p (union_l eq (h :: t)).
Proof.
  induction t; split; intros.
  * destruct H. 
    - unfold union_l. rewrite union_nil. assumption.
    - simpl in H. inversion H.
  * unfold union_l in H. rewrite union_nil in H.
    left. assumption.
  * destruct H. 
    - apply in_union_l. assumption.
    - (* this is true, prove later *)
      rewrite <- IHt in H.
      simpl. apply union_correct.
      right. apply union_correct. assumption.
  * rewrite <- (IHt a).
    destruct (In_dec eq p h).
    left. assumption.
    right.
    simpl in H. rewrite <- union_correct in H.
    destruct H. congruence.
    rewrite IHt. simpl. assumption.
Qed.

Lemma in_map_union_l:
  forall {A} is (p : A) i l {eq},
    In p (ZMap.get i l) ->
    In i is ->
    In p (union_l eq (map (fun z0 => ZMap.get z0 l) is)).
Proof.
  induction is; intros.
  * simpl in H0. inversion H0.
  * destruct (Z.eq_dec i a).
    unfold map. apply in_union_l_spec.
    left. rewrite <- e. assumption.
    unfold map. apply in_union_l_spec.
    destruct (In_dec eq p (ZMap.get a l)).
    - left. assumption.
    - right. unfold map in IHis.
      apply (IHis p i l). assumption.
      simpl in H0. destruct H0. congruence.
      assumption.
Qed.

Fixpoint contains {A : Type} (eq : forall (a b : A), {a = b} + {a <> b}) (a : A) (l : list A) :=
  match l with
    | nil => false
    | f :: r => if eq f a then true else contains eq a r
  end.

Fixpoint is_subset {A : Type} (eq : forall (a b : A), {a = b} + {a <> b}) (l1 l2 : list A) :=
  match l1 with
    | f :: r => andb (contains eq f l2) (is_subset eq r l2)
    | nil => true
  end.

Definition set_equiv {A : Type} (eq : forall (a b : A), {a = b} + {a <> b}) (l1 l2 : list A) := andb (is_subset eq l1 l2) (is_subset eq l2 l1).
  

(* These last two courtesy of ztatlock *)
Lemma subset_dec :
  forall {A : Type} {eq : forall (a b : A), {a = b} + {a <> b}} (l1 l2 : list A),
    { forall (a : A), In a l1 -> In a l2 } + { ~ forall (a : A), In a l1 -> In a l2}.
Proof.
  induction l1. 
  destruct l2; simpl; intuition.
  intro l2; destruct (IHl1 l2).
  destruct (in_dec eq a l2);
    simpl; [left | right]; intuition.
  subst; auto.
  right; intuition.
Defined.

Lemma set_equiv_dec :
  forall {A : Type} {eq : forall (a b : A), {a = b} + {a <> b}} (l1 l2 : list A),
    { forall (a : A), In a l1 <-> In a l2 } + { ~ forall (a : A), In a l1 <-> In a l2}.
Proof.
  intros. destruct (subset_dec (eq := eq) l1 l2).
  + destruct (subset_dec (eq := eq) l2 l1).
    - left; intuition.
    - right; intuition.
      apply n; intros; apply H; auto.
  + right; intuition.
    apply n; intros; apply H; auto.
Defined.

