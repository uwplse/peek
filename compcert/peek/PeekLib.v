Require Import Coqlib.
Require Import Asm.
Require Import Compare.
Require Import Maps.

Require Import PeekTactics.
Require Import Zlen.

(* all_pregs *)

Definition all_pregs : list preg := IR EAX :: IR EBX :: IR ECX :: IR EDX :: IR ESI :: IR EDI :: IR EBP :: IR ESP :: FR XMM0 :: FR XMM1 :: FR XMM2 :: FR XMM3 :: FR XMM4 :: FR XMM5 :: FR XMM6 :: FR XMM7 :: PC :: ST0 :: RA :: CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: FRH XMM0H :: FRH XMM1H :: FRH XMM2H :: FRH XMM3H :: FRH XMM4H :: FRH XMM5H :: FRH XMM6H :: FRH XMM7H :: nil.

Lemma all_pregs_correct:
  forall p,
    In p all_pregs.
Proof.
  destruct p; 
  try destruct i;
  try destruct f;
  try destruct c;
  try destruct h;
  unfold all_pregs;
  simpl;
  try solve [prove_or_eq reflexivity].
Qed.

Ltac disj_inv :=
  repeat match goal with
    | [ H : _ \/ _ |- _ ] => destruct H
    | [ H : _ = _ |- _ ] => inversion H
    | [ H : False |- _ ] => inversion H
  end.

Lemma nodup_all_pregs:
  NoDup all_pregs.
Proof.
  unfold all_pregs.
  repeat constructor;
  simpl; unfold not; intros;
  disj_inv.
Qed.

(* Jump info *)

Inductive jinfo : Set :=
  | cond_jump : testcond -> option testcond -> label -> jinfo
  | uncond_jump : label -> jinfo
  | non_jump : jinfo
  | unsupported : jinfo.

Definition jump_info (i : instruction) : jinfo :=
  match i with
    (* don't support jumps for now *)
    | Pjcc cond lab => unsupported
    | Pjmp_l lab => unsupported
    (* in the future support Pjcc2 and Pjmptbl, for now not *)
    | Pjcc2 _ _ _ => unsupported
    | Pjmptbl _ _ => unsupported
    (* all calls will forever be unsupported *)
    (* they don't belong being symbolically evaluated *)
    | Pjmp_s _ _ => unsupported
    | Pcall_s _ _ => unsupported
    | Pjmp_r _ _ => unsupported
    | Pcall_r _ _ => unsupported
    | Pret _ => unsupported
    | Pbuiltin _ _ _ => unsupported
    | Pannot _ _ => unsupported
    | _ => non_jump
  end.


(* Worklist *)

Definition nd_add (z : Z) (zs : list Z) : list Z :=
  if (in_dec Z.eq_dec z zs)
  then zs
  else z :: zs.

Fixpoint wl_add (l : list Z) (zs : list Z) : list Z :=
  match l with
    | nil => zs
    | f :: r => nd_add f (wl_add r zs)
  end.

Lemma wl_add_in:
  forall a b c,
    In a b ->
    In a (wl_add b c).
Proof.
  intros; induction b.
  * simpl in H. inv H.
  * simpl in H. destruct H.
    unfold wl_add. fold wl_add.
    unfold nd_add. break_match.
    subst a0. assumption.
    simpl. left. assumption.
    specialize (IHb H).
    simpl. unfold nd_add.
    break_match. assumption.
    simpl. right. assumption.
Qed.

Lemma wl_add_in_r:
  forall a b c,
    In a c ->
    In a (wl_add b c).
Proof.
  induction b; intros.
  * simpl in H. unfold wl_add.
    assumption.
  * simpl. unfold nd_add.
    break_match. apply IHb; auto.
    simpl. right. apply IHb; auto.
Qed.

Lemma wl_add_not:
  forall a b c,
    ~ In a (wl_add b c) ->
    (~ In a b /\ ~ In a c).
Proof.
  intros.
  split. unfold not. intros.
  apply wl_add_in with (c := c) in H0.
  congruence.
  unfold not. intros.
  apply wl_add_in_r with (b := b) in H0.
  congruence.
Qed.

Lemma nodup_nd_add:
  forall z l,
    NoDup l ->
    NoDup (nd_add z l).
Proof.
  induction 1.
  * unfold nd_add. break_match; constructor.
    assumption. constructor.
  * unfold nd_add. break_match.
    constructor. assumption. assumption.
    constructor. assumption.
    constructor. assumption. assumption.
Qed.
    
Lemma nodup_wl_add:
  forall zs l,
    NoDup l ->
    NoDup (wl_add zs l).
Proof.
  induction zs; intros.
  * simpl. assumption.
  * unfold wl_add. fold wl_add.
    specialize (IHzs l H).
    apply nodup_nd_add. assumption.
Qed.

(* ListLogic *)

Lemma exists_not_P:
  forall {A} (a : A) (l : list A) (P : A -> Prop),
    ~ P a -> (exists x, In x l /\ P x) -> (exists x, In x (a :: l) /\ P x).
Proof.
  intros. simpl. destruct H0.
  exists x. split. right.
  destruct H0. assumption.
  destruct H0. assumption.
Qed.

Lemma forall_not_in:
  forall {A} (a : A) (l : list A) (P : A -> Prop),
    ~ P a -> (forall x, In x l -> ~ P x) -> (forall x, In x (a :: l) -> ~ P x).
Proof.
  intros. simpl in H1. destruct H1. rewrite <- H1. assumption.
  apply H0. assumption.
Qed.

Lemma in_l_P:
  forall A (l : list A) {P : A -> Prop} (d : forall (a : A), {P a} + {~ P a}),
    ((exists x, In x l /\ P x) \/  forall x, In x l -> ~ P x).
Proof.
  induction l; intros.
  * right. intros. simpl in H. inversion H.
  * destruct (d a). left. exists a.
    simpl. split. left. reflexivity. assumption.
    destruct (IHl P d). left. apply exists_not_P; assumption.
    right. apply forall_not_in; assumption.
Qed.

(* MapLib *)

Lemma not_in_map:
  forall {A} l z (v : A) zmap,
    ~ In z l ->
    map (fun z0 => ZMap.get z0 (ZMap.set z v zmap)) l = map (fun z0 => ZMap.get z0 zmap) l.
Proof.
  induction l; intros.
  * simpl. reflexivity.
  * simpl. assert (z <> a). simpl in H. firstorder.
    f_equal. rewrite ZMap.gso; auto.
    apply IHl. simpl in H. firstorder.
Qed.

Lemma map_get_not_in:
  forall {A} l z (v : A) zm,
    ~ In z l ->
    map (fun z0 => ZMap.get z0 (ZMap.set z v zm)) l = map (fun z0 => ZMap.get z0 zm) l.
Proof.
  induction l; intros.
  * simpl. reflexivity.
  * simpl in H.
    assert ((~ a = z) /\ ~ In z l). tauto.
    destruct H0. simpl. rewrite <- (IHl z v zm H1).
    rewrite ZMap.gso by auto.
    reflexivity.
Qed.

Lemma in_map_set_equiv':
  forall {A} {B} (f : A -> B) (l1 l2 : list A),
    (forall x, In x l1 -> In x l2) ->
    (forall y, In y (map f l1) -> In y (map f l2)).
Proof.
  intros. 
  apply in_map_iff.
  apply in_map_iff in H0.
  break_exists.
  intuition.
  apply H in H2.
  eauto.
Qed.

Lemma in_map_set_equiv:
  forall {A} {B} (f : A -> B) (l1 l2 : list A),
    (forall x, In x l1 <-> In x l2) ->
    (forall y, In y (map f l1) <-> In y (map f l2)).
Proof.
  intros. split; intros.
  - eapply in_map_set_equiv'; try apply H.
    auto.
  - eapply in_map_set_equiv'; try apply H.
    auto.
Qed.

(* Range *)

Fixpoint range_helper(n:nat):list nat :=
  match n with
    | O => O :: nil
    | S n' => (S n') :: range_helper n'
  end.

Definition range(z:Z):list Z :=
  map Z.of_nat (range_helper (Z.to_nat z)).

Theorem range_helper_spec :
  forall (a b : nat),
    le a b ->
    In a (range_helper b).
Proof.
  induction b.
  * intros. destruct a. simpl. auto.
    inversion H.
  * intros. simpl. 
    apply le_lt_eq_dec in H. destruct H.
    right. assert (le a b). omega.
    apply IHb; auto.
    left. auto.
Qed.

Theorem range_spec :
  forall (a b : Z),
    a < b ->
    a >= 0 ->
    In a (range b).
Proof.
  intros. unfold range.
  rewrite <- nat_of_Z_eq with (z := a); auto.
  apply in_map. unfold nat_of_Z.
  apply range_helper_spec.
  apply Z2Nat.inj_le; omega.
Qed.


Lemma lt_range:
  forall (n m : nat),
    In n (range_helper m) <->
    le n m.
Proof.
  split; intros.
  * induction m.
    - simpl in H. destruct H. omega. inv H.
    - simpl in H. destruct H. omega. apply IHm in H. omega.
  * induction m.
    - simpl. left. destruct n; omega.
    - apply Compare.le_le_S_eq in H.
      destruct H. assert ((n <= m)%nat). omega.
      apply IHm in H0. simpl. right. assumption.
      simpl. left. auto.
Qed.

Lemma lt_range_contra:
  forall n m,
    gt n m <-> ~ In n (range_helper m).
Proof.
  split; intros.
  * unfold not. intros.
    rewrite lt_range in H0. omega.
  * destruct (le_lt_dec n m).
    - rewrite <- lt_range in l. contradiction.
    - omega.
Qed.

(* RegsLib *)

Lemma undef_regs_not_in:
  forall l p rs,
    ~ In p l ->
    (undef_regs l rs) p = rs p.
Proof.
  induction l; intros.
  * simpl. reflexivity.
  * simpl. simpl in H.
    assert (a <> p) by tauto.
    rewrite IHl by tauto.
    rewrite Pregmap.gso by auto.
    reflexivity.
Qed.

Lemma set_regs_not_in:
  forall l p v rs,
    ~ In p l ->
    (set_regs l v rs) p = rs p.
Proof.
  induction l; intros.
  * simpl. reflexivity.
  * simpl. simpl in H.
    assert (a <> p) by tauto.
    destruct v. reflexivity.
    rewrite IHl by tauto.
    rewrite Pregmap.gso by auto.
    reflexivity.
Qed.

Lemma set_regs_nil :
  forall r rs,
    set_regs r nil rs = rs.
Proof.
  intros. destruct r. simpl. reflexivity.
  simpl. reflexivity.
Qed.

Lemma set_regs_in:
  forall p r v rs rs',
    In p r ->
    rs p = rs' p ->
    (set_regs r v rs) p = (set_regs r v rs') p.
Proof.
  induction r; intros.
  * simpl in H. inv H.
  * simpl in H.
    destruct (in_dec preg_eq p r).
    simpl. destruct v. assumption.
    rewrite (IHr v0 (rs # a <- v) (rs' # a <- v)); auto.
      destruct (preg_eq a p). rewrite e. repeat rewrite Pregmap.gss. auto.
      repeat rewrite Pregmap.gso by auto. assumption.
   destruct H. rewrite H.
   simpl. destruct v. auto.
   repeat rewrite set_regs_not_in by auto.
   repeat rewrite Pregmap.gss. auto.
   congruence.
Qed.

Lemma undef_regs_in:
  forall p r rs rs',
    In p r ->
    (undef_regs r rs) p = (undef_regs r rs') p.
Proof.
  induction r; intros.
  * simpl in H. inv H.
  * destruct (in_dec preg_eq p r).
    simpl.
    rewrite (IHr (rs # a <- Values.Vundef) (rs' # a <- Values.Vundef)) by auto.
    reflexivity.
    simpl in H. destruct H.
    simpl. repeat rewrite undef_regs_not_in by auto.
    rewrite H. repeat rewrite Pregmap.gss. reflexivity.
    congruence.
Qed.

Lemma undef_regs_both:
  forall p rs rs' r,
    (~ In p r -> rs p = rs' p) ->
    (undef_regs r rs) p = (undef_regs r rs') p.
Proof.
  intros.
  destruct (in_dec preg_eq p r).
  eapply undef_regs_in; eauto.
  repeat rewrite undef_regs_not_in by auto.
  apply H. assumption.
Qed.

Lemma undef_regs_not_undef:
  forall rs regs p,
    (undef_regs regs rs) p <> Values.Vundef ->
    ~ In p regs.
Proof.
  induction regs; intros.
  * unfold not. intros. simpl in H0. inv H0.
  * simpl in H.
    destruct (in_dec preg_eq p regs).
    rewrite undef_regs_in with (rs' := rs) in H.
    apply IHregs in H. unfold not in H. specialize (H i). inv H.
    auto.
    destruct (preg_eq p a). subst.
    rewrite undef_regs_not_in in H by auto.
    rewrite Pregmap.gss in H. congruence.
    unfold not. intros.
    simpl in H0. destruct H0. symmetry in H0. congruence.
    specialize (n H0). inv n.
Qed.

Lemma zlen_nonneg:
  forall A l,
    @zlen A l >= 0.
Proof.
  induction l; unfold zlen; simpl; try omega.
  rewrite Zpos_P_of_succ_nat. unfold zlen in IHl.
  omega.
Qed.  


Lemma zlen_cons:
  forall A a l,
    @zlen A (a :: l) = (@zlen A l + 1).
Proof.
  intros. unfold zlen. simpl. unfold Z_of_nat'.
  unfold Z.of_nat.
  destruct (length l). simpl. auto.
  simpl. rewrite Pplus_one_succ_r. reflexivity.
Qed.

Lemma list_preppend_eq :
  forall {A} (a b c : list A),
    a ++ b = a ++ c ->
    b = c.
Proof.
  induction a; intros.
  simpl in *.
  trivial.
  simpl in *.
  inv H.
  eauto.
Qed.

Lemma list_pp_eq :
  forall {A} b c (a : A),
    b ++ (a :: nil) = c ++ (a :: nil) ->
    b = c.
Proof.
  induction b; destruct c; simpl in *;
  intros; auto. inv H. destruct c; inv H2.
  inv H. destruct b; simpl in *; inv H2.
  inv H. app IHb H2.
  subst b. reflexivity.
Qed.

Lemma list_postppend_eq :
  forall {A} (a b c : list A),
    b ++ a = c ++ a ->
    b = c.
Proof.
  induction a; intros.
  repeat rewrite app_nil_r in *.
  eauto.
  specialize (IHa (b ++ (a :: nil)) (c ++ a :: nil)).
  repeat rewrite app_ass in IHa.
  simpl in IHa.
  specialize (IHa H).
  eapply list_pp_eq in IHa; eauto.
Qed. 
Hint Resolve list_preppend_eq.

Lemma list_eq_middle_therefore_eq :
  forall {A} (c0 a c1 c2 c3 : list A),
    c0 ++ a ++ c1 = c2 ++ a ++ c3 ->
    zlen c0 = zlen c2 ->
    c0 = c2 /\ c1 = c3.
Proof.
  induction c0; intros.
  destruct c2.
  simpl in *.
  split; eauto.
  inv H0.
  simpl in *.
  split.

  destruct c2.
  inv H0.
  simpl in *.
  repeat rewrite zlen_cons in H0.
  assert (zlen c0 = zlen c2) by omega.
  inv H.
  eapply IHc0 in H1; eauto.
  f_equal.
  break_and.
  assumption.

  destruct c2.
  inv H0.
  simpl in *.
  repeat rewrite zlen_cons in H0.
  assert (zlen c0 = zlen c2) by omega.
  inv H.
  eapply IHc0 in H1; eauto.
  f_equal.
  break_and.
  assumption.
Qed.  

Lemma list_middle_eq :
  forall {A} (c0 a b c1 : list A),
    c0 ++ b ++ c1 = c0 ++ a ++ c1 ->
    a = b.
Proof.
  induction c0; intros.
  simpl in H.
  eapply list_postppend_eq in H.
  congruence.
  inv H. eauto.
Qed.


Definition Z_nat_ind :
  forall (P : Z -> Prop),
    P 0 ->
    P 1 ->
    (forall p, p < 0 -> P p) ->
    (forall p, p > 0 -> P p -> P (p + 1)) ->
    forall p, P p.
Proof.
  induction p; intros.
  assumption.
  induction p using positive_Peano_ind.
  assumption.
  replace (Z.pos (Pos.succ p)) with ((Z.pos p) + 1). Focus 2. simpl.
  f_equal. rewrite Pplus_one_succ_r. reflexivity. apply H2; eauto.
  apply Zgt_pos_0. apply H1.
  apply Zlt_neg_0.
Qed.


