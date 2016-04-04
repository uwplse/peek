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

Require Import AsmBits.
Require Import PeekTactics.
Require Import PregTactics.

Definition val_eq (v v' : val) : Prop :=
  match v with
    | Vundef =>
      forall b ofs,
        v' <> Vptr b ofs
    | Vptr _ _ => False
    | _ => v = v'
  end.

Lemma val_eq_or :
  forall v v',
    val_eq v v' ->
    (v = Vundef /\ (forall b ofs, v' <> Vptr b ofs))  \/ v = v'.
Proof.
  intros. unfold val_eq in *.
  break_match_hyp;
    try solve [left; split; intros; congruence];
    try inv_false;
    right; congruence.
Qed.

Lemma val_eq_lessdef :
  forall v v',
    val_eq v v' -> Val.lessdef v v'.
Proof.
    intros.
  app val_eq_or H; break_or; subst.
  break_and. subst. econstructor.
  econstructor.
Qed.

Lemma val_eq_def :
  forall v x,
    v = x ->
    forall v',      
      val_eq v v' ->
      x <> Vundef ->
      v' = x.
Proof.
  intros. unfold val_eq in H0.
  rewrite H in H0.
  break_match; simpl; try congruence.
  inv_false.
Qed.


Lemma val_eq_update :
  forall rs rs' v v' p r,
    (p <> r -> val_eq (rs p) (rs' p)) ->
    val_eq v v' ->
    val_eq (rs # r <- v p) (rs' # r <- v' p).
Proof.
  intros. preg_case. assumption.
  eapply H. congruence.
Qed.

Lemma val_eq_add :
  forall x y a b,
    val_eq x y ->
    val_eq a b ->
    val_eq (Val.add x a) (Val.add y b).
Proof.
  intros.
  unfold val_eq in *.
  repeat break_match_hyp; try inv_false; subst; simpl;
  intros; try congruence;
  try destruct y; try destruct b; subst; simpl; try congruence.
Qed.

Lemma val_eq_nextinstr :
  forall rs rs' p,
    val_eq (rs p) (rs' p) ->
    val_eq (nextinstr rs p) (nextinstr rs' p).
Proof.
  intros. unfold val_eq in *.
  break_match_hyp; eauto;
  unfold nextinstr;
  try inv_false;
  preg_case; preg_simpl;
  find_rewrite; simpl; eauto;
  try find_rewrite;
  try rewrite <- H; simpl; try congruence.
  destruct (rs' PC); 
  simpl; congruence.
Qed.

Definition flags : list preg :=
  (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil).

Lemma val_eq_nextinstr_nf :
  forall rs rs' p,
    (~ In p flags -> val_eq (rs p) (rs' p)) ->
    val_eq (nextinstr_nf rs p) (nextinstr_nf rs' p).
Proof.
  intros.
  unfold nextinstr_nf.
  eapply val_eq_nextinstr.
  simpl.
  do 5 (eapply val_eq_update; simpl; eauto; intros; try congruence).
  eapply H. intro. simpl in H5.
  repeat break_or; congruence.
Qed.

Ltac val_eq_op :=
  intros; unfold val_eq in *;
  match goal with
    | [ |- match ?X _ _ with _ => _ end ] =>
      unfold X
    | [ |- match ?X _ with _ => _ end ] =>
      unfold X
  end;
  repeat break_match_hyp;
    subst; eauto;
    try inv_false;
  intros; repeat break_match;
  subst; simpl;
  try congruence.


Lemma val_eq_zero_ext :
  forall v v',
    val_eq v v' ->
    forall n,
      val_eq (Val.zero_ext n v) (Val.zero_ext n v').
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_zero_ext.

Lemma val_eq_sign_ext :
  forall v v',
    val_eq v v' ->
    forall n,
      val_eq (Val.sign_ext n v) (Val.sign_ext n v').
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_sign_ext.


Lemma val_eq_singleoffloat :
  forall v v',
    val_eq v v' ->
      val_eq (Val.singleoffloat v) (Val.singleoffloat v').
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_singleoffloat.


Lemma val_eq_floatofsingle :
  forall v v',
    val_eq v v' ->
      val_eq (Val.floatofsingle v) (Val.floatofsingle v').
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_floatofsingle.


Lemma val_eq_mul :
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    val_eq (Val.mul a x) (Val.mul b y).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_mul.


Lemma val_eq_sub :
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    val_eq (Val.sub a x) (Val.sub b y).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_sub.


Lemma val_eq_neg :
  forall a b,
    val_eq a b ->
    val_eq (Val.neg a) (Val.neg b).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_neg.

Lemma val_eq_mulhu :
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    val_eq (Val.mulhu a x) (Val.mulhu b y).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_mulhu.


Lemma val_eq_mulhs :
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    val_eq (Val.mulhs a x) (Val.mulhs b y).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_mulhs.


Lemma val_eq_and :
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    val_eq (Val.and a x) (Val.and b y).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_and.


Lemma val_eq_vor :
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    val_eq (Val.or a x) (Val.or b y).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_vor.


Lemma val_eq_xor :
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    val_eq (Val.xor a x) (Val.xor b y).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_xor.

Lemma val_eq_notint :
  forall a b,
    val_eq a b ->
    val_eq (Val.notint a) (Val.notint b).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_notint.

Lemma val_eq_shl :
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    val_eq (Val.shl a x) (Val.shl b y).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_shl.

Lemma val_eq_shr :
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    val_eq (Val.shr a x) (Val.shr b y).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_shr.

Lemma val_eq_shru :
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    val_eq (Val.shru a x) (Val.shru b y).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_shru.

Lemma val_eq_ror :
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    val_eq (Val.ror a x) (Val.ror b y).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_ror.

Lemma val_eq_negative :
  forall a b,
    val_eq a b ->
    val_eq (Val.negative a) (Val.negative b).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_negative.


Lemma val_eq_sub_overflow :
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    val_eq (Val.sub_overflow a x) (Val.sub_overflow b y).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_sub_overflow.


Lemma val_eq_addf :
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    val_eq (Val.addf a x) (Val.addf b y).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_addf.


Lemma val_eq_subf :
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    val_eq (Val.subf a x) (Val.subf b y).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_subf.


Lemma val_eq_mulf :
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    val_eq (Val.mulf a x) (Val.mulf b y).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_mulf.


Lemma val_eq_divf :
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    val_eq (Val.divf a x) (Val.divf b y).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_divf.

Lemma val_eq_negf :
  forall a b,
    val_eq a b ->
    val_eq (Val.negf a) (Val.negf b).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_negf.

Lemma val_eq_absf :
  forall a b,
    val_eq a b ->
    val_eq (Val.absf a) (Val.absf b).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_absf.

Lemma val_eq_addfs :
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    val_eq (Val.addfs a x) (Val.addfs b y).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_addfs.

Lemma val_eq_subfs :
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    val_eq (Val.subfs a x) (Val.subfs b y).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_subfs.

Lemma val_eq_mulfs :
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    val_eq (Val.mulfs a x) (Val.mulfs b y).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_mulfs.

Lemma val_eq_divfs :
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    val_eq (Val.divfs a x) (Val.divfs b y).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_divfs.

Lemma val_eq_negfs :
  forall a b,
    val_eq a b ->
    val_eq (Val.negfs a) (Val.negfs b).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_negfs.

Lemma val_eq_absfs :
  forall a b,
    val_eq a b ->
    val_eq (Val.absfs a) (Val.absfs b).
Proof.
  val_eq_op.
Qed.

Hint Resolve val_eq_absfs.

Lemma val_eq_modu:
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    forall v v',
      Val.modu a x = Some v ->
      Val.modu b y = Some v' ->
      val_eq v v'.
Proof.
  intros.
  unfold val_eq in *.
  repeat break_match_hyp; subst;
  unfold Val.modu in *;
  simpl in *;
  repeat break_match_hyp;
  opt_inv.
  inv H1. reflexivity.
Qed.

Lemma val_eq_mods:
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    forall v v',
      Val.mods a x = Some v ->
      Val.mods b y = Some v' ->
      val_eq v v'.
Proof.
  intros.
  unfold val_eq in *.
  repeat break_match_hyp; subst;
  unfold Val.mods in *;
  simpl in *;
  repeat break_match_hyp;
  opt_inv.
  inv H1. reflexivity.
Qed.

Lemma val_eq_divs:
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    forall v v',
      Val.divs a x = Some v ->
      Val.divs b y = Some v' ->
      val_eq v v'.
Proof.
  intros.
  unfold val_eq in *.
  repeat break_match_hyp; subst;
  unfold Val.divs in *;
  simpl in *;
  repeat break_match_hyp;
  opt_inv.
  inv H1. reflexivity.
Qed.

Lemma val_eq_divu:
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    forall v v',
      Val.divu a x = Some v ->
      Val.divu b y = Some v' ->
      val_eq v v'.
Proof.
  intros.
  unfold val_eq in *.
  repeat break_match_hyp; subst;
  unfold Val.divu in *;
  simpl in *;
  repeat break_match_hyp;
  opt_inv.
  inv H1. reflexivity.
Qed.

Lemma val_eq_intoffloat:
  forall v v',
    val_eq v v' ->
    val_eq (Val.maketotal (Val.intoffloat v))
           (Val.maketotal (Val.intoffloat v')).
Proof.
  intros. unfold val_eq in *.
  repeat break_match_hyp; subst; simpl;
  repeat break_match; eauto;
  intros; try congruence;
  try solve [unfold option_map in *;
              break_match_hyp;
              simpl in *;
              try congruence];
  repeat match goal with
           | [ |- ?X _ <> _ ] => unfold X
           | [ |- context[match ?X _ with _ => _ end] ] => unfold X
         end;
    repeat break_match;
    unfold option_map in *;
    repeat break_match_hyp;
    try congruence.
Qed.

Lemma val_eq_floatofint:
  forall v v',
    val_eq v v' ->
    val_eq (Val.maketotal (Val.floatofint v))
           (Val.maketotal (Val.floatofint v')).
Proof.
  intros. unfold val_eq in *.
  repeat break_match_hyp; subst; simpl;
  repeat break_match; eauto;
  intros; try congruence;
  try solve [unfold option_map in *;
              break_match_hyp;
              simpl in *;
              try congruence];
  repeat match goal with
           | [ |- ?X _ <> _ ] => unfold X
           | [ |- context[match ?X _ with _ => _ end] ] => unfold X
         end;
    repeat break_match;
    unfold option_map in *;
    repeat break_match_hyp;
    try congruence.
Qed.

Lemma val_eq_singleofint:
  forall v v',
    val_eq v v' ->
    val_eq (Val.maketotal (Val.singleofint v))
           (Val.maketotal (Val.singleofint v')).
Proof.
  intros. unfold val_eq in *.
  repeat break_match_hyp; subst; simpl;
  repeat break_match; eauto;
  intros; try congruence;
  try solve [unfold option_map in *;
              break_match_hyp;
              simpl in *;
              try congruence];
  repeat match goal with
           | [ |- ?X _ <> _ ] => unfold X
           | [ |- context[match ?X _ with _ => _ end] ] => unfold X
         end;
    repeat break_match;
    unfold option_map in *;
    repeat break_match_hyp;
    try congruence.
Qed.

Lemma val_eq_intofsingle:
  forall v v',
    val_eq v v' ->
    val_eq (Val.maketotal (Val.intofsingle v))
           (Val.maketotal (Val.intofsingle v')).
Proof.
  intros. unfold val_eq in *.
  repeat break_match_hyp; subst; simpl;
  repeat break_match; eauto;
  intros; try congruence;
  try solve [unfold option_map in *;
              break_match_hyp;
              simpl in *;
              try congruence];
  repeat match goal with
           | [ |- ?X _ <> _ ] => unfold X
           | [ |- context[match ?X _ with _ => _ end] ] => unfold X
         end;
    repeat break_match;
    unfold option_map in *;
    repeat break_match_hyp;
    try congruence.
Qed.

Lemma val_eq_compare_floats :
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    forall f rs rs',
      In f flags ->
      val_eq (compare_floats a x rs f)
             (compare_floats b y rs' f).
Proof.
  intros.
  unfold flags in *; simpl in *; repeat break_or; try inv_false; subst;
  preg_simpl; repeat break_match; preg_simpl; simpl; eauto; intros; try congruence;
  unfold Val.of_bool; break_match; unfold Vtrue; unfold Vfalse;
  try break_match; simpl;
  try congruence.

Qed.

Lemma val_eq_compare_floats32 :
  forall a b x y,
    val_eq a b ->
    val_eq x y ->
    forall f rs rs',
      In f flags ->
      val_eq (compare_floats32 a x rs f)
             (compare_floats32 b y rs' f).
Proof.
  intros.
  unfold flags in *; simpl in *; repeat break_or; try inv_false; subst;
  preg_simpl; repeat break_match; preg_simpl; simpl; eauto; intros; try congruence;
  unfold Val.of_bool; break_match; unfold Vtrue; unfold Vfalse;
  try break_match; simpl;
  try congruence.
Qed.

