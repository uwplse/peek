Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Import Stacklayout.
Require Import Conventions.
Require Import Memory.
Require Import Asm.

Require Import PeekLib.
Require Import PeekTactics.
Require Import FindInstrLib.
Require Import PregTactics.

Require Import AsmBits.
Require Import MemoryAxioms.


Definition ptr_equiv_val (md : allocator_metadata) (v v' : val) : Prop :=
  match v with
    | Vptr b i =>
      exists bits,
        v' = Vint bits /\
        pinj md b i = Some bits
    | Vundef => v' = Vundef \/
                (exists i, v' = Vint i) \/
                (exists f, v' = Vfloat f) \/
                (exists s, v' = Vsingle s) \/
                (exists l, v' = Vlong l)
    | _ => v = v'
  end.

Definition ptr_equiv_rs (md : allocator_metadata) (rs rs' : regset) : Prop :=
  forall r,
    ptr_equiv_val md (rs r) (rs' r).

Ltac preg_unfold :=
  try unfold nextinstr_nf;
  try unfold nextinstr;
  try unfold undef_regs;
  try unfold set_regs.

Ltac preg_unfold_hyp H :=
  try unfold nextinstr_nf in H;
  try unfold nextinstr in H;
  try unfold undef_regs in H;
  try unfold set_regs in H.

Ltac preg_simpl_one_step_hyp H :=
  preg_unfold_hyp H;
  try rewrite Pregmap.gss in H;
  try rewrite Pregmap.gso in H by (try apply PC_neq; try apply PC_neq_crbit; try congruence; auto).

Ltac preg_simpl_hyp H :=
  repeat preg_simpl_one_step_hyp H.

Ltac preg_simpl_one_step :=
  preg_unfold;
  try rewrite Pregmap.gss;
  try rewrite Pregmap.gso by (try apply PC_neq; try apply PC_neq_crbit; try congruence; auto).

Ltac preg_simpl :=
  repeat preg_simpl_one_step; try symmetry; repeat preg_simpl_one_step; try symmetry.

Ltac preg_case :=
  match goal with
    | [ |- context[ (_ # ?X <- _) ?Y ]] => destruct (preg_eq X Y); try subst; preg_simpl
  end.

Ltac preg_omega H :=
  repeat (preg_case; try (simpl; rewrite H; simpl; solve [reflexivity | congruence])).

Lemma add_second_first :
  forall a b c,
    Int.add a (Int.add b c) = Int.add b (Int.add a c).
Proof.
  intros.
  rewrite Int.add_commut. rewrite Int.add_assoc. f_equal.
  apply Int.add_commut.
Qed.


Lemma ptr_equiv_update :
  forall md rs rs' v v',
    ptr_equiv_rs md rs rs' ->
    ptr_equiv_val md v v' ->
    forall r,
      ptr_equiv_rs md (rs # r <- v) (rs' # r <- v').
Proof.
  intros. unfold ptr_equiv_rs.
  intro. preg_case. auto.
  unfold ptr_equiv_rs in H. apply H.
Qed.

Lemma ptr_equiv_nonpointers :
  forall v,
    (forall b i, v <> Vptr b i) ->
    forall md,
      ptr_equiv_val md v v.
Proof.
  intros. unfold ptr_equiv_val.
  break_match; try solve [left; reflexivity];
  try reflexivity.
  specialize (H b i). congruence.
Qed.

Lemma ptr_equiv_self :
  forall md rs rs',
    ptr_equiv_rs md rs rs' ->
    forall r,
      ptr_equiv_val md (rs r) (rs' r).
Proof.
  intros. unfold ptr_equiv_rs in H.
  apply H.
Qed.

Lemma ptr_equiv_undef_self :
  forall md rs rs',
    ptr_equiv_rs md rs rs' ->
    forall r,
      ptr_equiv_val md Vundef (rs' r).
Proof.
  intros.
  unfold ptr_equiv_val.
  unfold ptr_equiv_rs in H. specialize (H r).
  destruct (rs r) eqn:?; simpl in H;
    repeat break_exists; repeat break_and;
    try solve [eauto];
    try solve [left; eauto];
    try solve [right; left; eauto];
    try solve [right; right; left; eauto];
    try solve [right; right; right; left; eauto];
    try solve [right; right; right; right; eauto].
Qed.

Lemma ptr_equiv_undef_int :
  forall md i,
    ptr_equiv_val md Vundef (Vint i).
Proof.
  intros. unfold ptr_equiv_val.
  right. eauto.
Qed.

Lemma ptr_equiv_undef_long :
  forall md i,
    ptr_equiv_val md Vundef (Vlong i).
Proof.
  intros. unfold ptr_equiv_val.
  right. eauto.
Qed.

Lemma ptr_equiv_undef_single :
  forall md i,
    ptr_equiv_val md Vundef (Vsingle i).
Proof.
  intros. unfold ptr_equiv_val.
  right. eauto.
Qed.

Lemma ptr_equiv_undef_float :
  forall md i,
    ptr_equiv_val md Vundef (Vfloat i).
Proof.
  intros. unfold ptr_equiv_val.
  right. eauto.
Qed.

Lemma ptr_equiv_bits :
  forall md b i bits,
    pinj md b i = Some bits ->
    ptr_equiv_val md (Vptr b i) (Vint bits).
Proof.
  intros. unfold ptr_equiv_val.
  eexists; split; try reflexivity.
  eauto.
Qed.

Definition ptr_equiv_binop (op : val -> val -> val) : Prop :=
  forall md a b x y,
    ptr_equiv_val md a x ->
    ptr_equiv_val md b y ->
    ptr_equiv_val md (op a b) (op x y).

Lemma ptr_equiv_update_binop :
  forall md rs rs',
    ptr_equiv_rs md rs rs' ->
    forall a b x y op,
      ptr_equiv_val md a x ->
      ptr_equiv_val md b y ->
      ptr_equiv_binop op ->
      forall r,
        ptr_equiv_rs md (rs # r <- (op a b)) (rs' # r <- (op x y)).
Proof.
  intros. apply ptr_equiv_update. assumption.
  unfold ptr_equiv_binop in H2. apply H2; assumption.
Qed.

Lemma ptr_equiv_add :
  ptr_equiv_binop (Val.add).
Proof.
  unfold ptr_equiv_binop. intros.
  unfold ptr_equiv_val. unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto].
  reflexivity.
  eexists. split. reflexivity.
  app pinj_add H1.
  symmetry. rewrite Int.add_commut. symmetry. eauto.
  eexists; split; try reflexivity.
  eapply pinj_add; eauto.
Qed.

Lemma ptr_equiv_sub :
  ptr_equiv_binop (Val.sub).
Proof.
  unfold ptr_equiv_binop. intros.
  unfold ptr_equiv_val. unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and;
  repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto].
  reflexivity.
  eexists. split. reflexivity.
  apply pinj_sub; assumption.
  destruct (eq_block b0 b1) eqn:?.
  subst. f_equal.
  eapply pinj_sub_ptr_diff; eassumption.
  right. eauto.
Qed.

Lemma ptr_equiv_mul :
  ptr_equiv_binop (Val.mul).
Proof.
  unfold ptr_equiv_binop. intros.
  unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and;
  repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto].
  reflexivity.
Qed.

Lemma ptr_equiv_longofwords :
  ptr_equiv_binop (Val.longofwords).
Proof.
  unfold ptr_equiv_binop. intros.
  unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and;
  repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto].
  reflexivity.
Qed.
  

Lemma ptr_equiv_mulhs :
  ptr_equiv_binop Val.mulhs.
Proof.
  unfold ptr_equiv_binop. intros.
  unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and;
  repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto].
  reflexivity.
Qed.

Lemma ptr_equiv_mulhu :
  ptr_equiv_binop Val.mulhu.
Proof.
  unfold ptr_equiv_binop. intros.
  unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and;
  repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto].
  reflexivity.
Qed.

Lemma ptr_equiv_and :
  ptr_equiv_binop Val.and.
Proof.
    unfold ptr_equiv_binop. intros.
  unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and;
  repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto].
  reflexivity.
Qed.

Lemma ptr_equiv_or :
  ptr_equiv_binop Val.or.
Proof.
  unfold ptr_equiv_binop. intros.
  unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and;
  repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto].
  reflexivity.
Qed.

Lemma ptr_equiv_xor :
  ptr_equiv_binop Val.xor.
Proof.
  unfold ptr_equiv_binop. intros.
  unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and;
  repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto].
  reflexivity.
Qed.

Lemma ptr_equiv_shl :
  ptr_equiv_binop Val.shl.
Proof.
  unfold ptr_equiv_binop. intros.
  unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and;
  repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  try break_match;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto];
  try reflexivity;
  simpl in *; try congruence;
  try solve [
        break_match;
        try solve [left; reflexivity];
        solve [right; eauto]].
  break_match_hyp; congruence.
Qed.

Lemma ptr_equiv_shru :
  ptr_equiv_binop Val.shru.
Proof.
  unfold ptr_equiv_binop. intros.
  unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and;
  repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  try break_match;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto];
  try reflexivity;
  simpl in *; try congruence;
  try solve [
        break_match;
        try solve [left; reflexivity];
        solve [right; eauto]].
  break_match_hyp; congruence.
Qed.

Lemma ptr_equiv_shr :
  ptr_equiv_binop Val.shr.
Proof.
  unfold ptr_equiv_binop. intros.
  unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and;
  repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  try break_match;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto];
  try reflexivity;
  simpl in *; try congruence;
  try solve [
        break_match;
        try solve [left; reflexivity];
        solve [right; eauto]].
  break_match_hyp; congruence.
Qed.

Lemma ptr_equiv_ror :
  ptr_equiv_binop Val.ror.
Proof.
  unfold ptr_equiv_binop. intros.
  unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and;
  repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  try break_match;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto];
  try reflexivity;
  simpl in *; try congruence;
  try solve [
        break_match;
        try solve [left; reflexivity];
        solve [right; eauto]].
  break_match_hyp; congruence.
Qed.
  
Lemma ptr_equiv_nextinstr :
  forall t rs rs',
    ptr_equiv_rs t rs rs' ->
    ptr_equiv_rs t (nextinstr rs) (nextinstr rs').
Proof.
  intros. unfold nextinstr.
  apply ptr_equiv_update_binop.
  assumption.
  apply ptr_equiv_self; assumption.
  apply ptr_equiv_nonpointers; intros; discriminate.
  apply ptr_equiv_add.
Qed.

Lemma ptr_equiv_nextinstr_nf :
  forall t rs rs',
    ptr_equiv_rs t rs rs' ->
    ptr_equiv_rs t (nextinstr_nf rs) (nextinstr_nf rs').
Proof.
  intros. unfold nextinstr_nf.
  simpl. apply ptr_equiv_nextinstr.
  repeat apply ptr_equiv_update; try assumption;
  apply ptr_equiv_nonpointers; intros; discriminate.
Qed.

Definition ptr_equiv_unop (op : val -> val) : Prop :=
  forall t v v',
    ptr_equiv_val t v v' ->
    ptr_equiv_val t (op v) (op v').

Lemma ptr_equiv_update_unop :
  forall t rs rs',
    ptr_equiv_rs t rs rs' ->
    forall a x op,
      ptr_equiv_val t a x ->
      ptr_equiv_unop op ->
      forall r,
        ptr_equiv_rs t (rs # r <- (op a)) (rs' # r <- (op x)).
Proof.
  intros. apply ptr_equiv_update; try assumption.
  unfold ptr_equiv_unop in H1. apply H1; assumption.
Qed.

Lemma ptr_equiv_neg :
  ptr_equiv_unop (Val.neg).
Proof.
  unfold ptr_equiv_unop. intros.
  unfold ptr_equiv_val in *.
  destruct v eqn:?;
    repeat break_or; repeat break_exists; repeat break_and;
    repeat break_or; repeat break_exists; repeat break_and;
  repeat break_and; repeat break_or; repeat break_exists;
    simpl; subst; simpl;
    try solve [left; reflexivity];
    try solve [right; eauto];
    reflexivity.
Qed.

Lemma ptr_equiv_not :
  ptr_equiv_unop (Val.notint).
Proof.
  unfold ptr_equiv_unop. intros.
  unfold ptr_equiv_val in *.
  destruct v eqn:?; 
    repeat break_or; repeat break_exists; repeat break_and;
    repeat break_or; repeat break_exists; repeat break_and;
  repeat break_and; repeat break_or; repeat break_exists;
    simpl; subst; simpl;
    try solve [left; reflexivity];
    try solve [right; eauto];
    reflexivity.
Qed.

Lemma undef_regs_not_in:
  forall (l : list preg) (p : preg) (rs : regset),
    ~ In p l -> undef_regs l rs p = rs p.
Proof.
  induction l; intros.
  * simpl. reflexivity.
  * simpl. simpl in H. 
    assert (a <> p) by tauto.
    rewrite IHl by tauto.
    rewrite Pregmap.gso by auto.
    reflexivity.
Qed.

Lemma undef_regs_in:
  forall (p : preg) (r : list preg) (rs : regset),
    In p r ->
    undef_regs r rs p = Vundef.
Proof.
  induction r; intros.
  * simpl in H. inversion H.
  * simpl in H. destruct H. subst.
    simpl. destruct (in_dec preg_eq p r).
    rewrite IHr; auto.
    rewrite undef_regs_not_in; auto.
    rewrite Pregmap.gss. reflexivity.
    simpl. rewrite IHr; auto.
Qed.

Lemma ptr_equiv_undef_regs :
  forall t rs rs',
    ptr_equiv_rs t rs rs' ->
    forall l,
      ptr_equiv_rs t (undef_regs l rs) (undef_regs l rs').
Proof.
  unfold ptr_equiv_rs in *. intros.
  unfold ptr_equiv_val.
  destruct (in_dec preg_eq r l).
  * rewrite undef_regs_in; auto.
    rewrite undef_regs_in; auto.
  * rewrite undef_regs_not_in; auto.
    rewrite undef_regs_not_in; auto.
    unfold ptr_equiv_val in H. apply H.
Qed.

Lemma ptr_equiv_init_undef :
  forall t,
    ptr_equiv_rs t (Pregmap.init Vundef) (Pregmap.init Vundef).
Proof.
  unfold ptr_equiv_rs. intros.
  unfold ptr_equiv_val.
  rewrite Pregmap.gi.
  left. reflexivity.
Qed.

Ltac pinj_add :=
  first [apply pinj_add | rewrite Int.add_commut; apply pinj_add].

Lemma ptr_equiv_zext :
  forall x,
    ptr_equiv_unop (Val.zero_ext x).
Proof.
  unfold ptr_equiv_unop. intros.
  unfold Val.zero_ext.
  unfold ptr_equiv_val in H.
  break_match_hyp;
    repeat break_or; repeat break_exists; repeat break_and;
    repeat break_or; repeat break_exists; repeat break_and;
  repeat break_and; repeat break_or; repeat break_exists;
    subst; try solve [left; reflexivity];
    try apply ptr_equiv_undef_int.
  apply ptr_equiv_nonpointers. intros. congruence.
Qed.

Lemma ptr_equiv_sext :
  forall x,
    ptr_equiv_unop (Val.sign_ext x).
Proof.
  unfold ptr_equiv_unop.
  intros. unfold Val.sign_ext.
  unfold ptr_equiv_val in H.
  break_match_hyp;
    repeat break_or; repeat break_exists; repeat break_and;
    repeat break_or; repeat break_exists; repeat break_and;
  repeat break_and; repeat break_or; repeat break_exists;
    subst; try solve [left; reflexivity];
    try apply ptr_equiv_undef_int.
  apply ptr_equiv_nonpointers. intros. congruence.
Qed.

Lemma ptr_equiv_intoffloat :
  forall t v v',
    ptr_equiv_val t v v' ->
    ptr_equiv_val t (Val.maketotal (Val.intoffloat v)) (Val.maketotal (Val.intoffloat v')).
Proof.
  intros. unfold ptr_equiv_val in *.
  unfold Val.maketotal. unfold Val.intoffloat.
  break_match_hyp;
    repeat break_or;
    repeat break_exists;
    repeat break_and;
    repeat break_or; repeat break_exists; repeat break_and;
  repeat break_and; repeat break_or; repeat break_exists;
    subst;
    try solve [left; reflexivity].
  break_match; try reflexivity;
  try solve [left; reflexivity].
  unfold option_map in Heqo. break_match_hyp; inv Heqo.
  right. left. eauto.
  repeat break_match;
    try reflexivity;
    try solve [left; reflexivity].
  unfold option_map in Heqo.
  subst. break_match_hyp; try congruence.
  congruence.
Qed.

Lemma ptr_equiv_floatofint :
  forall t v v',
    ptr_equiv_val t v v' ->
    ptr_equiv_val t (Val.maketotal (Val.floatofint v)) (Val.maketotal (Val.floatofint v')).
Proof.
  intros. unfold ptr_equiv_val in *.
  unfold Val.maketotal. unfold Val.floatofint.
  break_match_hyp;
    repeat break_or;
    repeat break_exists;
    repeat break_and;
  repeat break_and; repeat break_or; repeat break_exists;
    subst;
    try solve [left; reflexivity];
    try reflexivity.
  right. right. eauto.
  right. right. eauto.
Qed.

Lemma ptr_equiv_intofsingle :
  forall t v v',
    ptr_equiv_val t v v' ->
    ptr_equiv_val t (Val.maketotal (Val.intofsingle v)) (Val.maketotal (Val.intofsingle v')).
Proof.
  intros. unfold ptr_equiv_val in *.
  unfold Val.maketotal. unfold Val.intofsingle.
  break_match_hyp;
    repeat break_or;
    repeat break_exists;
    repeat break_and;
    repeat break_or; repeat break_exists; repeat break_and;
  repeat break_and; repeat break_or; repeat break_exists;
    subst;
    try solve [left; reflexivity].
  break_match; try reflexivity;
  try solve [left; reflexivity]. 
  unfold option_map in Heqo. break_match_hyp; subst;
                             inv Heqo.
  right. left. eauto.
  repeat break_match;
    try reflexivity;
    try solve [left; reflexivity];
    simpl.
  unfold option_map in Heqo. break_match_hyp; subst;
                             inv Heqo.
  congruence.
Qed.

Lemma ptr_equiv_singleofint :
  forall t v v',
    ptr_equiv_val t v v' ->
    ptr_equiv_val t (Val.maketotal (Val.singleofint v)) (Val.maketotal (Val.singleofint v')).
Proof.
  intros. unfold ptr_equiv_val in *.
  unfold Val.maketotal. unfold Val.singleofint.
  break_match_hyp;
    repeat break_or;
    repeat break_exists;
    repeat break_and;
    repeat break_or; repeat break_exists; repeat break_and;
    subst;
    try solve [left; reflexivity];
    try reflexivity;
    try solve [right; right; eauto].
Qed.

Lemma ptr_equiv_floatofsingle :
  ptr_equiv_unop (Val.floatofsingle).
Proof.
  unfold ptr_equiv_unop. intros.
  unfold ptr_equiv_val in *.
  unfold Val.floatofsingle.
  repeat break_match;
    try solve [left; reflexivity];
    try solve [right; left; eauto];
    try solve [right; right; left; eauto];
    try solve [right; right; right; eauto];
  congruence.
Qed.

Lemma ptr_equiv_singleoffloat :
  ptr_equiv_unop (Val.singleoffloat).
Proof.
  unfold ptr_equiv_unop. intros.
  unfold ptr_equiv_val in *.
  unfold Val.singleoffloat.
  repeat break_match;
    try solve [left; reflexivity];
    try solve [right; left; eauto];
    try solve [right; right; left; eauto];
    try solve [right; right; right; eauto];
  congruence.
Qed.

Definition ptr_equiv_list (t : allocator_metadata) (l1 l2 : list val) : Prop :=
  list_forall2 (ptr_equiv_val t) l1 l2.

Lemma ptr_equiv_decode_longs :
  forall t sg vargs vargs',
    ptr_equiv_list t vargs vargs' ->
    ptr_equiv_list t (decode_longs sg vargs) (decode_longs sg vargs').
Proof.
  induction sg; intros; unfold ptr_equiv_list in *.
  * econstructor.
  * simpl. repeat break_match; try solve [econstructor; eauto];
           try solve [inv H];
           try solve [inv H; econstructor; eauto; try apply IHsg; eauto];
           try solve [subst; inv H; inv H5].
    subst; econstructor; inv H; inv H5; try apply IHsg; auto.
    name ptr_equiv_longofwords pel. unfold ptr_equiv_binop in pel.
    apply pel; auto.
Qed.

Lemma ptr_equiv_hiword :
  ptr_equiv_unop (Val.hiword).
Proof.
  unfold ptr_equiv_unop. intros.
  unfold ptr_equiv_val in *.
  unfold Val.hiword.
  repeat break_match;
    try solve [left; reflexivity];
    try solve [right; left; eauto];
    try solve [right; right; left; eauto];
    try solve [right; right; right; eauto];
    congruence.
Qed.
  
Lemma ptr_equiv_loword :
  ptr_equiv_unop (Val.loword).
Proof.
  unfold ptr_equiv_unop. intros.
  unfold ptr_equiv_val in *.
  unfold Val.loword.
  repeat break_match;
    try solve [left; reflexivity];
    try solve [right; left; eauto];
    try solve [right; right; left; eauto];
    try solve [right; right; right; eauto];
    congruence.
Qed.

Lemma ptr_equiv_encode_long :
  forall t ot v v',
    ptr_equiv_val t v v' ->
    ptr_equiv_list t (encode_long ot v) (encode_long ot v').
Proof.
  intros.
  destruct ot; try destruct t0; simpl;
  unfold ptr_equiv_list;
  repeat econstructor; eauto;
  try apply ptr_equiv_hiword;
  try apply ptr_equiv_loword;
  auto.
Qed.

Lemma ptr_equiv_addf :
  ptr_equiv_binop Val.addf.
Proof.
  unfold ptr_equiv_binop. intros.
  unfold ptr_equiv_val. unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto]. 
  reflexivity.
Qed.

Lemma ptr_equiv_subf :
  ptr_equiv_binop Val.subf.
Proof.
  unfold ptr_equiv_binop. intros.
  unfold ptr_equiv_val. unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto]. 
  reflexivity.
Qed.

Lemma ptr_equiv_mulf :
  ptr_equiv_binop Val.mulf.
Proof.
  unfold ptr_equiv_binop. intros.
  unfold ptr_equiv_val. unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto]. 
  reflexivity.
Qed.

Lemma ptr_equiv_divf :
  ptr_equiv_binop Val.divf.
Proof.
  unfold ptr_equiv_binop. intros.
  unfold ptr_equiv_val. unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto]. 
  reflexivity.
Qed.

Lemma ptr_equiv_negf :
  ptr_equiv_unop Val.negf.
Proof.
  unfold ptr_equiv_unop. intros.
  unfold ptr_equiv_val. unfold ptr_equiv_val in *.
  destruct v eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto]. 
  reflexivity.
Qed.

Lemma ptr_equiv_absf :
  ptr_equiv_unop Val.absf.
Proof.
  unfold ptr_equiv_unop. intros.
  unfold ptr_equiv_val. unfold ptr_equiv_val in *.
  destruct v eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto]. 
  reflexivity.
Qed.

Lemma ptr_equiv_addfs :
  ptr_equiv_binop Val.addfs.
Proof.
  unfold ptr_equiv_binop. intros.
  unfold ptr_equiv_val. unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto]. 
  reflexivity.
Qed.

Lemma ptr_equiv_subfs :
  ptr_equiv_binop Val.subfs.
Proof.
  unfold ptr_equiv_binop. intros.
  unfold ptr_equiv_val. unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto]. 
  reflexivity.
Qed.

Lemma ptr_equiv_mulfs :
  ptr_equiv_binop Val.mulfs.
Proof.
  unfold ptr_equiv_binop. intros.
  unfold ptr_equiv_val. unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto]. 
  reflexivity.
Qed.

Lemma ptr_equiv_divfs :
  ptr_equiv_binop Val.divfs.
Proof.
  unfold ptr_equiv_binop. intros.
  unfold ptr_equiv_val. unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto]. 
  reflexivity.
Qed.

Lemma ptr_equiv_negfs :
  ptr_equiv_unop Val.negfs.
Proof.
  unfold ptr_equiv_unop. intros.
  unfold ptr_equiv_val. unfold ptr_equiv_val in *.
  destruct v eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto]. 
  reflexivity.
Qed.

Lemma ptr_equiv_absfs :
  ptr_equiv_unop Val.absfs.
Proof.
  unfold ptr_equiv_unop. intros.
  unfold ptr_equiv_val. unfold ptr_equiv_val in *.
  destruct v eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto]. 
  reflexivity.
Qed.


Lemma ptr_equiv_negative :
  ptr_equiv_unop Val.negative.
Proof.
  unfold ptr_equiv_unop. intros.
  unfold ptr_equiv_val. unfold ptr_equiv_val in *.
  destruct v eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto]. 
  reflexivity.
Qed.

Lemma ptr_equiv_sub_ovf :
  ptr_equiv_binop Val.sub_overflow.
Proof.
  unfold ptr_equiv_binop. intros.
  unfold ptr_equiv_val. unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto]. 
  reflexivity.
Qed.

Ltac ptr_equiv_conversion :=
  try apply ptr_equiv_intoffloat;
  try apply ptr_equiv_floatofint;
  try apply ptr_equiv_intofsingle;
  try apply ptr_equiv_singleofint.


Ltac ptr_equiv_ops :=
  try apply ptr_equiv_negative;
  try apply ptr_equiv_add;
  try apply ptr_equiv_sub;
  try apply ptr_equiv_mul;
  try apply ptr_equiv_not;
  try apply ptr_equiv_sext;
  try apply ptr_equiv_zext;
  try apply ptr_equiv_floatofsingle;
  try apply ptr_equiv_singleoffloat;
  try apply ptr_equiv_longofwords;
  try apply ptr_equiv_hiword;
  try apply ptr_equiv_loword;
  try apply ptr_equiv_mulhs;
  try apply ptr_equiv_mulhu;
  try apply ptr_equiv_and;
  try apply ptr_equiv_or;
  try apply ptr_equiv_xor;
  try apply ptr_equiv_shl;
  try apply ptr_equiv_shru;
  try apply ptr_equiv_shr;
  try apply ptr_equiv_ror;
  try apply ptr_equiv_addf;
  try apply ptr_equiv_subf;
  try apply ptr_equiv_mulf;
  try apply ptr_equiv_divf;
  try apply ptr_equiv_negf;
  try apply ptr_equiv_absf;
  try apply ptr_equiv_addfs;
  try apply ptr_equiv_subfs;
  try apply ptr_equiv_mulfs;
  try apply ptr_equiv_divfs;
  try apply ptr_equiv_negfs;
  try apply ptr_equiv_absfs;
  try apply ptr_equiv_sub_ovf;
  try apply ptr_equiv_neg.


Lemma ptr_equiv_map_args :
  forall t rs rs',
    ptr_equiv_rs t rs rs' ->
    forall args,
      ptr_equiv_list t (map rs args) (map rs' args).
Proof.
  induction args; intros.
  * econstructor; eauto.
  * econstructor. unfold ptr_equiv_rs in H. apply H.
    unfold ptr_equiv_list in IHargs. apply IHargs.
Qed.

Lemma ptr_equiv_set_regs :
  forall regs t rs rs',
    ptr_equiv_rs t rs rs' ->
    forall vals vals',
      ptr_equiv_list t vals vals' ->
      ptr_equiv_rs t (set_regs regs vals rs) (set_regs regs vals' rs').
Proof.
  induction regs; intros.
  * simpl. assumption.
  * inversion H0. subst. simpl. assumption.
    subst. simpl in *.
    apply IHregs.
    apply ptr_equiv_update. assumption. assumption.
    unfold ptr_equiv_list. assumption.
Qed.

Lemma ptr_equiv_compare_floats :
  forall t rs rs',
    ptr_equiv_rs t rs rs' ->
    forall a b x y,
      ptr_equiv_val t a x ->
      ptr_equiv_val t b y ->
      ptr_equiv_rs t (compare_floats a b rs) (compare_floats x y rs').
Proof.
  intros.
  unfold ptr_equiv_val in H0.
  unfold ptr_equiv_val in H1.
  destruct a eqn:?;
    destruct b eqn:?;
    repeat break_or;
    repeat break_exists;
    repeat break_and;
    subst;
    simpl;
  repeat apply ptr_equiv_update;
  try apply ptr_equiv_self;
  try solve [apply ptr_equiv_nonpointers; (intros; discriminate)];
  try apply ptr_equiv_undef_int;
  try apply ptr_equiv_bits;
  try assumption;
  unfold Val.of_bool;
  break_match;
  unfold Vtrue;
  unfold Vfalse;
  try apply ptr_equiv_undef_int;
  solve [apply ptr_equiv_nonpointers; (intros; discriminate)].
Qed.

Lemma ptr_equiv_compare_floats32 :
  forall t rs rs',
    ptr_equiv_rs t rs rs' ->
    forall a b x y,
      ptr_equiv_val t a x ->
      ptr_equiv_val t b y ->
      ptr_equiv_rs t (compare_floats32 a b rs) (compare_floats32 x y rs').
Proof.
  intros.
  unfold ptr_equiv_val in H0.
  unfold ptr_equiv_val in H1.
  destruct a eqn:?;
    destruct b eqn:?;
    repeat break_or;
    repeat break_exists;
    repeat break_and;
    subst;
    simpl;
  repeat apply ptr_equiv_update;
  try apply ptr_equiv_self;
  try solve [apply ptr_equiv_nonpointers; (intros; discriminate)];
  try apply ptr_equiv_undef_int;
  try apply ptr_equiv_bits;
  try assumption;
  unfold Val.of_bool;
  break_match;
  unfold Vtrue;
  unfold Vfalse;
  try apply ptr_equiv_undef_int;
  solve [apply ptr_equiv_nonpointers; (intros; discriminate)].
Qed.

Lemma ptr_equiv_val_exists :
  forall t rs rs',
    ptr_equiv_rs t rs rs' ->
    forall r v,
      rs r = v ->
      exists v',
        rs' r = v' /\ ptr_equiv_val t v v'.
Proof.
  intros. unfold ptr_equiv_rs in H.
  specialize (H r). exists (rs' r).
  split. reflexivity. subst. assumption.
Qed.

Lemma ptr_equiv_eval_testcond :
  forall t rs rs',
    ptr_equiv_rs t rs rs' ->
    forall c b,
      eval_testcond c rs = Some b ->
      eval_testcond c rs' = Some b.
Proof.
  intros.
  unfold eval_testcond in H0.
  repeat break_match_hyp;
    match goal with
      | [ H : Some _ = None |- _ ] => inv H
      | [ H : None = Some _ |- _ ] => inv H
      | [ |- _ ] => idtac
    end;
    simpl;
    repeat (
        match goal with
          | [ HX : rs _ = _ |- _ ] => eapply ptr_equiv_val_exists in HX; eauto;
          repeat break_exists; repeat break_and
        end;
        unfold ptr_equiv_val in *;
          subst;
        match goal with
          | [ HX : _ = rs' _ |- _ ] => rewrite <- HX
        end;
        try assumption).
Qed.

Lemma ptr_equiv_of_optbool :
  forall t rs rs',
    ptr_equiv_rs t rs rs' ->
    forall c,
      ptr_equiv_val t
        (Val.of_optbool (eval_testcond c rs))
        (Val.of_optbool (eval_testcond c rs')).
Proof.
  intros.
  unfold Val.of_optbool;
  try break_match;
  unfold Vtrue;
  unfold Vfalse;
  try apply ptr_equiv_undef_int;
  try solve [apply ptr_equiv_nonpointers; (intros; discriminate)].
  app ptr_equiv_eval_testcond Heqo. rewrite Heqo.
  destruct b;
  solve [apply ptr_equiv_nonpointers; (intros; discriminate)].
  repeat break_match;
    try apply ptr_equiv_undef_int;
    try solve [apply ptr_equiv_nonpointers; (intros; discriminate)].
Qed.

Lemma ptr_equiv_divu_pres :
  forall t rs rs',
    ptr_equiv_rs t rs rs' ->
    forall a b ans,
      Val.divu a b = Some ans ->
      forall c d,
        ptr_equiv_val t a c ->
        ptr_equiv_val t b d ->
        exists ans',
          Val.divu c d = Some ans' /\ ptr_equiv_val t ans ans'.
Proof.
  intros.
  unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and;
  repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  try break_match;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto];
  try reflexivity;
  simpl in *; try congruence;
  try solve [
        break_match;
        try solve [left; reflexivity];
        solve [right; eauto]];
  try solve [break_match_hyp; congruence].
  break_match_hyp. congruence.
  eauto.
Qed.

Lemma ptr_equiv_divs_pres :
  forall t rs rs',
    ptr_equiv_rs t rs rs' ->
    forall a b ans,
      Val.divs a b = Some ans ->
      forall c d,
        ptr_equiv_val t a c ->
        ptr_equiv_val t b d ->
        exists ans',
          Val.divs c d = Some ans' /\ ptr_equiv_val t ans ans'.
Proof.
  intros.
  unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and;
  repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  try break_match;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto];
  try reflexivity;
  simpl in *; try congruence;
  try solve [
        break_match;
        try solve [left; reflexivity];
        solve [right; eauto]];
  try solve [break_match_hyp; congruence].
  break_match_hyp. congruence.
  eauto.
Qed.

Lemma ptr_equiv_modu_pres :
  forall t rs rs',
    ptr_equiv_rs t rs rs' ->
    forall a b ans,
      Val.modu a b = Some ans ->
      forall c d,
        ptr_equiv_val t a c ->
        ptr_equiv_val t b d ->
        exists ans',
          Val.modu c d = Some ans' /\ ptr_equiv_val t ans ans'.
Proof.
  intros.
  unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and;
  repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  try break_match;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto];
  try reflexivity;
  simpl in *; try congruence;
  try solve [
        break_match;
        try solve [left; reflexivity];
        solve [right; eauto]];
  try solve [break_match_hyp; congruence].
  break_match_hyp. congruence.
  eauto.
Qed.

Lemma ptr_equiv_mods_pres :
  forall t rs rs',
    ptr_equiv_rs t rs rs' ->
    forall a b ans,
      Val.mods a b = Some ans ->
      forall c d,
        ptr_equiv_val t a c ->
        ptr_equiv_val t b d ->
        exists ans',
          Val.mods c d = Some ans' /\ ptr_equiv_val t ans ans'.
Proof.
  intros.
  unfold ptr_equiv_val in *.
  destruct a eqn:?; destruct b eqn:?;
           repeat break_or; repeat break_exists;
  repeat break_and;
  repeat break_or; repeat break_exists;
  repeat break_and; repeat break_or; repeat break_exists;
  try break_match;
  subst; simpl; try solve [left; reflexivity];
  try solve [right; eauto];
  try reflexivity;
  simpl in *; try congruence;
  try solve [
        break_match;
        try solve [left; reflexivity];
        solve [right; eauto]];
  try solve [break_match_hyp; congruence].
  break_match_hyp. congruence.
  eauto.
Qed.


Lemma load_result_val_pres :
  forall c t v v',
    ptr_equiv_val t v v' ->
    ptr_equiv_val t (Val.load_result c v) (Val.load_result c v').
Proof.
  intros. 
  destruct c; simpl; repeat break_match; subst;
  unfold ptr_equiv_val in H; try inversion H; 
  repeat break_exists; repeat break_and; repeat break_or;
  try inv H;
  try solve [apply ptr_equiv_nonpointers; (intros; discriminate)];
  try apply ptr_equiv_undef_int;
  try apply ptr_equiv_undef_float;
  try apply ptr_equiv_undef_single;
  try apply ptr_equiv_undef_long;
  try apply ptr_equiv_bits;
  repeat break_exists;
  try congruence.
  unfold ptr_equiv_val.
  assumption.
Qed.


Lemma ptr_equiv_no_ptr :
  forall t rs rs',
    ptr_equiv_rs t rs rs' ->
    no_ptr_regs rs'.
Proof.
  intros. unfold no_ptr_regs.
  unfold ptr_equiv_rs in H.
  intros. specialize (H x).
  unfold ptr_equiv_val in H.
  break_match_hyp;
    repeat break_or; repeat break_exists;
    repeat break_and; try rewrite H0;
    try discriminate;
    try rewrite H;
    try discriminate;
    try rewrite <- H;
    try discriminate.
Qed.

Lemma ptr_equiv_PC :
  forall t rs rs' b ofs,
    ptr_equiv_rs t rs rs' ->
    rs PC = Vptr b ofs ->
    (exists bits,
       rs' PC = Vint bits /\
       pinj t b ofs = Some bits).
Proof.
  intros. unfold ptr_equiv_rs in H.
  unfold ptr_equiv_val in H.
  specialize (H PC). rewrite H0 in H.
  eauto.
Qed.

Lemma int_eq_true :
  forall x y,
    Int.eq x y = true -> x = y.
Proof.
  intros. name (Int.eq_spec x y) ies.
  rewrite H in ies. auto.
Qed.

Lemma int_eq_false :
  forall x y,
    Int.eq x y = false -> x <> y.
Proof.
  intros. name (Int.eq_spec x y) ies.
  rewrite H in ies. auto.
Qed.

Lemma ptr_equiv_cmpu_ceq :
  forall t m m',
    match_metadata t m ->
    (* match_metadata t m' -> *)
    True ->
    forall a b x y,
      ptr_equiv_val t a x ->
      ptr_equiv_val t b y ->
      ptr_equiv_val t (Val.cmpu (Mem.valid_pointer m) Ceq a b) (Val.cmpu (Mem.valid_pointer m') Ceq x y).
Proof.
  intros.
  unfold ptr_equiv_val in H1.
  unfold ptr_equiv_val in H2.
  destruct a eqn:?; destruct b eqn:?;
  repeat break_or;
    repeat break_exists;
    repeat break_and;

  subst; unfold ptr_equiv_val;
  unfold Val.cmpu; simpl;
  try solve [left; reflexivity];
  try solve [break_match; right; left; unfold Vtrue; unfold Vfalse; eauto];
  try solve [destruct (Int.eq i i0) eqn:?; simpl; reflexivity];
  try solve [
    destruct (eq_block b0 b1) eqn:?;
    destruct ((Mem.valid_pointer m b0 (Int.unsigned i)
            || Mem.valid_pointer m b0 (Int.unsigned i - 1)) &&
           (Mem.valid_pointer m b1 (Int.unsigned i0)
            || Mem.valid_pointer m b1 (Int.unsigned i0 - 1))) eqn:?;
    try destruct (Int.eq i i0) eqn:?; simpl;
    try solve [left; reflexivity];
    subst;
    try solve [break_match; right; left; unfold Vtrue; unfold Vfalse; eauto];
    try destruct (Mem.valid_pointer m b0 (Int.unsigned i) &&
         Mem.valid_pointer m b1 (Int.unsigned i0)) eqn:?; simpl;
    try solve [
        right; left; break_match; unfold Vtrue; unfold Vfalse; eauto
      ];
    break_match;
    match goal with
      | [ H : Int.eq _ _ = true |- _ ] => app int_eq_true H
      | [ |- _ ] => idtac
    end;
    match goal with
      | [ H : Int.eq _ _ = false |- _ ] => app int_eq_false H
      | [ |- _ ] => idtac
    end;
    subst;
    try assert (x1 = x0) by (eapply psur_injective; eauto);
    try congruence].

  destruct (Int.eq i Int.zero) eqn:?;
  destruct (Mem.valid_pointer m b0 (Int.unsigned i0)
     || Mem.valid_pointer m b0 (Int.unsigned i0 - 1)) eqn:?;
  simpl;
  try solve [break_match; right; left; unfold Vtrue; unfold Vfalse; eauto].
  break_match; try reflexivity. 
  app int_eq_true Heqb1. subst.
  app int_eq_true Heqb. subst.

  
  eapply null_always_invalid in H3; try apply H.
  break_and. rewrite H3 in Heqb0. simpl in Heqb0. congruence.

  eapply Int.unsigned_zero.
  
  destruct (Int.eq i0 Int.zero) eqn:?;
  destruct (Mem.valid_pointer m b0 (Int.unsigned i)
     || Mem.valid_pointer m b0 (Int.unsigned i - 1)) eqn:?;
  simpl;
  try solve [break_match; right; left; unfold Vtrue; unfold Vfalse; eauto].
  break_match; try reflexivity.

  app int_eq_true Heqb1. subst.
  app int_eq_true Heqb. subst.

  eapply null_always_invalid in H3; try apply H.
  break_and. rewrite H3 in Heqb0. simpl in *.
  congruence.

  eapply Int.unsigned_zero.
  
  unfold Val.of_optbool.
  destruct (eq_block b0 b1); subst; simpl;
  break_match_sm;
  repeat match goal with
    | [ |- context[Int.eq ?X ?Y] ] => destruct (Int.eq X Y) eqn:?;
                                               unfold Vtrue; unfold Vfalse;
                                      simpl;
                                      try solve [right; left; eauto];
                                          try reflexivity
         end.
  app int_eq_true Heqb0. subst. 
  rewrite H3 in H4. inv H4. rewrite Int.eq_true in Heqb1. congruence.

  app int_eq_true Heqb1. subst.
  eapply pinj_injective_within_block in H3; try eapply H4.
  subst. rewrite Int.eq_true in Heqb0. congruence.

  app int_eq_true Heqb0. subst.
  rewrite andb_true_iff in Heqb. break_and.

  app Mem.valid_pointer_implies H2.
  app Mem.valid_pointer_implies H5.
  name (conj H3 H5) Hb1.
  name (conj H4 H2) Hb0.
  
  erewrite <- weak_valid_pointer_sur in Hb0; eauto.
  erewrite <- weak_valid_pointer_sur in Hb1; eauto.
  congruence.
Qed.

(* Definition mem_injectable (m : mem) := *)
(*   forall b i, *)
(*     (Mem.valid_pointer m b (Int.unsigned i)) *)
(*       || (Mem.valid_pointer m b (Int.unsigned i - 1)) = true -> *)
(*     pinj b i <> None. *)


Lemma ptr_equiv_cmpu_clt :
  forall t m m',
    match_metadata t m ->
    forall a b x y,
      ptr_equiv_val t a x ->
      ptr_equiv_val t b y ->
      ptr_equiv_val t (Val.cmpu (Mem.valid_pointer m) Clt a b) (Val.cmpu (Mem.valid_pointer m') Clt x y).
Proof.
  intros.
  unfold ptr_equiv_val in H0.
  unfold ptr_equiv_val in H1.
  destruct a eqn:?; destruct b eqn:?;
  repeat break_or;
    repeat break_exists;
    repeat break_and;

  subst; unfold ptr_equiv_val;
  unfold Val.cmpu; simpl;
  try solve [left; reflexivity];
  try solve [break_match; right; left; unfold Vtrue; unfold Vfalse; eauto];
  try solve [destruct (Int.ltu i i0) eqn:?; simpl; reflexivity].
  destruct (Int.eq i Int.zero &&
           (Mem.valid_pointer m b0 (Int.unsigned i0)
                              || Mem.valid_pointer m b0 (Int.unsigned i0 - 1)));
  simpl;
  solve [break_match; right; left; unfold Vtrue; unfold Vfalse; eauto].
  destruct (Int.eq i0 Int.zero &&
           (Mem.valid_pointer m b0 (Int.unsigned i)
                              || Mem.valid_pointer m b0 (Int.unsigned i - 1)));
  simpl;
  solve [break_match; right; left; unfold Vtrue; unfold Vfalse; eauto].

  destruct (eq_block b0 b1) eqn:?.
  destruct ((Mem.valid_pointer m b0 (Int.unsigned i)
            || Mem.valid_pointer m b0 (Int.unsigned i - 1)) &&
           (Mem.valid_pointer m b1 (Int.unsigned i0)
            || Mem.valid_pointer m b1 (Int.unsigned i0 - 1))) eqn:?;
  
           simpl;
  try solve [break_match; right; left; unfold Vtrue; unfold Vfalse; eauto].
  rewrite andb_true_iff in Heqb. break_and.
  subst. destruct (Int.ltu i i0) eqn:?.

  
  Focus 3. unfold Val.of_optbool.
  break_match_sm; simpl; right; left;
  break_match; unfold Vtrue; unfold Vfalse; eauto.

  unfold Int.ltu in Heqb. break_match_hyp; try congruence.
  clear Heqs0.
  erewrite psur_comparison in l; try apply H; eauto. simpl.
  unfold Int.ltu. break_match_sm; try omega. reflexivity.

  simpl.

  unfold Int.ltu in Heqb. break_match_hyp; try congruence.
  clear Heqs0. simpl.
  unfold Int.ltu. break_match_sm; try congruence.
  clear Heqs0.
  erewrite <- psur_comparison in l; try apply H; eauto.
  congruence.
Qed.
  
Lemma ptr_equiv_compare_ints :
  forall t rs rs',
    ptr_equiv_rs t rs rs' ->
    forall m m',
      match_metadata t m ->
      forall a b x y,
        ptr_equiv_val t a x ->
        ptr_equiv_val t b y ->
        ptr_equiv_rs t (compare_ints a b rs m) (compare_ints x y rs' m').
Proof.
  intros. unfold compare_ints.
  repeat apply ptr_equiv_update;
    try solve [apply ptr_equiv_nonpointers; (intros; discriminate)];
    try apply ptr_equiv_cmpu_ceq;
    try apply ptr_equiv_cmpu_clt;
    ptr_equiv_ops;
    try assumption.
  eauto.
Qed.

