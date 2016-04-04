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
Require Import Maps.

Require Import AsmBits.
Require Import MemoryAxioms.
Require Import PeekTactics.
Require Import StepLib.
Require Import PregTactics.
Require Import ValEq.

Require Import MemBits.
Require Import NoPtr.

Definition mem_nextblock_same (m m' : mem) : Prop :=
  Mem.nextblock m = Mem.nextblock m'.

Definition mem_perm_same (m m' : mem) : Prop :=
  forall b z k p,
    (Mem.mem_access m) !! b z k = Some p ->
    (Mem.mem_access m') !! b z k = Some p.

Lemma mem_perm_same_imp :
  forall m m',
    mem_perm_same m m' ->
    forall b x k p,
      Mem.perm m b x k p ->
      Mem.perm m' b x k p.
Proof.
  intros. unfold Mem.perm in *.
  unfold Mem.perm_order' in *.
  break_match_hyp; try inv_false.
  app H Heqo. collapse_match. eauto.
Qed.

Definition no_ptr_memval (v : memval) : Prop :=
  match v with
    | Fragment (Vptr _ _) _ _ => False
    | _ => True
  end.

Definition contents_equiv (c c' : PMap.t (ZMap.t memval)) : Prop :=
  forall b ofs,
    match ZMap.get ofs (c !! b) with
      | Undef => no_ptr_memval (ZMap.get ofs (c' !! b))
      | Fragment (Vptr _ _) _ _ => False
      | _ => ZMap.get ofs (c !! b) = ZMap.get ofs (c' !! b)
    end.

Definition mem_contents_equiv (m m' : mem) :=
  contents_equiv (Mem.mem_contents m) (Mem.mem_contents m').

Definition mem_eq (md : allocator_metadata) (m m' : mem) :=
  match_metadata md m /\ match_metadata md m' /\ mem_nextblock_same m m' /\ mem_perm_same m m' /\ mem_contents_equiv m m'.

Lemma perm_same_valid_access :
  forall m m',
    mem_perm_same m m' ->
    forall c b ofs p,
      Mem.valid_access m c b ofs p ->
      Mem.valid_access m' c b ofs p.
Proof.
  intros. unfold mem_perm_same in H.
  unfold Mem.valid_access in *.
  break_and. split; auto.
  unfold Mem.range_perm in *.
  intros. specialize (H0 _ H2).
  eapply mem_perm_same_imp; eauto.
Qed.

Lemma mem_load_exists :
  forall m m',
    mem_perm_same m m' ->
    forall c b z v,
      Mem.load c m b z = Some v ->
      exists v',
        Mem.load c m' b z = Some v'.
Proof.
  intros.
  app Mem.load_valid_access H0.
  app perm_same_valid_access H0.
  app Mem.valid_access_load H0.
Qed.

Ltac rwr_hyp HX :=
  match goal with
    | [ H : ZMap.get ?OFS (_ !! ?B) = _ |- _ ] =>
      copy (HX B OFS);
        rewrite H in *;
        clear H
  end.

Lemma contents_equiv_proj_bytes :
  forall m m',
    mem_contents_equiv m m' ->
    forall c z b l,
      proj_bytes (Mem.getN (size_chunk_nat c) z (Mem.mem_contents m) !! b) = Some l ->
      proj_bytes (Mem.getN (size_chunk_nat c) z (Mem.mem_contents m') !! b) = Some l.
Proof.
  intros. unfold mem_contents_equiv in H.
  unfold contents_equiv in H.
  destruct c; simpl in *;
  repeat (break_match_hyp; try congruence);
  repeat opt_inv; subst;
  repeat (rwr_hyp H; collapse_match);
  reflexivity.
Qed.

Lemma proj_value_length :
  forall q l,
    size_quantity_nat q <> length l ->
    proj_value q l = Vundef.
Proof.
  intros.
  destruct q; simpl in *;
  unfold proj_value;
  simpl in *;

  repeat (simpl in *;
      break_match; try congruence;
            simpl in H; try omega;
            repeat rewrite andb_false_r in *;
              repeat rewrite andb_false_l in *;
              try congruence
           ).
Qed.

Lemma val_eq_refl :
  forall v,
    proj_sumbool (Val.eq v v) = true.
Proof.
  intros. destruct (Val.eq v v); simpl; try congruence.
Qed.

Lemma contents_equiv_proj_value :
  forall m m',
    mem_contents_equiv m m' ->
    forall q c z b v,
      v <> Vundef ->
      proj_value q (Mem.getN (size_chunk_nat c) z (Mem.mem_contents m) !! b) = v ->
      proj_value q (Mem.getN (size_chunk_nat c) z (Mem.mem_contents m') !! b) = v.
Proof.
  intros.
  unfold mem_contents_equiv in H.
  unfold contents_equiv in H.
  destruct q;
    destruct c;
    try solve [
          rewrite proj_value_length in H1; try congruence;
          rewrite Mem.getN_length; simpl; unfold size_chunk_nat; simpl;
          unfold Pos.to_nat; simpl; congruence];
  
    simpl in H1;
    simpl;
  repeat match goal with
           | [ H2 : context[match ZMap.get ?X ?Y with _ => _ end] |- _ ] =>
             destruct (ZMap.get X Y) eqn:?;
                      try rwr_hyp H;
               repeat rewrite andb_false_r in *;
               try congruence
         end;
  repeat match goal with
           | [ H : context[match ?X with _ => _ end] |- _ ] =>
             match type of X with
               | nat =>
                 destruct X;
                   repeat rewrite andb_false_r in *;
                   simpl in *;
                   try congruence
               | _ => fail
             end
         end;
  repeat match goal with
           | [ H : match ?X with
                     | Vundef => ?Y = ?Z
                     | _ => _
                   end |- _ ] =>
             assert (Y = Z) by (destruct X; try inv_false; eauto);
               clear H
         end;
    repeat collapse_match;
    assumption.

Qed.

Lemma proj_bytes_mismatch :
  forall m m',
    mem_contents_equiv m m' ->
    forall l n z b,
      proj_bytes (Mem.getN n z (Mem.mem_contents m) !! b) = None ->
      proj_bytes (Mem.getN n z (Mem.mem_contents m') !! b) = Some l ->
      forall q,
        proj_value q (Mem.getN n z (Mem.mem_contents m) !! b) = Vundef.
Proof.
  intros.
  assert (size_quantity_nat q <> length (Mem.getN n z (Mem.mem_contents m) !! b) \/
          size_quantity_nat q = length (Mem.getN n z (Mem.mem_contents m) !! b)) by omega.
  destruct H2.
  eapply proj_value_length. eauto.
  rewrite Mem.getN_length in H2. subst n.
  unfold mem_contents_equiv in H.
  unfold contents_equiv in H.
  destruct q; unfold size_quantity_nat in *;
  simpl in H0; break_match_hyp; try congruence;
  simpl; try collapse_match; try reflexivity;
  rwr_hyp H; simpl in H1;
  repeat match goal with
           | [ H : match ?X with
                     | Vundef => ?Y = ?Z
                     | _ => _
                   end |- _ ] =>
             assert (Y = Z) by (destruct X; try inv_false; eauto);
               clear H
         end;
  rewrite <- H3 in H1; congruence.
Qed.

Lemma proj_value_no_ptr_l :
  forall q n z c c' b x y,
    contents_equiv c c' ->
    ~ proj_value q (Mem.getN n z (c !! b)) = Vptr x y.
Proof.
  intros.
  unfold proj_value.
  repeat break_match; try congruence.
  unfold contents_equiv in H.
  destruct n; simpl in *; try congruence.
  inv Heql. specialize (H b z).
  rewrite H1 in H.
  break_match_hyp; try congruence; try inv_false.
Qed.

Lemma proj_value_no_ptr_r :
  forall q n z c c' b x y,
    contents_equiv c c' ->
    ~ proj_value q (Mem.getN n z (c' !! b)) = Vptr x y.
Proof.
  intros.
  unfold proj_value.
  repeat break_match; try congruence.
  unfold contents_equiv in H.
  destruct n; simpl in *; try congruence.
  inv Heql. specialize (H b z).
  rewrite H1 in H.
  break_match_hyp; try congruence; try inv_false.
  unfold no_ptr_memval in *.
  break_match; try congruence.
  break_match_hyp; try congruence; try inv_false.
Qed.

Lemma eq_mem_load :
  forall md m m',
    mem_eq md m m' ->
    forall c b z v,
      Mem.load c m b z = Some v ->
      exists v',
        Mem.load c m' b z = Some v' /\
        val_eq v v'.
Proof.
  intros. unfold mem_eq in *.
  repeat break_and.
  unfold mem_perm_same.
  app mem_load_exists H3.
  exists x. split; auto.
  app Mem.load_result H0.
  app Mem.load_result H3.
  subst.
  unfold decode_val.
  break_match.
  app contents_equiv_proj_bytes Heqo.
  collapse_match.
  break_match; simpl; eauto.
  intros. congruence.
  break_match; try solve [simpl; eauto];
  break_match;

  try solve [unfold Val.load_result; break_match;
    try solve [simpl; eauto];
    app contents_equiv_proj_value Heqv;
    try congruence;
    collapse_match; simpl; eauto];
  try solve [unfold val_eq; break_match; eauto;
    app contents_equiv_proj_value Heqv;
    try congruence];
  try solve [simpl; intros; try congruence; eauto];
  
  try solve [erewrite proj_bytes_mismatch; try eassumption;
             try solve [simpl; eauto; intros; try congruence]].

  

  
  unfold Val.load_result; break_match;
  try solve [
        unfold val_eq; intros; try break_match; try congruence;
        try app proj_value_no_ptr_r Heqv0];
  app contents_equiv_proj_value Heqv; try collapse_match;
  try solve [simpl; congruence];
  try app proj_value_no_ptr_r Heqv.


  unfold Val.load_result; break_match;
  try solve [
        unfold val_eq; intros; try break_match; try congruence;
        try app proj_value_no_ptr_r Heqv0];
  app contents_equiv_proj_value Heqv; try collapse_match;
  try solve [simpl; congruence];
  try app proj_value_no_ptr_r Heqv.


  unfold Val.load_result.
  unfold val_eq; break_match;

  try solve [app contents_equiv_proj_value Heqv; try collapse_match;
             try find_rewrite;
             try solve [intros; simpl; congruence]];
  try solve [app proj_value_no_ptr_l Heqv].
  intros. intro. app proj_value_no_ptr_r H0.
Qed.

Lemma store_bits_perm_same :
  forall m m',
    mem_perm_same m m' ->
    forall c b ofs v v' m0,
      store_bits c m b ofs v = Some m0 ->
      exists m'0,
        store_bits c m' b ofs v' = Some m'0 /\ mem_perm_same m0 m'0.
Proof.
  intros.
  unfold mem_perm_same in H.
  unfold store_bits in H0.
  break_match_hyp; try congruence.
  inv H0.
  app perm_same_valid_access v0.
  unfold store_bits.
  break_match.
  eexists. split.
  reflexivity.
  unfold mem_perm_same. intros.
  simpl in *. unfold Mem.perm in *.
  simpl in *. eapply H; eauto.
  congruence.
Qed.

Lemma nextblock_store_bits :
  forall c m b ofs v m',
    store_bits c m b ofs v = Some m' ->
    Mem.nextblock m = Mem.nextblock m'.
Proof.
  intros. unfold store_bits in H.
  break_match_hyp; try congruence.
  inv H. simpl. reflexivity.
Qed.

Lemma mem_store_nextblock :
  forall m m',
    mem_perm_same m m' ->
    mem_nextblock_same m m' ->
    forall c b ofs v v' m0,
      store_bits c m b ofs v = Some m0 ->
      exists m'0,
        store_bits c m' b ofs v' = Some m'0 /\ mem_nextblock_same m0 m'0.
Proof.
  intros.
  app store_bits_perm_same H.
  break_and.
  exists x. split. eassumption.

  app nextblock_store_bits H.
  app nextblock_store_bits H1.
  
  unfold mem_nextblock_same in *.
  congruence.
Qed.

Lemma encode_val_bits_length :
  forall chunk v,
    length (encode_val_bits chunk v) = size_chunk_nat chunk.
Proof.
  intros.
  destruct chunk; unfold encode_val_bits; unfold size_chunk_nat;
  destruct v; simpl; unfold Pos.to_nat; simpl;
  reflexivity.
Qed.

Lemma setN_get_nth :
  forall l (ofs z : Z) c r,
    ofs <= z < ofs + Z.of_nat (length l) ->
    (ZMap.get z (Mem.setN l ofs c) = r <->
    nth (Z.to_nat (z - ofs)) l Undef = r).
Proof.
  induction l; intros. simpl in H. omega.
  simpl in H. rewrite Zpos_P_of_succ_nat in H.
  assert (z = ofs \/ z > ofs) by omega.
  destruct H0.
  subst z.
  unfold Mem.setN. fold Mem.setN.
  rewrite Mem.setN_outside by omega.
  rewrite ZMap.gss. simpl. rewrite Z.sub_diag. simpl.
  reflexivity.

  unfold Mem.setN. fold Mem.setN.
  rewrite IHl by omega.
  assert (0 < z - ofs) by omega.
  rewrite Z2Nat.inj_lt in H1 by omega.
  simpl in H1.
  simpl. break_match. omega.
  assert (Z.to_nat (z - (ofs + 1)) = n).

  assert (z - ofs = Z.succ (z - (ofs + 1))) by omega.
  rewrite H2 in Heqn.
  rewrite Z2Nat.inj_succ in Heqn. inv Heqn.
  reflexivity. omega.
  
  rewrite H2. reflexivity.
Qed.

Lemma nth_single :
  forall { A : Type } m n (e : A),
    nth n (list_repeat m e) e = e.
Proof.
  induction m; intros.
  simpl. break_match; eauto.
  simpl. break_match; eauto.
Qed.

Lemma val_eq_or :
  forall v v',
    val_eq v v' ->
    v = Vundef \/ v = v'.
Proof.
  intros. unfold val_eq in *.
  break_match; try solve [left; reflexivity];
  right; eauto. inv_false.
Qed.

Lemma no_ptr_encode_val_bits :
  forall v v' chunk n b i q x,
    val_eq v v' ->
    ~ nth n (encode_val_bits chunk v') Undef = Fragment (Vptr b i) q x.
Proof.
  intros v v' chunk.
  destruct chunk; destruct v';
  intros;
  simpl;
  unfold inj_bytes;
  unfold encode_int;
  unfold rev_if_be;
  destruct Archi.big_endian;
  simpl;

  repeat break_match; try congruence.
Qed.

Lemma contents_equiv_pres :
  forall mc mc',
    contents_equiv mc mc' ->
    forall v v',
      val_eq v v' ->
      forall chunk b ofs,
        contents_equiv (PMap.set b (Mem.setN (encode_val_bits chunk v) ofs mc !! b) mc)
                       (PMap.set b (Mem.setN (encode_val_bits chunk v') ofs mc' !! b) mc').
Proof.
  intros.
  unfold contents_equiv in *.

  intros. destruct (peq b b0);
    try solve [repeat rewrite PMap.gso by congruence; eapply H; eauto].
  subst.
  repeat rewrite PMap.gss.
  assert (Hrange : (ofs0 < ofs \/ ofs0 >= ofs + Z.of_nat (size_chunk_nat chunk)) \/
          (ofs <= ofs0 < ofs + Z.of_nat (size_chunk_nat chunk))) by omega.
  destruct Hrange.
  repeat rewrite Mem.setN_outside; try eapply H; eauto;
  rewrite encode_val_bits_length; omega.
  app val_eq_or H0.
  break_match;
    try (symmetry);
    try rewrite setN_get_nth by (rewrite encode_val_bits_length; omega);
    try rewrite setN_get_nth in Heqm by (rewrite encode_val_bits_length; omega);
    break_or; subst; try assumption.

  unfold no_ptr_memval.
  repeat break_match; eauto.
  rewrite setN_get_nth in Heqm0 by (rewrite encode_val_bits_length; omega).
  app no_ptr_encode_val_bits Heqm0.
  unfold no_ptr_memval.
  repeat break_match; eauto.
  rewrite setN_get_nth in Heqm0 by (rewrite encode_val_bits_length; omega).
  app no_ptr_encode_val_bits Heqm0.

  simpl in *; destruct chunk; rewrite nth_single in Heqm; try congruence.
  simpl in *; destruct chunk; rewrite nth_single in Heqm; try congruence.
  break_match; try symmetry;
  try rewrite setN_get_nth by (rewrite encode_val_bits_length; omega); eauto.
  app no_ptr_encode_val_bits Heqm.
Qed.  

Lemma eq_mem_store :
  forall md m m',
    mem_eq md m m' ->
    forall v v',
      val_eq v v' ->
      forall c b ofs m0,
        store_bits c m b ofs v = Some m0 ->
        exists m0',
          store_bits c m' b ofs v' = Some m0' /\
          mem_eq md m0 m0'.
Proof.
  intros.
  unfold mem_eq in *.
  repeat break_and.
  app mem_store_nextblock H1.
  break_and. rewrite H1.
  eexists; split; eauto.
  split; econstructor; try eapply H6; eauto.
  econstructor; eauto.
  split; eauto.
  app store_bits_perm_same H4.
  break_and. rewrite H4 in H1. inv H1.
  
  split; auto.
  unfold mem_contents_equiv in *.
  unfold store_bits in *.
  repeat break_match_hyp; repeat opt_inv.
  simpl.
  eapply contents_equiv_pres; eauto.
Qed.

Lemma mem_alloc_nextblock :
  forall m m',
    mem_nextblock_same m m' ->
    forall m0 b lo hi,
      Mem.alloc m lo hi = (m0,b) ->
      exists m'0,
        Mem.alloc m' lo hi = (m'0,b) /\ mem_nextblock_same m0 m'0.
Proof.
  intros.
  app Mem.nextblock_alloc H0.
  destruct (Mem.alloc m' lo hi) eqn:?.
  app Mem.nextblock_alloc Heqp.
  app Mem.alloc_result H1.
  app Mem.alloc_result H2.
  assert (b = b0).
  unfold mem_nextblock_same in H.
  congruence. subst.
  eexists; split. f_equal. congruence.
  unfold mem_nextblock_same.
  congruence.
Qed.

Lemma mem_alloc_perm :
  forall m m',
    mem_perm_same m m' ->
    mem_nextblock_same m m' ->
    forall m0 b lo hi,
      Mem.alloc m lo hi = (m0,b) ->
      exists m'0,
        Mem.alloc m' lo hi = (m'0,b) /\ mem_perm_same m0 m'0.  
Proof.
  intros.
  app mem_alloc_nextblock H0.
  break_and. exists x. rewrite H0. split. reflexivity.
  unfold mem_perm_same in H.
  unfold mem_perm_same.
  intros.
  destruct (eq_block b b0).
  Focus 2.
  app Mem.alloc_access_result H1.
  app Mem.alloc_access_result H0.
  rewrite H1 in *. rewrite H0 in *.
  app Mem.alloc_result H5.
  subst b. rewrite PMap.gso by congruence.
  unfold mem_nextblock_same in H2.
  rewrite PMap.gso in H4 by congruence.
  eapply H; eauto. subst.
  app Mem.alloc_access_result H1.
  app Mem.alloc_access_result H0.
  rewrite H1 in *. rewrite H0 in *.
  app Mem.alloc_result H5.
  subst.
  rewrite PMap.gss in *.
  unfold mem_nextblock_same in *.
  rewrite <- H2 in *. rewrite PMap.gss.
  assumption.
Qed.

Lemma contents_equiv_alloc :
  forall m m',
    mem_nextblock_same m m' ->
    mem_contents_equiv m m' ->
    forall m0 b lo hi,
      Mem.alloc m lo hi = (m0,b) ->
      exists m'0,
        Mem.alloc m' lo hi = (m'0,b) /\ mem_contents_equiv m0 m'0.
Proof.
  intros.
  app mem_alloc_nextblock H1. break_and.
  eexists. split. eassumption.
  unfold mem_contents_equiv in *.
  app Mem.mem_contents_alloc H2.
  app Mem.mem_contents_alloc H1.
  rewrite H2. rewrite H1.
  
  unfold contents_equiv. intros.
  destruct (peq b b0). subst.
  repeat rewrite PMap.gss.
  rewrite ZMap.gi. eauto.

  unfold no_ptr_memval. eauto.
  
  repeat rewrite PMap.gso by congruence.
  unfold contents_equiv in H0. apply H0.
Qed.

Lemma eq_mem_alloc :
  forall md m m',
    mem_eq md m m' ->
    forall lo hi m0 b,
      Mem.alloc m lo hi = (m0,b) ->
      exists m0',
        Mem.alloc m' lo hi = (m0',b) /\ mem_eq (md_alloc md lo hi b) m0 m0'.
Proof.
  intros.
  unfold mem_eq in *;
    repeat break_and.
  app contents_equiv_alloc H0.
  break_and. find_rewrite.
  eexists; split; eauto.
  split; try split; eauto.
  eapply match_alloc; try apply H5; eauto.
  eapply match_alloc; eauto.
  
  app mem_alloc_nextblock H5.
  break_and. find_rewrite. find_inversion.
  split.
  assumption.
  app mem_alloc_perm H3.
  break_and. find_rewrite. find_inversion.
  split; assumption.
Qed.

Lemma mem_free_perm :
  forall m m',
    mem_perm_same m m' ->
    forall b lo hi m0,
      Mem.free m b lo hi = Some m0 ->
      exists m'0,
        Mem.free m' b lo hi = Some m'0 /\ mem_perm_same m0 m'0.
Proof.
  intros.
  unfold mem_perm_same in H.
  app Mem.free_range_perm H0.
  assert (Mem.range_perm m' b lo hi Cur Freeable).
  unfold Mem.range_perm. intros.
  unfold Mem.range_perm in H0.
  specialize (H0 ofs H2).
  eapply mem_perm_same_imp; eauto.
  app Mem.range_perm_free H2.
  destruct H2. rewrite e.
  exists x. split. reflexivity.
  unfold mem_perm_same. intros.
  app Mem.free_result H1.
  app Mem.free_result e.
  subst. 
  unfold Mem.unchecked_free in H2.
  unfold Mem.unchecked_free. simpl in *.
  destruct (peq b b0).
  subst. rewrite PMap.gss in *.
  break_match; try assumption. eapply H; eauto.
  rewrite PMap.gso in * by congruence.
  eapply H; eauto.
Qed.

Lemma mem_free_nextblock :
  forall m m',
    mem_perm_same m m' ->
    mem_nextblock_same m m' ->
    forall b lo hi m0,
      Mem.free m b lo hi = Some m0 ->
      exists m'0,
        Mem.free m' b lo hi = Some m'0 /\ mem_nextblock_same m0 m'0.
Proof.
  intros.
  app mem_free_perm H. break_and.
  exists x. split; auto.
  app Mem.nextblock_free H1.
  app Mem.nextblock_free H.
  unfold mem_nextblock_same in *.
  congruence.
Qed.

Lemma eq_mem_free :
  forall md m m',
    mem_eq md m m' ->
    forall b lo hi m0,
      Mem.free m b lo hi = Some m0 ->
      exists m0',
        Mem.free m' b lo hi = Some m0' /\ mem_eq (md_free md lo hi b) m0 m0'.
Proof.
  intros.
  unfold mem_eq in *.
  repeat break_and.
  app mem_free_perm H0. break_and.
  app mem_free_nextblock H3. break_and.
  find_rewrite. find_inversion.
  find_rewrite.
  eexists; split; eauto.
  split. eapply match_free; try eapply H5; eauto.
  split. eapply match_free; eauto.
  
  split; eauto.
  app Mem.free_result H0.
  app Mem.free_result H5.
  subst.
  unfold mem_contents_equiv.
  unfold Mem.unchecked_free.
  simpl. eauto.
Qed.
  

Lemma eq_mem_valid_pointer :
  forall md m m',
    mem_eq md m m' ->
    forall b z,
      Mem.valid_pointer m b z = true ->
      Mem.valid_pointer m' b z = true.
Proof.
  intros.
  unfold mem_eq in *.
  repeat break_and.
  unfold mem_perm_same in *.
  destruct (Mem.valid_pointer m b z) eqn:?;
           destruct (Mem.valid_pointer m' b z) eqn:?;
           try congruence;
    unfold Mem.valid_pointer in *;
  unfold proj_sumbool in *;
  repeat break_match_hyp; try congruence.
  clear Heqs0.
  eapply mem_perm_same_imp in p; eauto; try congruence.
Qed.

Lemma val_eq_loadv :
  forall md m m',
    mem_eq md m m' ->
    forall a a',
      val_eq a a' ->
      forall c v v',
        Mem.loadv c m a = Some v ->
        Mem.loadv c m' a' = Some v' ->
        val_eq v v'.
Proof.
  intros.
  unfold Mem.loadv in *.
  repeat break_match_hyp; try congruence.
  simpl in H0. inv H0.
Qed.


Lemma val_eq_cmpu :
  forall md m m' c a b x y,
    val_eq a b ->
    val_eq x y ->
    mem_eq md m m' ->
    val_eq (Val.cmpu (Mem.valid_pointer m) c a x) (Val.cmpu (Mem.valid_pointer m') c b y).
Proof.
  intros.
  
  unfold val_eq in *.
  unfold Val.cmpu.

  destruct a; destruct x; try inv_false;
  subst; simpl; intros; try congruence;
  try solve [unfold Val.of_optbool; unfold Vtrue; unfold Vfalse;
             repeat break_match; try congruence].
Qed.

Lemma no_ptr_mem_eq :
  forall md m m',
    no_ptr_mem m ->
    mem_eq md m m' ->
    no_ptr_mem m'.
Proof.
  intros. unfold no_ptr_mem.
  unfold mem_eq in H0.
  repeat break_and.
  unfold mem_contents_equiv in H2.
  unfold contents_equiv in H2.
  intros. break_match; eauto.
  intros.
  specialize (H4 ofs z).
  rewrite Heqm0 in H4.
  repeat break_match_hyp; try congruence.
  unfold no_ptr_memval in H4. destruct v; congruence.
Qed.

Lemma eq_mem_empty :
  mem_eq md_init Mem.empty Mem.empty.
Proof.
  unfold mem_eq.
  repeat split.
  econstructor; eauto.
  econstructor; eauto.
  unfold mem_perm_same.
  intros. eauto.
  unfold mem_contents_equiv.
  unfold contents_equiv.
  unfold Mem.empty.
  simpl.
  intros.
  rewrite PMap.gi.
  rewrite ZMap.gi.
  simpl. eauto.
Qed.

Lemma eq_mem_drop_perm :
  forall md m m',
    mem_eq md m m' ->
    forall b lo hi p m0 m0',
      Mem.drop_perm m b lo hi p = Some m0 ->
      Mem.drop_perm m' b lo hi p = Some m0' ->
      mem_eq md m0 m0'.
Proof.
  intros.
  unfold mem_eq in *. repeat break_and.
  split.
  eapply match_drop_perm; try apply H0; eauto.
  split.
  eapply match_drop_perm; eauto.
  split.
  unfold mem_nextblock_same. simpl.
  unfold Mem.drop_perm in *.
  repeat break_match_hyp; try congruence;
  inv H1; inv H0. simpl.
  assumption.
  split;
    try solve [unfold Mem.drop_perm in *;
               repeat break_match_hyp; try congruence;
               inv H1; inv H0; simpl; apply H3].
  unfold Mem.drop_perm in *.
  repeat break_match_hyp; try congruence.
  inv H0. inv H1.
  unfold mem_perm_same. intros.
  unfold Mem.perm in *.
  simpl in *.
  unfold Mem.perm_order' in *.  
  destruct (peq b b0);
    repeat rewrite PMap.gso in * by congruence;
    subst;
    repeat rewrite PMap.gss in *.
  break_match_hyp; try inv_false.
  assumption. eapply H4; eauto. eapply H4; eauto.

  unfold Mem.drop_perm in *;
    repeat break_match_hyp;
    try congruence;
    repeat opt_inv;
    subst;
    eauto.
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

Lemma eq_mem_store_zeros_bits :
  forall hi md m m',
    mem_eq md m m' ->
    forall b lo m0 m0',
      store_zeros_bits m b lo hi = Some m0 ->
      store_zeros_bits m' b lo hi = Some m0' ->
      mem_eq md m0 m0'.
Proof.
  induction hi using Z_nat_ind; intros.
  * rewrite store_zeros_bits_equation in H0.
    break_match_hyp; try omega.
    inv H0.
    rewrite store_zeros_bits_equation in H1.
    break_match_hyp; try omega.
    inv H1. eauto.

  * rewrite store_zeros_bits_equation in H0.
    repeat break_match_hyp; try omega; try congruence.
    replace (1-1) with 0 in H0 by omega.
    rewrite store_zeros_bits_equation in H0.
    break_match_hyp; try omega.
    inv H0.

    rewrite store_zeros_bits_equation in H1.
    repeat break_match_hyp; try omega; try congruence.
    replace (1-1) with 0 in H1 by omega.
    rewrite store_zeros_bits_equation in H1.
    break_match_hyp; try omega.
    inv H1.
    app eq_mem_store Heqo. break_and.
    rewrite H1 in Heqo0. inv Heqo0.
    eauto. simpl. reflexivity.
  * rewrite store_zeros_bits_equation in H1.
    break_match_hyp; try omega.
    inv H1.
    rewrite store_zeros_bits_equation in H2.
    break_match_hyp; try omega.
    inv H2. eauto.
  * rewrite store_zeros_bits_equation in H1.
    rewrite store_zeros_bits_equation in H2.
    break_match_hyp; try omega.
    repeat break_match_hyp; try congruence.
    replace (hi + 1 - 1) with hi in * by omega.
    eapply IHhi.
    Focus 2. apply H1.
    Focus 2. apply H2.
    app eq_mem_store Heqo0; eauto.
    break_and. rewrite H4 in Heqo. inv Heqo. eauto.
    simpl. reflexivity.
Qed.  

Lemma eq_mem_store_init_data_bits :
  forall md m m',
    mem_eq md m m' ->
    forall ge b t ofs a m0 m0',
      store_init_data_bits t ge m b ofs a = Some m0 ->
      store_init_data_bits t ge m' b ofs a = Some m0' ->
      mem_eq md m0 m0'.
Proof.
  intros. destruct a; simpl in *;
          repeat break_match_hyp; try congruence;
          try app eq_mem_store H0;
          repeat break_and; try rewrite H0 in H1; simpl; instantiate;
          try congruence.
Qed.

Lemma eq_mem_store_init_data_list_bits :
  forall l ge md m m' b ofs m0 m0' t,
    mem_eq md m m' ->
    store_init_data_list_bits t ge m b ofs l = Some m0 ->
    store_init_data_list_bits t ge m' b ofs l = Some m0' ->
    mem_eq md m0 m0'.
Proof.
  induction l; intros.
  simpl in H0. simpl in H1. congruence.
  simpl in H0. simpl in H1.
  repeat break_match_hyp; try congruence.
  eapply IHl; instantiate; try apply H1; try apply H0.
  eapply eq_mem_store_init_data_bits; eauto.
Qed.
        

Lemma eq_mem_alloc_only_global_bits :
  forall t m m',
    mem_eq t m m' ->
    forall ge id g m0 m0' t' b x y x' y' b',
      alloc_only_global_bits t ge m (id,g) = Some (m0,t',x,b,y) ->
      alloc_only_global_bits t ge m' (id,g) = Some (m0',t',x',b',y') ->
      mem_eq t' m0 m0' /\ x = x' /\ y = y' /\ b = b'.
Proof.
  intros. unfold alloc_only_global_bits in *.
  repeat break_match_hyp; try congruence;
  repeat opt_inv; subst.
  app eq_mem_alloc Heqp0. break_and.
  rewrite H1 in Heqp. inv Heqp.
  split.
  eapply eq_mem_drop_perm; eauto.
  split; try split; try congruence.
  app eq_mem_alloc Heqp0. break_and.
  rewrite H1 in Heqp. inv Heqp.
  split.
  eapply eq_mem_drop_perm; eauto.
  repeat split; congruence.
  app eq_mem_alloc Heqp0. break_and.
  rewrite H1 in Heqp. inv Heqp.
  split.
  eapply eq_mem_drop_perm; eauto.
  repeat split; congruence.
Qed.
        
Lemma eq_mem_alloc_only_globals_bits:
  forall g t m m',
    mem_eq t m m' ->
    forall ge m0 m0' t' t'' l l',
      alloc_only_globals_bits t ge m g = Some (m0,t',l) ->
      alloc_only_globals_bits t ge m' g = Some (m0',t'',l') ->
      mem_eq t' m0 m0' /\ t' = t'' /\ l = l'.
Proof.
  induction g; intros.
  unfold alloc_globals_bits in H0. simpl in H0. inv H0.
  unfold alloc_globals_bits in H1. simpl in H1. inv H1.
  split; solve [auto].
  unfold alloc_globals_bits in H0.
  unfold alloc_globals_bits in H1.
  simpl in *.
  repeat break_match_hyp; try congruence;
  repeat opt_inv; subst.
  destruct a.
  assert (a0 = a2). {
    unfold alloc_only_global_bits in Heqo1;
    unfold alloc_only_global_bits in Heqo;
    repeat break_match_hyp; repeat opt_inv;
    subst_max.
    app eq_mem_alloc Heqp0; eauto. break_and. congruence.
    app eq_mem_alloc Heqp0; eauto. break_and. congruence.
    app eq_mem_alloc Heqp0; eauto. break_and. congruence.
  } idtac.
  subst.
  specialize (IHg a2 m3 m1).
  assert (mem_eq t' m0 m0' /\ t' = t'' /\ l1 = l0).
  eapply IHg; eauto.
  eapply eq_mem_alloc_only_global_bits; eauto.
  repeat break_and. split; try assumption.
  split. assumption.
  subst. f_equal.
  eapply eq_mem_alloc_only_global_bits in Heqo; try eapply Heqo1.
  repeat break_and. subst. reflexivity.
  eauto.
Qed.

Lemma eq_mem_set_perm :
  forall md m m',
    mem_eq md m m' ->
    forall b lo hi p m0 m0',
      set_perm m b lo hi p = Some m0 ->
      set_perm m' b lo hi p = Some m0' ->
      mem_eq md m0 m0'.
Proof.
  intros.
  unfold mem_eq in *. repeat break_and.

  split.
  eapply match_set_perm; try apply H0; eauto.
  split.
  eapply match_set_perm; eauto.
  
  unfold set_perm in *.
  repeat break_match_hyp; try congruence; repeat opt_inv; subst.

  split. 
  unfold mem_nextblock_same in *. simpl; eauto.
  unfold mem_perm_same in *. split; simpl; eauto.
  unfold Mem.perm in *. simpl.
  unfold Mem.perm_order' in *.
  intros.
  destruct (peq b b0); try subst;
    try rewrite PMap.gss in *;
    try rewrite PMap.gso in * by congruence;
    try solve [eapply H0; eauto].
  break_match_sm; simpl; eauto.
  eapply H4; eauto.
Qed.

Lemma eq_mem_store_global_bits :
  forall md m m',
    mem_eq md m m' ->
    forall ge b g m0 m0' md0 md0',
      store_global_bits md ge m b g = Some (m0,md0) ->
      store_global_bits md ge m' b g = Some (m0',md0') ->
      mem_eq md0 m0 m0' /\ md0 = md0'.
Proof.
  intros.
  unfold store_global_bits in *.
  repeat break_match_hyp; try congruence;
  repeat opt_inv; subst_max; split; try reflexivity.
  eapply eq_mem_set_perm; eauto.
  eapply eq_mem_set_perm; eauto.
  eapply eq_mem_set_perm; try eapply Heqo4; try eapply Heqo1.
  eapply eq_mem_store_init_data_list_bits; try eapply Heqo3; try eapply Heqo0.
  eapply eq_mem_store_zeros_bits; eauto.
Qed.

Lemma eq_mem_store_globals_bits :
  forall l md m m',
    mem_eq md m m' ->
    forall ge m0 m0' md',
      store_globals_bits md ge m l = Some (m0,md') ->
      store_globals_bits md ge m' l = Some (m0',md') ->
      mem_eq md' m0 m0'.
Proof.
  induction l; intros.
  simpl in *. congruence.
  simpl in *.
  repeat break_match_hyp; try congruence; repeat opt_inv; subst.
  app eq_mem_store_global_bits H. break_and.
  subst.
  eapply IHl; eauto.
Qed.

Lemma eq_mem_alloc_globals_bits:
  forall g t m m',
    mem_eq t m m' ->
    forall ge m0 m0' t',
      alloc_globals_bits t ge m g = Some (m0,t') ->
      alloc_globals_bits t ge m' g = Some (m0',t') ->
      mem_eq t' m0 m0'.
Proof.
  intros. unfold alloc_globals_bits in *.
  repeat break_match_hyp; try congruence.
  subst.
  eapply (eq_mem_alloc_only_globals_bits _ _ m m') in Heqo0; try eapply Heqo; eauto.
  repeat break_and. subst.
  eapply eq_mem_store_globals_bits; eauto.
Qed.
  
Lemma eq_mem_init :
  forall p m t,
    init_mem_bits p = Some (m,t) ->
    mem_eq t m m.
Proof.
  intros. unfold init_mem_bits in H.
  
  eapply eq_mem_alloc_globals_bits; eauto.
  eapply eq_mem_empty; eauto.
Qed.


Axiom mem_eq_extcall :
  forall ef ge vl m t v m',
    external_call ef ge vl m t v m' ->
    forall md m0,
      mem_eq md m m0 ->
      forall vl',
        list_forall2 val_eq vl vl' ->
        exists m0' v0,
          external_call ef ge vl' m0 t v0 m0' /\
          val_eq v v0 /\
          mem_eq (md_ec md ef ge vl' m0 t v0 m0') m' m0' /\
          md_ec md ef ge vl m t v m' = md_ec md ef ge vl' m0 t v0 m0'.


Axiom mem_eq_extcall' :
  forall ef ge vl m t v m',
    external_call' ef ge vl m t v m' ->
    forall md m0,
      mem_eq md m m0 ->
      forall vl',
        list_forall2 val_eq vl vl' ->
        exists m0' v0,
          external_call' ef ge vl' m0 t v0 m0' /\
          list_forall2 val_eq v v0 /\
          mem_eq (md_ec' md ef ge vl' m0 t v0 m0') m' m0' /\
          md_ec' md ef ge vl m t v m' = md_ec' md ef ge vl' m0 t v0 m0'.
