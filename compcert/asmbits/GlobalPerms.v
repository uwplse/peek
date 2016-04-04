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
Require Import MemBits.
Require Import Zlen.

Lemma perm_freeable :
  forall x,
    perm_order x Freeable ->
    x = Freeable.
Proof.
  intros. inv H; congruence.
Qed.

Lemma global_perms_store :
  forall ge m,
    global_perms ge m ->
    forall c b i v m',
      Mem.store c m b i v = Some m' ->
      global_perms ge m'.
Proof.
  intros. unfold global_perms in *.
  intros.
  app H H1.
  unfold Mem.perm in *.
  unfold Mem.perm_order' in *.
  break_and.
  exists x. split; try congruence.
  app Mem.store_access H0.
  congruence.
Qed.

Lemma global_perms_alloc :
  forall ge m,
    global_perms ge m ->
    forall lo hi b m',
      Mem.alloc m lo hi = (m',b) ->
      global_perms ge m'.
Proof.
  intros.
  unfold global_perms in *.
  intros.
  app H H1.
  break_and.
  assert (Mem.perm m b0 (Int.unsigned ofs) Cur x).
  unfold Mem.perm. unfold Mem.perm_order'. collapse_match.
  econstructor.

  

  destruct (plt b0 b).
  Focus 2.
  subst. name (Mem.nextblock_noaccess m b0 (Int.unsigned ofs) Cur) k.
  app Mem.alloc_result H0. subst.
  app k n. congruence.


  
  assert (b0 <> b).
  eapply Plt_ne; eauto.
  unfold Mem.perm in H0.
  unfold Mem.perm_order' in H0.
  name (Mem.alloc_access _ _ _ _ _ H0 _ p (Int.unsigned ofs) Cur) aa.
  rewrite aa in H1.
  exists x. split; eauto.
Qed.

Lemma global_perms_free_not_global :
  forall ge m b lo hi m',
    global_perms ge m ->
    Mem.free m b lo hi = Some m' ->
    forall ofs,
      lo <= Int.unsigned ofs < hi ->
      ~ is_global ge b ofs.
Proof.
  intros.
  unfold global_perms in *.
  intro.
  app H H2.
  break_and.
  app Mem.free_range_perm H0.
  unfold Mem.range_perm in H0.
  app H0 H1.
  clear H. clear H0.
  unfold Mem.perm in *.
  unfold Mem.perm_order' in *.
  break_match_hyp; try inv_false.
  app perm_freeable H1. subst.
  inv H2; try congruence.
Qed.

Lemma global_perms_free :
  forall ge m,
    global_perms ge m ->
    forall b lo hi m',
      Mem.free m b lo hi = Some m' ->
      global_perms ge m'.
Proof.
  intros.
  unfold global_perms. intros.
  unfold global_perms in H.
  app H H1. break_and.
  exists x. split; try congruence.
  app Mem.free_result H0.
  subst. unfold Mem.unchecked_free.
  simpl.
  destruct (peq b b0). subst.
  rewrite PMap.gss.
  break_match.
  unfold andb in Heqb.
  unfold proj_sumbool in Heqb.
  repeat break_match_hyp; try congruence.
  app global_perms_free_not_global H4. congruence.
  eauto.
  rewrite PMap.gso by congruence.
  eauto.
Qed.

Lemma global_perms_drop_perm :
  forall ge m,
    global_perms ge m ->
    forall b i j p m',
      Mem.drop_perm m b i j p = Some m' ->
      global_perms ge m'.
Proof.
  intros. unfold global_perms in *.
  intros. eapply H in H1.
  clear H. break_exists.
  break_and.
  unfold Mem.drop_perm in H0.
  break_match_hyp; inv H0.
  simpl. destruct (peq b b0).
  subst. rewrite PMap.gss.
  break_match.
  unfold Mem.range_perm in r.
  clear Heqs.
  unfold proj_sumbool in Heqb.
  unfold andb in Heqb.
  repeat break_match_hyp; try congruence.
  exploit (r (Int.unsigned ofs)); try omega; intros.
  unfold Mem.perm in H0.
  unfold Mem.perm_order' in H0.
  rewrite H in H0.
  app perm_freeable H0.
  exists x. split; eauto.
  rewrite PMap.gso by congruence.
  exists x. split; eauto.
Qed.  

Lemma global_perms_store_bits :
  forall ge m,
    global_perms ge m ->
    forall c b i v m',
      store_bits c m b i v = Some m' ->
      global_perms ge m'.
Proof.
  intros. unfold global_perms in *.
  intros.
  app H H1.
  unfold Mem.perm in *.
  unfold Mem.perm_order' in *.
  break_and.
  exists x. split; try congruence.
  unfold store_bits in H0.
  break_match_hyp; inv H0.
  simpl. assumption.
Qed.

(* external calls don't somehow free memory containing global variables or code *)
Axiom global_perms_ec :
  forall ef (ge : genv) l m t v m',
    external_call ef ge l m t v m' ->
    global_perms ge m ->
    global_perms ge m'.

Lemma global_perms_step :
  forall ge rs m md t rs' m' md',
    step_bits ge (State_bits rs m md) t (State_bits rs' m' md') ->
    global_perms ge m ->
    global_perms ge m'.
Proof.
  intros.
  invs; simpl; subst.
  *
    destruct i; simpl in H14;
    unfold goto_label_bits in *;
    unfold exec_load_bits in *;
    unfold exec_store_bits in *;
    unfold exec_big_load_bits in *;
    unfold exec_big_store_bits in *;
    simpl in *;
    repeat (break_match_hyp; try congruence);
    try st_inv;
    unfold storev_bits in *;
    repeat (break_match_hyp; try congruence);
    eauto;
    try solve [eapply global_perms_store_bits; eauto];
    try solve [eapply global_perms_store_bits;
                try eapply global_perms_store_bits; eauto];
    try solve [eapply global_perms_store_bits;
                try eapply global_perms_store_bits;
                try eapply global_perms_alloc; eauto];
    try solve [eapply global_perms_free; eauto].
  * inv H11.
    eapply global_perms_ec; eauto.
  * eapply global_perms_ec; eauto.
  * inv H11.
    eapply global_perms_ec; eauto.
Qed.

