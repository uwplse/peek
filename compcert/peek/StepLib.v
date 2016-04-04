Require Import Coqlib.
Require Import Asm.
Require Import Globalenvs.
Require Import Integers.

Require Import PeekTactics.
Require Import PeekLib.
Require Import PregTactics.
Require Import AsmBits.
Require Import MemoryAxioms.
Require Import GlobalPerms.


Lemma step_match_metadata :
  forall ge rs m md t rs' m' md',
    step_bits ge (State_bits rs m md) t (State_bits rs' m' md') ->
    match_metadata md m ->
    match_metadata md' m'.
Proof.
  intros.
  invs; subst;
  try solve [eapply match_ec'; eauto];
  try solve [eapply match_ec; eauto].
  destruct i;
    simpl in *;
    unfold exec_big_load_bits in *;
    unfold exec_big_store_bits in *;
    unfold exec_load_bits in *;
    unfold exec_store_bits in *;
    unfold goto_label_bits in *;
    unfold storev_bits in *;
    simpl in *;
    repeat break_match_hyp;
    try congruence;
    try st_inv;
    try solve [econstructor; eauto];
    try solve [econstructor; try econstructor; eauto].
  econstructor; try econstructor; try eapply match_alloc; eauto.
  eapply match_free; eauto.
Qed.  



Lemma step_md :
  forall ge rs m md t rs' m' md',
    step_bits ge (State_bits rs m md) t (State_bits rs' m' md') ->
    match_metadata md m /\ match_metadata md' m'.
Proof.
  intros. isplit.
  invs; auto.
  eapply step_match_metadata; eauto.
Qed.

Lemma step_gp :
  forall ge rs m md t rs' m' md',
    step_bits ge (State_bits rs m md) t (State_bits rs' m' md') ->
    global_perms ge m /\ global_perms ge m'.
Proof.
  intros. isplit.
  invs; eauto.
  eapply global_perms_step; eauto.
Qed.


Ltac break_instr_exec i :=
  destruct i;
  simpl in *;
  unfold exec_load_bits in *;
  unfold exec_store_bits in *;
  unfold exec_big_load_bits in *;
  unfold exec_big_store_bits in *;
  unfold goto_label_bits in *;
  repeat (break_match_hyp; try congruence);
  st_inv.


Lemma md_extends_step :
  forall ge rs m md t rs' m' md',
    step_bits ge (State_bits rs m md) t (State_bits rs' m' md') ->
    md_extends md md'.
Proof.
  intros.
  invs; subst; try solve [econstructor].
  break_instr_exec i;
    econstructor; eauto.
Qed.

