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


Ltac plus_one_go_away ofs :=
  match goal with
    | [ |- context[ofs + 1] ] => replace (ofs + 1) with (1 + ofs) by omega
  end;
  repeat match goal with
           | [ |- context[(?X + ofs) + 1]] => replace ((X + ofs) + 1) with ((X + 1) + ofs) by omega
         end;
  match goal with
    | [ |- context[?X + ofs] ] => try replace (X + ofs) with (7 + ofs) by omega;
        try replace (X + ofs) with (6 + ofs) by omega;
        try replace (X + ofs) with (5 + ofs) by omega;
        try replace (X + ofs) with (4 + ofs) by omega;
        try replace (X + ofs) with (3 + ofs) by omega;
        try replace (X + ofs) with (2 + ofs) by omega;
        try replace (X + ofs) with (1 + ofs) by omega
  end.


Lemma size_chunk_nat_cases :
  forall c,
    size_chunk_nat c = 1%nat
    \/ size_chunk_nat c = 2%nat
    \/ size_chunk_nat c = 4%nat
    \/ size_chunk_nat c = 8%nat.
Proof.
  intros.
  destruct c; prove_or_eq reflexivity;
  reflexivity.
Qed.

Definition wf_frag (m : memory_chunk) (v : val) (l : list memval) :=
  l = encode_val m v /\
  exists q l',
    l = Fragment v q (size_quantity_nat q - 1) :: l'.


Lemma z_neq :
  forall (y z : Z),
    y <> 0 ->
    z <> y + z.
Proof.
  intros. intro. omega.
Qed.


Lemma get_setN_encode :
  forall ofs chunk v c v' q n,
    ZMap.get ofs (Mem.setN (encode_val chunk v) ofs c) = Fragment v' q n ->
    size_chunk_nat chunk = Datatypes.S (size_quantity_nat q - 1).
Proof.
  intros.
  generalize H.
  clear H.
  
  destruct chunk eqn:?;
           subst chunk;
    destruct v eqn:?;
             subst v;
    simpl;
  



  unfold inj_bytes;
  unfold inj_value;
  unfold encode_int;
  unfold rev_if_be;
  repeat break_match;
  simpl;
  repeat (rewrite ZMap.gso by (plus_one_go_away ofs; eapply z_neq; omega));
  try rewrite ZMap.gss;
  intros;
  try congruence;
  inv H;
  simpl;
  try reflexivity.
Qed.

Lemma same_size_chunk :
  forall v' m v ofs chunk c,
    wf_frag m v' (Mem.getN (size_chunk_nat m) ofs (Mem.setN (encode_val chunk v) ofs c)) ->
    size_chunk_nat chunk = size_chunk_nat m.
Proof.
  intros.
  unfold wf_frag in H.
  break_and. repeat break_exists; subst.

  name H Henc. rewrite H0 in Henc.

  assert ((size_chunk_nat m > 0)%nat). {
    destruct m;
    unfold size_chunk_nat;
    simpl;
    unfold Pos.to_nat;
    simpl;
    omega.
  } idtac.


  destruct (size_chunk_nat m) eqn:?; try omega.
  simpl in H0. inv H0.
  destruct m eqn:?; destruct v' eqn:?;
  simpl in Henc;
  unfold inj_bytes in *;
  unfold inj_value in *;
  simpl in Henc;
  try solve [inv Henc];

  simpl in H;
  unfold size_chunk_nat in Heqn;
  simpl in Heqn;
  unfold Pos.to_nat in Heqn;
  simpl in Heqn;
  rewrite <- Heqn in *;
  subst m;
  subst v';

  repeat (destruct n; try omega);
  simpl in Henc;
  
  inv H; clear Henc;

  clear H4; clear H5; clear H6;
  try clear H7;
  try clear H8;
  try clear H9;
  try clear H10;
  rewrite H3 in H2; inv H2;

  eapply get_setN_encode; eauto.
Qed.  


