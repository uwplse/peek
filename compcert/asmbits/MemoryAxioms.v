Require Import Coqlib.
Require Import Values.
Require Import Integers.
Require Import Globalenvs.
Require Import AST.
Require Import Memory.
Require Import Asm.
Require Import Values.
Require Import Events.

(* Definition of store_bits *)
Require Import MemBits.


(*Stuart's Ring Magic *)

Lemma int_ring : ring_theory Int.zero Int.one Int.add Int.mul Int.sub Int.neg eq.
constructor; intros;
eauto using
  Int.add_zero_l, Int.add_assoc, Int.add_commut,
  Int.mul_one, Int.mul_assoc, Int.mul_commut,
  Int.mul_add_distr_l, Int.sub_add_opp, Int.add_neg_zero.
- (* 1 * x = x -- doesn't quite go through on its own *)
  rewrite Int.mul_commut. apply Int.mul_one.
Qed.

Definition eq_dec_bool x y := Coqlib.proj_sumbool (Int.eq_dec x y).

Lemma int_ring_dec : forall x y, eq_dec_bool x y = true -> x = y.
intros.
unfold eq_dec_bool, Coqlib.proj_sumbool in *.
destruct (Int.eq_dec _ _); congruence.
Qed.

Ltac int_ring_constants t :=
    match t with
    | Int.zero => constr:(Int.repr 0)
    | Int.one => constr:(Int.repr 1)
    | Int.repr _ => t
    | _ => constr:NotConstant
    end.

Add Ring IntRing : int_ring (decidable int_ring_dec, constants [int_ring_constants]).

(*end ring magic*)


Axiom allocator_metadata : Type.

Axiom md_alloc : allocator_metadata -> Z -> Z -> block -> allocator_metadata.
Axiom md_free : allocator_metadata -> Z -> Z -> block -> allocator_metadata.
Axiom md_ec' : allocator_metadata -> external_function ->
               Senv.t -> list val -> mem -> trace -> list val -> mem ->
               allocator_metadata.
Axiom md_ec : allocator_metadata -> external_function ->
              Senv.t -> list val -> mem -> trace -> val -> mem ->
              allocator_metadata.

Axiom md_init : allocator_metadata.

Inductive match_metadata : allocator_metadata -> mem -> Prop :=
| match_init :
    match_metadata md_init Mem.empty
| match_store_bits :
    forall md m c b ofs v m',
      match_metadata md m ->
      store_bits c m b ofs v = Some m' ->
      match_metadata md m'
| match_store :
    forall md m c b ofs v m',
      match_metadata md m ->
      Mem.store c m b ofs v = Some m' ->
      match_metadata md m'
| match_drop_perm :
    forall md m b lo hi p m',
      match_metadata md m ->
      Mem.drop_perm m b lo hi p = Some m' ->
      match_metadata md m'
| match_alloc :
    forall md m lo hi b m',
      match_metadata md m ->
      Mem.alloc m lo hi = (m',b) ->
      match_metadata (md_alloc md lo hi b) m'
| match_free :
    forall md m lo hi b m',
      match_metadata md m ->
      Mem.free m b lo hi = Some m' ->
      match_metadata (md_free md lo hi b) m'
| match_set_perm :
    forall md m b lo hi p m',
      match_metadata md m ->
      set_perm m b lo hi p = Some m' ->
      match_metadata md m'
| match_ec :
    forall md m ef ge va t vr m',
      match_metadata md m ->
      external_call ef ge va m t vr m' ->
      match_metadata (md_ec md ef ge va m t vr m') m'
| match_ec' :
    forall md m ef ge va t vr m',
      match_metadata md m ->
      external_call' ef ge va m t vr m' ->
      match_metadata (md_ec' md ef ge va m t vr m') m'.

Inductive md_extends : allocator_metadata -> allocator_metadata -> Prop :=
| ex_refl :
    forall md,
      md_extends md md
| ex_alloc :
    forall md lo hi b,
      md_extends md (md_alloc md lo hi b)
| ex_free :
    forall md lo hi b,
      md_extends md (md_free md lo hi b)
| ex_ec :
    forall md m ef ge va t vr m',
      md_extends md (md_ec md m ef ge va t vr m')
| ex_ec' :
    forall md m ef ge va t vr m',
      md_extends md (md_ec' md m ef ge va t vr m')
| ex_trans :
    forall a b c,
      md_extends a b ->
      md_extends b c ->
      md_extends a c.



(* Memory injection/surjection *)
(* Here we formalize what we believe to we true about the CompCert memory model *)
(* as the block/offset combination allows for infinite memory *)
(* but we run programs on physical hardware with finite memory *)
(* pinj: Where was this block/offset allocated? *)
(* pinj = Some does not mean that that result is a valid pointer *)
(* once allocated, pinj remembers for all time *)
Axiom pinj : allocator_metadata -> block -> int -> option int.
(* psur: what does this memory currently map to? *)
Axiom psur : allocator_metadata -> int -> option (block * int).

Axiom pinj_extends :
  forall t b ofs bits,
    pinj t b ofs = Some bits ->
    forall t',
      md_extends t t' ->
      pinj t' b ofs = Some bits.
                        

(* everything still injects after alloc *)
Lemma pinj_alloc :
  forall t b ofs bits,
    pinj t b ofs = Some bits ->
    forall lo hi b2,
      pinj (md_alloc t lo hi b2) b ofs = Some bits.
Proof.
  intros.
  eapply pinj_extends; eauto.
  simpl.
  econstructor.
Qed.

(* once pinj, always pinj *)
Lemma pinj_free :
  forall t b ofs bits,
    pinj t b ofs = Some bits ->
    forall lo hi b2,
      pinj (md_free t lo hi b2) b ofs = Some bits.
Proof.
  intros.
  eapply pinj_extends; eauto.
  econstructor.
Qed.

(* pinj preserved over external calls as well *)
Lemma pinj_ec :
  forall t b ofs bits,
    pinj t b ofs = Some bits ->
    forall ef ge va m tr vr m',
      pinj (md_ec t ef ge va m tr vr m') b ofs = Some bits.
Proof.
  intros.
  eapply pinj_extends; eauto.
  econstructor.
Qed.

Lemma pinj_ec' :
  forall t b ofs bits,
    pinj t b ofs = Some bits ->
    forall ef ge va m tr vr m',
      pinj (md_ec' t ef ge va m tr vr m') b ofs = Some bits.
Proof.
  intros.
  eapply pinj_extends; eauto.
  econstructor.
Qed.

Axiom pinj_add :
  forall t b ofs bits,
    pinj t b ofs = Some bits ->
    forall adj,
      pinj t b (Int.add ofs adj) = Some (Int.add bits adj).

Lemma pinj_sub :
  forall t b ofs bits,
    pinj t b ofs = Some bits ->
    forall adj,
      pinj t b (Int.sub ofs adj) = Some (Int.sub bits adj).
Proof.
  intros.
  repeat rewrite Int.sub_add_opp.
  eapply pinj_add; eauto.
Qed.

Axiom pinj_injective_within_block :
  forall t b ofs ofs' bits,
    pinj t b ofs = Some bits ->
    pinj t b ofs' = Some bits ->
    ofs = ofs'.


Lemma pinj_sub_ptr_diff :
  forall t x y b ofs1 ofs2,
    pinj t b ofs1 = Some x ->
    pinj t b ofs2 = Some y ->
    Int.sub ofs1 ofs2 = Int.sub x y.
Proof.
  intros.
  eapply pinj_add in H.
  instantiate (1 := ofs2) in H.
  eapply pinj_add in H0. instantiate (1 := ofs1) in H0.
  rewrite Int.add_commut in H0.
  assert (Int.add x ofs2 = Int.add y ofs1) by congruence.
  cut (x = Int.sub (Int.add y ofs1) ofs2).
  { intro. subst x. ring. }
  rewrite <- H1. ring.
Qed.  



(* Not sure if matching metadata is necessary, but universally quantified memory is scary *)
Axiom null_always_invalid :
  forall t m b ofs bits,
    match_metadata t m ->
    pinj t b ofs = Some bits ->
    Int.unsigned bits = 0 ->
    Mem.valid_pointer m b (Int.unsigned ofs) = false /\
    Mem.valid_pointer m b (Int.unsigned ofs - 1) = false.

Axiom weak_valid_pointer_sur :
  forall t m,
    match_metadata t m ->
    forall b ofs bits,
      psur t bits = Some (b,ofs) <->
      (pinj t b ofs = Some bits /\ Mem.weak_valid_pointer m b (Int.unsigned ofs) = true).

(* Needs to work with weakly valid pointers, not sure all the subtlety but this *)
(* puts the work off onto the allocator *)
Axiom psur_comparison :
  forall m t b ofs1 ofs2 bits1 bits2,
    match_metadata t m ->
    pinj t b ofs1 = Some bits1 ->
    Mem.weak_valid_pointer m b (Int.unsigned ofs1) = true ->
    pinj t b ofs2 = Some bits2 ->
    Mem.weak_valid_pointer m b (Int.unsigned ofs2) = true ->
    (Int.unsigned ofs1 < Int.unsigned ofs2 <->
    Int.unsigned bits1 < Int.unsigned bits2).

Lemma valid_pointer_sur :
  forall t m,
    match_metadata t m ->
    forall b ofs bits,
      (pinj t b ofs = Some bits /\ Mem.valid_pointer m b (Int.unsigned ofs) = true) ->
      psur t bits = Some (b,ofs).
Proof.
  intros. erewrite weak_valid_pointer_sur; eauto.
  destruct H0.
  split; try assumption.
  unfold Mem.weak_valid_pointer. rewrite H1.
  simpl. reflexivity.
Qed.

Lemma weak_valid_pointer_alloc_pres :
  forall m b z lo hi m' b',
    Mem.weak_valid_pointer m b z = true ->
    Mem.alloc m lo hi = (m',b') ->
    Mem.weak_valid_pointer m' b z = true.
Proof.
  intros.
  rewrite Mem.weak_valid_pointer_spec in *.
  destruct H;
    repeat erewrite Mem.valid_pointer_nonempty_perm in *;
    eapply Mem.perm_alloc_1 in H0.
  left. eauto. eauto.
  right. eauto. eauto.
Qed.

Lemma psur_alloc :
  forall md b ofs bits m,
    match_metadata md m ->
    psur md bits = Some (b,ofs) ->
    forall lo hi b' m',
      Mem.alloc m lo hi = (m',b') ->
      psur (md_alloc md lo hi b') bits = Some (b,ofs).
Proof.
  intros.
  assert (match_metadata (md_alloc md lo hi b') m').
  eapply match_alloc; eauto.
  erewrite weak_valid_pointer_sur in *; eauto.
  destruct H0.
  split. eapply pinj_extends; eauto.
  econstructor.
  eapply weak_valid_pointer_alloc_pres; eauto.
Qed.

Lemma weak_valid_pointer_free_pres :
  forall m b z lo hi m' b',
    Mem.weak_valid_pointer m b z = true ->
    Mem.free m b' lo hi  = Some m' ->
    (b <> b' \/ z < lo - 1 \/ hi < z) ->
    Mem.weak_valid_pointer m' b z = true.
Proof.
  intros.
  rewrite Mem.weak_valid_pointer_spec in *.
  destruct H;
    repeat erewrite Mem.valid_pointer_nonempty_perm in *;
    eapply Mem.perm_free_1 in H0.
  left. eauto. 
  destruct H1. left. congruence.
  right. omega. eauto. 
  right. eauto. 
  destruct H1. left. congruence.
  right. omega. eauto. 
Qed.

Lemma psur_free :
  forall md b ofs bits m,
    match_metadata md m ->
    psur md bits = Some (b,ofs) ->
    forall lo hi b' m',
      Mem.free m b' lo hi = Some m' ->
      (b <> b' \/ Int.unsigned ofs < lo - 1 \/ hi < Int.unsigned ofs) ->
      psur (md_free md lo hi b') bits = Some (b,ofs).
Proof.
  intros.
  assert (match_metadata (md_free md lo hi b') m').
  eapply match_free; eauto.
  erewrite weak_valid_pointer_sur in *; eauto.
  destruct H0.
  split. eapply pinj_extends; eauto.
  econstructor.
  eapply weak_valid_pointer_free_pres; eauto.
Qed.

      

(* inject and surject are inverses *)
Lemma pinj_psur_inverse :
  forall t m bits b ofs,
    match_metadata t m ->
    psur t bits = Some (b,ofs) ->
    pinj t b ofs = Some bits.
Proof.
  intros.
  eapply weak_valid_pointer_sur in H0; eauto.
  destruct H0. assumption.
Qed.

Ltac unify_psur :=
  match goal with
    | [ H : psur ?Y ?X = _ , H2 : psur ?Y ?X = _ |- _ ] => rewrite H in H2; inv H2
  end.

Ltac unify_pinj :=
  match goal with
    | [ H : pinj ?X ?Y ?Z = _, H2 : pinj ?X ?Y ?Z = _ |- _ ] => rewrite H in H2; inv H2
  end.

