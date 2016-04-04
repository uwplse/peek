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
Require Import PtrEquiv.
Require Import MemBits.
Require Import Zlen.
Require Import GlobalPerms.
Require Import SameSizeChunk.

Definition mem_nextblock_same (m m' : mem) : Prop :=
  Mem.nextblock m = Mem.nextblock m'.

Definition mem_perm_same (m m' : mem) :=
  forall b x p,
    (Mem.mem_access m) !! b x Cur = Some p ->
    (Mem.mem_access m') !! b x Cur = Some p.

Lemma perm_same_imp :
  forall m m',
    mem_perm_same m m' ->
    forall b x p,
      Mem.perm m b x Cur p ->
      Mem.perm m' b x Cur p.
Proof.
  intros. unfold mem_perm_same in *.
  unfold Mem.perm in *.
  unfold Mem.perm_order' in *.
  break_match_hyp; try inv_false.
  app H Heqo. collapse_match.
  assumption.
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
  intros.
  app mem_alloc_nextblock H0.
  break_and. exists x. rewrite H0. split. reflexivity.
  unfold mem_perm_same in H.
  unfold mem_perm_same.
  intros.
  erewrite Mem.alloc_access_result in H4 by eauto.
  erewrite Mem.alloc_access_result by eauto.
  destruct (peq b0 (Mem.nextblock m)). subst.
  unfold mem_nextblock_same in H2. rewrite <- H2.  
  rewrite PMap.gss in *. 
  assumption.
  unfold mem_nextblock_same in H2. rewrite <- H2.  
  rewrite PMap.gso in * by congruence.
  eapply H; eauto.
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
  assert (Mem.range_perm m' b lo hi Cur Freeable).
  app Mem.free_range_perm H0.
  unfold Mem.range_perm. intros.
  unfold Mem.range_perm in H0.
  specialize (H0 ofs H2).
  unfold Mem.perm in *.
  unfold Mem.perm_order' in *.
  break_match_hyp; try congruence.
  app H Heqo.
  collapse_match. eauto.
  inv_false.

  app Mem.range_perm_free H1.
  destruct H1. rewrite e.
  exists x. split. reflexivity.
  unfold mem_perm_same. intros.
  app Mem.free_result H0.
  app Mem.free_result e. subst.
  unfold Mem.unchecked_free in *.
  simpl in *.
  clear H4. clear H3.
  destruct (peq b b0); subst;
  repeat rewrite PMap.gss in *; repeat rewrite PMap.gso in * by congruence;
  try break_match;
  try apply H;
  try congruence.
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

Lemma perm_same_valid_access :
  forall m m',
    mem_perm_same m m' ->
    forall c b ofs p,
      Mem.valid_access m c b ofs p ->
      Mem.valid_access m' c b ofs p.
Proof.
  intros.
  unfold Mem.valid_access in *.
  break_and. split; auto.
  unfold Mem.range_perm in *.
  intros. specialize (H0 _ H2).
  eapply perm_same_imp; eauto.
Qed.

Lemma mem_store_perm_same :
  forall m m',
    mem_perm_same m m' ->
    forall c b ofs v v' m0,
      Mem.store c m b ofs v = Some m0 ->
      exists m'0,
        store_bits c m' b ofs v' = Some m'0 /\ mem_perm_same m0 m'0.
Proof.
  intros.
  unfold mem_perm_same in H.
  app Mem.store_valid_access_3 H0.
  app perm_same_valid_access H0.
  unfold store_bits.
  break_match.
  eexists. split.
  reflexivity.
  unfold mem_perm_same.
  simpl.
  intros. 
  app Mem.store_access H1.
  eapply H; try congruence.
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
      Mem.store c m b ofs v = Some m0 ->
      exists m'0,
        store_bits c m' b ofs v' = Some m'0 /\ mem_nextblock_same m0 m'0.
Proof.
  intros.
  app mem_store_perm_same H.
  break_and.
  exists x. split. eassumption.

  app Mem.nextblock_store H1.
  app nextblock_store_bits H.
  unfold mem_nextblock_same in *.
  congruence.
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


Definition wf_frag_bits (m : memory_chunk) (v : val) ( l : list memval) :=
  l = encode_val_bits m v.

  Ltac dl m n H0 :=
    destruct m; simpl in H0; try congruence;
    match goal with
      | [ H : context[Val.eq ?X ?Y] |- _ ] => destruct (Val.eq X Y)
    end;
    simpl in H0;
    try congruence;
    match goal with
      | [ H : context[quantity_eq ?X ?Y] |- _ ] => destruct (quantity_eq X Y)
    end;
    simpl in H0;
    try congruence;
    repeat (destruct n; simpl in H0; try congruence);
    subst.


Lemma check_value_length :
  forall l q v,
    check_value (size_quantity_nat q) v q l = true ->
    length l = size_quantity_nat q.
Proof.
  intros;
  do 8 (try destruct l); destruct q;
  simpl in *; try congruence;
  dl m n H; dl m0 n H; dl m1 n H;
  dl m2 n H; dl m3 n H; dl m4 n H;
  dl m5 n H; dl m6 n H.
  destruct l. reflexivity. congruence.
Qed.

Lemma check_value_wf_64 :
  forall v l,
    check_value (size_quantity_nat Q64) v Q64 l = true ->
    wf_frag Many64 v l.
Proof.
  intros.
  app check_value_length H.
  simpl in H.
  do 9 (try destruct l);
    simpl in H;
    try omega.


  dl m n H0.
  dl m0 n H0.
  dl m1 n H0.
  dl m2 n H0.
  dl m3 n H0.
  dl m4 n H0.
  dl m5 n H0.
  dl m6 n H0.
  unfold wf_frag.
  unfold encode_val.
  split. Focus 2. eexists. eexists.
  f_equal. unfold size_quantity_nat. instantiate (2 := Q64). simpl. reflexivity.
  break_match; unfold inj_value; simpl; reflexivity.
Qed.

Lemma check_value_wf_32 :
  forall chunk v l b o i s,
    (chunk = Mint32 /\ (v = Vptr b o)) \/
    (chunk = Many32 /\ (v = Vptr b o \/ v = Vint i \/ v = Vsingle s)) ->
    check_value (size_quantity_nat Q32) v Q32 l = true ->
    wf_frag chunk v l.
Proof.
  intros.
  app check_value_length H0.
  simpl in H.
  do 5 (try destruct l);
    simpl in H0;
    try omega.

  dl m n H1.
  dl m0 n H1.
  dl m1 n H1.
  dl m2 n H1.
  unfold wf_frag.
  repeat break_or; split. break_and.
  unfold encode_val.
  subst.
  reflexivity. 
  exists Q32. eexists. reflexivity.
  
  unfold encode_val.
  break_and. subst.
  repeat break_or; subst; reflexivity.
  exists Q32. eexists. reflexivity.
Qed.

Lemma malformed_load_undef :
  forall m v l q n,
    ~ wf_frag m v (Fragment v q n :: l) ->
    (decode_val m (Fragment v q n :: l) = Vundef \/
     (wf_frag Many32 v (Fragment v q n :: l) /\ exists i, v = Vint i)).
Proof.
  intros.
  destruct m; simpl; auto;
  unfold decode_val;
  break_match;
  simpl in Heqo; try congruence;
  unfold proj_value;
  break_match; unfold Val.load_result;
  simpl; try solve [left; reflexivity];
  try break_match; try solve [left; reflexivity];
  try solve [
        app (check_value_wf_32 Mint32) Heqb; congruence
      ];
  try solve [
        app (check_value_wf_32 Many32) Heqb; congruence
      ];
  try solve [
        app check_value_wf_64 Heqb; congruence
      ].
  Grab Existential Variables.
  exact Float32.zero. 
  exact Int.zero.
  exact Int.zero.
  exact Int.zero.
  exact xH.
  exact Float32.zero.
  exact Int.zero.
  exact xH.
  exact Float32.zero.
  exact Int.zero.
  exact xH.
  exact Float32.zero.
  exact Int.zero.
Qed.

Definition frag_equiv (t : allocator_metadata) (b b' : ZMap.t memval) (z : Z) : Prop :=
  match ZMap.get z b with
    | Fragment (Vptr blk ofs) Q32 3 =>
      forall m,
        (m = Mint32 \/ m = Many32) ->
        wf_frag m (Vptr blk ofs) (Mem.getN 4 z b) ->
        exists v',
          wf_frag_bits m v' (Mem.getN 4 z b') /\
          ptr_equiv_val t (Vptr blk ofs) v'
    | Fragment (Vint i) Q32 3 =>
      forall m,
        (m = Mint32 \/ m = Many32) ->
        wf_frag m (Vint i) (Mem.getN 4 z b) ->
        exists v',
          wf_frag_bits m v' (Mem.getN 4 z b') /\
          ptr_equiv_val t (Vint i) v'
    | Fragment Vundef q n => True
    | Fragment v q n =>
      (n = size_quantity_nat q - 1)%nat ->
      forall m,
        wf_frag m v (Mem.getN (size_quantity_nat q) z b) ->
        exists v',
          wf_frag_bits m v' (Mem.getN (size_quantity_nat q) z b') /\
          ptr_equiv_val t v v'
    | Byte bits => ZMap.get z b' = Byte bits
    | Undef => True
  end.

Definition no_pointer (b : ZMap.t memval) (z : Z) :=
  match ZMap.get z b with
    | Fragment v _ _ => forall b o, v <> Vptr b o
    | _ => True
  end.

Definition contents_equiv (t : allocator_metadata) (c c' : PMap.t (ZMap.t memval)) :=
  forall b ofs,
    frag_equiv t (c !! b) (c' !! b) ofs /\ no_pointer (c' !! b) ofs.

Lemma encode_val_bits_length :
  forall chunk v,
    length (encode_val_bits chunk v) = size_chunk_nat chunk.
Proof.
  intros.
  destruct chunk; unfold encode_val_bits; unfold size_chunk_nat;
  destruct v; simpl; unfold Pos.to_nat; simpl;
  reflexivity.
Qed.

Lemma inj_bytes_byte :
  forall y x,
    x <> nil ->
    y = inj_bytes x ->
    exists bits l,
      y = Byte bits :: l.
Proof.
  intros.
  rewrite H0.
  destruct x; try congruence.
  unfold inj_bytes.
  simpl. eexists; eauto.
Qed.

Lemma encode_int_not_nil :
  forall n x,
    (n > 0)%nat ->
    encode_int n x <> nil.
Proof.
  intros. destruct n; try omega.
  unfold encode_int.
  simpl. unfold rev_if_be.
  break_match; try congruence.
  simpl.
  match goal with
    | [ |- ?X ++ _ <> nil ] => destruct X
  end; simpl; congruence.
Qed.

Lemma wf_frag_inv :
  forall m v m' v',
    wf_frag m v (encode_val m' v') ->
    (m = m' \/ (m = Many32 /\ m' = Mint32) \/ (m = Mint32 /\ m' = Many32)) /\ v = v'.
Proof.
  intros. unfold wf_frag in H.
  break_and. repeat break_exists.
  unfold encode_val in H0.
  do 2 break_match_hyp;
    subst;
    simpl in H0; try congruence;
    unfold inj_value in *; simpl in H0;
    inv H0;
  try solve [
  unfold encode_val in H; break_match;
    unfold inj_value in H;
    simpl in H; try congruence;
    eauto];
  unfold encode_val in H; break_match;
  unfold inj_value in H;
    simpl in H; try congruence;
    eauto;
    try app inj_bytes_byte H;
    try congruence;
    apply encode_int_not_nil;
    omega.
Qed.

Lemma wf_frag_length_size :
  forall m v l,
    wf_frag m v l ->
    size_chunk_nat m = length l.
Proof.
  unfold wf_frag; intros.
  break_and. subst. repeat break_exists.
  unfold encode_val in H.
  repeat break_match; simpl; try inv H;
  simpl; reflexivity.
Qed.

Lemma of_nat_length :
  forall chunk,
    Z.of_nat (size_chunk_nat chunk) = size_chunk chunk.
Proof.
  destruct chunk; simpl; omega.
Qed.

Lemma getN_setN_same :
  forall vl p c n,
    n = length vl ->
    Mem.getN n p (Mem.setN vl p c) = vl.
Proof.
  intros. subst n.
  apply Mem.getN_setN_same.
Qed.


Lemma Zplus_comm :
  forall (x y : Z),
    x + y = y + x.
Proof.
  intros. omega.
Qed.


Lemma wf_frag_only_lengths :
  forall m v l,
    wf_frag m v l ->
    length l = 4%nat \/ length l = 8%nat.
Proof.
  intros.
  app wf_frag_length_size H.
  rewrite <- H.
  destruct m; simpl; eauto;
  unfold wf_frag in H0;
  break_and; unfold encode_val in *;
  break_match_hyp;
  repeat break_exists;
  subst l; simpl in *;
  try congruence;
  unfold inj_bytes in *; unfold encode_int in *;
  unfold rev_if_be in *; break_match_hyp; simpl in *; try congruence.
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


Lemma getN_get :
  forall chunk ofs c h l,
    Mem.getN (size_chunk_nat chunk) ofs c = h :: l ->
    ZMap.get ofs c = h.
Proof.
  intros; destruct chunk; simpl in H; inv H; reflexivity.
Qed.

Lemma nth_succ_encode_head_frag_false :
  forall n v v' m q,
    nth (Datatypes.S n) (encode_val m v) Undef = Fragment v' q (size_quantity_nat q - 1) ->
    False.
Proof.
  intros. destruct m; destruct v; simpl in H; try break_match_hyp; try congruence;
          unfold inj_bytes in H; unfold encode_int in H; simpl in H;
          unfold rev_if_be in *; try break_match_hyp; simpl in H; try break_match_hyp; try congruence;
          do 8 (try break_match_hyp; try congruence);
          destruct q; simpl in H; inv H.
Qed.

Lemma get_last_part_malformed :
  forall n chunk m v z v0 ofs c,
    ofs < z < ofs + size_chunk chunk ->
    ~wf_frag m v (Mem.getN n z (Mem.setN (encode_val chunk v0) ofs c)).
Proof.
  intros. intro.
  app wf_frag_only_lengths H0.
  break_or.
  * assert (n = 4%nat).
      rewrite <- H2.
      rewrite Mem.getN_length. reflexivity.
    subst n.
    unfold wf_frag in H1.
    break_and. repeat break_exists.
    simpl in H1. inv H1.
    rewrite setN_get_nth in H4. Focus 2. rewrite encode_val_length.
    rewrite of_nat_length. omega.
    assert (0 < z - ofs) by omega.
    app Z2Nat.inj_lt H1; try omega. simpl in H1.
    destruct (Z.to_nat (z - ofs)); try omega.
    app nth_succ_encode_head_frag_false H4.
  * assert (n = 8%nat).
      rewrite <- H2.
      rewrite Mem.getN_length. reflexivity.
    subst n.
    unfold wf_frag in H1.
    break_and. repeat break_exists.
    simpl in H1. inv H1.
    rewrite setN_get_nth in H4. Focus 2. rewrite encode_val_length.
    rewrite of_nat_length. omega.
    assert (0 < z - ofs) by omega.
    app Z2Nat.inj_lt H1; try omega. simpl in H1.
    destruct (Z.to_nat (z - ofs)); try omega.
    app nth_succ_encode_head_frag_false H4.
Qed.


Lemma nth_zero_encode_non_head_frag_false :
  forall v v' m q k,
    (k < size_quantity_nat q - 1)%nat ->
    nth O (encode_val m v) Undef = Fragment v' q k ->
    False.
Proof.
  intros.
  destruct m; destruct v; simpl in H0; try break_match_hyp; try congruence;
  unfold inj_bytes in H0; unfold encode_int in H0; simpl in H0;
  unfold rev_if_be in *; try break_match_hyp; simpl in H0; try break_match_hyp; try congruence;
  do 8 (try break_match_hyp; try congruence);
  destruct q; simpl in H0; inv H0;
  simpl in *; try omega.
Qed.

Lemma encode_head_non_head_frag_false :
  forall v v' m q k l,
    (k < size_quantity_nat q - 1)%nat ->
    encode_val m v = Fragment v' q k :: l ->
    False.
Proof.
  intros.
  eapply nth_zero_encode_non_head_frag_false. apply H.
  instantiate (3 := m). instantiate (1 := v'). instantiate (1 := v).
  rewrite H0. simpl. reflexivity.
Qed.

Lemma Pos_to_nat_gtz :
  forall x,
    (Pos.to_nat x > 0)%nat.
Proof.
  intros.
  destruct (Pos2Nat.is_succ x).
  omega.
Qed.


Lemma getN_firstn :
  forall n z l c,
    (length l > n)%nat ->
    Mem.getN n z (Mem.setN l z c) = firstn n l.
Proof.
  induction n; intros.
  * simpl. reflexivity.
  * simpl.
    destruct l; simpl in H; try omega.
    simpl. rewrite IHn by omega.
    rewrite Mem.setN_outside by omega.
    rewrite ZMap.gss. reflexivity.
Qed.

Lemma getN_setN_tail :
  forall n z ofs,
    z < ofs < z + Z.of_nat n ->
    forall h l c,
    exists l' l'',
      Mem.getN n z (Mem.setN (h :: l) ofs c) = l' ++ h :: l'' /\ length l' = Z.to_nat (ofs - z).
Proof.
  induction n; intros.
  simpl in H. omega.
  simpl. rewrite Mem.setN_outside by omega.
  assert (z + 1 = ofs \/ z + 1 < ofs) by omega. 
  destruct H0. subst ofs.
  rewrite ZMap.gso by (rewrite Zplus_comm; apply z_neq; omega).
  destruct n. simpl in H. omega.
  simpl.
  rewrite Mem.setN_outside by omega.
  rewrite ZMap.gss. exists (ZMap.get z c :: nil).
  exists (Mem.getN n (z + 1 + 1)
                   (Mem.setN l (z + 1 + 1) (ZMap.set (z + 1) h c))).
  split; try reflexivity.
  replace (z + 1 - z) with 1 by omega.
  simpl. reflexivity.
  assert (z+1 < ofs < z+1 + (Z.of_nat n)). split; try omega.
  simpl in H.
  rewrite Zpos_P_of_succ_nat in H. omega.
  edestruct (IHn (z + 1) ofs H1 h l c). destruct H2.
  break_and.  simpl in H2. rewrite H2.
  rewrite ZMap.gso. exists (ZMap.get z c :: x). exists x0.
  split. simpl. reflexivity. simpl. rewrite H3.
  rewrite <- Z2Nat.inj_succ by omega. f_equal. omega.
  destruct (Z.eq_dec z ofs); auto. omega.
Qed.

Lemma encode_val_not_nil :
  forall m v,
    encode_val m v <> nil.
Proof.
  destruct m; destruct v; simpl; try congruence;
  unfold encode_int; unfold inj_value; simpl;
  unfold rev_if_be; try break_match; simpl;
  try congruence.
Qed.

Lemma get_before_beginning_malformed :
  forall n chunk m v z v0 ofs c,
    z < ofs < z + Z.of_nat n ->
    ~wf_frag m v (Mem.getN n z (Mem.setN (encode_val chunk v0) ofs c)).
Proof.
  intros. intro.
  app wf_frag_only_lengths H0.
  break_or.
  * assert (n = 4%nat).
      rewrite <- H2.
      rewrite Mem.getN_length. reflexivity.
    subst n.
    app wf_frag_length_size H1.
    rewrite H2 in H1.
    destruct (encode_val chunk v0) eqn:?. app encode_val_not_nil Heql.
    app getN_setN_tail H. break_and.
    rewrite H in H0. 
    assert (0 < ofs - z < 4). simpl in H3. omega.
    unfold wf_frag in H0. repeat break_and. repeat break_exists.
    app Z2Nat.inj_lt H5; try omega.
    app Z2Nat.inj_lt H6; try omega.
    simpl in H5. simpl in H6. unfold Pos.to_nat in H6. simpl in H6.
    do 4 (try destruct x; simpl in H4; try omega);
      rewrite <- H4 in *; simpl in H8;
      inv H8; destruct m; destruct v; simpl in H0; inv H0;
      match goal with
        | [ H : encode_val _ _ = _ :: _ |- _ ] => app encode_head_non_head_frag_false H
      end;
      simpl; omega.

  * assert (n = 8%nat).
      rewrite <- H2.
      rewrite Mem.getN_length. reflexivity.
    subst n.
    app wf_frag_length_size H1.
    rewrite H2 in H1.
    destruct (encode_val chunk v0) eqn:?. app encode_val_not_nil Heql.
    app getN_setN_tail H. break_and.
    rewrite H in H0. 
    assert (0 < ofs - z < 8). simpl in H3. omega.
    unfold wf_frag in H0. repeat break_and. repeat break_exists.
    app Z2Nat.inj_lt H5; try omega.
    app Z2Nat.inj_lt H6; try omega.
    simpl in H5. simpl in H6. unfold Pos.to_nat in H6. simpl in H6.
    do 8 (try destruct x; simpl in H4; try omega);
      rewrite <- H4 in *; simpl in H8;
      inv H8; destruct m; destruct v; simpl in H0; inv H0;
      match goal with
        | [ H : encode_val _ _ = _ :: _ |- _ ] => app encode_head_non_head_frag_false H
      end;
      simpl; omega.

Qed.

Lemma wf_frag_getN_aligned :
  forall m v n z chunk v0 ofs c,
    wf_frag m v (Mem.getN n z (Mem.setN (encode_val chunk v0) ofs c)) ->
    z = ofs \/ z + Z.of_nat n <= ofs \/ z >= ofs + size_chunk chunk.
Proof.
  intros.
  assert (Hrange : ((z = ofs \/ z + Z.of_nat n <= ofs \/ z >= ofs + size_chunk chunk) \/
           (ofs < z < ofs + size_chunk chunk) \/
           (ofs < z + Z.of_nat n /\ z < ofs))) by omega.
  destruct Hrange. auto.
  exfalso.

  (* Now we just need contradiction *)
  destruct H0.
  * (* z gets something starting from middle of encode *)
    eapply get_last_part_malformed; eauto. 

    
  * (* z gets something ending with start of encode *)
    eapply get_before_beginning_malformed; eauto. omega.
Qed.



Lemma nth_inj_bytes :
  forall l n,
  exists r,
    nth n (inj_bytes l) Undef = r /\
    (r = Undef \/ (exists bits, r = Byte bits)).
Proof.
  induction l; intros.
  simpl. break_match; exists Undef; split; eauto.
  simpl. break_match.
  exists (Byte a). split; eauto.
  destruct (IHl n0).
  exists x. eauto.
Qed.

Lemma ptr_equiv_encode_undef :
  forall t v v',
    ptr_equiv_val t v v' ->
    forall z ofs chunk,
      ofs <= z < ofs + Z.of_nat (size_chunk_nat chunk) ->
      nth (Z.to_nat (z - ofs)) (encode_val chunk v) Undef = Undef ->
      exists r,
        nth (Z.to_nat (z - ofs)) (encode_val_bits chunk v') Undef = r.
Proof.
  intros.
  unfold ptr_equiv_val in H.
  break_match_hyp;
    repeat break_or;
    repeat break_exists;
    repeat break_and;
    destruct chunk;
    subst;
    simpl;
  try solve [
  eexists;
        repeat break_match; try reflexivity; eauto
      ];
  eexists; reflexivity.
Qed.

Lemma ptr_equiv_encode_byte :
  forall t v v',
    ptr_equiv_val t v v' ->
    forall z ofs chunk,
      ofs <= z < ofs + Z.of_nat (size_chunk_nat chunk) ->
      forall bits,
        nth (Z.to_nat (z - ofs)) (encode_val chunk v) Undef = Byte bits ->
        nth (Z.to_nat (z - ofs)) (encode_val_bits chunk v') Undef = Byte bits.
Proof.
  intros.
  unfold ptr_equiv_val in H.
  break_match_hyp;
    repeat break_or;
    repeat break_exists;
    repeat break_and;
    destruct chunk;
    subst;
    simpl in *;
    repeat break_match_hyp;
    congruence.
Qed.

Lemma wf_frag_ptr_equiv :
  forall t v v',
    ptr_equiv_val t v v' ->
    forall m chunk,
      wf_frag m v (encode_val chunk v) ->
      wf_frag_bits m v' (encode_val_bits chunk v').
Proof.
  intros.
  unfold ptr_equiv_val in H.
  break_match_hyp;
    repeat break_or;
    repeat break_exists;
    repeat break_and;
    destruct chunk;
    subst;
    unfold wf_frag in H0; unfold wf_frag_bits;
    simpl in *;
    repeat break_match_hyp;
    simpl in *;
    repeat break_and;
    unfold inj_value in *;
    unfold inj_bytes in *;
    simpl in *;
    try congruence;
    repeat break_exists;
    try congruence;
  
  unfold encode_int in *; simpl in *;
  unfold rev_if_be in *; break_match;
  simpl in *; congruence.
Qed.





(* Don't go back before this *)

(* This is necessary. *)
(* We need this true *)
Lemma frag_equiv_pres :
  forall t c c' z,
    frag_equiv t c c' z ->
    forall v v',
      ptr_equiv_val t v v' ->
      forall chunk ofs,
        frag_equiv t (Mem.setN (encode_val chunk v) ofs c)
                   (Mem.setN (encode_val_bits chunk v') ofs c') z.
Proof.
  intros.
  name (encode_val_length chunk v) evl.
  name (encode_val_bits_length chunk v') evl'.
  unfold frag_equiv.
  break_match; repeat break_exists;
  eauto.
  assert (Hrange : (z < ofs \/ z >= ofs + Z.of_nat (size_chunk_nat chunk)) \/
          (ofs <= z < ofs + Z.of_nat (size_chunk_nat chunk))) by omega.
  destruct Hrange.
  repeat rewrite Mem.setN_outside in * by omega.
  unfold frag_equiv in H.
  rewrite Heqm in H. eauto.
  erewrite <- encode_val_length in H1.
  instantiate (1 := v) in H1.
  rewrite setN_get_nth in Heqm by omega.
  repeat rewrite setN_get_nth by omega.
  app ptr_equiv_encode_byte Heqm; omega.

  name (of_nat_length chunk) ofl.
  name (of_nat_length chunk) ofl'.
  rewrite <- evl in ofl.
  rewrite <- evl' in ofl'.
  
  
  unfold size_quantity_nat;
    destruct v0; destruct q;
    repeat break_match;
    intros;
    auto;
    try solve [simpl in *; omega];
    match goal with
      | [ H : wf_frag _ _ _ |- _ ] =>
        app wf_frag_getN_aligned H

    end;
    match goal with
      | [ H : wf_frag _ _ _ |- _ ] =>
        app wf_frag_length_size H
    end;
    rewrite Mem.getN_length in H3;
    break_or;
    try (
        rewrite Mem.setN_outside in Heqm by (simpl in H5; rewrite evl; omega);
        rewrite Mem.getN_setN_outside in H4 by omega;
        rewrite Mem.getN_setN_outside by omega;
        unfold frag_equiv in H;
        rewrite Heqm in H;
        apply H;
        eauto
      );
  rewrite <- H3 in H4;
  app same_size_chunk H4;
  repeat rewrite getN_setN_same in * by omega;
  eexists; split;
  try match goal with
    | [ H : wf_frag _ _ _ |- _ ] => app wf_frag_inv H; break_and; subst v
  end;
  try match goal with
    | [ H : ptr_equiv_val _ _ |- _ ] => app wf_frag_ptr_equiv H
  end;
  try eapply wf_frag_ptr_equiv; eauto;
  assumption.
  
Qed.


Lemma getN_in_or_out :
  forall l ofs ofs0 c r,
    ZMap.get ofs0 (Mem.setN l ofs c) = r ->
    In r l \/ ZMap.get ofs0 c = r.
Proof.
  induction l; intros.
  simpl in H. right. auto.
  simpl in H. app IHl H.
  destruct H. left. simpl. right. auto.
  assert (ofs = ofs0 \/ ofs <> ofs0) by omega.
  destruct H1. subst ofs. rewrite ZMap.gss in H.
  simpl. left. left. auto.
  rewrite ZMap.gso in H by congruence.
  right. auto.
Qed.

Lemma frag_not_in_inj_bytes :
  forall x v q n,
    ~ In (Fragment v q n) (inj_bytes x).
Proof.
  induction x; intros. simpl.
  auto.
  simpl. 
  apply Classical_Prop.and_not_or.
  split; try congruence.
  apply IHx.
Qed.

Lemma no_pointer_ptr_equiv :
  forall t v v',
    ptr_equiv_val t v v' ->
    forall c,
      (forall ofs, no_pointer c ofs) ->
      forall chunk ofs0 ofs,
        no_pointer (Mem.setN (encode_val_bits chunk v') ofs c) ofs0.
Proof.
  intros.
  unfold no_pointer.
  break_match; auto.
  intros.
  app getN_in_or_out Heqm.
  destruct Heqm.
  Focus 2. unfold no_pointer in H0.
  specialize (H0 ofs0).
  rewrite H2 in H0.
  apply H0.

  unfold ptr_equiv_val in H.
  break_match_hyp;
    repeat break_or;
    repeat break_exists;
    repeat break_and;
    destruct chunk;
    subst;
    simpl in H2;
    repeat break_or;
    try congruence;
  try app frag_not_in_inj_bytes H2.
Qed.

Lemma contents_equiv_pres :
  forall t mc mc',
    contents_equiv t mc mc' ->
    forall v v',
      ptr_equiv_val t v v' ->
      forall chunk b ofs,
        contents_equiv t (PMap.set b (Mem.setN (encode_val chunk v) ofs mc !! b) mc)
                       (PMap.set b (Mem.setN (encode_val_bits chunk v') ofs mc' !! b) mc').
Proof.
  intros.
  unfold contents_equiv in *.

  intros. destruct (peq b b0). subst.
  split.
  repeat rewrite PMap.gss. app frag_equiv_pres H0.
  apply H. rewrite PMap.gss.
  eapply no_pointer_ptr_equiv; eauto.
  apply H.
  repeat rewrite PMap.gso by congruence.
  apply H.
Qed.

Definition mem_contents_equiv (t : allocator_metadata) (m m' : mem) :=
  match_metadata t m /\ match_metadata t m' /\
  contents_equiv t (Mem.mem_contents m) (Mem.mem_contents m').

Lemma mem_contents_equiv_store :
  forall t m m',
    mem_perm_same m m' ->
    mem_contents_equiv t m m' ->
    forall v v',
      ptr_equiv_val t v v' ->
      forall c b i m'',
        Mem.store c m b i v = Some m'' ->
        exists m''',
          (store_bits c m' b i v' = Some m''' /\
           mem_perm_same m m' /\
           mem_contents_equiv t m'' m''').
Proof.
  intros.
  app mem_store_perm_same H2.
  break_and.
  eexists; split. eauto.
  split.
  app Mem.store_mem_contents H3.
  name H2 Hst_bits.
  unfold store_bits in H2.
  break_match_hyp; try congruence.
  unfold mem_contents_equiv. split.
  eapply match_store; eauto.
  unfold mem_contents_equiv in H0.
  repeat break_and. eauto.
  split. eapply match_store_bits; eauto.
  unfold mem_contents_equiv in *. repeat break_and.
  eauto.
  inv H2.
  unfold mem_contents_equiv in H0.
  repeat break_and.
  simpl. app Mem.store_mem_contents H3.  
  rewrite H3. eapply contents_equiv_pres; eauto.
Qed.

Lemma ptr_equiv_undef_anything :
  forall t v,
    (forall b ofs, v <> Vptr b ofs) ->
    ptr_equiv_val t Vundef v.
Proof.
  intros. unfold ptr_equiv_val.
  destruct v. left. auto.
  right. left. eauto.
  right. right. right. right. eauto.
  right. right. left. eauto.
  right. right. right. left. eauto.
  specialize (H b i). congruence.
Qed.

Tactic Notation "especialize" constr(H) "as" ident(H2) := 
  match type of H with
    | forall (x : ?X), _ =>
      let f := fresh "x" in
      evar (f : X);
        name (H f) H2;
          subst f
  end.

Lemma frag_equiv_proj_bytes :
  forall t c c',
    (forall ofs, frag_equiv t c c' ofs) ->
    forall chunk ofs l,
      proj_bytes (Mem.getN (size_chunk_nat chunk) ofs c) = Some l ->
      proj_bytes (Mem.getN (size_chunk_nat chunk) ofs c') = Some l.
Proof.
  intros.
  destruct chunk;
    simpl in H0;
    simpl;

  
  repeat match goal with
    | [ H : context[match (ZMap.get ?X ?Y) with _ => _ end], H2 : forall _, frag_equiv _ _ _ _ |- _ ] =>       
      let H4 := fresh "H" in
      destruct (ZMap.get X Y) eqn:H4;
        try congruence;
        let H3 := fresh "H" in
        especialize H2 as H3;
          unfold frag_equiv in H3;
          instantiate (1 := X) in H3;
          rewrite H4 in H3;
          try find_rewrite;
          clear H3;
          clear H4;
          eauto
         end.

Qed.

Lemma no_pointer_proj_value :
  forall c',
    (forall ofs, no_pointer c' ofs) ->
    forall chunk q ofs b o,
      proj_value q (Mem.getN (size_chunk_nat chunk) ofs c') <> Vptr b o.
Proof.
  intros. unfold proj_value.
  break_match. destruct chunk; simpl; congruence.
  break_match; try solve [
                     destruct chunk; simpl; congruence
                   ].
  break_match; try solve [
                     destruct chunk; simpl; congruence
                   ].
  do 2 try break_match;
    try congruence; subst;
  unfold no_pointer in H;
  simpl in Heql; inv Heql;
  specialize (H ofs).
  destruct (size_chunk_nat chunk) eqn:?.
  destruct chunk; simpl in Heqn0;
  unfold size_chunk_nat in Heqn0;
  simpl in Heqn0; unfold Pos.to_nat in Heqn0;
  simpl in Heqn0; try congruence.
  simpl in H1. inv H1.
  rewrite H2 in H. apply H.
Qed.


Lemma quantity_chunk_same :
  forall q v chunk ofs c,
    check_value (size_quantity_nat q) v q (Mem.getN (size_chunk_nat chunk) ofs c) = true ->
    size_quantity_nat q = size_chunk_nat chunk.
Proof.
  intros.
  app check_value_length H.
  rewrite Mem.getN_length in H. congruence.
Qed.

Lemma frag_equiv_proj_value :
  forall t c c',
    (forall ofs, frag_equiv t c c' ofs) ->
    forall q chunk ofs v,
      proj_value q (Mem.getN (size_chunk_nat chunk) ofs c) = v ->
      ((v <> Vundef /\ size_chunk_nat chunk = 8%nat) \/
       (((exists i, v = Vint i) \/ (exists b o, v = Vptr b o) \/ (exists s, v = Vsingle s)) /\ size_chunk_nat chunk = 4%nat)) ->
      proj_bytes (Mem.getN (size_chunk_nat chunk) ofs c') = None ->
      exists v',
        proj_value q (Mem.getN (size_chunk_nat chunk) ofs c') = v' /\
        ptr_equiv_val t v v'.
Proof.
  
  intros.
  assert (size_chunk_nat chunk = 4%nat \/ size_chunk_nat chunk = 8%nat) by omega.
  destruct H3.
  break_or; try break_and; try congruence.
  repeat break_or; repeat break_exists;
  unfold proj_value in H0;
  repeat break_match_hyp; try congruence;
  subst v;
  app getN_get Heql;
  name Heqb HH; rewrite <- H0 in HH; app quantity_chunk_same HH;
  rewrite H1 in HH;
  rewrite H1 in *;
  destruct q; simpl in HH; try congruence;
  try (
      app (check_value_wf_32 Many32) H4);
  
  simpl in H5; rewrite Heql in H5;
  repeat match goal with
      | [ H : context[Val.eq ?X ?Y] |- _ ] => destruct (Val.eq X Y); try congruence
      | [ H : context[quantity_eq ?X ?Y] |- _ ] => destruct (quantity_eq X Y); simpl in H; try congruence
         end;
  subst;
  do 4 (try destruct n; simpl in H5; try congruence);

  unfold frag_equiv in H; specialize (H ofs);
  rewrite Heql in H;
  app H H4;
  clear H5.

  break_and. simpl in H5. subst x0. eexists.
  unfold wf_frag_bits in H4. rewrite H4 in H2.
  simpl in H2. rewrite proj_inj_bytes in H2. inv H2.

  break_and. simpl in H5. break_exists. break_and.
  subst x1.
  unfold wf_frag_bits in H4. rewrite H4 in H2.
  simpl in H2. rewrite proj_inj_bytes in H2. inv H2.

  break_and. simpl in H5. subst x0.
  unfold wf_frag_bits in H4. unfold size_quantity_nat in H4.
  rewrite H4. unfold encode_val_bits. rewrite proj_inj_value.
  eexists; split; try reflexivity.
  unfold proj_value. rewrite Heqb.
  apply ptr_equiv_nonpointers; intros; congruence.

  break_or; break_and; try congruence.
  unfold proj_value in H0.
  do 3 (break_match_hyp; try congruence).
  
  app getN_get Heql.
  name Heqb HH.
  rewrite <- H4 in HH.
  app quantity_chunk_same HH.
  rewrite H1 in HH.
  destruct q; simpl in HH; try congruence.
  app check_value_wf_64 H5.
  rewrite H4 in H6.

  simpl in H6;
  repeat match goal with
      | [ H : context[Val.eq ?X ?Y] |- _ ] => destruct (Val.eq X Y); try congruence
      | [ H : context[quantity_eq ?X ?Y] |- _ ] => destruct (quantity_eq X Y); simpl in H; try congruence
         end;
  subst;
  do 8 (try destruct n; simpl in H6; try congruence).

  unfold frag_equiv in H; specialize (H ofs);
  rewrite Heql in H; destruct v; try congruence;
  rewrite H1 in *; unfold size_quantity_nat in *;
  app H H5; try break_and;
  clear H6;

  unfold wf_frag_bits in *; rewrite H5 in *;
  simpl in H8; try break_exists; try break_and; subst;
  unfold encode_val_bits; rewrite proj_inj_value;
  eexists; split; try reflexivity;
  unfold proj_value; unfold size_quantity_nat; rewrite Heqb;
  try solve [apply ptr_equiv_nonpointers; intros; congruence].
  simpl. eexists; eauto.

  Grab Existential Variables.
  exact Vzero.
  exact Int.zero.
  exact Int.zero.
  exact xH.
  exact Float32.zero.
  exact Int.zero.
  exact Float32.zero.
  exact Int.zero.
  exact xH.
Qed.

Lemma proj_value_len :
  forall l q,
    size_quantity_nat q <> length l ->
    proj_value q l = Vundef.
Proof.
  intros; simpl.
  unfold proj_value. do 3 (break_match; try reflexivity).
  app check_value_length Heqb. rewrite Heqb in H. congruence.
Qed.

Lemma proj_value_frag_equiv :
  forall t c c',
    (forall ofs, frag_equiv t c c' ofs) ->
    (forall ofs, no_pointer c' ofs) ->
    forall q ofs chunk,
      proj_bytes (Mem.getN (size_chunk_nat chunk) ofs c') = None ->
      ptr_equiv_val t
        (Val.load_result chunk (proj_value q (Mem.getN (size_chunk_nat chunk) ofs c)))
        (Val.load_result chunk (proj_value q (Mem.getN (size_chunk_nat chunk) ofs c'))).
Proof.
  intros. unfold Val.load_result.
  destruct (Val.eq (proj_value q (Mem.getN (size_chunk_nat chunk) ofs c)) Vundef).
  * (* original is undef *)
    rewrite e.
    destruct chunk; apply ptr_equiv_undef_anything;
    try break_match; intros; try congruence;
    try app no_pointer_proj_value Heqv.
    apply no_pointer_proj_value; eauto.
  * (* original is not undef *)
    do 2 try break_match; try congruence;
    try solve [
          rewrite proj_value_len in Heqv by (
                                             rewrite Mem.getN_length;
                                             destruct q; simpl; auto;
                                             unfold size_chunk_nat; simpl;
                                             unfold Pos.to_nat; simpl;
                                             congruence); congruence];

        
    try (app frag_equiv_proj_value Heqv; break_and; try find_rewrite);
    try (break_match; subst; simpl in H4; congruence);
    try simpl in H4; try rewrite <- H4;
    try solve [
          apply ptr_equiv_nonpointers; intros; congruence];
    try break_match;
    try solve [
          apply ptr_equiv_nonpointers; intros; congruence];
    try solve [
          apply ptr_equiv_undef_anything; intros; congruence];
    try break_exists; try break_and; try congruence;
    try solve [app no_pointer_proj_value Heqv0; inv_false];
    try (
          app frag_equiv_proj_value Heqv; [break_and; rewrite H3 in Heqv0; subst x;
                                           simpl in H4; break_exists; break_and; congruence | idtac]);
    try solve [right; split; eauto];
    try solve [
          app frag_equiv_proj_value Heqv;
          try solve [right; split; eauto];
          break_and; rewrite H3 in Heqv0; subst x; assumption];
    try solve [
          app frag_equiv_proj_value Heqv;
          try solve [right; split; eauto];
          break_and; rewrite H3 in Heqv0; subst x; simpl in *; congruence].

    unfold ptr_equiv_val.
    break_match; try congruence;
    app frag_equiv_proj_value Heqv; try congruence;
    break_and; simpl in H4; try congruence.
    break_exists. break_and. subst.
    eexists; eauto.

Qed.
  
Lemma frag_equiv_decode :
  forall t c c',
    (forall ofs, frag_equiv t c c' ofs) ->
    (forall ofs, no_pointer c' ofs) ->
    forall chunk ofs,
      ptr_equiv_val t (decode_val chunk (Mem.getN (size_chunk_nat chunk) ofs c))
                    (decode_val chunk (Mem.getN (size_chunk_nat chunk) ofs c')).
Proof.
  intros. 
  
  unfold decode_val.
  break_match.
  app frag_equiv_proj_bytes Heqo.
  find_rewrite.
  break_match;
    apply ptr_equiv_nonpointers;
    intros; congruence.

  destruct chunk;
    try solve [
          break_match;
          try apply ptr_equiv_undef_anything;
          try apply ptr_equiv_nonpointers;
          try intros; try congruence];
    break_match;
    try solve [
          eapply proj_value_frag_equiv;
          eauto];
  unfold proj_value;
  do 3 (try break_match;
        try apply ptr_equiv_undef_int;
        try apply ptr_equiv_undef_long;
  try (apply ptr_equiv_nonpointers; intros; congruence)).
  destruct v; try apply ptr_equiv_undef_int.
  
  app (check_value_wf_32 Many32) Heqb.
  name Heqb Hwf.
  rewrite <- Heql0 in Hwf.
  simpl. unfold frag_equiv in H.
  simpl in Heql0. inv Heql0.
  specialize (H ofs).
  rewrite H3 in H.
  unfold wf_frag in Heqb.
  break_and. repeat break_exists.
  simpl in H2. unfold inj_value in H2.
  simpl in H2. inv H2. app H Hwf.
  break_and.
  unfold wf_frag_bits in H5.
  replace (size_chunk_nat Mint32) with (4%nat) in Heqo0 by (simpl; reflexivity).
  rewrite H5 in Heqo0.
  simpl in H6. subst x1.
  simpl in Heqo0.
  rewrite proj_inj_bytes in Heqo0. inv Heqo0.
  rewrite decode_encode_int_4. reflexivity.

  app (check_value_wf_32 Many32) Heqb.
  name Heqb Hwf.
  rewrite <- Heql0 in Hwf.
  simpl. unfold frag_equiv in H.
  simpl in Heql0. inv Heql0.
  specialize (H ofs).
  rewrite H3 in H.
  unfold wf_frag in Heqb.
  break_and. repeat break_exists.
  simpl in H2. unfold inj_value in H2.
  simpl in H2. inv H2. app H Hwf.
  break_and.
  unfold wf_frag_bits in H5.
  replace (size_chunk_nat Mint32) with (4%nat) in Heqo0 by (simpl; reflexivity).
  rewrite H5 in Heqo0.
  simpl in H6. unfold encode_val_bits in Heqo0.
  break_exists. break_and. subst x1.
  rewrite proj_inj_bytes in Heqo0. inv Heqo0.
  rewrite decode_encode_int_4. eauto.

  
  unfold Val.load_result. break_match; try solve [apply ptr_equiv_undef_int];
  app (check_value_wf_32 Many32) Heqb;
  name Heqb Hwf;
  rewrite <- Heql0 in Hwf;
  simpl; unfold frag_equiv in H;
  simpl in Heql0; inv Heql0;
  specialize (H ofs);
  rewrite H3 in H;
  unfold wf_frag in Heqb;
  break_and; repeat break_exists;
  simpl in H2; unfold inj_value in H2;
  simpl in H2; inv H2; app H Hwf;
  break_and;
  unfold wf_frag_bits in H5;
  replace (size_chunk_nat Many32) with (4%nat) in * by (simpl; reflexivity).
  rewrite H5 in Heqo0.
  simpl in H6. subst x1.
  simpl in Heqo0.
  rewrite proj_inj_bytes in Heqo0. inv Heqo0.
  rewrite decode_encode_int_4. reflexivity.

  simpl in H6. subst x1.
  replace (size_quantity_nat Q32) with (4%nat) in * by reflexivity.
  rewrite H5 in Heqo0. simpl in Heqo0. congruence.

  simpl in H6. break_exists. break_and. subst x1.
  replace (size_quantity_nat Q32) with (4%nat) in * by reflexivity.
  rewrite H5 in Heqo0. 
  unfold encode_val_bits in Heqo0.
  rewrite proj_inj_bytes in Heqo0. inv Heqo0.
  rewrite decode_encode_int_4. eauto.


  unfold Val.load_result. 
  app (check_value_wf_64) Heqb;
  name Heqb Hwf;
  rewrite <- Heql0 in Hwf.
  unfold frag_equiv in H.
  simpl in Heql0; inversion Heql0;
  specialize (H ofs). clear Heql0. clear H4.
  rewrite H3 in H;
  unfold wf_frag in Heqb;
  break_and; repeat break_exists.
  destruct v; simpl in H2; try (apply ptr_equiv_nonpointers; intros; congruence);
  unfold inj_value in H2; simpl in H2; inversion H2; inv H4;
  subst x;
  replace (size_quantity_nat Q64) with (8%nat) in * by reflexivity;
  replace (size_chunk_nat Many64) with (8%nat) in * by (simpl; reflexivity);
  app H Hwf;
  
  break_and;
    unfold wf_frag_bits in H5;
    simpl;
    rewrite H5 in Heqo0; simpl in H6;
    try (subst x; subst x0;
         simpl in Heqo0; congruence).

  break_exists. break_and.
  subst x. subst x0. simpl in Heqo0. congruence.

  
  Grab Existential Variables.
  exact Float32.zero.
  exact Int.zero.        
  exact Int.zero.
  exact Int.zero.
  exact xH.
  exact Float32.zero.
  exact Int.zero.
  exact xH.
  exact Float32.zero.
  exact Int.zero.
  exact Float32.zero.
  exact Int.zero.
  exact xH.
Qed.

Lemma contents_equiv_load_ptr_equiv :
  forall t m m',
    mem_perm_same m m' ->
    mem_contents_equiv t m m' ->
    forall c b i v,
      Mem.load c m b i = Some v ->
      exists v',
        Mem.load c m' b i = Some v' /\
        ptr_equiv_val t v v'.
Proof.
  intros.
  app mem_load_exists H.
  exists x.
  app Mem.load_result H1.
  app Mem.load_result H.
  split; auto.
  subst.
  apply frag_equiv_decode.
  intros. unfold mem_contents_equiv in H0.
  unfold contents_equiv in H0. apply H0.
  unfold mem_contents_equiv in H0.
  unfold contents_equiv in H0.
  apply H0.
Qed.

Lemma ptr_equiv_md_alloc :
  forall t v v' lo hi b,
    ptr_equiv_val t v v' ->
    ptr_equiv_val (md_alloc t lo hi b) v v'.
Proof.
  intros. unfold ptr_equiv_val in *.
  break_match_hyp; simpl; eauto.
  break_exists. break_and.
  eexists; split; eauto.
  eapply pinj_alloc. eauto.
Qed.

Lemma frag_equiv_alloc_pres :
  forall t lo hi b c c' ofs,
    frag_equiv t c c' ofs ->
    frag_equiv (md_alloc t lo hi b) c c' ofs.
Proof.
  intros. unfold frag_equiv in H.
  break_match_hyp;
    unfold frag_equiv; find_rewrite; eauto.
  repeat (break_match_hyp; try find_rewrite; eauto);
    intros; subst; exploit H; intros; eauto;
    break_exists; break_and; eexists; split; eauto;
    eapply ptr_equiv_md_alloc; eauto.
Qed.

Lemma contents_equiv_alloc :
  forall t m m',
    mem_nextblock_same m m' ->
    mem_contents_equiv t m m' ->
    forall m0 b lo hi,
      Mem.alloc m lo hi = (m0,b) ->
      exists m'0,
        Mem.alloc m' lo hi = (m'0,b) /\ mem_contents_equiv (md_alloc t lo hi b) m0 m'0.
Proof.
  intros.
  app mem_alloc_nextblock H1. break_and.
  eexists. split. eassumption.
  unfold mem_contents_equiv in *.
  repeat break_and.
  isplit.
  eapply match_alloc; try apply H2; eauto.
  isplit.
  eapply match_alloc; try apply H1; eauto.

  app Mem.mem_contents_alloc H2.
  app Mem.mem_contents_alloc H1.
  rewrite H2. rewrite H1.
  unfold contents_equiv.
  intros. split.
  destruct (peq b b0). subst.
  repeat rewrite PMap.gss.
  unfold frag_equiv. 
  repeat rewrite ZMap.gi. auto.
  repeat rewrite PMap.gso by congruence.
  unfold contents_equiv in H5.
  specialize (H5 b0 ofs).
  break_and.
  eapply frag_equiv_alloc_pres; eauto.
  
  destruct (peq b b0). subst.
  repeat rewrite PMap.gss.
  unfold no_pointer.
  repeat rewrite ZMap.gi. auto.

  repeat rewrite PMap.gso by congruence.
  unfold contents_equiv in *.
  specialize (H5 b0 ofs). break_and. eauto.
Qed.


(* We need some notion about what has been allocated so far *)
(* build up an inductive datatype of evidence that something's been allocated *)
(* Note: this doesn't say anything about whether something's been freed *)

Inductive allocated : allocator_metadata -> block -> Prop :=
| alloc_now :
    forall t b lo hi,
      allocated (md_alloc t lo hi b) b
| alloc_prev_alloc :
    forall t b lo hi x,
      allocated t x ->
      allocated (md_alloc t lo hi b) x
| alloc_prev_free :
    forall t b lo hi x,
      allocated t x ->
      allocated (md_free t lo hi b) x
| alloc_prev_ec :
    forall ef ge vl m tr v m' t b,
      allocated t b ->
      allocated (md_ec t ef ge vl m tr v m') b
| alloc_prev_ec' :
    forall ef ge vl m tr v m' t b,
      allocated t b ->
      allocated (md_ec' t ef ge vl m tr v m') b.


Definition is_global_block (ge : Genv.t fundef unit) (b : block) : Prop :=
  exists id, Genv.find_symbol ge id = Some b.

Definition globals_allocated (ge : Genv.t fundef unit) (t : allocator_metadata) :=
  forall b,
    is_global_block ge b ->
    allocated t b.


Definition ptr_equiv_mem (ge : Genv.t fundef unit) (t : allocator_metadata) (m m' : mem) : Prop := 
  mem_nextblock_same m m' /\ mem_perm_same m m' /\ mem_contents_equiv t m m'
  /\ globals_allocated ge t /\  
  global_perms ge m'.

Lemma ptr_equiv_valid_globals_r :
  forall ge t m m',
    ptr_equiv_mem ge t m m' ->
    valid_globals ge m'.
Proof.
  intros.
  unfold ptr_equiv_mem in *.
  repeat break_and; eauto.
  eapply global_perms_valid_globals; eauto.
Qed.

Lemma ptr_equiv_global_perms_r :
  forall ge t m m',
    ptr_equiv_mem ge t m m' ->
    global_perms ge m'.
Proof.
  intros.
  unfold ptr_equiv_mem in *;
    repeat break_and;
    auto.
Qed.
  
  
Lemma ptr_equiv_match_metadata_l :
  forall ge t m m',
    ptr_equiv_mem ge t m m' ->
    match_metadata t m.
Proof.
  intros. unfold ptr_equiv_mem in H.
  repeat break_and. unfold mem_contents_equiv in H1.
  repeat break_and. eauto.
Qed.

Lemma ptr_equiv_match_metadata_r :
  forall ge t m m',
    ptr_equiv_mem ge t m m' ->
    match_metadata t m'.
Proof.
  intros. unfold ptr_equiv_mem in H.
  repeat break_and. unfold mem_contents_equiv in H1.
  repeat break_and. eauto.
Qed.

Lemma valid_globals_store :
  forall ge m,
    valid_globals ge m ->
    forall c b i v m',
      Mem.store c m b i v = Some m' ->
      valid_globals ge m'.
Proof.
  intros.
  unfold valid_globals in *.
  intros. app H H1.
  app Mem.store_access H0.
  unfold Mem.valid_pointer in *.
  unfold Mem.perm_dec in *.
  unfold proj_sumbool in *.
  break_match_hyp; try congruence.
  clear Heqs. unfold Mem.perm_order' in p.
  break_match_hyp; try inv_false.
  rewrite <- H0 in Heqo.
  break_match; try congruence.
  clear Heqs.
  unfold Mem.perm_order' in *.
  break_match_hyp; try inv_false; try congruence.
Qed.

(* Lemma valid_globals_store_bits : *)
(*   forall ge m, *)
(*     valid_globals ge m -> *)
(*     forall c b i v m', *)
(*       store_bits c m b i v = Some m' -> *)
(*       valid_globals ge m'. *)
(* Proof. *)
(*   intros. unfold valid_globals in *. *)
(*   intros. app H H1. *)
(*   unfold Mem.valid_pointer in *. *)
(*   unfold Mem.perm_dec in *. *)
(*   unfold proj_sumbool in *. *)
(*   repeat break_match; try congruence. *)
(*   clear Heqs. clear Heqs0. *)
(*   unfold store_bits in *. *)
(*   break_match_hyp; try congruence; try find_inversion. *)
(*   simpl in n. congruence. *)
(* Qed. *)


Lemma ptr_equiv_mem_store :
  forall ge t m m',
    ptr_equiv_mem ge t m m' ->
    forall v v',
      ptr_equiv_val t v v' ->
      forall c b i m'',
        Mem.store c m b i v = Some m'' ->
        exists m''',
          (store_bits c m' b i v' = Some m''' /\ ptr_equiv_mem ge t m'' m''').
Proof.
  intros. 
  unfold ptr_equiv_mem in H. repeat break_and.
  name H3 Hcont. unfold mem_contents_equiv in H3.
  app mem_contents_equiv_store H1.
  repeat break_and. exists x. split.
  eauto.
  app mem_store_perm_same H7.
  break_and.
  app mem_store_nextblock H.
  repeat break_and.
  rewrite H7 in H1. inv H1.
  rewrite H in H7. inv H7.

  unfold ptr_equiv_mem.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  eapply global_perms_store_bits; eauto.
Qed.

Lemma ptr_equiv_mem_load :
  forall ge t m m',
    ptr_equiv_mem ge t m m' ->
    forall c b i v,
      Mem.load c m b i = Some v ->
      exists v',
        (Mem.load c m' b i = Some v' /\ ptr_equiv_val t v v').
Proof.
  intros.
  unfold ptr_equiv_mem in H.
  repeat break_and.
  app mem_load_exists H1.
  exists x.
  split. assumption.
  app Mem.load_result H0.
  app Mem.load_result H1.
  subst v. subst x.
  unfold mem_contents_equiv in H2.
  eapply frag_equiv_decode; eauto.
  apply H2. apply H2.
Qed.

(* Lemma valid_globals_alloc : *)
(*   forall ge m, *)
(*     valid_globals ge m -> *)
(*     forall lo hi b m', *)
(*       Mem.alloc m lo hi = (m',b) -> *)
(*       valid_globals ge m'. *)
(* Proof. *)
(*   intros. *)
(*   unfold valid_globals in *. *)
(*   intros. app H H1. *)
(*   rewrite Mem.valid_pointer_valid_access in *. *)
(*   app Mem.valid_access_alloc_other H1. *)
(* Qed. *)

Lemma ptr_equiv_mem_alloc :
  forall ge t m m',
    ptr_equiv_mem ge t m m' ->
    forall m0 b lo hi,
      Mem.alloc m lo hi = (m0,b) ->
      exists m'0,
        Mem.alloc m' lo hi = (m'0,b) /\ ptr_equiv_mem ge (md_alloc t lo hi b) m0 m'0.
Proof.
  intros. unfold ptr_equiv_mem in *.
  break_and.
  app mem_alloc_nextblock H.
  repeat break_and. 
  app mem_alloc_perm H1. break_and. rewrite H in H1.
  inv H1. rewrite H.

  app contents_equiv_alloc H0. break_and.
  eexists. 
  
  split; try reflexivity; eauto.
  split; eauto. split; eauto.

  
  rewrite H0 in H. inv H.
  split.
  assumption.
  

  split.

  unfold globals_allocated in *.
  intros. app H5 H.
  econstructor; eauto.

  eapply global_perms_alloc; eauto.
Qed.


Lemma ptr_equiv_md_free :
  forall t v v' lo hi b,
    ptr_equiv_val t v v' ->
    ptr_equiv_val (md_free t lo hi b) v v'.
Proof.
  intros. unfold ptr_equiv_val in *.
  break_match_hyp; simpl; eauto.
  break_exists. break_and.
  eexists; split; eauto.
  eapply pinj_free. eauto.
Qed.

Lemma frag_equiv_free_pres :
  forall t lo hi b c c' ofs,
    frag_equiv t c c' ofs ->
    frag_equiv (md_free t lo hi b) c c' ofs.
Proof.
  intros. unfold frag_equiv in H.
  break_match_hyp;
    unfold frag_equiv; find_rewrite; eauto.
  repeat (break_match_hyp; try find_rewrite; eauto);
    intros; subst; exploit H; intros; eauto;
    break_exists; break_and; eexists; split; eauto;
    eapply ptr_equiv_md_free; eauto.
Qed.

Lemma contents_equiv_md_free :
  forall t c c' lo hi b,
    contents_equiv t c c' ->
    contents_equiv (md_free t lo hi b) c c'.
Proof.
  unfold contents_equiv. intros.
  specialize (H b0 ofs). break_and. split;
    try eapply frag_equiv_free_pres; eauto.
Qed.

Lemma ptr_equiv_mem_free :
  forall ge t m m',
    ptr_equiv_mem ge t m m' ->
    forall b lo hi m0,
      Mem.free m b lo hi = Some m0 ->
      exists m'0,
        Mem.free m' b lo hi = Some m'0 /\ ptr_equiv_mem ge (md_free t lo hi b) m0 m'0.
Proof.
  intros.
  unfold ptr_equiv_mem in H. repeat break_and. 
  app mem_free_perm H1. break_and.
  app mem_free_nextblock H0.
  break_and. rewrite H0 in H1. inv H1.
  exists x. split. auto.
  unfold ptr_equiv_mem.
  split. auto.
  split. auto.

  split.
  app Mem.free_result H7.
  app Mem.free_result H0.
  unfold mem_contents_equiv in *.
  repeat break_and.
  isplit.
  eapply match_free; try apply H1; eauto.
  isplit.
  eapply match_free; try apply H7; eauto.
  
  subst x. subst m0.
  unfold Mem.unchecked_free.
  simpl.

  eapply contents_equiv_md_free; eauto.

  split.

  unfold globals_allocated in *.
  intros. app H3 H1. econstructor; eauto.

  eapply global_perms_free; eauto.

Qed.


Lemma perm_same_range_perm :
  forall m m',
    mem_perm_same m m' ->
    forall b i j y,
      Mem.range_perm m b i j Cur y ->
      Mem.range_perm m' b i j Cur y.
Proof.
  intros. unfold Mem.range_perm in H0.
  unfold Mem.range_perm. intros.
  specialize (H0 ofs H1).
  eapply perm_same_imp; eauto.
Qed.

Lemma perm_same_drop_perm :
  forall m b i j perm m0 m',
    mem_perm_same m m' ->
    Mem.drop_perm m b i j perm = Some m0 ->
    exists m0',
      Mem.drop_perm m' b i j perm = Some m0'.
Proof.
  intros.
  unfold Mem.drop_perm in *.
  break_match_hyp; try congruence.
  
  app perm_same_range_perm r.
  
  break_match; try congruence. inv H0.
  eexists; split; try reflexivity.

Qed.


Lemma ptr_equiv_drop_perm :
  forall ge t m m',
    ptr_equiv_mem ge t m m' ->
    forall b i j m0 perm,
      Mem.drop_perm m b i j perm = Some m0 ->
      exists m0',
        Mem.drop_perm m' b i j perm = Some m0' /\
        ptr_equiv_mem ge t m0 m0'.
Proof.
  intros.
  unfold ptr_equiv_mem in H. break_and.
  break_and.
  app perm_same_drop_perm H0.
  find_rewrite. eexists; split; eauto.
  
  
  unfold ptr_equiv_mem. repeat isplit.
  
  * unfold mem_nextblock_same. simpl.
    unfold Mem.drop_perm in *; repeat break_match_hyp; try congruence; repeat find_inversion.
    apply H.

  * repeat break_and.
    unfold Mem.drop_perm in *.
    repeat break_match_hyp; try congruence;
    repeat opt_inv; subst;
    unfold mem_perm_same in *;
    unfold mem_nextblock_same in *;
    simpl in *.
    intros.
    destruct (peq b b0);
      try subst b;
      repeat rewrite PMap.gss in *;
      repeat rewrite PMap.gso in * by congruence;
      try break_match;
      eauto.
  * unfold mem_contents_equiv in *.
    repeat break_and. isplit.
    eapply match_drop_perm; try apply H3; eauto.
    isplit.
    eapply match_drop_perm; try eapply H0; eauto.
    unfold Mem.drop_perm in *; repeat break_match_hyp; try congruence; repeat find_inversion; simpl in *. assumption.
  * repeat break_and; eauto.
  * eapply global_perms_drop_perm; eauto.
    repeat break_and. eauto.
Qed.

(* I hate this *)

(* Lemma ptr_equiv_store_raw : *)
(*   forall m m', *)
(*     ptr_equiv_mem m m' -> *)
(*     forall v v' chunk, *)
(*       (ptr_equiv_val v v' /\ encode_val chunk v' = encode_val_bits chunk v') -> *)
(*       forall b ofs m0, *)
(*         Mem.store chunk m b ofs v = Some m0 -> *)
(*         exists m0', *)
(*           Mem.store chunk m' b ofs v' = Some m0' /\ *)
(*           ptr_equiv_mem m0 m0'. *)
(* Proof. *)
(*   intros. app Mem.store_valid_access_3 H1. *)
(*   unfold ptr_equiv_mem in H. repeat break_and. *)
(*   app perm_same_valid_access H1. *)
(*   app Mem.valid_access_store H1. destruct H1. *)
(*   instantiate (1 := v') in e. *)
(*   rewrite e. eexists; split; eauto. *)
(*   unfold ptr_equiv_mem. split. *)
(*   app Mem.nextblock_store H2. *)
(*   app Mem.nextblock_store e. *)
(*   unfold mem_nextblock_same in *. congruence. *)
(*   split. *)

(*   unfold mem_perm_same. intros. *)
(*   app Mem.perm_store_2 H2. *)
(*   unfold mem_perm_same in H3.  *)
(*   app H4 H2. *)
(*   app Mem.perm_store_1 e. *)

(*   unfold mem_contents_equiv in *. *)
(*   app Mem.store_mem_contents H2.  *)
(*   app Mem.store_mem_contents e. rewrite e. *)
(*   rewrite H3. *)
(*   rewrite H2. *)
(*   eapply contents_equiv_pres. assumption. *)
(*   assumption. *)
(* Qed. *)
  

(* Lemma ptr_equiv_store_zero : *)
(*   forall m m', *)
(*     ptr_equiv_mem m m' -> *)
(*     forall b ofs m0, *)
(*       Mem.store Mint8unsigned m b ofs Vzero = Some m0 -> *)
(*       exists m0', *)
(*         Mem.store Mint8unsigned m' b ofs Vzero = Some m0' /\ *)
(*         ptr_equiv_mem m0 m0'. *)
(* Proof. *)
(*   intros. app Mem.store_valid_access_3 H0. *)
(*   unfold ptr_equiv_mem in H. repeat break_and. *)
(*   app perm_same_valid_access H0. *)
(*   app Mem.valid_access_store H0. destruct H0. *)
(*   instantiate (1 := Vzero) in e. *)
(*   rewrite e. eexists; split; eauto. *)
(*   unfold ptr_equiv_mem. split. *)
(*   app Mem.nextblock_store H1. *)
(*   app Mem.nextblock_store e. *)
(*   unfold mem_nextblock_same in *. congruence. *)
(*   split. *)

(*   unfold mem_perm_same. intros. *)
(*   app Mem.perm_store_2 H1. *)
(*   unfold mem_perm_same in H2. *)
(*   app H2 H1. *)
(*   app Mem.perm_store_1 e. *)

(*   unfold mem_contents_equiv in *. *)
(*   app Mem.store_mem_contents H1.  *)
(*   app Mem.store_mem_contents e. rewrite e. *)
(*   replace (encode_val Mint8unsigned Vzero) with (encode_val_bits Mint8unsigned Vzero) by (simpl; reflexivity). *)
(*   rewrite H1. *)
(*   eapply contents_equiv_pres. assumption. *)
(*   simpl. reflexivity. *)
(* Qed. *)

(* Not really useful anymore *)
Lemma ptr_equiv_store_zeros :
  forall l ge t m m',
    ptr_equiv_mem ge t m m' ->
      forall b ofs m0,
        store_zeros m b ofs l = Some m0 ->
        exists m0',
          store_zeros_bits m' b ofs l = Some m0' /\
          ptr_equiv_mem ge t m0 m0'.
Proof.
  induction l using Z_nat_ind; intros.
  rewrite store_zeros_equation in *. break_match_hyp; try omega. inv H0. eauto.
  rewrite store_zeros_bits_equation. rewrite Heqs.
  eauto.
  rewrite store_zeros_equation in *. break_match_hyp; try omega. inv H0. eauto.
  rewrite store_zeros_bits_equation. rewrite Heqs.
  break_match_hyp; try congruence.
  rewrite store_zeros_equation in H2. break_match_hyp; try omega. inv H2.
  app ptr_equiv_mem_store Heqo. break_and. rewrite H1.
  eexists; split; eauto.
  replace (1-1) with 0 by omega.
  rewrite store_zeros_bits_equation.
  break_match; try omega. reflexivity.
  simpl. reflexivity.
  rewrite store_zeros_equation in H1.
  break_match_hyp; try omega. inv H1.
  rewrite store_zeros_bits_equation. break_match; try omega.
  eauto.

  rewrite store_zeros_equation in H1. break_match_hyp; try omega.
  break_match_hyp; try congruence.
  replace (l + 1 - 1) with l in H1 by omega.
  app ptr_equiv_mem_store Heqo; simpl; try reflexivity.
  break_and.

  eapply IHl in H1; eauto.
  rewrite store_zeros_bits_equation. break_match; try omega.
  collapse_match.
  replace (l + 1 - 1) with l by omega.
  eauto.
Qed.


