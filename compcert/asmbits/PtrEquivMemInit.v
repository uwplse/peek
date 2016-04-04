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
Require Import GlobalPerms.
Require Import PtrEquiv.
Require Import PtrEquivMem.

Definition injectable_init_data (ge : Genv.t fundef unit) (t : allocator_metadata) (a : init_data) : Prop :=
  match a with
    | Init_addrof id ofs =>
      forall b,
        Genv.find_symbol ge id = Some b ->
        pinj t b ofs <> None
    | _ => True
  end.

(* This is almost but not quite init_data_size *)
(* since for some reason 64 bit floats can be 32 bit aligned *)
Definition align_init_data (v : init_data) : Z :=
  match v with
    | Init_float64 _ => 4
    | Init_space _ => 1
    | _ => Genv.init_data_size v
  end.

Inductive ofs_aligned : Z -> list init_data -> Prop :=
| align_nil :
    forall ofs,
      ofs_aligned ofs nil
| align_cons :
    forall ofs l v,
      ofs_aligned (ofs + Genv.init_data_size v) l ->
      (align_init_data v | ofs) ->
      ofs_aligned ofs (v :: l).


Lemma store_init_data_list_aligned :
  forall l (ge : Genv.t fundef unit) m b ofs m',
    Genv.store_init_data_list ge m b ofs l = Some m' ->
    ofs_aligned ofs l.
Proof.
  induction l; intros.
  econstructor.
  econstructor.
  simpl in H.
  repeat break_match_hyp; try congruence.
  eapply IHl. eassumption.
  simpl in H.
  break_match_hyp; try congruence.
  unfold Genv.store_init_data in Heqo.
  repeat break_match_hyp; try congruence; simpl;
  first [NP _app Mem.store_valid_access_3 Mem.store | idtac];
  unfold Mem.valid_access in *;
  repeat break_and;
  simpl in *;
  try assumption.
  eapply Z.divide_1_l.
Qed.

Definition symbol_sane (ge : Genv.t fundef unit) (id : ident) : Prop :=
  Genv.find_symbol ge id <> None.


Definition init_data_symbol_sane (ge : Genv.t fundef unit) (d : init_data) : Prop :=
  match d with
    | Init_addrof id i => symbol_sane ge id
    | _ => True
  end.

Definition inj_globdef (gd : globdef fundef unit) (ge : Genv.t fundef unit) (md : allocator_metadata) (m : mem) (b : block) : Prop :=
  match gd with
    | Gvar v =>
      (forall ofs,
         0 <= ofs < Genv.init_data_list_size (gvar_init v) ->
         (Mem.mem_access m) !! b ofs Cur = Some Writable) /\
      ofs_aligned 0 (gvar_init v) /\
      (forall d, In d (gvar_init v) -> init_data_symbol_sane ge d) /\
      (forall d, In d (gvar_init v) -> injectable_init_data ge md d) /\
      Plt b (Mem.nextblock m)
    | Gfun _ => Plt b (Mem.nextblock m)
  end.

Lemma store_zeros_bits_nextblock :
  forall hi m b lo m',
    store_zeros_bits m b lo hi = Some m' ->
    Mem.nextblock m = Mem.nextblock m'.
Proof.
  induction hi using Z_nat_ind; intros;
  try rewrite store_zeros_bits_equation in H.
  break_match_hyp; try omega. congruence.
  break_match_hyp; try omega.
  break_match_hyp; try congruence.
  rewrite store_zeros_bits_equation in H.
  break_match_hyp; try omega.
  inv H. unfold store_bits in *.
  break_match_hyp; try congruence.
  inv Heqo. simpl. congruence.
  rewrite store_zeros_bits_equation in H0.
  break_match_hyp; try congruence.
  rewrite store_zeros_bits_equation in H0.
  break_match_hyp; try omega.
  break_match_hyp; try congruence.
  replace (hi + 1 - 1) with hi in H0 by omega.
  app IHhi H0.
  unfold store_bits in *.
  repeat break_match_hyp; try congruence.
  inv Heqo. simpl in H0. congruence.
Qed.

Lemma store_init_data_bits_nextblock :
  forall md ge m b ofs a m',
    store_init_data_bits md ge m b ofs a = Some m' ->
    Mem.nextblock m = Mem.nextblock m'.
Proof.
  intros.
  destruct a; simpl in H;
  try congruence;
  unfold store_bits in *;
  repeat break_match_hyp;
  try opt_inv;
  subst;
  simpl;
  try congruence.
Qed.  

Lemma store_init_data_list_bits_nextblock :
  forall l md ge m b ofs m',
    store_init_data_list_bits md ge m b ofs l = Some m' ->
    Mem.nextblock m = Mem.nextblock m'.
Proof.
  induction l; intros.
  simpl in H. congruence.
  simpl in H. break_match_hyp; try congruence.
  eapply store_init_data_bits_nextblock in Heqo.
  rewrite Heqo.
  eapply IHl; eauto.
Qed.


Lemma store_global_bits_nextblock :
  forall md ge m b g m' md',
    store_global_bits md ge m b g = Some (m',md') ->
    Mem.nextblock m = Mem.nextblock m'.
Proof.
  intros. unfold store_global_bits in *.
  repeat break_match_hyp; try congruence;
  try opt_inv; subst;
  unfold set_perm in *;
  repeat break_match_hyp; try congruence;
  opt_inv; subst; simpl; try reflexivity.
  
  app store_zeros_bits_nextblock Heqo.
  app store_init_data_list_bits_nextblock Heqo0.
  congruence.
  
Qed.

Lemma store_globals_bits_nextblock :
  forall l md ge m m' md',
    store_globals_bits md ge m l = Some (m',md') ->
    Mem.nextblock m = Mem.nextblock m'.
Proof.
  induction l; intros.
  simpl in H. congruence.
  simpl in H. repeat break_match_hyp; try congruence.
  subst. app IHl H. app store_global_bits_nextblock Heqo.
  congruence.
Qed.

Lemma store_zeros_bits_access :
  forall l m b ofs m',
    store_zeros_bits m b ofs l = Some m' ->
    Mem.mem_access m = Mem.mem_access m'.
Proof.
  induction l using Z_nat_ind;
  intros;
  rewrite store_zeros_bits_equation in *;
  intros.
  * break_match_hyp; try omega. inv H. reflexivity.
  * break_match_hyp; try omega. break_match_hyp; try congruence.
    rewrite store_zeros_bits_equation in *.
    break_match_hyp; try omega. inv H.
    unfold store_bits in *.
    repeat break_match_hyp; try congruence.
    inv Heqo. simpl. reflexivity.
  * break_match_hyp; try omega. inv H0. reflexivity.
  * break_match_hyp; try omega.
    break_match_hyp; try congruence.
    replace (l + 1 - 1) with l in * by omega.
    app IHl H0.
    rewrite <- H0.
    unfold store_bits in *.
    break_match_hyp; try congruence.
    inv Heqo. simpl. reflexivity.
Qed.

Lemma store_init_data_list_bits_access :
  forall l a ge m b ofs m',
    store_init_data_list_bits a ge m b ofs l = Some m' ->
    Mem.mem_access m = Mem.mem_access m'.
Proof.
  induction l; intros. simpl in H. inv H. reflexivity.
  simpl in H. break_match_hyp; try congruence.
  app IHl H. rewrite <- H.
  unfold store_init_data_bits in *.
  repeat break_match_hyp; try congruence;
  try solve [unfold store_bits in *;
              break_match_hyp;
              try congruence;
              try opt_inv;
              simpl;
              reflexivity].
Qed.

Lemma store_global_bits_access :
  forall md ge m b g m' md',
    store_global_bits md ge m b g = Some (m',md') ->
    forall b' z k,
      b <> b' ->
      (Mem.mem_access m) !! b' z k= (Mem.mem_access m') !! b' z k.
Proof.
  intros. unfold store_global_bits in *.
  unfold set_perm in *.
  repeat break_match_hyp; try congruence;
  repeat opt_inv; subst m'; try subst m0; try subst m2; simpl;
  try rewrite PMap.gso by congruence;
  try reflexivity.
  
  app store_zeros_bits_access Heqo.
  app store_init_data_list_bits_access Heqo0.
  repeat break_match_hyp; try congruence.
Qed.

Lemma store_global_bits_md :
  forall md ge m b g m' md',
    store_global_bits md ge m b g = Some(m',md') ->
    md = md'.
Proof.
  intros. unfold store_global_bits in *.
  repeat break_match_hyp; try congruence.
Qed.


Lemma inj_globdef_store_global_bits :
  forall md ge m b g m' md',
    store_global_bits md ge m b g = Some(m',md') ->
    forall g0 b0,
      b <> b0 ->
      inj_globdef g0 ge md m b0 ->
      inj_globdef g0 ge md' m' b0.
Proof.
  intros.
  unfold inj_globdef in *.
  break_match; auto.
  app store_global_bits_nextblock H. congruence.
  repeat break_and.
  repeat split; try assumption.
  intros. 
  app store_global_bits_access H.
  
  rewrite <- H. apply H1. solve [eauto].
  app store_global_bits_md H. subst. solve [eauto].
  app store_global_bits_nextblock H. congruence.
Qed.

Lemma store_global_bits_fun_succeeds :
  forall md ge m b f,
    Plt b (Mem.nextblock m) ->
    exists m' md',
      store_global_bits md ge m b (Gfun f) = Some (m', md').
Proof.
  unfold store_global_bits. intros.
  unfold set_perm.
  repeat break_match; try congruence;
  eauto.
Qed.

Lemma store_zeros_bits_succeeds :
  forall hi m b lo,
    (forall ofs,
       lo <= ofs < lo + hi ->
       (Mem.mem_access m) !! b ofs Cur = Some Writable) ->
    exists m',
      store_zeros_bits m b lo hi = Some m'.
Proof.
  induction hi using Z_nat_ind; intros;
  rewrite store_zeros_bits_equation.
  break_match; try omega. eauto.
  break_match; try omega.
  unfold store_bits.
  break_match. rewrite store_zeros_bits_equation.
  break_match; try omega. eauto.
  break_match_hyp; try congruence.
  clear Heqs0. unfold Mem.valid_access in *.
  unfold Mem.range_perm in n.
  exfalso. apply n. split.
  intros. unfold size_chunk in H0.
  assert (ofs = lo) by omega. subst.
  unfold Mem.perm. unfold Mem.perm_order'.
  rewrite H by omega. econstructor.
  unfold align_chunk. 
  apply Z.divide_1_l.
  break_match; try omega. eauto.
  break_match; eauto.
  break_match. replace (hi + 1 - 1) with hi by omega.
  eapply IHhi. intros.
  unfold store_bits in Heqo. break_match_hyp; try congruence.
  inv Heqo. simpl. eapply H0. omega.
  unfold store_bits in Heqo.
  break_match; try congruence.
  exfalso. apply n.
  unfold Mem.valid_access.
  split. unfold Mem.range_perm. intros.
  unfold Mem.perm. unfold Mem.perm_order'.
  rewrite H0. econstructor.
  simpl in H1. omega.
  simpl. eapply Z.divide_1_l.
Qed.

Lemma store_init_data_list_bits_succeeds :
  forall l md ge m b ofs,
    (forall o,
       ofs <= o < ofs + Genv.init_data_list_size l ->
       (Mem.mem_access m) !! b o Cur = Some Writable ) ->
    ofs_aligned ofs l ->
    (forall d, In d l -> init_data_symbol_sane ge d) ->
    (forall x, In x l -> injectable_init_data ge md x) ->
  exists m',
    store_init_data_list_bits md ge m b ofs l = Some m'.
Proof.
  induction l; intros.
  simpl. eauto.
  simpl. break_match.
  edestruct IHl with (m := m0). intros.
  unfold store_init_data_bits in Heqo.
  simpl in H. instantiate (1 := ofs + Genv.init_data_size a) in H3.
  repeat break_match;
    try congruence;
    unfold store_bits in *;
    repeat break_match;
    try congruence;
    try opt_inv;
    simpl;
    try apply H;
    destruct a; unfold Genv.init_data_size in *; fold Genv.init_data_list_size; try omega;
    try congruence.
  subst. apply H. unfold Genv.init_data_size in *.
  assert (Z.max z 0 >= 0). 
  rewrite Zmax_spec. break_match; try omega.
  omega.

  inv H0. assumption.

  intros. eapply H1. simpl. right. assumption.

  intros. eapply H2. simpl. right. assumption.
  
  erewrite H3.
  eauto.

  
  name (Genv.init_data_list_size_pos l) gpl.
  unfold store_init_data_bits in *.
  repeat break_match; try congruence;
  unfold store_bits in *;
  repeat break_match; try congruence;
  exfalso; try apply n;
  try (unfold Mem.valid_access; split; unfold Mem.range_perm;
       unfold Mem.perm; intros; try erewrite H; try solve [simpl; econstructor]);
  try (
        unfold Genv.init_data_list_size; fold Genv.init_data_list_size;
        unfold Genv.init_data_size; unfold size_chunk in *; try omega);
  simpl; inv H0; try assumption.

  exploit H2. simpl. left. reflexivity.
  intros. simpl in H0.
  app H0 Heqo0. 

  exploit H1. simpl. left. reflexivity.
  intros. unfold init_data_symbol_sane in H0.
  unfold symbol_sane in H0. unfold fundef in *.
  rewrite Heqo0 in H0. congruence.
Qed.

Lemma store_global_bits_var_succeeds :
  forall md ge m b v,
    (forall ofs,
       0 <= ofs < Genv.init_data_list_size (gvar_init v) ->
       (Mem.mem_access m) !! b ofs Cur = Some Writable ) ->
    ofs_aligned 0 (gvar_init v) ->
    (forall d, In d (gvar_init v) -> init_data_symbol_sane ge d) ->
    (forall x, In x (gvar_init v) -> injectable_init_data ge md x) ->
    (Plt b (Mem.nextblock m)) ->
    exists m' md',
      store_global_bits md ge m b (Gvar v) = Some (m',md').
Proof.
  intros. unfold store_global_bits.
  edestruct (store_zeros_bits_succeeds).
  intros. apply H.
  replace (Genv.init_data_list_size (gvar_init v)) with
                   (0 + (Genv.init_data_list_size (gvar_init v))) by omega.
  apply H4.
  rewrite H4.
  app store_zeros_bits_access H4.
  edestruct (store_init_data_list_bits_succeeds) with (m := x).
  intros. instantiate (1 := gvar_init v) in H6.
  instantiate (1 :=0) in H6.
  rewrite <- H4.
  apply H. omega.
  assumption.
  eassumption. eassumption.
  erewrite H6.
  app store_init_data_list_bits_access H6.
  unfold set_perm.
  break_match; eauto.
  break_match_hyp; try congruence.
  NP _app store_zeros_bits_nextblock store_zeros_bits.
  NP _app store_init_data_list_bits_nextblock store_init_data_list_bits.
  congruence.
Qed.


Lemma store_global_bits_succeeds :
  forall md ge m b g,
    inj_globdef g ge md m b ->    
    exists m' md',
      store_global_bits md ge m b g = Some (m',md').
Proof.
  intros.
  unfold inj_globdef in *.
  break_match_hyp.
  eapply store_global_bits_fun_succeeds; eauto.
  repeat break_and.
  
  eapply store_global_bits_var_succeeds; eauto.
  
Qed.



Lemma store_globals_bits_succeeds :
  forall l md ge m,
  (forall id b g, In (id,b,g) l -> inj_globdef g ge md m b) ->
    list_norepet (map snd (map fst l)) ->
  exists m' md',
    store_globals_bits md ge m l = Some (m',md').
Proof.
  induction l; intros.
  simpl. eauto.
  simpl. repeat break_let. subst.
  break_match.
  repeat break_let. subst.
  eapply IHl. intros.
  eapply inj_globdef_store_global_bits; eauto.
  simpl in H0.
  inv H0.
  intro. subst.
  apply H4.
  eapply in_map in H1. eapply in_map in H1.
  instantiate (1 := fst) in H1.
  instantiate (1 := snd) in H1.
  simpl in H1. assumption.
  
  
  eapply H. simpl. right. eauto.
  simpl in H0. inv H0. assumption.
  edestruct store_global_bits_succeeds;
    try find_rewrite; eauto.

  eapply H. simpl. left. reflexivity.
Qed.


(* We need injectable global definitions *)
Axiom init_mem_inj_globdef :
  forall p m m0 a l,
    Genv.alloc_globals (Genv.globalenv p) Mem.empty (prog_defs p) = Some m ->
    alloc_only_globals_bits md_init (Genv.globalenv p) Mem.empty (prog_defs p) = Some (m0,a,l) ->
    forall id b g,
      In (id,b,g) l -> inj_globdef g (Genv.globalenv p) a m0 b.

Lemma alloc_only_globals_bits_nextblock :
  forall l md ge m m' md' l',
    alloc_only_globals_bits md ge m l = Some (m',md',l') ->
    forall b,
      In b (map snd (map fst l')) -> ~ Plt b (Mem.nextblock m).
Proof.
  induction l; intros.
  simpl in H. inv H.
  simpl in H0. inv_false.
  simpl in H. repeat break_match_hyp; try congruence.
  subst. inv H.
  simpl in H0. break_or.
  * clear -Heqo.
    unfold alloc_only_global_bits in Heqo.
    destruct a.
    repeat break_match_hyp; try congruence;
    inv Heqo;
    NP _app Mem.alloc_result Mem.alloc;
    subst;
    eapply Plt_strict.
  * app IHl Heqo0.
    unfold alloc_only_global_bits in Heqo.
    destruct a.
    repeat break_match_hyp; try congruence;
    inv Heqo;
    NP _app Mem.nextblock_alloc Mem.alloc;
    subst;
    unfold Mem.drop_perm in *;
    repeat break_match_hyp; try congruence;
    opt_inv; subst; simpl in *;
    rewrite Heqp in *;
    intro; apply Heqo0;
    eapply Plt_trans_succ; eauto.
Qed.


Lemma alloc_only_globals_bits_list_norepet :
  forall l md ge m m' md' l',
    alloc_only_globals_bits md ge m l = Some (m',md',l') ->
    list_norepet (map snd (map fst l')).
Proof.
  induction l; intros.
  * simpl in H. inv H. simpl. econstructor.

  * simpl in H. repeat break_match_hyp; try congruence.
    subst. inv H. simpl. econstructor.

    name (alloc_only_globals_bits_nextblock _ _ _ _ _ _ _ Heqo0) Hb.
    intro. app Hb H.

  unfold alloc_only_global_bits in Heqo.
  destruct a.
  repeat break_match_hyp; try congruence;
  inv Heqo;
  NP _app Mem.nextblock_alloc Mem.alloc;
  NP _app Mem.alloc_result Mem.alloc;
  subst; try rewrite Heqp in *;
  unfold Mem.drop_perm in *;
    repeat break_match_hyp; try congruence;
    opt_inv; subst; simpl in *;
    try rewrite Heqp in *;
    apply H;
    eapply Plt_succ.
  eapply IHl; eauto.
Qed.

Lemma alloc_drop :
  forall m lo hi b m',
    Mem.alloc m lo hi = (m',b) ->
    forall k,
    exists m'',
      Mem.drop_perm m' b lo hi k = Some m''.
Proof.
  intros. app Mem.alloc_access_result H.
  unfold Mem.drop_perm.
  break_match; try solve [eauto].
  exfalso. apply n.
  unfold Mem.range_perm.
  intros.
  unfold Mem.perm.
  unfold Mem.perm_order'.
  rewrite H.
  app Mem.alloc_result H0.
  subst. rewrite PMap.gss.
  unfold proj_sumbool. unfold andb.
  repeat break_match; try congruence; try omega. inv Heqo.
  econstructor.
Qed.

Lemma alloc_only_global_bits_succeeds :
  forall md ge m id g,
  exists m' md' b,
    alloc_only_global_bits md ge m (id,g) = Some (m',md',id,b,g).
Proof.
  intros. unfold alloc_only_global_bits.
  destruct g; try destruct f;
  break_let; app alloc_drop Heqp; rewrite H0; eauto.
Qed.

Lemma alloc_only_globals_bits_succeeds :
  forall l md ge m,
    exists m' md' l',
    alloc_only_globals_bits md ge m l = Some (m',md',l').
Proof.
  induction l; intros.
  simpl. eauto.
  simpl.
  repeat break_match; eauto.
  subst. edestruct IHl.
  repeat break_exists. rewrite H in Heqo0. congruence.
  destruct a.
  edestruct alloc_only_global_bits_succeeds.
  repeat break_exists.
  rewrite H in Heqo. congruence.
Qed.


Lemma init_mem_bits_succeeds :
  forall p m,
    Genv.init_mem p = Some m ->
    exists m' t,
      init_mem_bits p = Some (m',t).
Proof.
  intros.
  unfold Genv.init_mem in *.
  unfold init_mem_bits.
  unfold alloc_globals_bits.
  break_match; repeat break_let; eauto; subst.

  * edestruct store_globals_bits_succeeds; eauto.

    intros. eapply init_mem_inj_globdef; eauto.
    
    eapply alloc_only_globals_bits_list_norepet; eauto.
  
  * edestruct alloc_only_globals_bits_succeeds.
    repeat break_exists. rewrite H0 in Heqo. congruence.
Qed.  



Lemma alloc_global_nextblock_match :
  forall ge m a m' md m0 m0' md' i b g,
    Genv.alloc_global ge m a = Some m' ->
    alloc_only_global_bits md ge m0 a = Some (m0', md', i, b, g) ->
    Mem.nextblock m = Mem.nextblock m0 ->
    Mem.nextblock m' = Mem.nextblock m0'.
Proof.
  intros. unfold Genv.alloc_global in *.
  unfold alloc_only_global_bits in *.
  repeat break_match_hyp; try congruence; subst; simpl in *;
  repeat opt_inv; subst;
  unfold Mem.drop_perm in *;
  repeat break_match_hyp; try congruence; repeat opt_inv;
  subst; simpl in *;
  app Mem.nextblock_alloc Heqp1; app Mem.nextblock_alloc Heqp0;
  try congruence.
  app Genv.store_zeros_nextblock Heqo0.
  app Genv.store_init_data_list_nextblock Heqo1.
  congruence.
Qed.

Lemma alloc_globals_nextblock_match :
  forall l ge md m0 m0' m m' md' l',
    Genv.alloc_globals ge m0 l = Some m0' ->
    alloc_only_globals_bits md ge m l = Some (m',md',l') ->
    Mem.nextblock m0 = Mem.nextblock m ->
    Mem.nextblock m0' = Mem.nextblock m'.
Proof.
  induction l; intros;
  simpl in *. congruence.
  * repeat break_match_hyp; try congruence; subst; simpl in *;
    repeat opt_inv; subst.
    eapply IHl; eauto.
    eapply alloc_global_nextblock_match; eauto.
Qed.

Lemma allocated_preserved_alloc_global_bits :
  forall md b,
    allocated md b ->
    forall ge m gl m' md' id b' g,
      alloc_only_global_bits md ge m gl = Some (m',md',id,b',g) ->
      allocated md' b.
Proof.
  intros.
  unfold alloc_only_global_bits in H0.
  break_let. subst.
  repeat break_match_hyp; try congruence; find_inversion;
  try solve [
        econstructor; eauto].
Qed.

Lemma allocated_preserved_alloc_globals_bits :
  forall gl md b,
    allocated md b ->
    forall ge m m' md' l,
      alloc_only_globals_bits md ge m gl = Some (m',md',l) ->
      allocated md' b.
Proof.
  induction gl; intros.
  simpl in H0. inv H0. eauto.
  simpl in H0. repeat break_match_hyp; try congruence.
  subst. find_inversion.
  app allocated_preserved_alloc_global_bits Heqo.
Qed.

Definition gd_size (gd : globdef fundef unit) : Z :=
  match gd with
    | Gfun (Internal f) => zlen (fn_code f)
    | Gfun (External _) => 1
    | Gvar v => Genv.init_data_list_size (gvar_init v)
  end.

Definition list_of_globals (l : list (ident * block * globdef fundef unit)) (ge : Genv.t fundef unit) : Prop :=
  forall b ofs,
    is_global ge b ofs -> exists id gd,(In (id,b,gd) l /\ 0 <= Int.unsigned ofs < gd_size gd).

Definition list_of_global_blocks (l : list (ident * block * globdef fundef unit)) (ge : Genv.t fundef unit) : Prop :=
  forall b,
    is_global_block ge b -> exists id gd, (In (id,b,gd) l).

Lemma list_of_globals_empty :
  forall (p : program),
    list_of_globals nil (Genv.empty_genv fundef unit (prog_public p)).
Proof.
  unfold list_of_globals. intros.
  unfold is_global in H.
  break_or.

  unfold in_code_range in H0.
  unfold Genv.find_funct_ptr in H0.
  unfold Genv.empty_genv in H0.
  simpl in H0.
  rewrite PTree.gempty in H0. inv_false.

  unfold in_var_range in H0.
  unfold Genv.find_var_info in H0.
  unfold Genv.empty_genv in H0.
  simpl in H0.
  rewrite PTree.gempty in H0. inv_false.
Qed.

Lemma in_var_range_add_fun :
  forall ge id f b ofs,
    in_var_range (Genv.add_global ge (id, Gfun f)) b ofs ->
    in_var_range ge b ofs.
Proof.
  intros. unfold in_var_range in *.
  unfold Genv.add_global in *.
  unfold Genv.find_var_info in *. simpl in *.
  assumption.
Qed.

Lemma in_code_range_add_var :
  forall ge id v b ofs,
    in_code_range (Genv.add_global ge (id, Gvar v)) b ofs ->
    in_code_range ge b ofs.
Proof.
  intros. unfold in_code_range in *.
  unfold Genv.add_global in *.
  unfold Genv.find_funct_ptr in *. simpl in *.
  assumption.
Qed.

Lemma in_code_range_not_next :
  forall ge id gd b ofs,
    in_code_range (Genv.add_global ge (id,gd)) b ofs ->
    b <> Genv.genv_next ge ->
    in_code_range ge b ofs.
Proof.
  intros. unfold in_code_range in *.
  destruct gd; unfold Genv.find_funct_ptr in *;
  unfold Genv.add_global in *; simpl in *;
  try rewrite PTree.gso in * by congruence;
  eauto.
Qed.

Lemma in_var_range_not_next :
  forall ge id gd b ofs,
    in_var_range (Genv.add_global ge (id,gd)) b ofs ->
    b <> Genv.genv_next ge ->
    in_var_range ge b ofs.
Proof.
  intros. unfold in_var_range in *.
  destruct gd; unfold Genv.find_var_info in *;
  unfold Genv.add_global in *; simpl in *;
  try rewrite PTree.gso in * by congruence;
  eauto.
Qed.

Lemma list_of_globals_cons :
  forall l ge,
    list_of_globals l ge ->
    forall id gd,
      list_of_globals ((id,Genv.genv_next ge,gd)::l) (Genv.add_global ge (id,gd)).
Proof.
  intros.
  unfold list_of_globals in *.
  intros. unfold is_global in H0.
  destruct gd; break_or;
  try (
        try eapply in_var_range_add_fun in H1;
        try eapply in_code_range_add_var in H1;
        exploit H; unfold is_global; try solve [right; eassumption];
        try solve [left; eassumption];
        intros; repeat break_exists;
        break_and; eexists; eexists; simpl;
        split; try right; eauto);

  destruct (peq b (Genv.genv_next ge));
  try subst;
  try (
      try eapply in_var_range_not_next in H1;
      try eapply in_code_range_not_next in H1;
      try congruence;
      exploit H; unfold is_global; try solve [right; eassumption];
      try solve [left; eassumption];
      intros; repeat break_exists;
      break_and; eexists; eexists; simpl;
      split; try right; eauto).

  unfold in_code_range in *.
  unfold Genv.find_funct_ptr in *.
  unfold Genv.add_global in *.
  simpl in *.
  rewrite PTree.gss in *.
  eexists; eexists; split; try left; try reflexivity; 
  unfold gd_size; destruct f; try omega.
  
  unfold in_var_range in *.
  unfold Genv.find_var_info in *.
  unfold Genv.add_global in *.
  simpl in *.
  rewrite PTree.gss in *.
  eexists; eexists; split; try left; try reflexivity; 
  unfold gd_size; try omega.
Qed.

Lemma alloc_only_global_bits_result :
  forall md ge m a m' md' i b g,
    alloc_only_global_bits md ge m a = Some (m',md',i,b,g) ->
    b = Mem.nextblock m /\ a = (i,g) /\ Mem.nextblock m' = Pos.succ (Mem.nextblock m).
Proof.
  intros. unfold alloc_only_global_bits in *.
  repeat break_match_hyp; try congruence;
  NP _app Mem.alloc_result Mem.alloc;
  NP _app Mem.nextblock_alloc Mem.alloc;
  opt_inv; repeat split;
  try congruence;
  unfold Mem.drop_perm in *;
  repeat break_match_hyp;
  try congruence;
  opt_inv;
  subst;
  subst m';
  simpl;
  assumption.
  
Qed.

Lemma list_of_globals_permut :
  forall b a c ge,
    list_of_globals (b ++ a :: c) ge ->
    list_of_globals (a :: b ++ c) ge.
Proof.
  unfold list_of_globals in *.
  intros. app H H0.
  exists x. exists x0.
  break_and; split; try assumption.
  rewrite in_app in *.
  simpl. rewrite in_app. simpl in H0.
  tauto.
Qed.

Lemma alloc_only_globals_list_ind :
  forall l n ge m md m' md' l',
    Mem.nextblock m = Genv.genv_next ge ->
    list_of_globals n ge ->
    alloc_only_globals_bits md (Genv.add_globals ge l) m l = Some (m',md',l') ->
    list_of_globals (l' ++ n) (Genv.add_globals ge l).
Proof.
  induction l; intros.
  simpl in H1. inv H1. simpl. assumption.
  simpl in H1. repeat break_match_hyp; try congruence. subst.
  opt_inv. subst.
  app alloc_only_global_bits_result Heqo. repeat break_and. subst.
  rewrite H. simpl.
  app IHl Heqo0; try solve [simpl; congruence];
  try solve [eapply list_of_globals_cons; eauto].
  eapply list_of_globals_permut; eauto.
Qed.
  

Lemma alloc_only_globals_list :
  forall l' md p m' md',
    alloc_only_globals_bits md (Genv.globalenv p) Mem.empty (prog_defs p) = Some (m',md',l') ->
    list_of_globals l' (Genv.globalenv p).
Proof.
  intros.
  unfold Genv.globalenv in *.
  replace l' with (l' ++ nil) by eapply app_nil_r; eauto.
  eapply alloc_only_globals_list_ind; eauto.
  simpl. reflexivity.
  eapply list_of_globals_empty.
Qed.


Lemma list_of_global_blocks_cons :
  forall l ge,
    list_of_global_blocks l ge ->
    forall id gd,
      list_of_global_blocks ((id,Genv.genv_next ge,gd)::l) (Genv.add_global ge (id,gd)).
Proof.
  unfold list_of_global_blocks in *.
  intros.
  unfold is_global_block in *.
  repeat break_exists.
  unfold Genv.find_symbol in *.
  unfold Genv.add_global in *.
  simpl in *.
  destruct (peq x id).
  * subst. rewrite PTree.gss in H0. opt_inv; subst.
    eauto.
  * rewrite PTree.gso in H0 by congruence.
    exploit H. eauto.
    intros.
    repeat break_exists.
    eauto.
Qed.

Lemma list_of_global_blocks_permut :
  forall b a c ge,
    list_of_global_blocks (b ++ a :: c) ge ->
    list_of_global_blocks (a :: b ++ c) ge.
Proof.
  unfold list_of_global_blocks in *.
  intros. app H H0.
  exists x. exists x0.
  rewrite in_app in *.
  simpl. rewrite in_app. simpl in H0.
  tauto.
Qed.

Lemma alloc_only_globals_blocks_list_ind :
  forall l n ge m md m' md' l',
    Mem.nextblock m = Genv.genv_next ge ->
    list_of_global_blocks n ge ->
    alloc_only_globals_bits md (Genv.add_globals ge l) m l = Some (m',md',l') ->
    list_of_global_blocks (l' ++ n) (Genv.add_globals ge l).
Proof.
  induction l; intros.
  simpl in H1. inv H1. simpl. assumption.
  simpl in H1. repeat break_match_hyp; try congruence. subst.
  opt_inv. subst.
  app alloc_only_global_bits_result Heqo. repeat break_and. subst.
  rewrite H. simpl.
  app IHl Heqo0; try solve [simpl; congruence];
  try solve [eapply list_of_global_blocks_cons; eauto].
  eapply list_of_global_blocks_permut; eauto.
Qed.

Lemma alloc_only_global_blocks_list :
  forall l' md p m' md',
    alloc_only_globals_bits md (Genv.globalenv p) Mem.empty (prog_defs p) = Some (m',md',l') ->
    list_of_global_blocks l' (Genv.globalenv p).
Proof.
  intros.
  replace l' with (l' ++ nil) by eapply app_nil_r.
  eapply alloc_only_globals_blocks_list_ind; eauto.
  simpl. reflexivity.
  unfold list_of_global_blocks. intros.
  unfold is_global_block in *.
  unfold Genv.find_symbol in *.
  simpl in *.
  break_exists.
  rewrite PTree.gempty in *.
  congruence.
Qed.

(* Fixpoint lookup_global {F V : Type} (id : ident) (l : list (ident * globdef F V)) : option (globdef F V) := *)
(*   match l with *)
(*     | nil => None *)
(*     | (id',gd) :: r => if peq id id' then Some gd else lookup_global id r *)
(*   end. *)

(* Definition global_size (id : ident) (p : program) : Z := *)
(*   match lookup_global id (prog_defs p) with *)
(*     | Some (Gfun (Internal f)) => zlen (fn_code f) *)
(*     | Some (Gfun (External e)) => 1 *)
(*     | Some (Gvar v) => Genv.init_data_list_size (gvar_init v) *)
(*     | None => 0 *)
(*   end. *)

(* Definition ident_allocated (t : allocator_metadata) (p : program) (b : block) (id : ident) : Prop := *)
(*   forall ofs, *)
(*     0 <= Int.unsigned ofs <= global_size id p -> *)
(*     allocated t b ofs. *)

Lemma alloc_only_globals_allocated_ind :
  forall l p md m m' md' gl,
    alloc_only_globals_bits md (Genv.globalenv p) m gl = Some (m',md',l) ->
    forall id b g,
      In (id,b,g) l ->
      allocated md' b.
Proof.
  induction l; intros.
  * simpl in *; inv_false.
  * simpl in H0.
    break_or.
    -
      unfold alloc_only_globals_bits in H.
      destruct gl; simpl in H; try congruence.
      fold alloc_only_globals_bits in H.
      repeat (break_match_hyp; try congruence).
      find_inversion.
      eapply allocated_preserved_alloc_globals_bits; eauto.
      unfold alloc_only_global_bits in Heqo.
      break_let.
      repeat (break_match_hyp; try congruence);
        opt_inv; subst; econstructor;
        unfold gd_size in *;
        try omega.
    - destruct gl; simpl in H; inv H.
      repeat (break_match_hyp; try congruence).
      find_inversion.
      eapply IHl; eauto.
Qed.

Lemma store_globals_bits_md :
  forall l md ge m m' md',
    store_globals_bits md ge m l = Some (m',md') ->
    md = md'.
Proof.
  induction l; intros.
  simpl in H. congruence.
  simpl in H. repeat break_match_hyp; try congruence.
  subst. app IHl H. subst.
  unfold store_global_bits in *.
  repeat break_match_hyp; try congruence.
Qed.

Lemma globals_allocated_init :
      forall p m md,
        init_mem_bits p = Some (m,md) ->
        globals_allocated (Genv.globalenv p) md.
Proof.
  unfold init_mem_bits.
  unfold alloc_globals_bits.
  intros.
  repeat break_match_hyp; try congruence.
  subst.
  app store_globals_bits_md H.
  subst.
  name (alloc_only_globals_allocated_ind _ _ _ _ _ _ _ Heqo) Hf.
  unfold globals_allocated. intros.
  app alloc_only_global_blocks_list Heqo.
  unfold list_of_global_blocks in Heqo.
  
  app Heqo H. 
  eapply Hf; eauto.
Qed.

Lemma global_perms_empty :
  forall (p : program),
    global_perms (Genv.empty_genv fundef unit (prog_public p)) Mem.empty.
Proof.
  intros. unfold global_perms.
  intros. unfold is_global in *.
  break_or.
  unfold in_code_range in *.
  unfold Genv.empty_genv in *. unfold Genv.find_funct_ptr in *.
  simpl in *.
  rewrite PTree.gempty in H0. inv_false.
  unfold in_var_range in *.
  unfold Genv.empty_genv in *. unfold Genv.find_var_info in *.
  simpl in *.
  rewrite PTree.gempty in H0. inv_false.
Qed.  



Definition addr_in_list (b : block) (ofs : int) (l : list (ident * block * globdef fundef unit)) : Prop :=
  exists id gd,
    In (id,b,gd) l /\ 0 <= Int.unsigned ofs < gd_size gd.

Lemma store_globals_bits_untouched :
  forall l b,
    ~ In b (map snd (map fst l)) ->
    forall md ge m m' md',
      store_globals_bits md ge m l = Some (m',md') ->
      (Mem.mem_access m) !! b = (Mem.mem_access m') !! b.
Proof.
  induction l; intros.
  simpl in H0. inv H0. reflexivity.
  simpl in H0. repeat break_match_hyp; try congruence; subst.
  simpl in H.
  eapply Decidable.not_or in H.
  break_and.
  cut ((Mem.mem_access m0) !! b = (Mem.mem_access m') !! b);
    try solve [eapply IHl; eauto].
  intros. rewrite <- H2. clear H2. clear IHl.
  clear H0.
  
  unfold store_global_bits in *.
  repeat break_match_hyp; try congruence;
  opt_inv; subst;
  unfold set_perm in *;
  repeat break_match_hyp; try congruence;
  opt_inv; subst; simpl;
  rewrite PMap.gso by congruence; try reflexivity.
  
  app store_zeros_bits_access Heqo0.
  app store_init_data_list_bits_access Heqo1.
  congruence.
Qed.


Lemma store_globals_perms :
  forall l ge md m m' md',
    list_norepet (map snd (map fst l)) ->
    store_globals_bits md ge m l = Some (m',md') ->
    forall b ofs,
      addr_in_list b ofs l ->
      exists p,
        (Mem.mem_access m') !! b (Int.unsigned ofs) Cur = Some p /\ p <> Freeable.
Proof.
  induction l; intros;
  unfold addr_in_list in *;
  intros;
  repeat break_exists; repeat break_and.
  simpl in H1. inv_false.
  simpl in H1. break_or.
  * simpl in H0.
    break_match_hyp; try congruence.
    break_let. subst.
    simpl in H. inv H.
    app store_globals_bits_untouched H0.
    rewrite <- H0.
    unfold store_global_bits in Heqo.
    repeat break_match_hyp; try congruence;
    opt_inv; subst; simpl in *;
    unfold set_perm in *; break_match_hyp; try congruence; opt_inv; subst;
    simpl; rewrite PMap.gss; unfold andb; unfold proj_sumbool;
    break_match; try omega; eexists; split; try reflexivity; try congruence;
    repeat break_if; try congruence; try omega.

    clear H. clear H0.
    clear Heqs0.
    rewrite Zmax_spec in g.
    break_match_hyp; try congruence; try omega.
    clear H. clear H0.
    clear Heqs0.
    rewrite Zmax_spec in g.
    break_match_hyp; try congruence; try omega.   
    
    unfold Genv.perm_globvar.
    repeat break_match; try congruence.

  * simpl in H. inv H.
    destruct a. destruct p.
    simpl in H6.
    simpl in H0. repeat break_match_hyp; try congruence.
    subst.
    eapply IHl; eauto.

    Grab Existential Variables.
    exact Freeable.
    exact Freeable.
    exact Freeable.
    
Qed.


Lemma store_globals_perms' :
  forall l ge md m m' md',
    store_globals_bits md ge m l = Some (m',md') ->
    list_of_globals l ge ->
    list_norepet (map snd (map fst l)) ->
    global_perms ge m'.
Proof.
  unfold global_perms.
  intros.
  eapply store_globals_perms; eauto.
  unfold list_of_globals in *.
  unfold addr_in_list.
  
  solve [eauto].
Qed.
  

Lemma store_init_data_list_match_md :
  forall l t ge m b ofs m',
    store_init_data_list_bits t ge m b ofs l = Some m' ->
    match_metadata t m ->
    match_metadata t m'.
Proof.
  induction l; intros.
  simpl in H. congruence.
  simpl in H. repeat (break_match_hyp; try congruence).
  app IHl H.
  unfold store_init_data_bits in *.
  repeat break_match_hyp; try congruence; subst;
  eapply match_store_bits; eauto.
Qed.


Lemma store_zeros_bits_match_md:
  forall hi m b lo m',
    store_zeros_bits m b lo hi = Some m' ->
    forall t,
      match_metadata t m ->
      match_metadata t m'.
Proof.
  induction hi using Z_nat_ind; intros;
  try solve [rewrite store_zeros_bits_equation in *;
             break_match_hyp; try omega; try congruence].
  * try rewrite store_zeros_bits_equation in *.
    break_match_hyp; try omega.
    break_match_hyp; try congruence.
    replace (1-1) with 0 in * by omega.
    try rewrite store_zeros_bits_equation in *.
    break_match_hyp; try omega.
    opt_inv; subst.
    eapply match_store_bits; eauto.
  * try rewrite store_zeros_bits_equation in H0.
    break_match_hyp; try omega.
    break_match_hyp; try congruence.
    replace (hi + 1 - 1) with hi in * by omega.
    eapply IHhi in H0; eauto.
    eapply match_store_bits; eauto.
Qed.

Lemma store_globals_bits_match_md :
  forall l t ge m m' t',
    store_globals_bits t ge m l = Some (m',t') ->
    match_metadata t m ->
    match_metadata t' m'.
Proof.
  induction l; intros.
  simpl in H. inv H. assumption.
  simpl in H.
  repeat (try (break_let; subst); try (break_match_hyp; try congruence)).
  eapply IHl; eauto.
  
  unfold store_global_bits in Heqo.
  repeat break_match_hyp; try congruence; subst; try opt_inv; subst.
  eapply match_set_perm; eauto.
  eapply match_set_perm; eauto.
  eapply match_set_perm; [ | eassumption].
  eapply store_init_data_list_match_md; eauto.
  eapply store_zeros_bits_match_md; eauto.
Qed.

Lemma alloc_only_globals_bits_match_md :
  forall l t m ge m' t' l',
    alloc_only_globals_bits t ge m l = Some (m',t',l') ->
    match_metadata t m ->
    match_metadata t' m'.
Proof.
  induction l; intros.
  * simpl in H. inv H. congruence.
  * simpl in H. repeat (break_match_hyp; try congruence); subst; opt_inv; subst.
    eapply IHl; eauto.
    unfold alloc_only_global_bits in Heqo.
    repeat (break_match_hyp; try congruence);
      try opt_inv; subst;
      eapply match_drop_perm; try eapply match_alloc; eauto.
Qed.


Lemma alloc_only_globals_bits_contents :
  forall l t ge m m' t' l',
    alloc_only_globals_bits t ge m l = Some (m',t',l') ->
    (forall b ofs, ZMap.get ofs (Mem.mem_contents m) !! b = Undef) ->
    (forall b ofs, ZMap.get ofs (Mem.mem_contents m') !! b = Undef).
Proof.
  induction l; intros; simpl in *; try congruence.
  repeat (break_match_hyp; try congruence); repeat opt_inv; subst.
  app IHl Heqo0.
  destruct a; simpl in *.
  repeat (break_match_hyp; try congruence); repeat opt_inv; subst;
  NP _app Mem.mem_contents_alloc Mem.alloc;
  unfold Mem.drop_perm in *;
  repeat break_match_hyp; try congruence; opt_inv; subst; simpl; intros;
  rewrite Heqp;
  destruct (peq b0 b1); try subst;
  try rewrite PMap.gso by congruence;
  try rewrite PMap.gss;
  try eapply H0;
  rewrite ZMap.gi;
  reflexivity.
Qed.

  
(* Inductive globvar_contents_bits (ge : Genv.t fundef unit) (md : allocator_metadata) : list init_data -> list memval -> Prop := *)
(* | gc_nil_bits : globvar_contents_bits ge md nil nil *)
(* | gc_int8_bits : *)
(*     forall l l', *)
(*       globvar_contents_bits ge md l l' -> *)
(*       forall n, *)
(*         globvar_contents_bits ge md ((Init_int8 n) :: l) ((encode_val_bits Mint8unsigned (Vint n)) ++ l') *)
(* | gc_int16_bits : *)
(*     forall l l', *)
(*       globvar_contents_bits ge md l l' -> *)
(*       forall n, *)
(*         globvar_contents_bits ge md ((Init_int16 n) :: l) ((encode_val_bits Mint16unsigned (Vint n)) ++ l') *)
(* | gc_int32_bits : *)
(*     forall l l', *)
(*       globvar_contents_bits ge md l l' -> *)
(*       forall n, *)
(*         globvar_contents_bits ge md ((Init_int32 n) :: l) ((encode_val_bits Mint32 (Vint n)) ++ l') *)
(* | gc_int64_bits : *)
(*     forall l l', *)
(*       globvar_contents_bits ge md l l' -> *)
(*       forall n, *)
(*         globvar_contents_bits ge md ((Init_int64 n) :: l) ((encode_val_bits Mint64 (Vlong n)) ++ l') *)
(* | gc_float32_bits : *)
(*     forall l l', *)
(*       globvar_contents_bits ge md l l' -> *)
(*       forall n, *)
(*         globvar_contents_bits ge md ((Init_float32 n) :: l) ((encode_val_bits Mfloat32 (Vsingle n)) ++ l') *)
(* | gc_float64_bits : *)
(*     forall l l', *)
(*       globvar_contents_bits ge md l l' -> *)
(*       forall n, *)
(*         globvar_contents_bits ge md ((Init_float64 n) :: l) ((encode_val_bits Mfloat64 (Vfloat n)) ++ l') *)
(* | gc_space_bits : *)
(*     forall l l', *)
(*       globvar_contents_bits ge md l l' -> *)
(*       forall k, *)
(*         globvar_contents_bits ge md ((Init_space k) :: l) ((list_repeat (nat_of_Z k) Undef) ++ l') *)
(* | gc_addrof_bits : *)
(*     forall l l', *)
(*       globvar_contents_bits ge md l l' -> *)
(*       forall symb ofs b bits, *)
(*         Genv.find_symbol ge symb = Some b -> *)
(*         pinj md b ofs = Some bits -> *)
(*         globvar_contents_bits ge md ((Init_addrof symb ofs) :: l) ((encode_val_bits Mint32 (Vint bits))). *)

(* Inductive globvar_contents (ge : Genv.t fundef unit) (md : allocator_metadata) : list init_data -> list memval -> Prop := *)
(* | gc_nil : globvar_contents ge md nil nil *)
(* | gc_int8 : *)
(*     forall l l', *)
(*       globvar_contents ge md l l' -> *)
(*       forall n, *)
(*         globvar_contents ge md ((Init_int8 n) :: l) ((encode_val_bits Mint8unsigned (Vint n)) ++ l') *)
(* | gc_int16 : *)
(*     forall l l', *)
(*       globvar_contents ge md l l' -> *)
(*       forall n, *)
(*         globvar_contents ge md ((Init_int16 n) :: l) ((encode_val_bits Mint16unsigned (Vint n)) ++ l') *)
(* | gc_int32 : *)
(*     forall l l', *)
(*       globvar_contents ge md l l' -> *)
(*       forall n, *)
(*         globvar_contents ge md ((Init_int32 n) :: l) ((encode_val_bits Mint32 (Vint n)) ++ l') *)
(* | gc_int64 : *)
(*     forall l l', *)
(*       globvar_contents ge md l l' -> *)
(*       forall n, *)
(*         globvar_contents ge md ((Init_int64 n) :: l) ((encode_val_bits Mint64 (Vlong n)) ++ l') *)
(* | gc_float32 : *)
(*     forall l l', *)
(*       globvar_contents ge md l l' -> *)
(*       forall n, *)
(*         globvar_contents ge md ((Init_float32 n) :: l) ((encode_val_bits Mfloat32 (Vsingle n)) ++ l') *)
(* | gc_float64 : *)
(*     forall l l', *)
(*       globvar_contents ge md l l' -> *)
(*       forall n, *)
(*         globvar_contents ge md ((Init_float64 n) :: l) ((encode_val_bits Mfloat64 (Vfloat n)) ++ l') *)
(* | gc_space : *)
(*     forall l l', *)
(*       globvar_contents ge md l l' -> *)
(*       forall k, *)
(*         globvar_contents ge md ((Init_space k) :: l) ((list_repeat (nat_of_Z k) Undef) ++ l') *)
(* | gc_addrof : *)
(*     forall l l', *)
(*       globvar_contents ge md l l' -> *)
(*       forall symb ofs b, *)
(*         Genv.find_symbol ge symb = Some b -> *)
(*         globvar_contents ge md ((Init_addrof symb ofs) :: l) ((encode_val_bits Mint32 (Vptr b ofs))). *)

(* Above we have what it means for a list of init values to map to mem contents *)

(* We want to argue that at each step, getN memory contents line up with what they should be *)
(* Also we want to argue that globvar_contents is frag_equiv *)




(* We want some commuting lemma here *)
(* like: if I have frag_equiv memories, and I alloc *)

Lemma frag_equiv_alloc_only_unchanged :
  forall l m m' t ge t' ll,
  (forall b ofs, ZMap.get ofs ((Mem.mem_contents m) !! b) = Undef) ->
    alloc_only_globals_bits t ge m l = Some (m',t',ll) ->
    forall b ofs, ZMap.get ofs ((Mem.mem_contents m') !! b) = Undef.
Proof.
  induction l; intros; simpl in *.
  inv H0. apply H.

  repeat break_match_hyp; try congruence.
  repeat (opt_inv; subst).
  app IHl Heqo0.
  unfold alloc_only_global_bits in Heqo.
  destruct a.
  repeat (break_match_hyp; try congruence);
    repeat (opt_inv; subst);
  NP _app Mem.mem_contents_alloc Mem.alloc;
  unfold Mem.drop_perm in *;
  try break_match_hyp; try congruence;
  repeat (opt_inv; subst); simpl;
  try rewrite Heqp;
  clear Heqo0; clear H0;

  intros; destruct (peq b1 b0); try subst;
  try rewrite PMap.gss; try rewrite PMap.gso by congruence;
  try apply H; rewrite ZMap.gi; reflexivity.
  
Qed.


Inductive same_globals : list (ident * globdef fundef unit) -> list (ident * block * globdef fundef unit) -> Prop :=
| sg_empty :
      same_globals nil nil
| sg_app :
    forall b id g l l',
      same_globals l l' ->
      same_globals (l ++ (id,g)::nil) (l' ++ (id,b,g)::nil).

Lemma alloc_only_globals_bits_app :
  forall a (ge : Genv.t fundef unit) m b m' t t' ll,
    alloc_only_globals_bits t ge m (a ++ b) = Some (m',t',ll) ->
    exists m0 t0 a0 b0,
      alloc_only_globals_bits t ge m a = Some (m0,t0,a0) /\ alloc_only_globals_bits t0 ge m0 b = Some (m',t',b0) /\ ll = a0 ++ b0.
Proof.
  induction a; intros.
  exists m. simpl in *. eexists. eexists. eexists.
  split; try split. eassumption. reflexivity.
  simpl in H. repeat break_match_hyp; try congruence.
  repeat (opt_inv; subst).
  use IHa; eauto. repeat break_exists; repeat break_and. subst.
  simpl. repeat collapse_match.
  repeat eexists. assumption.
Qed.

Lemma same_globals_alloc_only_globals_bits :
  forall l t ge m m' t' ll,
    alloc_only_globals_bits t ge m l = Some (m',t',ll) ->
    same_globals l ll.
Proof.
  induction l using rev_ind; intros.
  simpl in H. inv H. econstructor.
  simpl in H.


  use alloc_only_globals_bits_app; eauto.
  repeat break_exists; repeat break_and.
  simpl in *.  
  repeat (break_match_hyp; try congruence);
    repeat (opt_inv; subst).
  use IHl; eauto.
  destruct x.
  unfold alloc_only_global_bits in Heqo.
  repeat break_match_hyp; try congruence;
  repeat (opt_inv; subst);
  econstructor; eauto.
  
Qed.

Inductive correct_blocks : list (ident * block * globdef fundef unit) -> block -> Prop :=
| Zero : forall p,
           correct_blocks nil p
| More : forall id b g r,
           correct_blocks r (Pos.succ b) ->
           correct_blocks ((id,b,g) :: r) b.


Lemma correct_blocks_alloc :
  forall l t ge m m' t' ll,
    alloc_only_globals_bits t ge m l = Some (m',t',ll) ->
    correct_blocks ll (Mem.nextblock m).
Proof.
  induction l; intros.
  simpl in H.
  inv H. econstructor.
  simpl in H. repeat break_match_hyp; try congruence.
  repeat (opt_inv; subst).
  NP _app alloc_only_global_bits_result alloc_only_global_bits.
  repeat break_and. subst.
  econstructor.
  rewrite <- H2.
  eapply IHl; eauto.
Qed.

Lemma alloc_globals_app :
  forall a (ge : Genv.t fundef unit) m b m',
    Genv.alloc_globals ge m (a ++ b) = Some m' ->
    exists m0,
      Genv.alloc_globals ge m a = Some m0 /\ Genv.alloc_globals ge m0 b = Some m'.
Proof.
  induction a; intros.
  exists m. simpl in *. split; auto.
  simpl in H. break_match_hyp; try congruence.
  use IHa; eauto. break_exists; break_and.
  simpl. collapse_match.
  eauto.
Qed.


Lemma store_globals_bits_app :
  forall a (ge : Genv.t fundef unit) t m b m' t',
    store_globals_bits t ge m (a ++ b) = Some (m',t') ->
    exists m0 t0,
      store_globals_bits t ge m a = Some (m0,t0) /\ store_globals_bits t0 ge m0 b = Some (m',t').
Proof.
  induction a; intros.
  exists m. exists t. simpl in *. split; auto.
  simpl in H.
  subst. repeat break_let. subst.  
  break_match_hyp; try congruence.
  subst. repeat break_let. subst.  
  use IHa; eauto. repeat break_exists; break_and.
  simpl. collapse_match.
  eauto.
Qed.


Lemma contents_drop_perm :
  forall m b lo hi p m',
    Mem.drop_perm m b lo hi p = Some m' ->
    Mem.mem_contents m = Mem.mem_contents m'.
Proof.
  intros.
  unfold Mem.drop_perm in *.
  repeat break_match_hyp; try opt_inv; simpl; try congruence.
Qed.

Lemma frag_equiv_store_init_data_list :
  forall l t ge m m' b ofs mB mB',
    (forall b ofs, frag_equiv t (Mem.mem_contents m) !! b (Mem.mem_contents m') !! b ofs) ->
    Genv.store_init_data_list ge m b ofs l = Some mB ->
    store_init_data_list_bits t ge m' b ofs l = Some mB' ->
    (forall b ofs, frag_equiv t (Mem.mem_contents mB) !! b (Mem.mem_contents mB') !! b ofs).
Proof.
  induction l; intros.
  simpl in *. repeat opt_inv. subst. apply H.
  simpl in *.
  repeat break_match_hyp; try congruence.
  use IHl; try apply H0; try apply H1; try apply H; try apply H2.
  intros.
  clear H0 H1 H2.

  destruct a; simpl in *;
  repeat opt_inv; subst; try solve [apply H];
  try solve [
  NP _app Mem.store_mem_contents Mem.store;
  unfold store_bits in *;
  break_match_hyp; try congruence; opt_inv; simpl;
  clear H2; rewrite Heqo0;
  use frag_equiv_pres; try apply H;
  unfold encode_val_bits in H1;
  destruct (peq b b1); subst;
  try solve [
        try specialize (H1 (Vint i) (Vint i) eq_refl);
        try specialize (H1 (Vlong i) (Vlong i) eq_refl);
        try specialize (H1 (Vsingle f) (Vsingle f) eq_refl);
        try specialize (H1 (Vfloat f) (Vfloat f) eq_refl);
        repeat rewrite PMap.gss; apply H1];
  try solve [repeat rewrite PMap.gso by congruence;
              apply H]].


  repeat (break_match_hyp; try congruence).
  NP _app Mem.store_mem_contents Mem.store;
  unfold store_bits in *;
  break_match_hyp; try congruence; opt_inv; simpl;
  clear H2; rewrite Heqo0;
  use frag_equiv_pres; try apply H;
  unfold encode_val_bits in H1;
  destruct (peq b b1); subst;
  try solve [repeat rewrite PMap.gso by congruence;
              apply H].
  specialize (H1 (Vptr b2 i0) (Vint i1)).
  simpl in H1. use H1. eexists; eauto.
  repeat rewrite PMap.gss. specialize (H3 Mint32). simpl in H3. apply H3.
  
Qed.



Lemma frag_equiv_store_zeros :
  forall hi lo b m m' t mB mB',
    (forall b ofs, frag_equiv t (Mem.mem_contents m) !! b (Mem.mem_contents m') !! b ofs) ->
    store_zeros m b lo hi = Some mB ->
    store_zeros_bits m' b lo hi = Some mB' ->
    (forall b ofs, frag_equiv t (Mem.mem_contents mB) !! b (Mem.mem_contents mB') !! b ofs).
Proof.
  induction hi using Z_nat_ind; intros;
  rewrite store_zeros_equation in *;
  rewrite store_zeros_bits_equation in *;
  try break_match_hyp; try omega;
  repeat (opt_inv; subst).
  apply H.
  repeat (break_match_hyp; try congruence).
  rewrite store_zeros_equation in *;
  rewrite store_zeros_bits_equation in *;
  try break_match_hyp; try omega.
  repeat (opt_inv; subst).
  NP _app Mem.store_mem_contents Mem.store. find_rewrite.
  unfold store_bits in *. break_match_hyp; try congruence.
  opt_inv. simpl.
  destruct (peq b b0). subst. repeat rewrite PMap.gss.
  use frag_equiv_pres; simpl in *; eauto.
  specialize (H1 Vzero Vzero eq_refl Mint8unsigned).
  simpl in H1. apply H1.
  repeat rewrite PMap.gso by congruence.
  apply H.

  apply H0.

  repeat (break_match_hyp; try congruence).
  replace (hi + 1 - 1) with hi in * by omega.
  use (IHhi (lo + 1)); try apply H1; try apply H2.

  intros. clear H3.
  NP _app Mem.store_mem_contents Mem.store. find_rewrite.
  unfold store_bits in *. break_match_hyp; try congruence.
  opt_inv. simpl.
  destruct (peq b b1). subst. repeat rewrite PMap.gss.
  use frag_equiv_pres; simpl in *; eauto.
  specialize (H4 Vzero Vzero eq_refl Mint8unsigned).
  simpl in H4. apply H4.
  repeat rewrite PMap.gso by congruence.
  apply H0.
  apply H3.
Qed.
  
    
Lemma frag_equiv_store_global :
  forall ge id g m m' t mB mB' t',
    (forall b ofs, frag_equiv t (Mem.mem_contents m) !! b (Mem.mem_contents m') !! b ofs) ->
    Genv.alloc_global ge m (id,g) = Some mB ->
    store_global_bits t ge m' (Mem.nextblock m) g = Some (mB',t') ->
    (forall b ofs, frag_equiv t' (Mem.mem_contents mB) !! b (Mem.mem_contents mB') !! b ofs).
Proof.
  intros.
  unfold Genv.alloc_global in *.
  unfold store_global_bits in *.
  destruct g; simpl in *.
  * repeat break_let; subst.
    break_match_hyp; try congruence; try opt_inv; subst; simpl in *.
    unfold set_perm in *.
    break_match_hyp; try congruence. simpl in *.
    opt_inv. clear H2.
    unfold Mem.drop_perm in *.
    break_match_hyp; try congruence. opt_inv. subst.
    simpl.
    NP _app Mem.mem_contents_alloc Mem.alloc.
    rewrite Heqp.
    destruct (peq b b0).
    - subst b0.
      unfold frag_equiv.
      rewrite PMap.gss. simpl.
      rewrite ZMap.gi. auto.

    - rewrite PMap.gso by congruence.
      apply H.

  * 
    repeat (break_match_hyp; try congruence); repeat opt_inv; subst.
    unfold set_perm in *.
    unfold Mem.drop_perm in *.
    repeat break_match_hyp; try congruence;
    repeat opt_inv; subst. simpl.
    NP _app Mem.alloc_result Mem.alloc. subst b0.
    eapply frag_equiv_store_init_data_list;
      try eapply Heqo3; try eapply Heqo0.
    intros.
    eapply frag_equiv_store_zeros;
      try apply Heqo2; try apply Heqo.
    intros.
    NP _app Mem.mem_contents_alloc Mem.alloc.
    rewrite H0.
    destruct (peq (Mem.nextblock m) b1).
    subst. rewrite PMap.gss.
    unfold frag_equiv.
    rewrite ZMap.gi. auto.
    rewrite PMap.gso by congruence.
    apply H.
Qed.

Lemma correct_blocks_head :
  forall l l' b,
    correct_blocks (l ++ l') b ->
    correct_blocks l b.
Proof.
  induction l; intros;
  try econstructor; eauto.
  simpl in H. inv H.
  econstructor; eauto.
Qed.

Lemma correct_blocks_tail :
  forall l l' b,
    correct_blocks (l ++ l') b ->
    exists b',
      correct_blocks l' b'.
Proof.
  induction l; intros.
  simpl in H. eauto.
  simpl in H. inv H.
  use IHl; eauto.
Qed.



Lemma correct_blocks_nextblock :
  forall l l',
    same_globals l l' ->
    forall id b g m ge x1,
      correct_blocks (l' ++ (id,b,g)::nil) (Mem.nextblock m) ->
      Genv.alloc_globals ge m l = Some x1 ->
      b = Mem.nextblock x1.
Proof.
  induction 1; intros.
  simpl in H0. inv H0.
  simpl in H. inv H. reflexivity.
  app correct_blocks_head H0.

  app alloc_globals_app H1.
  break_and.
  use IHsame_globals; try apply H1.
  apply H0.

  rewrite app_ass in H2. simpl in H2.
  app Genv.alloc_globals_nextblock H4. rewrite H4.
  simpl.
  rewrite <- H5.
  app correct_blocks_tail H2.
  inv H2. inv H15. reflexivity.
Qed.

(* same block thing *)
Lemma frag_equiv_store_gs_ind :
  forall ge l l',
    same_globals l l' ->
    forall m m' t mB mB' t',
      correct_blocks l' (Mem.nextblock m) ->
      (forall b ofs, frag_equiv t (Mem.mem_contents m) !! b (Mem.mem_contents m') !! b ofs) ->
      Genv.alloc_globals ge m l = Some mB ->
      store_globals_bits t ge m' l' = Some (mB',t') ->
      (forall b ofs, frag_equiv t' (Mem.mem_contents mB) !! b (Mem.mem_contents mB') !! b ofs).
Proof.
  induction 1; intros;
  simpl in *;
  repeat (opt_inv; subst).
  apply H0.

  use alloc_globals_app; eauto.
  use store_globals_bits_app; eauto.
  repeat break_exists; repeat break_and.
  use IHsame_globals; eauto.

  eapply correct_blocks_head; eauto.
  
  simpl in H8.
  break_match_hyp; try congruence.
  break_let. subst. opt_inv. subst.
  unfold Genv.alloc_globals in H9.
  break_match_hyp; try congruence.
  opt_inv.
  simpl. subst.
  
  assert (b = Mem.nextblock x1).
  {

    eapply correct_blocks_nextblock; eauto.
    
  } idtac.
  subst.
  eapply frag_equiv_store_global; try apply Heqo0; try apply Heqo.
  eassumption.
Qed.


Lemma append_nil :
  forall {A} (l : list A) (x y : A),
    x :: nil = l ++ y :: nil ->
    l = nil.
Proof.
  induction l; intros; try reflexivity.
  simpl in H. inv H.
  destruct l. simpl in H2. congruence.
  simpl in H2.
  congruence.
Qed.
  

Lemma frag_equiv_store_globals_bits :
  forall l ll ge m t m' m0 m0' t' m00 ti,
    Mem.nextblock m = Mem.nextblock m00 ->
    (forall b ofs, ZMap.get ofs ((Mem.mem_contents m) !! b) = Undef) ->
    (forall b ofs, ZMap.get ofs ((Mem.mem_contents m00) !! b) = Undef) ->
      Genv.alloc_globals ge m l = Some m' ->
      alloc_only_globals_bits ti ge m00 l = Some (m0,t,ll) ->
      store_globals_bits t ge m0 ll = Some (m0', t') ->
      (forall b ofs, frag_equiv t' (Mem.mem_contents m') !! b (Mem.mem_contents m0') !! b ofs).
Proof.
  intros.
  use frag_equiv_alloc_only_unchanged; eauto.
  use same_globals_alloc_only_globals_bits; eauto.

  eapply frag_equiv_store_gs_ind; eauto.

  rewrite H.
  eapply correct_blocks_alloc; eauto.
  intros.
  
  unfold frag_equiv.
  rewrite H0.
  auto.
  
Qed.



Fixpoint get_globdef (b : block) (l : list (ident * block * globdef fundef unit)) : option (globdef fundef unit) :=
  match l with
    | nil => None
    | (_,b',g) :: r => if peq b b' then Some g else get_globdef b r
  end.

Definition global_size (g : globdef fundef unit) : Z :=
  match g with
    | Gfun _ => 1
    | Gvar v => Genv.init_data_list_size (gvar_init v)
  end.

(* everything that should be untouched is untouched *)
Definition in_global_range (b : block) (z : Z) (l : list (ident * block * globdef fundef unit)) : Prop :=
  exists g,
    get_globdef b l = Some g /\
    0 <= z < global_size g.


Lemma in_range_dec :
  forall (a b c : Z),
    {a <= b < c} + { b < a \/ b >= c }.
Proof.
  intros.
  destruct (zlt b a).
  right. omega.
  destruct (zlt b c).
  left. omega.
  right. omega.
Qed.

Lemma in_global_range_dec :
  forall l b z,
    { in_global_range b z l /\ exists g, get_globdef b l = Some g } + {~ in_global_range b z l}.
Proof.
  intros.
  destruct (get_globdef b l) eqn:?.
  assert ({0 <= z < global_size g} + {z < 0 \/ z >= global_size g}).
  apply in_range_dec.

  destruct H.
  left. split; unfold in_global_range; eauto.
  right. intro.
  unfold in_global_range in H.
  repeat break_exists. break_and.
  rewrite H in Heqo. inv Heqo.
  omega.

  right. intro.
  unfold in_global_range in *.
  break_exists. break_and.
  rewrite H in Heqo. congruence.
  
Qed.

Definition has_access (m : mem) (b : block) (ofs : Z) (op : option permission) : Prop :=
  forall k, PMap.get b (Mem.mem_access m) ofs k = op.

Definition final_global_perm (g : globdef fundef unit) : permission :=
  match g with
    | Gfun _ => Nonempty
    | Gvar v => Genv.perm_globvar v
  end.

Definition globs_access (m : mem) (l : list (ident * block * globdef fundef unit)) : Prop :=
  forall b z g,
    in_global_range b z l ->
    get_globdef b l = Some g ->
    has_access m b z (Some (final_global_perm g)).

Definition no_other_access (m : mem) (l : list (ident * block * globdef fundef unit)) : Prop :=
  forall b z,
    ~ in_global_range b z l ->
    has_access m b z None.
  
Lemma perm_same_globs :
  forall m m' l,
    globs_access m l ->
    globs_access m' l ->
    no_other_access m l ->
    mem_perm_same m m'.
Proof.
  intros.
  unfold mem_perm_same.
  intros.
  destruct (in_global_range_dec l b x).
  break_and.
  break_exists.
  unfold globs_access in H.
  use H; eauto. unfold has_access in H5.
  rewrite H5 in H2.
  inv H2.
  unfold globs_access in H0.
  use H0; eauto.
  
  app H1 n.
  unfold has_access in n.
  rewrite n in H2. congruence.
Qed.

Lemma get_globdef_end :
  forall l b id' b' g' g,
    get_globdef b (l ++ (id',b',g') :: nil) = Some g ->
    get_globdef b l = Some g \/
    (b = b' /\ g = g').
Proof.
  induction l; intros.
  simpl in H. break_match_hyp; right; split; congruence.
  
  simpl in *.
  repeat break_let. subst.
  break_match_hyp; try congruence. subst.
  left. auto.
  eapply IHl; eauto.
Qed.

Lemma get_globdef_tail :
  forall l b g,
    get_globdef b l = Some g ->
    forall l',
      get_globdef b (l ++ l') = Some g.
Proof.
  induction l; intros.
  simpl in H. congruence.
  simpl in *. repeat break_let.
  subst. break_match_hyp; try congruence.
  use IHl; eauto.
Qed.

Lemma correct_blocks_distinct_head_plt :
  forall l id' b' g' l' x,
    correct_blocks (l ++ (id',b',g') :: l') (Pos.succ x) ->
    Plt x b'.
Proof.
  induction l; intros.
  simpl in H. inv H.
  eapply Plt_succ.
  inv H.
  app IHl H3; eauto.
  eapply Plt_trans. eapply Plt_succ. assumption.
Qed.

Lemma correct_blocks_distinct_head :
  forall l id' b' g' l' x,
    correct_blocks (l ++ (id',b',g') :: l') (Pos.succ x) ->
    x <> b'.
Proof.
  intros.
  eapply Plt_ne;
    eapply correct_blocks_distinct_head_plt;
    eauto.
Qed.


Lemma block_unique :
  forall l id' b' b g' x y,
    correct_blocks (l ++ (id',b',g') :: nil) y ->
    get_globdef b l = Some x ->
    b <> b'.
Proof.
  induction l; intros.
  simpl in *. congruence.

  destruct a. destruct p. simpl in H.
  inv H.
  app correct_blocks_distinct_head H6.
  simpl in H0.
  break_match_hyp; try congruence.
  use IHl; eauto.
Qed.

Lemma in_global_range_end :
  forall l b z id' b' g' y,
    in_global_range b z (l ++ (id',b',g') :: nil) ->
    correct_blocks (l ++ (id',b',g') :: nil) y ->
    ((in_global_range b z l /\ b <> b') \/ (b = b' /\ 0 <= z < global_size g')).
Proof.
  intros.
  unfold in_global_range in *.
  repeat break_exists. repeat break_and.
  destruct (get_globdef b l) eqn:?.
  app get_globdef_end H.
  assert (g = x). {
    app get_globdef_tail Heqo.
    rewrite Heqo in H3. congruence.
  } idtac. subst.
  left.
  split; eauto.
  eapply block_unique; eauto.
  
  app get_globdef_end H.
  destruct H; try congruence.
  break_and. subst.
  right.
  split; eauto.
Qed.

Lemma correct_blocks_succ_tail :
  forall l id b g id' b' g' x l',
    correct_blocks (l ++ (id,b,g) :: (id',b',g') :: l') x ->
    b' = Pos.succ b.
Proof.
  induction l; intros.
  simpl in H. inv H. simpl in H5. inv H5.
  reflexivity.
  simpl in H. inv H.
  use IHl; eauto.
Qed.

Lemma correct_blocks_alloc_globals :
  forall l l',
    same_globals l l' ->
    forall ge m x id b g,
      Genv.alloc_globals ge m l = Some x ->
      correct_blocks (l' ++ (id,b,g) :: nil) (Mem.nextblock m) ->
      b = Mem.nextblock x.
Proof.
  induction 1; intros.
  simpl in H0. inv H0. simpl in H. congruence.
  eapply alloc_globals_app in H0.
  repeat (break_exists; break_and).
  
  app (correct_blocks_head (l' ++ (id,b,g) :: nil)) H1.
  assert (b0 = Pos.succ b).
  {
    repeat rewrite app_ass in H3.
    simpl in H3.
    use correct_blocks_succ_tail; eauto.
  }
  use IHsame_globals; eauto.
  simpl in H2.
  repeat break_match_hyp; try congruence; repeat (opt_inv; subst);
  NP _app Mem.nextblock_alloc Mem.alloc;
  unfold Mem.drop_perm in *;
  repeat break_match_hyp; try congruence; opt_inv; subst; simpl; auto.
  NP _app Genv.store_zeros_nextblock store_zeros.
  NP _app Genv.store_init_data_list_nextblock Genv.store_init_data_list.

  congruence.
Qed.

Lemma store_zeros_access :
  forall hi m b lo m',
    store_zeros m b lo hi = Some m' ->
    Mem.mem_access m = Mem.mem_access m'.
Proof.
  induction hi using Z_nat_ind; intros;
  rewrite store_zeros_equation in *.

  break_match_hyp; try congruence; try omega.
  break_match_hyp; try congruence; try omega.
  break_match_hyp; try congruence; try omega.
  replace (1-1) with 0 in * by omega.
  rewrite store_zeros_equation in *.
  break_match_hyp; try congruence; try omega.
  inv H.
  symmetry.
  eapply Mem.store_access; eauto.

  break_match_hyp; try congruence; try omega.
  break_match_hyp; try congruence; try omega.
  break_match_hyp; try congruence; try omega.

  replace (hi + 1 - 1) with hi in * by omega.
  use IHhi; eauto.

  NP _app Mem.store_access Mem.store. congruence.
Qed.


Lemma store_init_data_list_access :
  forall l (ge : Genv.t fundef unit) m b ofs m',
    Genv.store_init_data_list ge m b ofs l = Some m' ->
    Mem.mem_access m = Mem.mem_access m'.
Proof.
  induction l; intros.
  simpl in H. congruence.

  simpl in H. break_match_hyp; try congruence.
  app IHl H.

  destruct a; simpl in Heqo;
  try break_match_hyp;
  try (NP _app Mem.store_access Mem.store); try congruence.
    
Qed.

Lemma alloc_globals_access_other :
  forall (ge : Genv.t fundef unit) x id g m',
    Genv.alloc_global ge x (id,g) = Some m' ->
    forall b0,
      b0 <> Mem.nextblock x ->
      (Mem.mem_access m') !! b0 = (Mem.mem_access x) !! b0.
Proof.
  intros. simpl in H.
  repeat break_match_hyp; try congruence; repeat break_let; subst; simpl in *;
  unfold Mem.drop_perm in *; repeat break_match_hyp; try congruence;
  opt_inv; subst; simpl;
  NP _app Mem.alloc_result Mem.alloc; subst;
  rewrite PMap.gso by congruence;
  NP _app Mem.alloc_access_result Mem.alloc.

  rewrite H.
  rewrite PMap.gso by congruence. reflexivity.

  NP _app store_zeros_access store_zeros.
  NP _app store_init_data_list_access Genv.store_init_data_list.
  rewrite <- Heqo0.
  rewrite <- Heqo.
  rewrite H. rewrite PMap.gso by congruence.
  reflexivity.
Qed.



Lemma correct_blocks_get_globdef :
  forall l id b g x g',
    correct_blocks (l ++ (id,b,g) :: nil) x ->
    get_globdef b (l ++ (id,b,g) :: nil) = Some g' ->
    g = g'.
Proof.
  induction l; intros.
  simpl in H0. rewrite peq_true in H0.
  congruence.

  destruct a. destruct p.
  inv H.
  assert (x <> b) by (eapply correct_blocks_distinct_head; eauto).
  simpl in H0. break_match_hyp; try congruence.

  eapply IHl; eauto.

Qed.

Lemma z_range_helper :
  forall a b c,
    zle a b && zlt b c = false ->
    b < a \/ b >= c.
Proof.
  intros.
  rewrite andb_false_iff in H.
  break_or; [left | right];
  unfold proj_sumbool in *;
  break_match_hyp; try congruence; omega.
Qed.


Lemma alloc_globals_globs_access :
  forall l ll,
    same_globals l ll ->
    forall ge m m',
      correct_blocks ll (Mem.nextblock m) ->
      Genv.alloc_globals ge m l = Some m' ->
      globs_access m' ll.
Proof.
  induction 1; intros.
  unfold globs_access.
  intros.
  simpl in H2. congruence.

  app correct_blocks_head H0.
  app alloc_globals_app H1. break_and.
  use IHsame_globals; eauto.

  unfold globs_access in *.
  intros.
  eapply in_global_range_end in H8; eauto.
  app correct_blocks_alloc_globals H2; eauto.
  
  break_or; repeat break_and.
  {
    (* non-conflicting access *)
    match goal with
      | [ H : in_global_range _ _ _ |- _ ] => copy H; inv H
    end;
    match goal with
      | [ H : in_global_range _ _ _ |- _ ] => app H5 H;
          repeat break_and; eauto
    end.

    unfold has_access in *.
    intros.
    app get_globdef_tail H12. rewrite H12 in H9. inv H9.
    unfold Genv.alloc_globals in H4.
    break_match_hyp; try congruence. inv H4.

    use alloc_globals_access_other; eauto.
    rewrite H4 by congruence. apply H11.

  } {
    (* the global that we just stored *)
    
    subst. unfold has_access.
    intros.
    simpl in H4.
    repeat break_match_hyp; try congruence;
    NP _app Mem.alloc_result Mem.alloc; subst;
    opt_inv; subst;
    unfold Mem.drop_perm in *;
    repeat break_match_hyp; try congruence;
    opt_inv; subst; simpl;
    rewrite PMap.gss;
    break_match; try omega;
    try f_equal;
    use correct_blocks_get_globdef; eauto; subst g0; simpl; try reflexivity;
    app z_range_helper Heqb;
    simpl in *; omega.

  }
Qed.

Lemma correct_blocks_store_bits_other_access :
  forall l b,
    correct_blocks l b ->
    forall t ge m m' t',
      store_globals_bits t ge m l = Some (m',t') ->
      forall b' z k,
        Plt b' b ->
        (Mem.mem_access m') !! b' z k = (Mem.mem_access m) !! b' z k.
Proof.
  induction l; intros.
  simpl in H0. inv H0. reflexivity.

  simpl in H0. repeat break_match_hyp; try congruence; subst.
  inv H.
  app IHl H0;
    try solve [
          try eapply Plt_trans; try apply H1;
          try eapply Plt_succ].
  rewrite H0.
  clear H. clear IHl.
  symmetry.
  eapply store_global_bits_access; eauto.
  app Plt_ne H1.
  
Qed.

Lemma store_globals_bits_globs_access :
    forall ll  x,
      correct_blocks ll x ->
      forall ge m m' t t',
        store_globals_bits t ge m ll = Some (m',t') ->
        globs_access m' ll.
Proof.
  induction 1; intros.
  unfold globs_access. intros.
  simpl in H1.
  congruence.
  unfold globs_access. intros.
  simpl in H2. break_match_hyp; try congruence.
  subst. opt_inv; subst.
  inv H1. break_and.
  simpl in H1. rewrite peq_true in H1.
  inv H1.
  simpl in H0. break_match_hyp; try congruence.
  break_let. subst.
  unfold has_access.
  intros.


  
  app correct_blocks_store_bits_other_access H0;
    try solve [  eapply Plt_succ].
    rewrite H0.
  clear H0.


  unfold store_global_bits in Heqo.
  repeat break_match_hyp; try congruence;
  try opt_inv; subst;
  unfold set_perm in *;
  repeat break_match_hyp; try congruence;
  opt_inv; subst; simpl;

  clear H1; simpl in *;
  rewrite PMap.gss.

  rewrite Zmax_spec.
  repeat break_match; try congruence; try omega.
  unfold proj_sumbool in *. repeat break_match_hyp; try congruence; try omega.
  simpl in *. congruence.
  app z_range_helper Heqb0. omega.
  break_match; try congruence.
  app z_range_helper Heqb0. omega.
  break_match; try congruence.
  app z_range_helper Heqb0. omega.


  

  inv H1. break_and.
  simpl in H1. break_match_hyp; try congruence.
  rewrite H2 in H1; opt_inv; subst.
  clear Heqs. clear Heqs0.
  simpl in H0. break_match_hyp; try congruence.
  break_let. subst.
  app IHcorrect_blocks H0.
  unfold globs_access in H0.
  eapply H0; eauto.
  econstructor; eauto.
Qed.

Lemma not_in_global_range_app :
  forall l b z id b' g,
    ~ in_global_range b z (l ++ (id,b',g) :: nil) ->
    ~ in_global_range b z l.
Proof.

  intros. 
  intro.
  apply H. inv H0. econstructor. 
  break_and.
  erewrite get_globdef_tail; eauto.
Qed.

Lemma correct_blocks_global_size :
  forall l' x id b g,
    correct_blocks (l' ++ (id,b,g) :: nil) x ->
    forall z,
      0 <= z < global_size g ->
      in_global_range b z (l' ++ (id,b,g) :: nil).
Proof.
  induction l'; intros.
  inv H. inv H6. econstructor. simpl.
  rewrite peq_true. split; auto.

  destruct a. destruct p.
  simpl in H. inv H. app IHl' H6.
  inv H6. break_and.
  app correct_blocks_distinct_head H.
  
  econstructor; eauto.
  
  simpl. break_match; try congruence.
  rewrite H1. split; auto.
Qed.

Lemma has_no_other_access_alloc_globals_ind :
  forall l ll,
    same_globals l ll ->
    forall m,
      correct_blocks ll (Mem.nextblock m) ->
      forall ge m',
        Genv.alloc_globals ge m l = Some m' ->
        forall b z k,
          ~ in_global_range b z ll ->
          (Mem.mem_access m) !! b z k = (Mem.mem_access m') !! b z k.
Proof.
  induction 1; intros.
  simpl in H0. congruence.
  app correct_blocks_head H0.
  app alloc_globals_app H1. break_and.
  app not_in_global_range_app H2. 
  app IHsame_globals H1. rewrite H1.


  app correct_blocks_alloc_globals H7.
  subst b.

  assert (b0 <> Mem.nextblock x \/ (b0 = Mem.nextblock x /\ (~ 0 <= z < global_size g))).
  {
    destruct (peq b0 (Mem.nextblock x)); auto.
    right. split; auto.
    intro. apply H6.
    subst b0.
    eapply correct_blocks_global_size; eauto.

  } idtac.

  destruct H7.
  unfold Genv.alloc_globals in H5.
  break_match_hyp; try congruence.
  
  app alloc_globals_access_other Heqo.
  rewrite <- Heqo. inv H5. reflexivity.
  repeat break_and. subst b0.
  clear H1.
  simpl in H5.
  repeat break_match_hyp; try congruence; try opt_inv; subst;
  NP _app Mem.alloc_result Mem.alloc; subst;
  NP _app Mem.alloc_access_result Mem.alloc.
  unfold Mem.drop_perm in *.
  break_match_hyp; try congruence.
  opt_inv. simpl.
  repeat break_and. clear H10.
  rewrite H1.
  repeat rewrite PMap.gss.
  repeat break_match; try reflexivity; try congruence.
  unfold proj_sumbool in Heqb. repeat break_match_hyp; simpl in *; try congruence; try omega.
  rewrite Mem.nextblock_noaccess. reflexivity.
  intro. app Plt_ne H7.

  unfold Mem.drop_perm in *.
  break_match_hyp; try congruence.
  opt_inv. simpl. clear H10.

  NP _app store_init_data_list_access Genv.store_init_data_list.
  NP _app store_zeros_access store_zeros.
  rewrite <- Heqo1. rewrite <- Heqo0.
  
  rewrite H1.
  repeat rewrite PMap.gss.
  repeat break_match; try reflexivity; try congruence.
  unfold proj_sumbool in Heqb. repeat break_match_hyp; simpl in *; try congruence; try omega.
  rewrite Mem.nextblock_noaccess. reflexivity.
  intro. 
  app Plt_ne H11.

Qed.
  

Lemma no_other_access_alloc_globals :
  forall l ll,
    same_globals l ll ->
    forall ge minit m,
      correct_blocks ll (Mem.nextblock minit) ->
      Genv.alloc_globals ge minit l = Some m ->
      (forall b ofs, has_access minit b ofs None) ->
      no_other_access m ll.
Proof.
  intros.
  unfold no_other_access. intros.

  unfold has_access in *.
  intros.
  erewrite <- has_no_other_access_alloc_globals_ind; eauto.
Qed.
  
  
  
Lemma perm_same_alloc_globals :
  forall ge minit l m tinit m0 t ll m' tt,
    (forall b ofs, has_access minit b ofs None) ->
    Genv.alloc_globals ge minit l = Some m ->
    alloc_only_globals_bits tinit ge minit l = Some (m0,t,ll) ->
    store_globals_bits t ge m0 ll = Some (m',tt) ->
    mem_perm_same m m'.
Proof.
  (* Genv.alloc_globals will set the perm of each global to what it should be *)
  (* alloc_only_globals_bits will set to writeable  *)
  (* store_globals_bits will set to proper perm *)
  intros.
  NP _app same_globals_alloc_only_globals_bits alloc_only_globals_bits.
  NP _app correct_blocks_alloc alloc_only_globals_bits.
  
  eapply perm_same_globs.
  eapply alloc_globals_globs_access; eauto.
  eapply store_globals_bits_globs_access; eauto.
  eapply no_other_access_alloc_globals; eauto.
Qed.


Lemma no_pointer_set_perm :
  forall m b lo hi p m',
    set_perm m b lo hi p = Some m' ->
    (forall b' ofs', no_pointer (Mem.mem_contents m) !! b' ofs') ->
    (forall b' ofs', no_pointer (Mem.mem_contents m') !! b' ofs').
Proof.
  intros.
  unfold set_perm in *.
  repeat (break_match_hyp; try congruence); try opt_inv; subst; simpl in *; eauto.
Qed.

Lemma no_pointer_store_bits :
  forall c m b ofs v m',
    store_bits c m b ofs v = Some m' ->
    (forall b' ofs', v <> Vptr b' ofs') ->
    (forall b' ofs', no_pointer (Mem.mem_contents m) !! b' ofs') ->
    (forall b' ofs', no_pointer (Mem.mem_contents m') !! b' ofs').
Proof.
  intros. unfold store_bits in *.
  repeat (break_match_hyp; try congruence); try opt_inv; subst; simpl in *; eauto.
  destruct (peq b b'); subst; try rewrite PMap.gso by congruence; eauto.
  rewrite PMap.gss.
  unfold no_pointer.
  break_match; auto.
  NP _app getN_in_or_out Mem.setN. clear H.
  break_or.
  unfold encode_val_bits in *.
  destruct v; destruct c; simpl in *; repeat break_or; try inv_false; try congruence;
  NP _app frag_not_in_inj_bytes inj_bytes; try inv_false.

  unfold no_pointer in *.
  specialize (H1 b' ofs').
  rewrite H in H1.
  assumption.
Qed.

Lemma no_pointer_store_init_data_list_bits :
  forall l t ge m b ofs m',
    store_init_data_list_bits t ge m b ofs l = Some m' ->
    (forall b' ofs', no_pointer (Mem.mem_contents m) !! b' ofs') ->
    (forall b' ofs', no_pointer (Mem.mem_contents m') !! b' ofs').
Proof.
  induction l; intros;
  simpl in *; try opt_inv; subst; eauto.
  repeat (break_match_hyp; try congruence).
  eapply IHl; eauto.
  destruct a; simpl in *;
  repeat (break_match_hyp; try congruence);
  try solve [eapply no_pointer_store_bits; eauto; try congruence].
  opt_inv; subst; eauto.
Qed.

Lemma no_pointer_store_zeros_bits :
  forall hi lo m b m',
    store_zeros_bits m b lo hi = Some m' ->
    (forall b' ofs', no_pointer (Mem.mem_contents m) !! b' ofs') ->
    (forall b' ofs', no_pointer (Mem.mem_contents m') !! b' ofs').
Proof.
  induction hi using Z_nat_ind; intros; rewrite store_zeros_bits_equation in *;
  break_match_hyp; try omega; try opt_inv; subst; eauto.

  break_match_hyp; try congruence.
  rewrite store_zeros_bits_equation in *.
  break_match_hyp; try omega.
  opt_inv; subst.
  eapply no_pointer_store_bits; eauto;
  unfold Vzero; congruence.
  
  break_match_hyp; try congruence.
  replace (hi + 1 - 1) with hi in * by omega.
  eapply IHhi; eauto.
  eapply no_pointer_store_bits; eauto;
  unfold Vzero; congruence.
Qed.

Lemma no_ptr_store_globals_bits :
  forall l t ge m m' t',
    store_globals_bits t ge m l = Some (m',t') ->
    (forall b ofs, no_pointer (Mem.mem_contents m) !! b ofs) ->
    (forall b ofs, no_pointer (Mem.mem_contents m') !! b ofs).
Proof.
  induction l; intros;
  simpl in H; repeat (break_match_hyp; try congruence);
  try opt_inv; subst; try congruence; eauto.
  eapply IHl; eauto. intros.
  unfold store_global_bits in *.
  repeat (break_match_hyp; try congruence); subst;
  opt_inv; subst;
  eapply no_pointer_set_perm; eauto.
  eapply no_pointer_store_init_data_list_bits; eauto.
  eapply no_pointer_store_zeros_bits; eauto.
Qed.



(* Here we are forced to "cheat" a bit, due to the cheats in higher levels in CompCert *)
(* Asm and AsmBits don't have identical initialization behavior, as Asm only allocated 1 byte per function, and AsmBits allocates a byte per instruction *)
Axiom init_match_metadata_left :
  forall (p : Asm.program) m m' t,
    Genv.init_mem p = Some m ->
    init_mem_bits p = Some (m',t) ->
    match_metadata t m.


Lemma init_equiv :
  forall (p : Asm.program) m m' t,
    Genv.init_mem p = Some m ->
    init_mem_bits p = Some (m',t) ->
    ptr_equiv_mem (Genv.globalenv p) t m m'.
Proof.
  intros.
  unfold ptr_equiv_mem.
  unfold Genv.init_mem in *.
  unfold init_mem_bits in *.
  unfold alloc_globals_bits in *.
  repeat break_match_hyp; try congruence; subst.

  unfold mem_contents_equiv.
  repeat match goal with
           | [ |- _ /\ _ ] => split
         end.

  * app alloc_globals_nextblock_match Heqo.
    app store_globals_bits_nextblock H0.
    unfold mem_nextblock_same.
    congruence.

  * eapply perm_same_alloc_globals; eauto.
    intros. unfold has_access.
    intros. unfold Mem.empty. simpl.
    rewrite PMap.gi. reflexivity.

  * eapply init_match_metadata_left;

    unfold Genv.init_mem; unfold init_mem_bits;
    unfold alloc_globals_bits;
    eauto.
    collapse_match.
    eauto.
    
  *
    NP _app store_globals_bits_md store_globals_bits. subst.    
    eapply store_globals_bits_match_md; eauto.
    eapply alloc_only_globals_bits_match_md; eauto.
    eapply match_init.


  * unfold contents_equiv.

    use alloc_only_globals_bits_contents; eauto.

    intros. unfold Mem.empty. simpl.
    rewrite PMap.gi. rewrite ZMap.gi. reflexivity.

    intros.
    NP _app frag_equiv_store_globals_bits store_globals_bits.

    split. eassumption.

    NP _app no_ptr_store_globals_bits store_globals_bits.
    intros.
    
    unfold no_pointer. simpl.
    rewrite H1. auto.
    
  * eapply globals_allocated_init; eauto.
    unfold init_mem_bits. unfold alloc_globals_bits.
    repeat collapse_match; eauto.

  * eapply store_globals_perms'; eauto.
    eapply alloc_only_globals_list; eauto.
    eapply alloc_only_globals_bits_list_norepet; eauto.
Qed.
    

Lemma ptr_equiv_init :
  forall (p : Asm.program) m,
    Genv.init_mem p = Some m ->
    exists m' t,
      init_mem_bits p = Some (m',t) /\ ptr_equiv_mem (Genv.globalenv p) t m m'.
Proof.
  intros.
  (* Show init doesn't fail *)
  app init_mem_bits_succeeds H.
  rewrite H. eexists; eexists; split; eauto.

  eapply init_equiv; eauto.
Qed.
