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
Require Import ProgPropDec.

Require Import AsmBits.
Require Import MemoryAxioms.
Require Import PtrEquivMem. (* helpful lemmas *)
Require Import MemBits.

Lemma no_ptr_mem_load :
  forall m,
    no_ptr_mem m ->
    forall c b ofs v,
      Mem.load c m b ofs = Some v ->
      forall x y,
        v <> Vptr x y.
Proof.
  intros. unfold no_ptr_mem in *.
  app Mem.load_result H0.
  subst v.
  unfold decode_val.
  break_match.
  break_match; try congruence.
  break_match; try congruence;
  unfold Val.load_result;
  unfold proj_value;
  try break_match; try congruence;
  simpl in *;
  try (break_match_hyp; try congruence).
  break_match_hyp; try congruence.
  specialize (H ofs b).
  rewrite Heqm1 in H. subst v. congruence.
  break_match_hyp; try congruence.
  specialize (H ofs b).
  rewrite Heqm1 in H. subst v. congruence.
  inv Heql.
  break_match; try congruence.

  specialize (H ofs b).
  rewrite H2 in H. apply H.
Qed.

Lemma goto_label_bits_mem :
  forall f l rs m rs' m' t b,
    goto_label_bits t f l b rs m = Nxt rs' m' t ->
    m = m'.
Proof.
  intros. unfold goto_label_bits in *.
  repeat break_match_hyp; try congruence.
Qed.


Lemma no_ptr_encode :
  forall v,
    (forall x y, v <> Vptr x y) ->
    forall v1 q n c,
      In (Fragment v1 q n) (encode_val_bits c v) ->
      (forall x y, v1 <> Vptr x y).
Proof.
  intros.
  destruct c; destruct v; try congruence;
  unfold encode_val_bits in *; simpl in *;
  repeat break_or; try inv_false;
  try congruence;
  app frag_not_in_inj_bytes H0.
Qed.

Lemma no_ptr_mem_preserved_store :
  forall m,
    no_ptr_mem m ->
    forall c b ofs v m',
      store_bits c m b ofs v = Some m' ->
      (forall x y, v <> Vptr x y) ->
      no_ptr_mem m'.
Proof.
  intros. unfold store_bits in H0.
  break_match_hyp; inv H0.
  unfold no_ptr_mem. intros. simpl.
  destruct (peq b ofs0).
  subst b.
  rewrite PMap.gss.
  break_match; eauto.
  app getN_in_or_out Heqm0.
  break_or.
  eapply no_ptr_encode; eauto.
  unfold no_ptr_mem in H.
  specialize (H z ofs0). rewrite H2 in H. apply H.
  rewrite PMap.gso by congruence. apply H.
Qed.

Lemma no_ptr_mem_preserved_alloc :
  forall m,
    no_ptr_mem m ->
    forall lo hi m' b,
      Mem.alloc m lo hi = (m',b) ->
      no_ptr_mem m'.
Proof.
  intros. app Mem.mem_contents_alloc H0.
  unfold no_ptr_mem.
  rewrite H0.
  intros.
  rewrite PMap.gsspec.
  destruct (peq ofs b).
  rewrite ZMap.gi. auto.
  apply H.
Qed.

Lemma no_ptr_mem_preserved_free :
  forall m,
    no_ptr_mem m ->
    forall lo hi m' b,
      Mem.free m b lo hi = Some m' ->
      no_ptr_mem m'.
Proof.
  intros. app Mem.free_result H0.
  subst m'. unfold Mem.unchecked_free in *.
  unfold no_ptr_mem. intros. simpl in *.
  apply H.
Qed.

Lemma no_ptr_empty :
  no_ptr_mem Memory.Mem.empty.
Proof.
  unfold no_ptr_mem.
  unfold Memory.Mem.empty.
  simpl.
  intros.
  rewrite PMap.gi. rewrite ZMap.gi.
  exact I.
Qed.

Lemma no_ptr_mem_preserved_drop_perm :  
  forall m b lo hi perm m',
    no_ptr_mem m ->
    Mem.drop_perm m b lo hi perm = Some m' ->
    no_ptr_mem m'.
Proof.
  intros. unfold Mem.drop_perm in H0.
  break_match_hyp; try opt_inv.
  unfold no_ptr_mem in *.
  intros. simpl in *.
  apply H.
Qed.

Lemma no_ptr_mem_preserved_mem_store :
  forall c m b ofs m' v,
    no_ptr_mem m ->
    (forall x y, v <> Vptr x y) ->
    Mem.store c m b ofs v = Some m' ->
    no_ptr_mem m'.
Proof.
  intros.
  app Mem.store_mem_contents H1.

  unfold no_ptr_mem.
  rewrite H1. intros.

  destruct (peq b ofs0);
    try rewrite PMap.gso by congruence;
    try apply H.
  subst b.
  rewrite PMap.gss.

  break_match; eauto.
  app getN_in_or_out Heqm0.
  break_or.
  destruct c; destruct v; simpl in H4;
  repeat break_or; try inv_false; try congruence;
  app frag_not_in_inj_bytes H4.

  unfold no_ptr_mem in H.
  specialize (H z ofs0). rewrite H4 in H.
  apply H.
Qed.

Lemma no_ptr_mem_preserved_store_zeros :
  forall z m b ofs m',
    no_ptr_mem m ->
    store_zeros m b ofs z = Some m' ->
    no_ptr_mem m'.
Proof.
  induction z using Z_nat_ind; intros;
  match goal with
    | [ H : context[store_zeros] |- _ ] => rewrite store_zeros_equation in H
  end;
  simpl in *.
  inv H0. eauto.
  break_match_hyp; inv H0.
  rewrite store_zeros_equation in H2. simpl in *.
  inv H2. app no_ptr_mem_preserved_mem_store Heqo.
  intros. unfold Vzero. congruence.
  break_match_hyp; try omega. inv H1. eauto.
  break_match_hyp; try omega. break_match_hyp; inv H1.
  app no_ptr_mem_preserved_mem_store Heqo.
  replace (z + 1 - 1) with z in H3 by omega.
  app IHz H3.
  intros. unfold Vzero. congruence.
Qed.

Lemma no_ptr_mem_preserved_store_zeros_bits :
  forall z m b ofs m',
    no_ptr_mem m ->
    store_zeros_bits m b ofs z = Some m' ->
    no_ptr_mem m'.
Proof.
  induction z using Z_nat_ind; intros;
  match goal with
    | [ H : context[store_zeros_bits] |- _ ] => rewrite store_zeros_bits_equation in H
  end;
  simpl in *.
  inv H0. eauto.
  break_match_hyp; inv H0.
  rewrite store_zeros_bits_equation in H2. simpl in *.
  inv H2. app no_ptr_mem_preserved_store Heqo.
  intros. unfold Vzero. congruence.
  break_match_hyp; try omega. inv H1. eauto.
  break_match_hyp; try omega. break_match_hyp; inv H1.
  app no_ptr_mem_preserved_store Heqo.
  replace (z + 1 - 1) with z in H3 by omega.
  app IHz H3.
  intros. unfold Vzero. congruence.
Qed.

Lemma no_ptr_mem_preserved_init_data_bits :
  forall ge m b ofs a m' t,
    no_ptr_mem m ->
    store_init_data_bits t ge m b ofs a = Some m' ->
    no_ptr_mem m'.
Proof.
  intros.
  destruct a; simpl in *;
          try solve [
                eapply no_ptr_mem_preserved_store;
                intros; eauto; try congruence].
  inv H0. eauto.
  repeat break_match_hyp; inv H0.
  eapply no_ptr_mem_preserved_store; eauto.
  
  intros; congruence.
Qed.

Lemma no_ptr_mem_preserved_init_data_list_bits :
  forall (ge : Genv.t fundef unit) l m b ofs m' t,
    no_ptr_mem m ->
    store_init_data_list_bits t ge m b ofs l = Some m' ->
    no_ptr_mem m'.
Proof.
  induction l; intros.
  simpl in H0. inv H0. eauto.
  simpl in H0.
  break_match_hyp; inv H0.
  app no_ptr_mem_preserved_init_data_bits Heqo.
Qed.

Lemma no_ptr_alloc_global :
  forall ge m id g m' t t' b,
    no_ptr_mem m ->
    alloc_only_global_bits t ge m (id,g) = Some (m',t',id,b,g) ->
    no_ptr_mem m'.
Proof.
  intros.
  unfold alloc_only_global_bits in H0.
  break_match_hyp. break_let.
  app no_ptr_mem_preserved_alloc Heqp.
  repeat (break_match_hyp; try congruence).
  app no_ptr_mem_preserved_drop_perm Heqo.
  inv H0. eauto.
  app no_ptr_mem_preserved_alloc Heqp0.
  app no_ptr_mem_preserved_drop_perm Heqo.
  inv H0. eauto.
  break_let.
  app no_ptr_mem_preserved_alloc Heqp.
  inv H0. eauto.
  repeat break_match_hyp; try congruence.
  inv H3.
  eapply no_ptr_mem_preserved_drop_perm; eauto.
Qed.

Lemma alloc_only_global_bits_ret_same :
  forall t ge m i g m' t' i' b g',
    alloc_only_global_bits t ge m (i,g) = Some (m',t',i',b,g') ->
    i = i' /\ g = g'.
Proof.
  intros. unfold alloc_only_global_bits in H.
  repeat break_match_hyp; split; try congruence.
Qed.


Lemma no_ptr_alloc_globals_bits :
  forall ge l m m' t t' l',
    no_ptr_mem m ->
    alloc_only_globals_bits t ge m l = Some (m',t',l') ->
    no_ptr_mem m'.
Proof.
  induction l; intros.
  simpl in H0. inv H0. eauto.
  simpl in H0. break_match_hyp; inv H0.
  destruct a.
  repeat break_let.
  break_match_hyp; try congruence.
  repeat break_let. find_inversion.
  app alloc_only_global_bits_ret_same Heqo.
  break_and. subst.
  app no_ptr_alloc_global H0.
Qed.

Lemma alloc_only_globals_bits_no_ptr :
  forall l md ge m m' a l',
    alloc_only_globals_bits md ge m l = Some (m',a,l') ->
    no_ptr_mem m ->
    no_ptr_mem m'.
Proof.
  induction l; intros.
  simpl in H. inv H. eauto.
  simpl in H. repeat break_match_hyp; try congruence.
  opt_inv. subst.
  app IHl Heqo0.
  unfold alloc_only_global_bits in Heqo.
  repeat break_match_hyp; try congruence; try opt_inv; subst.
  * eapply no_ptr_mem_preserved_drop_perm;
    try eapply Heqo1.
    eapply no_ptr_mem_preserved_alloc; eauto.
  * eapply no_ptr_mem_preserved_drop_perm;
    try eapply Heqo1.
    eapply no_ptr_mem_preserved_alloc; eauto.
  * eapply no_ptr_mem_preserved_drop_perm;
    try apply Heqo1.
    eapply no_ptr_mem_preserved_alloc; eauto.
Qed.

Lemma no_ptr_mem_preserved_store_init_data_list_bits :
  forall l md ge m b ofs m',
    store_init_data_list_bits md ge m b ofs l = Some m' ->
    no_ptr_mem m ->
    no_ptr_mem m'.
Proof.
  induction l; intros.
  simpl in H. inv H. eauto.
  simpl in H. repeat break_match_hyp; try congruence.
  app IHl H. unfold store_init_data_bits in Heqo.
  repeat break_match_hyp; try congruence;
  try solve [eapply no_ptr_mem_preserved_store; eauto; try congruence].
  inv Heqo. eauto.
Qed.

Lemma no_ptr_mem_preserved_set_perm :
  forall m lo hi b p m',
    set_perm m b lo hi p = Some m' ->
    no_ptr_mem m ->
    no_ptr_mem m'.
Proof.
  intros.
  unfold set_perm in *.
  repeat break_match_hyp; try congruence.
  inv H.
  unfold no_ptr_mem in *. simpl.
  eapply H0.
Qed.

Lemma no_ptr_mem_preserved_store_globals_bits :
  forall l md ge m m' md',
    store_globals_bits md ge m l = Some (m',md') ->
    no_ptr_mem m ->
    no_ptr_mem m'.
Proof.
  induction l; intros.
  simpl in *. opt_inv.
  subst. eauto.
  simpl in H. repeat break_match_hyp; try congruence; try opt_inv.
  subst.
  app IHl H.
  unfold store_global_bits in Heqo.
  repeat break_match_hyp; try congruence; try opt_inv; subst; eauto.
  eapply no_ptr_mem_preserved_set_perm; eauto.
  eapply no_ptr_mem_preserved_set_perm; eauto.
  eapply no_ptr_mem_preserved_set_perm; eauto.
  eapply no_ptr_mem_preserved_store_init_data_list_bits; eauto.
  eapply no_ptr_mem_preserved_store_zeros_bits; eauto.
Qed.
  

Lemma no_ptr_mem_init :
  forall prog m t,
    init_mem_bits prog = Some (m,t) ->
    no_ptr_mem m.
Proof.
  intros. unfold init_mem_bits in H.
  unfold alloc_globals_bits in H.
  repeat break_match_hyp; try congruence.
  subst. 
  app no_ptr_alloc_globals_bits Heqo;
    try eapply no_ptr_empty.
  eapply no_ptr_mem_preserved_store_globals_bits; eauto.
Qed.

Lemma no_ptr_regs_preserved' :
  forall ge rs m t rs' m' md md',
    no_ptr_regs rs ->
    no_ptr_mem m ->
    step_bits ge (State_bits rs m md) t (State_bits rs' m' md') ->
    no_ptr_regs rs' /\ no_ptr_mem m'.
Proof.
  intros.
  name H Hno_ptr.
  invs; subst.
  
  *
    destruct i;
    match goal with
      | [ H : exec_instr_bits _ _ _ _ _ _ _ = Nxt _ _ _ |- _ ] => simpl in H
    end;
    unfold exec_store_bits in *;
    unfold exec_load_bits in *;
    unfold goto_label_bits in *;
    unfold exec_big_load_bits in *;
    unfold exec_big_store_bits in *;
    repeat break_match_hyp;
    try st_inv;
    split; eauto;
    unfold no_ptr_regs in *;
    unfold nextinstr; intros;
    repeat preg_case; preg_simpl;
    match goal with
      | [ H : rs PC = _ |- _ ] => try rewrite H
    end;
    repeat preg_case; preg_simpl;
    match goal with
      | [ H : rs PC = _ |- _ ] => try rewrite H
    end;
    simpl; try congruence;
    try apply Hno_ptr;
    try solve [
          unfold eval_addrmode_no_ptr;
          unfold Values.Val.zero_ext;
          unfold Values.Val.sign_ext;
          unfold Values.Val.maketotal;
          unfold Values.Val.singleoffloat;
          unfold Values.Val.floatofsingle;
          unfold Values.Val.sub;
          unfold Values.Val.add;
          unfold Values.Val.mul;
          unfold Values.Val.mulhs;
          unfold Values.Val.mulhu;
          unfold Values.Val.notint;
          unfold Values.Val.shr;
          unfold Values.Val.shru;
          unfold Values.Val.xor;
          unfold Values.Val.ror;
          unfold Values.Val.neg;
          unfold Values.Val.negative;
          unfold Values.Val.or;
          unfold Values.Val.and;
          unfold Values.Val.shl;
          unfold Values.Vzero;
          unfold Values.Val.intoffloat;
          unfold Values.Val.floatofint;
          unfold Values.Val.intofsingle;
          unfold Values.Val.singleofint;
          unfold Values.Val.sub_overflow;
          unfold Values.Val.cmpu;
          unfold Values.Val.addf;
          unfold Values.Val.subf;
          unfold Values.Val.mulf;
          unfold Values.Val.divf;
          unfold Values.Val.negf;
          unfold Values.Val.absf;
          unfold Values.Val.addfs;
          unfold Values.Val.subfs;
          unfold Values.Val.mulfs;
          unfold Values.Val.divfs;
          unfold Values.Val.negfs;
          unfold Values.Val.absfs;
          unfold Values.Val.of_optbool;
          unfold Values.Vtrue;
          unfold Values.Vfalse;
          unfold Values.Vzero;
          unfold option_map;
          repeat (break_match; try congruence);
          repeat match goal with
            | [ H : rs _ = _ |- _ ] => app Hno_ptr H
          end];

    try solve [simpl_exec;
                repeat break_match_hyp; try state_inv;
                preg_case; try congruence; apply Hno_ptr];

    try solve [
    repeat break_match;
      repeat preg_case;
      preg_simpl;
      try congruence;
      try apply Hno_ptr;
      unfold Values.Val.of_bool;
      repeat break_match;
      unfold Values.Vtrue;
      unfold Values.Vfalse;
      try congruence;
      try find_rewrite;
      simpl;
        congruence];


    try solve [
          unfold Values.Val.divs in *;
          unfold Values.Val.divu in *;
          unfold Values.Val.mods in *;
          unfold Values.Val.modu in *;
          repeat break_match_hyp; opt_inv; try congruence];

    try solve [unfold Values.Vzero; congruence];
    try solve [
          unfold Memory.Mem.loadv in *;
          break_match_hyp;
          try opt_inv;
          unfold no_ptr_mem in H0;
          eapply no_ptr_mem_load; eauto];

    try solve [
          unfold no_ptr_mem in H0;
          eapply H0; eauto];
    try solve [
          erewrite <- goto_label_bits_mem by eauto;
          eauto];
    try solve [
          unfold storev_bits in *;
          break_match_hyp;
          try congruence;
          eapply no_ptr_mem_preserved_store;
          eauto].
    
    unfold exec_store_bits in *.
    unfold storev_bits in *.
    repeat break_match_hyp; try congruence.
    
    inv Heqo.
    eapply no_ptr_mem_preserved_store.
    eauto.
    eauto.
    intros.
    preg_simpl.
    congruence.

    (* Pmovups_rm *)
    unfold Mem.loadv in *.
    repeat break_match_hyp; try congruence.
    eapply no_ptr_mem_load; eauto.
    
    (* Pmovups_mr *)
    unfold storev_bits in *.
    repeat break_match_hyp; try congruence.
    app no_ptr_mem_preserved_store Heqo.
    app no_ptr_mem_preserved_store Heqo0.
    
    
    (*solve inc case*)
    (*TODO include in proof structure above*)
    unfold Values.Val.add.
    repeat break_match;
      try congruence.
    inv Heqv0.
    inv Heqv0.
    apply H in Heqv. contradiction.
        
    app no_ptr_mem_preserved_alloc Heqp.
    app no_ptr_mem_preserved_store Heqo.
    app no_ptr_mem_preserved_store Heqo0.
    eapply no_ptr_mem_load; eauto.
    eapply no_ptr_mem_load; eauto.
    app no_ptr_mem_preserved_free Heqo3.

  * eauto.
  * split.
    unfold nextinstr. unfold no_ptr_regs in *.
    intros. preg_case.
    rewrite H8. simpl. congruence.
    apply Hno_ptr.
    eauto.
  * eauto.
Qed.

Lemma no_ptr_regs_preserved :
  forall p rs m t rs' m' md md',
    no_ptr_regs rs ->
    no_ptr_mem m ->
    step_bits (Genv.globalenv p) (State_bits rs m md) t (State_bits rs' m' md') ->
    no_ptr_regs rs' /\ no_ptr_mem m'.
Proof.
  eauto using no_ptr_regs_preserved'.
Qed.

Lemma no_ptr_regs_preserved_star' :
  forall ge t s1 s2,
    star step_bits ge s1 t s2 ->
    forall rs m rs' m' md md',
      s1 = State_bits rs m md ->
      s2 = State_bits rs' m' md' ->
    (no_ptr_regs rs /\ no_ptr_mem m) ->
    no_ptr_regs rs' /\ no_ptr_mem m'.
Proof.
  induction 1; simpl; intros. auto.
  subst. inv H0. auto.
  subst. destruct s2.
  eapply no_ptr_regs_preserved' in H; try solve [break_and; eauto].
Qed.

Lemma no_ptr_regs_preserved_star :
  forall p t s1 s2,
    star step_bits (Genv.globalenv p) s1 t s2 ->
    forall rs m rs' m' md md',
      s1 = State_bits rs m md ->
      s2 = State_bits rs' m' md' ->
    (no_ptr_regs rs /\ no_ptr_mem m) ->
    no_ptr_regs rs' /\ no_ptr_mem m'.
Proof.
  eauto using no_ptr_regs_preserved_star'.
Qed.
