Require Import Coqlib.
Require Import Asm.
Require Import Globalenvs.
Require Import Integers.

Require Import ProgPropDec.
Require Import PeekTactics.
Require Import PeekLib.
Require Import PregTactics.
Require Import StepLib.
Require Import AsmBits.
Require Import MemoryAxioms.
Require Import GlobalPerms.
Require Import FindInstrLib.
Require Import AsmCallingConv.

Lemma step_nextinstr_same_block :
  forall p rs m md rs' m' md' t,
    no_PC_overflow_prog p ->
    step_bits (Genv.globalenv p) (State_bits rs m md) t (State_bits rs' m' md') ->
    forall b ofs bits b' ofs' bits',
      rs PC = Values.Vint bits ->
      psur md bits = Some (b,ofs) ->
      rs' PC = Values.Vint bits' ->
      psur md' bits' = Some (b',ofs') ->
      rs' PC = nextinstr rs PC ->
      b = b'.
Proof.
  intros.
  NP _app step_md step_bits.
  NP _app step_gp step_bits.
  NP _app md_extends_step step_bits.
  repeat break_and.
  repeat match goal with
           | [ H : global_perms _ _ |- _ ] => eapply global_perms_valid_globals in H
         end.
  assert (is_global (Genv.globalenv p) b ofs). {
    unfold is_global.
    left. unfold in_code_range.
    invs; repeat unify_PC; repeat unify_psur;
    unfold fundef in *; repeat collapse_match;
    try NP apex in_range_find_instr find_instr;
    try omega. 
    rewrite Int.unsigned_zero. omega.
  } idtac.

  assert (Int.unsigned (Int.add ofs Int.one) = Int.unsigned ofs + 1). {
    unfold Int.add. rewrite Int.unsigned_one.
    invs; repeat unify_PC; repeat unify_psur;
    try solve [
          erewrite unsigned_repr_PC; eauto;
          left; replace (Int.unsigned ofs + 1 - 1) with (Int.unsigned ofs) in * by omega; eassumption].
    rewrite Int.unsigned_zero. rewrite Int.unsigned_repr.
    omega. unfold Int.max_unsigned.
    unfold Int.modulus. unfold Int.wordsize.
    unfold Wordsize_32.wordsize.
    unfold two_power_nat.
    unfold shift_nat.
    simpl. omega.
  } idtac.
  erewrite weak_valid_pointer_sur in H2; eauto.
  break_and.
  preg_simpl_hyp H5.
  rewrite H1 in H5.
  erewrite weak_valid_pointer_sur in H4; eauto.
  break_and. simpl in H5.
  unify_PC.
  app pinj_add H2. instantiate (1 := Int.one) in H2.
  eapply pinj_extends in H2; eauto.
  assert (Memory.Mem.weak_valid_pointer m' b (Int.unsigned (Int.add ofs Int.one)) = true). {
    rewrite Memory.Mem.weak_valid_pointer_spec.
    rewrite H12. right.
    replace (Int.unsigned ofs + 1 - 1) with (Int.unsigned ofs) by omega.
    eapply H9. assumption.
  } idtac.
  name (conj H4 H14) Hpsur1. erewrite <- weak_valid_pointer_sur in Hpsur1; eauto.
  name (conj H2 H15) Hpsur2. erewrite <- weak_valid_pointer_sur in Hpsur2; eauto.
  unify_psur. reflexivity.
Qed.

Definition labeled_jump (i : instruction) (l : label) : Prop :=
  match i with
    | Pjmp_l l' => l = l'
    | Pjcc _ l' => l = l'
    | Pjcc2 _ _ l' => l = l'
    | Pjmptbl _ ls => In l ls
    | _ => False
  end.

Inductive in_same_block (s1 s2 : state_bits) : Prop :=
  | in_b :
      forall rs m rs' m' b i i' bits bits' md md',
        s1 = State_bits rs m md ->
        s2 = State_bits rs' m' md' ->
        rs PC = Values.Vint bits ->
        rs' PC = Values.Vint bits' ->
        psur md bits = Some (b,i) ->
        psur md' bits' = Some (b,i') ->
        in_same_block s1 s2.

Lemma labeled_jump_same_block : 
  forall p rs m md t rs' m' md' bits b ofs bits' b' ofs' f i,
    (exists l, labeled_jump i l) ->
    no_PC_overflow_prog p ->
    step_bits (Genv.globalenv p) (State_bits rs m md) t (State_bits rs' m' md') ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,ofs) ->
    rs' PC = Values.Vint bits' ->
    psur md' bits' = Some (b',ofs') ->
    Genv.find_funct_ptr (Genv.globalenv p) b = Some (AST.Internal f) ->
    find_instr (Int.unsigned ofs) (fn_code f) = Some i ->
    b = b'.
Proof.
  intros.
  invs; repeat unify_PC; repeat unify_psur; unfold fundef in *; try find_one_instr; unify_find_funct_ptr; unify_find_instr; simpl in H; try solve [break_exists; inv_false].

  assert ((exists l', labeled_jump i l' /\ goto_label_bits md f0 l' b rs m = Nxt rs' m' md') \/ rs' PC = nextinstr rs PC). {
    break_exists; destruct i; simpl in H; try inv_false; simpl in H21.
    left. exists l. split; eauto. simpl. auto.
    repeat break_match_hyp; try congruence.
    left. exists l. split; auto. simpl. auto.
    right. inv H21. reflexivity.
    repeat break_match_hyp; try congruence; try solve [right; congruence].
    left. exists l. split; auto. simpl. auto.
    repeat break_match_hyp; try congruence.
    left. exists l. split; auto.
    simpl. app list_nth_z_in Heqo.
  } idtac.

  destruct H3;
    try solve [
          eapply step_nextinstr_same_block; eauto].
  clear H.
  break_exists.
  break_and.

  unfold goto_label_bits in *.
  repeat break_match_hyp; try congruence.
  inv H3.
  clear H21.

  preg_simpl_hyp H4.
  inv H4.

  app label_pos_find_instr Heqo.
  assert (is_global (Genv.globalenv p) b (Int.repr (z-1))). {
    unfold is_global.
    left. unfold in_code_range.
    unfold fundef in *. collapse_match.
    apex in_range_find_instr Heqo.
    erewrite unsigned_repr_PC; eauto. omega.
  } idtac.

  assert (Int.unsigned (Int.repr z) - 1 = Int.unsigned (Int.repr (z - 1))). {
    erewrite unsigned_repr_PC; eauto.
    erewrite unsigned_repr_PC; eauto.
  } idtac.    
  assert (Memory.Mem.weak_valid_pointer m' b (Int.unsigned (Int.repr z)) = true). {
    rewrite Memory.Mem.weak_valid_pointer_spec.
    right. eapply global_perms_valid_globals in H23.
    unfold valid_globals in *.
    rewrite H7.
    eapply H23. auto.
  } idtac.

  name (conj Heqo0 H8) Hpsur.
  erewrite <- weak_valid_pointer_sur in Hpsur; eauto.
  congruence.
Qed.


Lemma step_no_call_nextinstr_or_label :
  forall p rs m md rs' m' md' t f i,
    no_PC_overflow_prog p ->
    no_builtin_clobber_PC_prog p ->
    step_bits (Genv.globalenv p) (State_bits rs m md) t (State_bits rs' m' md') ->
    forall b ofs bits b' ofs' bits',
      rs PC = Values.Vint bits ->
      psur md bits = Some (b,ofs) ->
      rs' PC = Values.Vint bits' ->
      psur md' bits' = Some (b',ofs') ->
      Genv.find_funct_ptr (Genv.globalenv p) b = Some (AST.Internal f) ->
      find_instr (Int.unsigned ofs) (fn_code f) = Some i ->
      ~ is_call_return i ->
      rs' PC = nextinstr rs PC \/ (exists l, labeled_jump i l).
Proof.
  intros.
    invs; repeat unify_PC; repeat unify_psur;
    unfold fundef in *; repeat unify_find_funct_ptr;
    try solve [left; reflexivity]; unify_find_instr.

    Focus 2.
    left. unfold nextinstr_nf.
    unfold undef_regs. fold undef_regs.
    unfold nextinstr.
    rewrite Pregmap.gss.
    repeat rewrite Pregmap.gso by congruence.
    repeat rewrite Pregmap.gss.
    assert (code_of_prog (fn_code f0) p). {
      app Genv.find_funct_ptr_inversion H6. unfold code_of_prog.
      destruct f0. simpl. eauto.
    } idtac.
    app H0 H3.
    app H3 H18.
    
    rewrite set_regs_not_in by tauto.
    rewrite undef_regs_not_in by tauto.
    reflexivity.

    
    destruct i;
      simpl in H22;
      simpl in H8;
      try inv_false;
      try solve [right; simpl; eauto];
      unfold exec_load_bits in *;
      unfold exec_store_bits in *;
      unfold exec_big_load_bits in *;
      unfold exec_big_store_bits in *;
      unfold compare_floats in *;
      unfold compare_floats32 in *;
      repeat (break_match_hyp; try congruence);
      try st_inv;
      try solve [left; preg_simpl; reflexivity].
    app list_nth_z_in Heqo.
Qed.

Lemma step_no_call_same_block :
  forall p rs m md rs' m' md' t f i,
    no_PC_overflow_prog p ->
    no_builtin_clobber_PC_prog p ->
    step_bits (Genv.globalenv p) (State_bits rs m md) t (State_bits rs' m' md') ->
    forall b ofs bits b' ofs' bits',
      rs PC = Values.Vint bits ->
      psur md bits = Some (b,ofs) ->
      rs' PC = Values.Vint bits' ->
      psur md' bits' = Some (b',ofs') ->
      Genv.find_funct_ptr (Genv.globalenv p) b = Some (AST.Internal f) ->
      find_instr (Int.unsigned ofs) (fn_code f) = Some i ->
      ~ is_call_return i ->
      b = b'.
Proof.
  intros.
  NP _app step_no_call_nextinstr_or_label step_bits.
  break_or.
  eapply step_nextinstr_same_block; eauto.
  eapply labeled_jump_same_block; eauto.
Qed.

