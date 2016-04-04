Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Asm.
Require Import Axioms.
Require Import Floats.

Require Import PeekTactics.
Require Import PregTactics.
Require Import PeekLib.
Require Import SplitLib.
Require Import StepLib.
Require Import FindInstrLib.
Require Import ProgPropDec.
Require Import AsmCallingConv.
Require Import MemoryAxioms.
Require Import AsmBits.

Require Import Zlen.

Definition is_jump (i:instruction): Prop :=
  match i with
    | Pjmp_l l => True
    | Pjmp_s s _ => True
    | Pjmp_r r _ => True
    | Pjcc c l => True
    | Pjcc2 c1 c2 l => True
    | Pjmptbl r tbl => True
    | Pcall_s s _ => True
    | Pcall_r r _ => True
    | Pret _ => True
    | _ => False
  end.

Lemma is_jump_dec:
  forall i,
    { is_jump i } + {~ is_jump i }.
Proof.
  intros. simpl. destruct i; auto;
  left; unfold is_jump; auto.
Qed.


Definition uncond_jmp(l:label)(c:code):list Z :=
  match (label_pos l 0 c) with
    | None => nil
    | Some z => 
      match (find_instr z c) with
        | Some _ => z :: nil
        | None => nil
      end
  end.

(* Lemma uncond_jmp_ok: *)
(*   forall c l z, *)
(*     In z (uncond_jmp l c) -> *)
(*     exists i, find_instr z c = Some i. *)
(* Proof. *)
(*   intros. unfold uncond_jmp in H. *)
(*   repeat break_match_hyp. simpl in H. *)
(*   destruct H. rewrite <- H. exists i. *)
(*   auto. inv H. simpl in H. inv H. *)
(*   simpl in H. inv H. *)
(* Qed. *)

Definition cond_jmp(l:label)(c:code)(z:Z):list Z :=
  (z + 1) :: uncond_jmp l c.

(* Lemma cond_jmp_ok: *)
(*   forall c l z z', *)
(*     In z (cond_jmp l c z') -> *)
(*     exists i, find_instr z c = Some i. *)
(* Proof. *)
(*   intros. unfold cond_jmp in H. *)
(*   break_match_hyp. simpl in H. *)
(*   destruct H. rewrite <- H. exists i. auto. *)
(*   eapply uncond_jmp_ok; eauto. *)
(*   eapply uncond_jmp_ok; eauto. *)
(* Qed. *)

Definition find_tbl_pos (t : list label)(c : code):list Z :=
  (flat_map (fun l => (uncond_jmp l c)) t).

(* Lemma find_tbl_pos_ok: *)
(*   forall t c z, *)
(*     In z (find_tbl_pos t c) -> *)
(*     exists i, find_instr z c = Some i. *)
(* Proof. *)
(*   induction t; intros. *)
(*   * simpl in H. inv H. *)
(*   * simpl in H. rewrite in_app in H. destruct H. *)
(*     eapply uncond_jmp_ok. eauto. *)
(*     apply IHt. auto. *)
(* Qed. *)

Lemma is_call_dec:
  forall i, 
    {is_call i} + {~ is_call i}.
Proof.
  intros. 
  destruct i;
    try (left; exact I);
    right; auto.
Qed.
    
(* Fixpoint find_calls_rec (c : code) (z : Z) : list Z := *)
(*   match c with  *)
(*     | nil => nil  *)
(*     | i :: is => if is_call_dec i *)
(*                  then z + 1 :: find_calls_rec is (z + 1) *)
(*                  else find_calls_rec is (z + 1) *)
(*   end. *)

(* Definition find_calls (c : code) : list Z := *)
(*   find_calls_rec c 0. *)

(* look up instruction *)
(* if not a jump, succ is simply next instr *)
(* if it's a jump with labels we can find where it goes to *)
Definition succ (z:Z)(c:code):option (list Z) :=
  match (find_instr z c) with
    | Some (instr) =>
      match instr with
        | Pjmp_l l => Some (uncond_jmp l c)
        | Pjcc c1 l => Some (cond_jmp l c z)
        | Pjcc2 c1 c2 l => Some (cond_jmp l c z)
        | Pjmptbl r tbl => Some (find_tbl_pos tbl c)
        | Pret _ => None
        | Pjmp_r _ _ => None
        | Pjmp_s _ _ => None
        | Pcall_r _ _ => None
        | Pcall_s _ _ => None
        | _ => Some (z+1 :: nil)
      end
    | None => None
  end.

Lemma no_succ_calls :
  forall z c i,
    find_instr z c = Some i ->
    is_call_return i ->
    succ z c = None.
Proof.
  unfold succ. intros.
  repeat break_match; inv H;
  unfold is_call_return in H0;
  try inversion H0; reflexivity.
Qed.

Lemma succ_some_no_call :
  forall z c i,
    find_instr z c = Some i ->
    ~ is_call_return i ->
    exists ss,
      succ z c = Some ss.
Proof.
  intros. unfold succ.
  repeat break_match; simpl;
  try (inv H; specialize (H0 I); inv H0);
  eexists; eauto.
Qed.

Definition in_bool {A} (eq_dec : forall (x y : A), {x = y} + {x <> y}) (elem : A) (l : list A) : bool :=
  if in_dec eq_dec elem l then true else false.

Definition from_opt {A} (ol : option (list A)) : list A :=
  match ol with
    | Some l => l
    | None => nil
  end.

Definition pred (z : Z) (c : code) : list Z :=
  filter (fun idx => in_bool Z.eq_dec z (from_opt (succ idx c))) (range (zlen c)).

(* External interface lemma *)
Lemma succ_pred:
  forall c z z' i i' sl,
    find_instr z' c = Some i ->
    find_instr z c = Some i' ->
    succ z c = Some sl ->
    In z' sl -> 
    In z (pred z' c).
Proof.
  induction c; intros.
  * simpl in H. inv H.
  * unfold pred.
    apply filter_In.
    split. assert (exists i', find_instr z (a :: c) = Some i').
    exists i'. auto. 
    apply in_range_find_instr in H3.
    destruct H3.
    apply range_spec; auto.
    unfold in_bool. break_match.
    reflexivity.
    unfold from_opt in n. 
    clear Heqs.
    rewrite H1 in n.
    congruence.
Qed.


Lemma step_nextinstr:
  forall t ge b rs m rs' m' z f s c i bits t',
    f = mkfunction s c ->
    exec_instr_bits ge t f i b rs m = Nxt rs' m' t' ->
    rs PC = Values.Vint bits ->
    psur t bits = Some (b,z) ->
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    find_instr (Int.unsigned z) c = Some i ->
    (((nextinstr rs) PC = rs' PC) \/ is_jump i).
Proof.
  intros.
  rename H into f_s_c; rename H0 into H; rename H1 into H0; rename H2 into H1; rename H3 into H2.
  destruct i;
    try solve [right; simpl; auto];
    left;
    unfold exec_instr_bits in *;
    unfold exec_load_bits in *;
    unfold exec_store_bits in *;
    unfold exec_big_load_bits in *;
    unfold exec_big_store_bits in *;
    repeat break_match_hyp;
    try state_inv;
    preg_simpl;
    try reflexivity;
    repeat (break_match; preg_simpl; try reflexivity).
Qed.

Lemma nextinstr_next:
  forall t rs rs' b z z' c i bits bits' m,
    rs PC = Values.Vint bits ->
    psur t bits = Some (b,z) ->
    rs' PC = Values.Vint bits' ->
    psur t bits' = Some (b,z') ->
    nextinstr rs PC = rs' PC ->
    find_instr (Int.unsigned z) c = Some i ->
    no_PC_overflow c ->
    match_metadata t m ->
    Int.unsigned z = Int.unsigned z' - 1.
Proof.
  intros. unfold nextinstr in H3.
  rewrite H in *. rewrite H1 in *.
  preg_simpl_hyp H3. simpl in H3.
  inv H3.
  rewrite (weak_valid_pointer_sur) in H0; eauto.
  rewrite (weak_valid_pointer_sur) in H2; eauto.
  repeat break_and.
  app pinj_add H0.
  eapply pinj_injective_within_block in H2; try eapply H0; eauto.
  subst z'.
  rewrite Int.unsigned_add_carry.
  unfold Int.add_carry. 
  replace (Int.unsigned Int.one) with 1 by auto.
  replace (Int.unsigned Int.zero) with 0 by auto.
  destruct (zlt (Int.unsigned z + 1 + 0) Int.modulus).
  replace (Int.unsigned Int.zero) with 0 by auto.
  omega.
  unfold no_PC_overflow in H5.
  app H5 H4. unfold Int.max_unsigned in H4. omega.
Qed.

Lemma uncond_jmp_sound:
  forall ge rs m t rs' m' b i i' f s c l z bits bits' md md',
  step_bits ge (State_bits rs m md) t (State_bits rs' m' md') ->
    rs PC = Values.Vint bits ->
    rs' PC = Values.Vint bits' ->
    psur md bits = Some (b,i) ->
    psur md' bits' = Some (b,i') ->
    f = mkfunction s c ->
    @Genv.find_funct_ptr fundef unit ge b = Some (Internal f) ->
    goto_label_bits md f l b rs m = Nxt rs' m' md' ->
    label_pos l 0 c = Some z ->
    no_PC_overflow c ->
    labels_valid c ->
    In (Int.unsigned i') (uncond_jmp l c).
Proof.
  intros.
  unfold uncond_jmp.
  rewrite H7. break_match. subst.
  unfold goto_label_bits in H6. simpl in *. rewrite H7 in H6.
  assert (match_metadata md m).
  invs; eauto.
  break_match_hyp; try congruence. inv H6.
  preg_simpl_hyp H1. inv H1.
  left. 
  erewrite weak_valid_pointer_sur in H3; eauto. break_and.
  eapply pinj_injective_within_block in Heqo0; try eapply H1; eauto.
  subst.
  rewrite Int.unsigned_repr. reflexivity.
  unfold no_PC_overflow in H8. app H8 Heqo. omega.
  unfold labels_valid in H9. app H9 H7.
  rewrite H7 in Heqo. inv Heqo.

Qed.

Lemma cond_jmp_sound:
  forall ge rs m t rs' m' b i i' f s c l z z' bits bits' md md',
  step_bits ge (State_bits rs m md) t (State_bits rs' m' md') ->
  rs PC = Values.Vint bits ->
  psur md bits = Some (b,i) ->
  rs' PC = Values.Vint bits' ->
  psur md' bits' = Some (b,i') ->
    f = mkfunction s c ->
    @Genv.find_funct_ptr fundef unit ge b = Some (Internal f) ->
    goto_label_bits md f l b rs m = Nxt rs' m' md' ->
    label_pos l 0 c = Some z ->
    no_PC_overflow c ->
    labels_valid c ->
    In (Int.unsigned i') (cond_jmp l c z').
Proof.
  intros. unfold cond_jmp.
  simpl. right.
  eapply uncond_jmp_sound; eauto.
Qed.

Lemma find_tbl_pos_sound:
  forall ge rs m t rs' m' b i i' f s c l z tbl r ofs bits bits' md md',
  step_bits ge (State_bits rs m md) t (State_bits rs' m' md') ->
    rs PC = Values.Vint bits ->
    rs' PC = Values.Vint bits' ->
    psur md bits = Some (b,i) ->
    psur md' bits' = Some (b,i') ->
    f = mkfunction s c ->
    @Genv.find_funct_ptr fundef unit ge b = Some (Internal f) ->
    goto_label_bits md f l b rs m = Nxt rs' m' md' ->
    find_instr (Int.unsigned i) c = Some (Pjmptbl r tbl) ->
    rs r = Values.Vint ofs ->
    list_nth_z tbl (Int.unsigned ofs) = Some l ->
    label_pos l 0 c = Some z ->
    no_PC_overflow c ->
    labels_valid c ->
    In (Int.unsigned i') (find_tbl_pos tbl c).
Proof.
  intros. unfold find_tbl_pos. 
  apply list_nth_z_in in H9.
  apply in_flat_map. exists l. split; auto.
  eapply uncond_jmp_sound; eauto.
Qed.


(* successor is sound when stepping in the same block   *)
(*   as long as it's not a call or return instruction   *)
Lemma succ_sound_locally (p : Asm.program):
  forall rs m rs' m' t b i i' f s c sl instr bits bits' md md',
    step_bits (Genv.globalenv p) (State_bits rs m md) t (State_bits rs' m' md') ->
    rs PC = Values.Vint bits ->
    rs' PC = Values.Vint bits' ->
    psur md bits = Some (b,i) ->
    psur md' bits' = Some (b,i') ->
    f = mkfunction s c ->
    Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal f) ->
    find_instr (Int.unsigned i) c = Some instr ->
    (no_PC_overflow c /\ labels_valid c /\ no_builtin_clobber_PC c /\ ~ is_call_return instr) ->
    calling_conv_correct_bits p ->
    succ (Int.unsigned i) c = Some sl ->
    In (Int.unsigned i') sl.
Proof.
  intros.
  inv_step H.
  * (* unify duplicated vars *)
    (* TODO make inv_step_bits Ltac for this *)
    repeat unify_PC. repeat unify_psur.

    destruct f0.
    unify_find_funct_ptr.
    simpl in *.
    unify_find_instr.
    
    app step_nextinstr H0.
    
    destruct (is_jump_dec instr).
  - unfold succ in *.
      rewrite H22 in *.
      destruct instr; inv i0; inv H9; simpl in *; name H23 Hgoto.
       + (* uncond_jmp *)
         repeat break_and.
         unfold goto_label_bits in H23.
         repeat break_match_hyp; try congruence.
         inv H23.
         eapply uncond_jmp_sound; eauto.
       + (* cond_jmp cond *)
         repeat break_match_hyp; try congruence.
         { unfold goto_label_bits in H23.
           repeat break_match_hyp; try congruence.
           eapply cond_jmp_sound; eauto; tauto.
         } {
           unfold cond_jmp. simpl. left.
           inv H23.
           eapply nextinstr_next 
             with (rs := rs) (rs' := nextinstr rs) in H2; eauto.
           omega. repeat break_and. eassumption.
         }
       + (* cond_jmp cond /\ cond *)
         repeat break_match_hyp; try congruence; try find_inversion.
         { unfold goto_label_bits in H23.
           repeat break_match_hyp; try congruence.
           find_inversion.
           eapply cond_jmp_sound; eauto; tauto.
         } {
           unfold cond_jmp. simpl. left.
           eapply nextinstr_next 
             with (rs := rs)(rs' := nextinstr rs) in H2; eauto.
           omega. tauto.
         } {
           unfold cond_jmp. simpl. left.
           eapply nextinstr_next 
             with (rs := rs)(rs' := nextinstr rs) in H2; eauto.
           omega. tauto.
         }
       + repeat break_match_hyp; try congruence; try find_inversion.
         unfold goto_label_bits in H23.
         break_match_hyp; try congruence.
         eapply find_tbl_pos_sound; eauto.
         tauto. tauto.
    - break_or; try congruence.
      repeat break_and.
      
      NP _app step_md step_bits.
      NP _app step_gp step_bits.
      repeat break_and.
      app (nextinstr_next md') H4.
      
      destruct instr; unfold succ in H9; rewrite H22 in H9;
      simpl in H9; inv H9; simpl in n; try inv_false;
      try instantiate (1 := i') in H4;
      try rewrite H4; try solve [simpl; left; omega].

      erewrite weak_valid_pointer_sur in *; eauto.
      NP _app md_extends_step step_bits.
      repeat break_and.
      split. eapply pinj_extends; eauto.
      app global_perms_valid_globals H13.
      eapply Memory.Mem.valid_pointer_implies.
      eapply H13. unfold is_global.
      left. unfold in_code_range. unfold fundef in *.
      repeat collapse_match.
      simpl. NP apex in_range_find_instr find_instr. omega.
      
      
  * repeat unify_PC. repeat unify_psur. repeat unify_find_funct_ptr.
    simpl in *.
    repeat unify_find_instr.
    
    
    unfold succ in H9. rewrite H6 in H9. inv H9.
    preg_simpl_hyp H1.
    simpl in H1. 
    repeat break_and.
    unfold no_builtin_clobber_PC in *.
    app H7 H6.
    fold undef_regs in *.
    rewrite set_regs_not_in in H1 by (break_and; auto).
    assert (undef_regs (map preg_of (Machregs.destroyed_by_builtin ef)) rs PC <> Values.Vundef).
    unfold Values.Val.add in *.
    break_match_hyp; try congruence.
    apply undef_regs_not_undef in H11.
    rewrite undef_regs_not_in in H1 by auto.
    rewrite H0 in H1.
    simpl. left.
    unfold no_PC_overflow in *.
    app H2 H10.
    (* app psur_ec' H17. *)
    eapply match_ec' in H25; eauto.
    erewrite weak_valid_pointer_sur in * by eauto.
    repeat break_and.
    simpl in H1. inv H1.
    app step_gp H. break_and.
    app step_md H1. break_and.
    erewrite weak_valid_pointer_sur in H17; eauto.
    break_and.
    assert (md_extends md (md_ec' md ef (Genv.globalenv p) (map rs args) m t vl m')) by (econstructor; eauto).
    eapply pinj_extends in H17; eauto.
    eapply pinj_add in H17.
    eapply pinj_injective_within_block in H3; try eapply H17.
    subst.
    unfold Int.add. rewrite Int.unsigned_repr.
    rewrite Int.unsigned_one. reflexivity.
    rewrite Int.unsigned_one. omega.
  * repeat unify_PC. repeat unify_psur. simpl in *.
    repeat unify_find_funct_ptr. simpl in *.
    repeat unify_find_instr.

    unfold succ in *. rewrite H6 in *.
    eapply (nextinstr_next (md_ec md ef (Genv.globalenv p) vargs m t v m')) with (rs := rs) in H1; eauto.
    inv H9. simpl. left.
    rewrite H1. 
    omega.

    NP _app step_md step_bits.
    NP _app step_gp step_bits.
    repeat break_and.
    erewrite weak_valid_pointer_sur in *; eauto.
    repeat break_and.
    preg_simpl_hyp H1.
    rewrite H0 in *.
    simpl in H1. inv H1.
    assert (md_extends md (md_ec md ef (Genv.globalenv p) vargs m t v m')) by (econstructor; eauto).
    eapply pinj_extends in H16; eauto.
    split; eauto.
    eapply Memory.Mem.valid_pointer_implies.
    eapply global_perms_valid_globals in H10.
    eapply H10.
    unfold is_global. left.
    unfold in_code_range.
    unfold fundef in *.
    repeat collapse_match.
    simpl.
    apex in_range_find_instr H6; try omega.

    tauto.
    eapply match_ec; eauto.
    
  * repeat unify_PC. repeat unify_psur.
    repeat unify_find_funct_ptr.
Qed.
