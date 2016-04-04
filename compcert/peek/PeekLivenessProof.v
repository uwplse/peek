Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Asm.
Require Import Axioms.
Require Import Floats.
Require Import Machregs.
Require Import Maps.
Require Import Errors.

Require Import PeekLib.
Require Import PeekTactics.
Require Import PregTactics.
Require Import SplitLib.
Require Import FindInstrLib.
Require Import StepLib.
Require Import SameBlockLib.
Require Import Pred.
Require Import Use.
Require Import UseBasic.
Require Import Union.
Require Import PeekLiveness.
Require Import PeekLivenessLib.
Require Import AsmCallingConv.
Require Import ProgPropDec.
Require Import ValEq.
Require Import MemEq.
Require Import Zlen.

Require Import AsmBits.
Require Import MemoryAxioms.
Require Import NoPtr.

Lemma union_map_ZMap_get:
  forall x l l2,
    (forall p z, In p (ZMap.get z l) <-> In p (ZMap.get z l2)) ->
    (forall p, In p (union_l preg_eq (map (fun z0 => ZMap.get z0 l) x)) <->
               In p (union_l preg_eq (map (fun z0 => ZMap.get z0 l2) x))).
Proof.
  induction x; intros.
  * simpl. reflexivity.
  * simpl.
    split; intros; apply union_correct in H0;
    apply union_correct; destruct H0.
  - rewrite H in H0. left. assumption.
  - right. apply (IHx l l2 H); auto.
  - left. rewrite <- H in H0. assumption.
  - right. apply (IHx l l2 H); auto.
Qed.

Lemma in_update:
  forall c z l l2,
    (forall p, (* l and l2 are same at z *)
       In p (ZMap.get z l) <-> In p (ZMap.get z l2)) ->
    ( forall z0, (* l and l2 are same at all other z0 *)
        z0 <> z -> (forall p, In p (ZMap.get z0 l) <-> In p (ZMap.get z0 l2))) ->
    (forall p,
       In p (ZMap.get z (update_liveness c z l)) <-> In p (ZMap.get z (update_liveness c z l2))).
Proof.
  intros;
  unfold update_liveness in *;
  repeat break_match;
  repeat rewrite ZMap.gss;
  try rewrite <- H;
  try reflexivity.

  assert (forall z' p, In p (ZMap.get z' l) <-> In p (ZMap.get z' l2)).
  intros.
  destruct (Z.eq_dec z' z).
  rewrite e. apply (H p0).
  apply (H0 z' n0 p0).

  unfold transfer.
  repeat rewrite <- add_in_spec.
  repeat rewrite <- rem_in.
  split; intros; destruct H2; try (left; assumption); right;
  destruct H2; split; auto;
  eapply union_map_ZMap_get; eauto.
  intros. rewrite H1. reflexivity.
Qed.

(* if we update but an update had no change, erase that update *)
(* can't state cleaner, since not technically equal, just bidirictionally equivalent *)
Lemma update_no_change:
  forall z c l z0,
    (forall a,
       In a (ZMap.get z l) <-> In a (ZMap.get z (update_liveness c z l))) ->
    (forall p,
       In p (ZMap.get z0 (update_liveness c z0 (update_liveness c z l))) <->
       In p (ZMap.get z0 (update_liveness c z0 l))).
Proof.
  intros. destruct (Z.eq_dec z0 z).
  rewrite e in *.
  apply in_update. intros.
  split; intros;
  apply (H p0). assumption. assumption.
  intros. rewrite update_neq; auto. reflexivity.

  apply in_update. rewrite update_neq; auto.
  intros. reflexivity.
  intros.  destruct (Z.eq_dec z1 z).
  rewrite e. rewrite H. 
  reflexivity.
  rewrite update_neq. reflexivity. auto.
Qed.

Lemma app_under_not:
  forall (A B : Prop),
    (A -> B) ->
    ~ B ->
    ~ A.
Proof.
  unfold not in *.
  intros. apply H in H1.
  apply H0 in H1. exact H1.
Qed.

Lemma update_find_none:
  forall c z l,
    find_instr z c = None ->
    update_liveness c z l = l.
Proof.
  intros. unfold update_liveness.
  rewrite H. reflexivity.
Qed.

Lemma find_some_succ_none_call_ret:
  forall z c i,
    find_instr z c = Some i ->
    succ z c = None ->
    is_call_return i.
Proof.
  intros. unfold succ in H0. rewrite H in H0.
  break_match_hyp; inv H0; unfold is_call_return;
  auto.
Qed.

Lemma iteration_step_lemma :
  forall c it,
    in_wl_or_updated c it -> match (update_iter_state c it) with
                               | inl lm => reached_fixed_point c lm
                               | inr it => in_wl_or_updated c it
                             end.
Proof.
  intros. destruct (update_iter_state c it) eqn:?.
  * unfold update_iter_state in Heqs. destruct it. destruct w.
    Focus 2. break_match_hyp; inversion Heqs.
    inv Heqs. unfold in_wl_or_updated in H.
    unfold reached_fixed_point. intros.
    destruct (Z_lt_ge_dec z 0);
      destruct (Z_ge_lt_dec z (zlen c)).
    rewrite update_range with (c := c). reflexivity. omega.
    rewrite update_range with (c := c). reflexivity. omega.
    rewrite update_range with (c := c). reflexivity. omega.
    assert ((z >= 0) /\ (z < zlen c)). omega.
    destruct (H z H0). simpl in H1. inv H1.
    apply (H1 p).

  * unfold in_wl_or_updated in *.
    unfold update_iter_state in Heqs.
    destruct it. destruct w. inv Heqs.
    destruct i. intros.
    destruct (in_dec Z.eq_dec z0 w0). left. assumption.
    right. break_match_hyp; inv Heqs.
  + (* ran update but didn't change, thus sets equiv *)
    (* z0 is not in the worklist *)
    (* thus prove that z0 has its local fixed point property *)
    (* if z = z0, update just happened, all good *)
    (* use rewrite of H to get right *)
    destruct (Z.eq_dec z0 z).
    rewrite e in *.
    intros.
    rewrite update_twice. reflexivity.

    (* if z <> z0, use fact that update can't have touched z0 *)
    (* or z0 would be on the worklist *)
    (* thus z0 property holds. *)
    (* this will require knowledge of relation of pred and succ *)
    (* might not have that yet *)
    intros. destruct (in_dec Z.eq_dec z0 (z :: w0)).
    simpl in i0. destruct i0; congruence.
    rewrite update_neq by auto.

    (* now we want to collapse the update to z *)
    (* pretend it's not there, since it didn't change anything *)
    rewrite update_no_change; try assumption.
    destruct (H z0 H0); try congruence.
    apply H1.

  + (* ran update, something did change. *)
    (* z0 is not in the worklist before update *)
    (* if z0 = z *)
    (* we just ran update, and thus fixed point is preserved *)
    destruct (Z.eq_dec z0 z).
    rewrite e in *.
    intros.
    rewrite update_twice. reflexivity.

    (* if z0 <> z *)
    (* we know z0 not in pred z, since hypothesis n *)
    (* thus the only change didn't affect result for z0 *)
    intros. apply wl_add_not in n.
    destruct n.

    destruct (find_instr z c) eqn:?.
    name H0 Hfi. apply in_range_find_instr in Hfi. destruct Hfi.

    destruct (succ z0 c) eqn:?.

    apply (app_under_not _ _ (succ_pred c z0 z i x l0 Heqo H3 Heqo0)) in H1.
    rewrite update_indep; eauto.

    rewrite update_neq; auto.
    destruct (H z0 H0). simpl in H4. destruct H4; congruence.
    rewrite <- H4. reflexivity.

    destruct (H z0 H0). simpl in H4. destruct H4; congruence.

    app find_some_succ_none_call_ret Heqo0.
    unfold update_liveness at 2.
    rewrite H3. rewrite H5.
    break_match; try congruence.
    break_match.
  - rewrite update_neq by auto. rewrite H4.
    rewrite ZMap.gss.
    unfold update_liveness. rewrite H3.
    rewrite Heqs. rewrite Heqs1.
    rewrite ZMap.gss. reflexivity.
  - rewrite update_neq by auto. rewrite H4.
    app is_call_or_return_dec i0.
    destruct i0; try congruence.
    break_exists. subst x.
    rewrite ZMap.gss.
    unfold update_liveness. rewrite H3.
    rewrite Heqs. rewrite Heqs1.
    rewrite ZMap.gss. reflexivity.
  - rewrite update_find_none by auto.
    destruct (H z0 H0). simpl in H3. destruct H3; congruence.
    rewrite <- H3. reflexivity.
Qed.

Lemma find_liveness_fixed_point :
  forall lm c,
    find_liveness c = Some lm ->
    reached_fixed_point c lm.
Proof.
  intros. unfold find_liveness in H.
  eapply iter_prop; try eapply (iteration_step_lemma c); eauto.
  simpl. intros. left.
  apply range_spec. destruct H0. unfold zlen in H1. unfold Z_of_nat' in H1.
  assumption. destruct H0. assumption.
Qed.

Lemma all_reached_fixed_point:
  forall p,
    ensure_liveness_prog (prog_defs p) = OK tt ->
    forall c,
      code_of_prog c p ->
      exists lm,
        find_liveness c = Some lm /\ reached_fixed_point c lm /\ ensure_liveness lm c = OK tt.
Proof.
  intros. app ensure_liveness_prog_sound H.
  break_and. app find_liveness_fixed_point H.
Qed.

Lemma step_PC :
  forall ge t rs m rs' m' md md',
    step_bits ge (State_bits rs m md) t (State_bits rs' m' md') ->
    exists b,
      exists i,
        exists bits,
          rs PC = Values.Vint bits /\ psur md bits = Some (b,i).
Proof.
  intros.
  inv_step H; subst; repeat eexists; eauto.
Qed.

Lemma step_funct_ptr :
  forall ge t rs m rs' m' b i bits md md',
    step_bits ge (State_bits rs m md) t (State_bits rs' m' md') ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,i) ->
    exists f,
      Genv.find_funct_ptr ge b = Some f.
Proof.
  intros.
  inv_step H; subst; eexists; unify_psur; eauto.
Qed.

Lemma step_instr :
  forall ge t rs m rs' m' b i s c bits md md',
    step_bits ge (State_bits rs m md) t (State_bits rs' m' md') ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,i) ->
    Genv.find_funct_ptr ge b = Some (Internal (mkfunction s c)) ->
    exists instr,
      find_instr (Int.unsigned i) c = Some instr.
Proof.
  intros.
  inv_step H; unify_psur; unify_find_funct_ptr; eexists; eauto.
Qed.


Lemma undef_PC :
  forall l bits rs,
    undef_regs l rs PC = Values.Vint bits ->
    rs PC = Values.Vint bits.
Proof.
  induction l; intros.
  * simpl in H. auto.
  * simpl in H.
    destruct (preg_eq a PC). subst.
    preg_simpl_hyp H. fold undef_regs in *.
    apply IHl in H. preg_simpl_hyp H. congruence.
    apply IHl in H. preg_simpl_hyp H. assumption.
Qed.

(* Lemma psur_same_block : *)
(*   forall bits b i b' i' md m, *)
(*     match_metadata md m -> *)
(*     psur md bits = Some (b,i) -> *)
(*     psur md (Int.add bits Int.one) = Some (b',i') -> *)
(*     b = b'. *)
(* Proof. *)
(*   (* Not true *) *)
(*   (* How do we fix? *) *)
(* Qed. *)

(* Lemma same_block : *)
(*   forall ge rs m t rs' m' b b' i' i instr s c bits bits' md md', *)
(*     step_bits ge (State_bits rs m md) t (State_bits rs' m' md') -> *)
(*     rs PC = Values.Vint bits -> *)
(*     rs' PC = Values.Vint bits' -> *)
(*     psur md bits = Some (b,i) -> *)
(*     psur md' bits' = Some (b',i') -> *)
(*     Genv.find_funct_ptr ge b = Some (Internal (mkfunction s c)) -> *)
(*     find_instr (Int.unsigned i) c = Some instr -> *)
(*     ~ is_call_return instr -> *)
(*     no_builtin_clobber_PC c -> *)
(*     b = b'. *)
(* Proof. *)
(*   intros. inv_step H. *)
(*   * destruct instr; *)
(*     try solve [specialize (H6 I); inv_false]; *)
(*     unify_psur; *)
(*     unify_find_funct_ptr; *)
(*     simpl in *; *)
(*     unify_find_instr; *)
(*     unfold exec_instr_bits in *; *)
(*     unfold exec_load_bits in *; *)
(*     unfold exec_store_bits in *; *)
(*     unfold exec_big_load_bits in *; *)
(*     unfold exec_big_store_bits in *; *)
(*     unfold goto_label_bits in *; *)
(*     repeat break_match_hyp; *)
(*     try congruence; *)
(*     try st_inv; *)
(*     repeat match goal with *)
(*              | [ H : _ PC = _ |- _ ] => progress (preg_simpl_hyp H) *)
(*            end; *)
(*     try find_rewrite; simpl in *; *)
(*     try find_inversion; *)
(*     unfold exec_instr_bits in *; *)
(*     unfold exec_load_bits in *; *)
(*     unfold exec_store_bits in *; *)
(*     unfold exec_big_load_bits in *; *)
(*     unfold exec_big_store_bits in *; *)
(*     unfold goto_label_bits in *; *)
(*     repeat break_match_hyp; *)
(*     try st_inv; *)
(*     repeat match goal with *)
(*              | [ H : _ PC = _ |- _ ] => progress (preg_simpl_hyp H) *)
(*              | [ H : Values.Val.add _ _ = _ |- _ ] => progress (preg_simpl_hyp H) *)
(*            end; *)
(*     try find_rewrite; simpl in *; *)
(*     try find_inversion; *)
(*     try solve [eapply psur_same_block; eauto]; *)
    
(*     (* How do we do this? *) *)
    

(*   *  *)
(*     unify_psur; *)
(*     unify_find_funct_ptr; *)
(*     simpl in *; *)
(*     unify_find_instr; *)
(*     simpl_exec. *)
(*     repeat match goal with *)
(*              | [ H : _ PC = _ |- _ ] => progress (preg_simpl_hyp H) *)
(*            end. *)

(*     unfold no_builtin_clobber_PC in *. *)
(*     app H7 H5. fold undef_regs in *. *)
(*     break_and. *)
(*     rewrite set_regs_not_in in H1 by assumption. *)
(*     rewrite undef_regs_not_in in H1 by assumption. *)
(*     try state_inv; *)
(*       repeat match goal with *)
(*                | [ H : _ PC = _ |- _ ] => progress (preg_simpl_hyp H) *)
(*                | [ H : Values.Val.add _ _ = _ |- _ ] => progress (preg_simpl_hyp H) *)
(*              end; *)
(*       try find_rewrite; simpl in *; *)
(*       try find_inversion; *)
(*       try solve [eapply psur_same_block; eauto]. *)
(*   * *)
(*     unify_psur; *)
(*     unify_find_funct_ptr; *)
(*     simpl in *; *)
(*     unify_find_instr; *)
(*     simpl_exec. *)
(*     repeat match goal with *)
(*              | [ H : _ PC = _ |- _ ] => progress (preg_simpl_hyp H) *)
(*            end. *)
(*     try find_rewrite; simpl in *; *)
(*     try find_inversion; *)
(*     try solve [eapply psur_same_block; eauto]. *)
(*   * unify_psur; *)
(*     unify_find_funct_ptr. *)
(* Qed. *)

Lemma update_PC_live :
  forall z c lm,
    find_instr z c <> None ->
    In PC (ZMap.get z (update_liveness c z lm)).
Proof.
  intros. unfold update_liveness.
  break_match; try congruence.
  unfold succ; rewrite Heqo; simpl.
  break_match; break_match; try rewrite ZMap.gss; try (simpl; left; reflexivity).
  destruct i; unfold transfer; unfold use; unfold use_def; unfold use_def';
  apply add_in_l; try (left; reflexivity).
  clear Heqs.
  repeat break_let; repeat find_inversion.
  simpl. left. reflexivity.
  break_let. simpl. left. reflexivity.
  break_let. simpl. left. reflexivity.
  break_let. simpl. left. reflexivity.
  destruct i; simpl in n; try specialize (n I); try congruence; try inv_false;
  exfalso; auto.
Qed.

Definition liveness_fun_f (ge : genv) (b : Values.block) (z : Z) : list preg :=
  match (Genv.find_funct_ptr ge b) with
    | Some (Internal (mkfunction _ c)) =>
      match find_liveness c with
        | None => PC :: nil
        | Some lm => ZMap.get z lm
      end
    | Some (External ef) => regs_live_across_call
    | None => regs_live_across_call
  end.

Definition PC_live (c : code) (l : liveness_map_t) : Prop :=
  forall z, find_instr z c = None -> In PC (ZMap.get z l).

Definition PC_live_iter (c : code) (it : iter_state) : Prop :=
  match it with
    | mkstate lm _ => PC_live c lm
  end.

Lemma PC_live_init :
  forall c,
    PC_live_iter c (init_state c).
Proof.
  intros. unfold init_state.
  unfold PC_live_iter. unfold PC_live.
  intros. 
  rewrite ZMap.gi. simpl. left.
  reflexivity.
Qed.

Lemma PC_live_pres (c : code) :
  forall it,
    (PC_live_iter c) it ->
    match ((update_iter_state c) it) with
      | inl b => (PC_live c) b
      | inr a => (PC_live_iter c) a
    end.
Proof.
  intros. unfold PC_live_iter in H.
  destruct it.
  unfold update_iter_state.
  destruct w. auto.
  break_match. break_match_hyp. inv Heqs. inv Heqs.
  break_match_hyp. inv Heqs.
  unfold PC_live_iter. unfold PC_live. intros.
  destruct (zeq z z0).
  rewrite e. unfold update_liveness.
  rewrite H0. unfold PC_live in H. apply H. auto.
  unfold update_liveness.
  repeat break_match; try rewrite ZMap.gso by auto;
  unfold PC_live in H; apply H; auto.
  inv Heqs.
  unfold PC_live_iter. unfold PC_live in *. intros.
  unfold update_liveness.
  destruct (zeq z z0). rewrite e. rewrite H0.
  apply H. auto.
  repeat break_match; try rewrite ZMap.gso by auto;
  unfold PC_live in H; apply H; auto.
Qed.

Lemma find_liveness_out_of_range :
  forall c l,
    find_liveness c = Some l ->
    PC_live c l.
Proof.
  intros.
  unfold find_liveness in H.
  eapply iter_prop; eauto. apply PC_live_pres.
  apply PC_live_init.
Qed.

Lemma PC_always_live :
  forall p,
    ensure_liveness_prog (prog_defs p) = OK tt ->
    forall f b i,
      In PC (liveness_fun_f f b i).
Proof.
  intros. unfold liveness_fun_f.
  break_match; simpl; auto.
  break_match; simpl; auto.
  break_match; simpl; auto.
  break_match; simpl; auto.
  app find_liveness_out_of_range Heqo0.
  app find_liveness_fixed_point H0.
  unfold reached_fixed_point in H0.
  rewrite H0.
  rename fn_code into c.
  destruct (find_instr i c) eqn:?.
  apply update_PC_live. congruence.
  app find_liveness_out_of_range H1.
  unfold PC_live in H1. app H1 Heqo1.
  unfold update_liveness. rewrite H3.
  assumption.
Qed.

Ltac cop :=
  match goal with
    | [ H : Genv.find_funct_ptr _ _ = Some (Internal (mkfunction _ ?X))  |- code_of_prog ?X _ ] =>
      solve [app Genv.find_funct_ptr_inversion H; unfold code_of_prog; eauto]
  end.

Ltac collapse_match_hyp :=
  match goal with
    | [ H : context[match ?X with _ => _ end], H2 : ?X = _ |- _ ] =>  rewrite H2 in H
    | [ H : context[match ?X with _ => _ end], H2 : _ = ?X |- _ ] => rewrite <- H2 in H
  end.

Lemma fixed_point_liveness:
  forall p,
    (no_PC_overflow_prog p /\ labels_valid_prog p /\ calling_conv_correct_bits p /\ no_builtin_clobber_PC_prog p) ->
    ensure_liveness_prog (prog_defs p) = OK tt ->
    (forall c,
       code_of_prog c p ->
       exists lm,
         find_liveness c = Some lm /\ reached_fixed_point c lm /\ ensure_liveness lm c = OK tt) ->
    liveness_fun_correct p (liveness_fun_f).
Proof.
  intros.
  unfold liveness_fun_correct. unfold exec_preserved. unfold match_live.
  intros.
  destruct sl. destruct sr.
  destruct sl'. simpl.
  unfold calling_conv_correct_bits in *;
  NP _app step_PC step_bits.
  repeat break_and.
  NP _app step_funct_ptr step_bits.
  match goal with
    | [ x : fundef |- _ ] => destruct x
  end.
  (* started in Internal code *)
  * match goal with
      | [ f : function |- _ ] => destruct f
    end.
    (* We took a step. Either that was a call, a return, or a normal instruction *)
    P exploit no_ptr_regs; eauto; intros; repeat break_and.
    match goal with
      | [ H : context[step_bits] |- _ ] =>
        app step_instr H
    end.
    match goal with
      | [ H : find_instr _ _ = Some ?X |- _ ] => destruct (is_call_return_dec X)
    end;
      match goal with
        | [ H : is_call_return _ |- _ ] => app is_call_or_return_dec H
        | [ |- _ ] => idtac
      end;
      repeat break_or.
    - (* is a call *)
      match goal with
        | [ H: call_steps_to_beginning_bits _ , H2: step_bits _ _ _ _ |- _ ] => unfold call_steps_to_beginning_bits in H; app H H2
      end.
      match goal with
        | [ H1: call_liveness_correct_bits _ ,
                H2: step_bits _ _ _ _  ,
                    H3: forall _, In _ (liveness_fun_f _ _ _) -> val_eq (?X _) (?Y _) |- _]
          => unfold call_liveness_correct_bits in H1; app (H1 X Y) H2
      end.
      {
        (* Prove liveness matches up by ensure_liveness, for function entry *)
        repeat break_and.
        lazymatch goal with
          | [ H : step_bits _ _ _ (State_bits ?X ?Y ?MD), H2 : mem_eq _ _ ?Y |- _ ] =>
            exists (State_bits X Y MD);
              app no_ptr_regs_preserved H
        end.
        repeat break_and.
        repeat (split; auto; intros).
        
        P1 _eapply val_eq.
        repeat unify_PC.
        repeat unify_psur.
        match goal with
          | [ H : In ?X (liveness_fun_f _ _ _) |- In ?X _ ] =>
            unfold liveness_fun_f in H;
              repeat collapse_match_hyp
        end.
        break_match_hyp; eauto.
        break_match_hyp.
        (* WORKS TO HERE *)
        match goal with
          | [ H : forall c : code, _, H2 : context[match find_liveness ?X with _ => _ end] |- _ ] =>
            exploit (H X); try cop; intros
        end.
        repeat break_exists; repeat break_and.
        collapse_match_hyp.
        repeat rewrite Int.unsigned_zero in *.
        match goal with
          | [ H : ensure_liveness ?X _ = OK tt,
                  H2 : In ?Y (ZMap.get _ ?X)
              |- In ?Y _ ] =>
            unfold ensure_liveness in H;
              repeat break_match; try congruence
        end.
        unfold entry_ok in *.
        break_match_hyp; try congruence.
        unfold parameter_regs in *.
        match goal with
          | [ H : subset_dec _ _ = _ |- _ ] =>
            clear H
        end.
        rewrite app_nil_r in *.
        intuition.
        
      }
      {
        (* Prove liveness matches up by fixed point *)
        repeat break_and.
        intros.
        P1 _eapply val_eq.
        eassumption. eassumption.
        repeat break_and.
        unfold liveness_fun_f.
        repeat collapse_match.
        match goal with
          | [ H : forall c : code, _ |- context[find_liveness ?X] ] =>
            exploit (H X); try cop; intros
        end.
        repeat break_exists; repeat break_and.
        repeat collapse_match.
        match goal with
          | [ H : reached_fixed_point _ ?X |- context[?X] ] =>
            unfold reached_fixed_point in H;
              rewrite H
        end.
        unfold update_liveness.
        repeat collapse_match.
        repeat (break_match; try congruence; [idtac]).
        rewrite ZMap.gss. assumption.
      }
    - (* is a return *)
      break_exists. subst.
      match goal with
        | [ H: return_steps_back_to_call_bits _ , H2: step_bits _ _ _ _ |- _ ] => unfold return_steps_back_to_call_bits in H; app H H2
      end.
      match goal with
        | [ H : context[Pret ?X] |- _ ] => destruct X
      end.
      match goal with
        | [ H1: return_liveness_correct_bits _ ,
                H2: step_bits _ _ _ _  ,
                    H3: forall _, In _ (liveness_fun_f _ _ _) -> val_eq (?X _) (?Y _) |- _]
          => unfold return_liveness_correct_bits in H1; app (H1 X Y) H2
      end;
        repeat break_and.
      {
        match goal with
          | [ H : step_bits _ _ _ (State_bits ?X ?Y ?MD), H2 : mem_eq _ _ ?Y |- _ ] =>
            exists (State_bits X Y MD);
              app no_ptr_regs_preserved H
        end.
        repeat break_and.
        repeat (split; auto; intros).
        P1 _eapply val_eq.

        repeat unify_PC.
        repeat unify_psur.
        match goal with
          | [ H : In ?X (liveness_fun_f _ _ _) |- In ?X _ ] =>
            unfold liveness_fun_f in H;
              repeat collapse_match_hyp
        end.

        match goal with
          | [ H : forall c : code, _, H2 : context[match find_liveness ?X with _ => _ end] |- _ ] =>
            exploit (H X); try cop; intros
        end.
        repeat break_exists.
        repeat break_and.
        collapse_match_hyp.
        match goal with
          | [ H : ensure_liveness ?X _ = OK tt,
                  H2 : In ?Y (ZMap.get _ ?X)
              |- In ?Y _ ] =>
            unfold ensure_liveness in H;
              repeat break_match; try congruence
        end.
        unfold ret_ok in *.
        unfold calls_well_typed_bits in *.
        repeat break_and.

        match goal with
          | [ H : forall _ _, _ |- In ?X _ ] => exploit H; eauto
        end;
          try match goal with
                | [ H : In ?X _ |- _ ] => instantiate (1 := X)
              end.
        match goal with
          | [ |- context[?X - 1 + 1] ] => replace (X - 1 + 1) with (X) by omega
        end.
        solve [eauto].
        intros.
        match goal with
          | [ H : internal_calls_well_typed_bits _,
                  H2 : In _ (_ ++ _ (call_type _))
              |- _ ] =>
            unfold internal_calls_well_typed_bits in H;
              erewrite H in H2
        end;
        match goal with
          | [ H : find_instr _ _ = Some (Pret _) |- _ ] => try apply H
        end;
        eauto;
        match goal with
          | [ H : forall p : preg, _ -> val_eq (?X p) (?Y p),
                H2 : ?X PC = _
                |- ?Y PC = _ ] =>
            exploit (H PC); try rewrite H2 in *; intros;
            try eapply PC_always_live; eauto; simpl; intuition
        end.


      }
      {

        (* Prove liveness matches up by fixed point *)
        intros.
        P1 _eapply val_eq.
        eassumption.
        eassumption.
        repeat break_and.
        unfold liveness_fun_f.
        repeat collapse_match.
        
        match goal with
          | [ H : forall c : code, _ |- context[find_liveness ?X] ] =>
            exploit (H X); try cop; intros
        end.
        repeat break_exists; repeat break_and.
        repeat collapse_match.
        match goal with
          | [ H : reached_fixed_point _ ?X |- context[?X] ] =>
            unfold reached_fixed_point in H;
              rewrite H
        end.
        unfold update_liveness.
        repeat collapse_match.
        unfold is_call_return_dec.
        unfold is_call_dec.
        unfold call_type.
        
        rewrite ZMap.gss.
        unfold return_regs_sig.
        assumption.

      }

    - (* Show we started in code of this program *)
      assert (Hcop : code_of_prog fn_code p) by cop.
      (* Show the initial regsets agreed on registers used by this instr *)
      assert (Huse : forall p0 : preg, In p0 (use x2) -> val_eq (r p0) (r0 p0)).
      {
        intros.
        apply H19.
       unfold liveness_fun_f.
       collapse_match.
       specialize (H1 _ Hcop).
       break_exists.
       repeat break_and.
       collapse_match.
       unfold reached_fixed_point in *.
       rewrite H23. unfold update_liveness.
       repeat collapse_match.
       break_match; try congruence.
       edestruct succ_some_no_call; eauto.
       collapse_match. rewrite ZMap.gss.
       unfold transfer.
       eapply add_in_l; eauto.
      }
      (* Show the right PC is the same as the left *)
      assert (HPC : r0 PC = Values.Vint x1).
      {
        eapply (val_eq_def _ _ H3).
        eapply Huse.
        unfold use. unfold use_def.
        break_let. simpl. left. auto.
        congruence.
      }
      (* leverage use_spec' to show we can take a step *)
      app (use_def_spec p r r1 r0) H20. break_and.
      eexists; split; eauto. subst a. eassumption.
      simpl. intros. break_and.
      app no_ptr_regs_preserved H20.
      repeat break_and.
      split; eauto.
      split; eauto.
      split; try reflexivity.
      split; eauto.

      subst a.

      intros. 

      unfold liveness_fun_f in H10.
      specialize (H1 _ Hcop).
      repeat break_exists. repeat break_and.
      find_rewrite. find_rewrite.
      app def_spec' H21. instantiate (1 := p0) in H21.
      app def_spec' H26. instantiate (1 := p0) in H26.

      (* either p0 was updated by this instruction, or it wasn't *)
      destruct (in_dec preg_eq p0 (def x2)).
      + eapply H23. eauto.
      + repeat break_or; try congruence.
        rewrite <- H32. rewrite <- H26.
        eapply H19.
        unfold liveness_fun_f. repeat collapse_match.
        unfold reached_fixed_point in *.
        rewrite H28.
        unfold update_liveness.
        repeat collapse_match.
        break_match; try congruence.
        edestruct succ_some_no_call; eauto.
        collapse_match.
        rewrite ZMap.gss.
        

        assert (b = x). {
          symmetry.
          eapply step_no_call_same_block; try eapply H30; eauto.
        } idtac.

        subst. unfold liveness_fun_f in H18.
        find_rewrite. find_rewrite.
        app succ_sound_locally H21; eauto.
        unfold transfer.
        eapply add_in_r.
        rewrite <- rem_in.
        split; auto.
        eapply in_map_union_l; eauto.
        exploit (H23 PC). unfold def. unfold use_def. break_let.
        simpl. left. auto. intros.
        rewrite p1 in *. simpl in H34.
        congruence.
        split; auto.
        unfold calling_conv_correct_bits.
        intuition idtac.
  * (* assert prior agreement *)
    simpl.
    specialize (H2 x1 x x0 H5 H3).
    repeat break_and.
    unfold liveness_fun_f in H18. rewrite H4 in H18.
    (* use calling convention *)
    unfold calling_conv_correct_bits in *.
    repeat break_and.
    unfold external_fun_liveness_correct_bits in *.

    app H12 H15. repeat break_and.
    eexists; split; try eassumption.
    subst a. eassumption.
    simpl.

    intros.
    app no_ptr_regs_preserved H15.
    repeat break_and.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    intros.
    unfold liveness_fun_f in H26.

    unfold external_fun_steps_back_to_call_bits in *.
    exploit (H22 PC). 
    simpl. left. reflexivity. intros.
    rewrite p1 in *. 
    simpl in H27.
    symmetry in H27.
    subst a.

    exploit (H18 PC).
    simpl. left. reflexivity. intros.
    rewrite H3 in H17. simpl in H17. symmetry in H17.
    
    app H13 H24.
    repeat break_and.
    repeat break_exists.
    repeat break_and.
    unify_PC.
    unify_psur.

    
    rewrite H30 in H26.
    assert (code_of_prog x8 p) by cop.
    specialize (H1 _ H23).
    repeat break_exists; repeat break_and.
    rewrite H1 in *.
    apply H22.

    unfold ensure_liveness in *.
    repeat break_match_hyp; try congruence.
    unfold ret_ok in *.
    repeat break_match_hyp; try congruence.
    
    
    app r2 H32. instantiate (2 := p0) in H32.
    unfold calls_well_typed_bits in *.
    repeat break_and.
    unfold external_calls_well_typed_bits in H35.
    erewrite H35 in H32; eauto.
    
    replace (Int.unsigned i - 1 + 1) with (Int.unsigned i) by omega.
    assumption.

    Grab Existential Variables.
    exact Pnop.
Qed.

Theorem liveness_analysis_correct:
  forall p,
    (no_PC_overflow_prog p /\ labels_valid_prog p /\ calling_conv_correct_bits p /\ no_builtin_clobber_PC_prog p) ->
    ensure_liveness_prog (prog_defs p) = OK tt ->
    liveness_fun_correct p liveness_fun_f.
Proof.
  intros. apply fixed_point_liveness; auto.
  intros. eapply all_reached_fixed_point; eauto.
Qed.
