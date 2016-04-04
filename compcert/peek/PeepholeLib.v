Require Import Coqlib.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Asm.
Require Import Integers.
Require Import Maps.
Require Import Errors.
Require Import Machregs.

Require Import ProofIrrelevance.

Require Import PeekLiveness.
Require Import SplitLib.
Require Import FindInstrLib.
Require Import PeekTactics.
Require Import PregTactics.
Require Import AsmCallingConv. 
Require Import Union.
Require Import StepIn. 
Require Import PeekLivenessProof.
Require Import Use.
Require Import PeekLib.
Require Import SameBlockLib.
Require Import StepEquiv. (* Where rewrite is defined *)
Require Import ProgPropDec. 
Require Import ForwardJumps. 

Require Import AsmBits.
Require Import MemoryAxioms.

Require Import ValEq.
Require Import MemEq.

Require Import Peephole.
Require Import Zlen.

Section PRESERVATION.

Variable rwr: rewrite.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSF: transf_program rwr prog = OK tprog.
Hypothesis CALLING_CONV : calling_conv_correct_bits prog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall id, Genv.find_symbol (Genv.globalenv (tprog)) id = Genv.find_symbol ge id.
Proof.
  unfold transf_program in TRANSF. 
  repeat break_match_hyp; inversion TRANSF.
  apply Genv.find_symbol_transf.
Qed.

Lemma public_symbols_preserved:
  forall id,
    Genv.public_symbol (Genv.globalenv tprog) id = Genv.public_symbol ge id.
Proof.
  unfold transf_program in TRANSF.
  repeat break_match_hyp; inversion TRANSF.
  apply Genv.public_symbol_transf.
Qed.

Lemma offsets_preserved:
  forall id i, symbol_offset (Genv.globalenv (tprog)) id i = symbol_offset ge id i.
Proof.
  intros. unfold symbol_offset.
  rewrite symbols_preserved; auto.
Qed.

Lemma functions_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr (Genv.globalenv (tprog)) b = Some (transf_fundef rwr f).
Proof.
  intros.
  unfold transf_program in TRANSF. 
  repeat break_match_hyp; inversion TRANSF.
  apply Genv.find_funct_ptr_transf; auto.
Qed.

Lemma code_translated:
  forall b s c,
  Genv.find_funct_ptr ge b = Some (Internal (mkfunction s c)) ->
  Genv.find_funct_ptr (Genv.globalenv (tprog)) b = Some (Internal (mkfunction s (transf_code rwr c))).
Proof.
  intros. exploit functions_translated; eauto.
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info (Genv.globalenv (tprog)) b = Genv.find_var_info ge b.
Proof.
  intros.
  unfold transf_program in TRANSF. repeat break_match_hyp; inversion TRANSF.
  apply Genv.find_var_info_transf; auto.
Qed.

Lemma eval_addrmode_pres:
  forall a rs,
  eval_addrmode (Genv.globalenv (tprog)) a rs = eval_addrmode ge a rs.
Proof.
  intros; destruct a.
  destruct base; destruct ofs; destruct const; simpl; auto;
  try destruct p0; try destruct p; rewrite offsets_preserved; auto.
Qed.

Lemma eval_addrmode_bits_pres:
  forall md a rs,
  eval_addrmode_bits (Genv.globalenv (tprog)) md a rs = eval_addrmode_bits ge md a rs.
Proof.
  intros; destruct a.
  unfold eval_addrmode_bits.
  rewrite eval_addrmode_pres. reflexivity.
Qed.

Lemma eval_addrmode_no_ptr_pres:
  forall md a rs,
  eval_addrmode_no_ptr (Genv.globalenv (tprog)) md a rs = eval_addrmode_no_ptr ge md a rs.
Proof.
  intros; destruct a.
  unfold eval_addrmode_no_ptr.
  destruct base; destruct ofs; destruct const; simpl; auto;
  try destruct p0; try destruct p; rewrite offsets_preserved; auto.
Qed.

Lemma exec_load_pres:
  forall c m a rs rd rs' m',
  exec_load ge c m a rs rd = Next rs' m' ->
  exec_load (Genv.globalenv (tprog)) c m a rs rd = Next rs' m'.
Proof.
  unfold exec_load; intros.
  rewrite eval_addrmode_pres; auto.
Qed.

Lemma exec_load_bits_pres:
  forall c m a rs rd rs' m' md md',
  exec_load_bits ge md c m a rs rd = Nxt rs' m' md' ->
  exec_load_bits (Genv.globalenv (tprog)) md c m a rs rd = Nxt rs' m' md'.
Proof.
  unfold exec_load_bits; intros.
  rewrite eval_addrmode_bits_pres; auto.
Qed.

Lemma exec_store_pres:
  forall c m a rs rd l rs' m',
  exec_store ge c m a rs rd l = Next rs' m' ->
  exec_store (Genv.globalenv (tprog)) c m a rs rd l = Next rs' m'.
Proof.
  unfold exec_store; intros.
  rewrite eval_addrmode_pres; auto.
Qed.

Lemma exec_store_bits_pres:
  forall c m a rs rd l rs' m' md md',
  exec_store_bits ge md c m a rs rd l = Nxt rs' m' md' ->
  exec_store_bits (Genv.globalenv (tprog)) md c m a rs rd l = Nxt rs' m' md'.
Proof.
  unfold exec_store_bits; intros.
  rewrite eval_addrmode_bits_pres; auto.
Qed.

Lemma exec_big_load_bits_pres:
  forall c m a rs rd rs' m' md md',
  exec_big_load_bits ge md c m a rs rd = Nxt rs' m' md' ->
  exec_big_load_bits (Genv.globalenv (tprog)) md c m a rs rd = Nxt rs' m' md'.
Proof.
  unfold exec_big_load_bits in *; intros.
  break_let. repeat rewrite eval_addrmode_bits_pres; auto.
Qed.

Lemma exec_big_store_bits_pres:
  forall c m a rs rd l rs' m' md md',
  exec_big_store_bits ge md c m a rs rd l = Nxt rs' m' md' ->
  exec_big_store_bits (Genv.globalenv (tprog)) md c m a rs rd l = Nxt rs' m' md'.
Proof.
  unfold exec_big_store_bits; intros.
  break_let. repeat rewrite eval_addrmode_bits_pres; auto.
Qed.

Lemma length_pres:
  forall c,
  length (transf_code rwr c) = length c.
Proof.
  intros. unfold transf_code.
  repeat break_match; auto.
  apply split_pat_spec in Heqo.
  rewrite Heqo.
  repeat rewrite app_length.
  rewrite (len_same rwr).
  reflexivity.
Qed.

Inductive transf_range : Values.block -> Z -> Z -> Prop :=
  | t_s:
      forall b i j s c c1 c2,
        Genv.find_funct_ptr ge b = Some (Internal (mkfunction s c)) ->
        (split_pat rwr.(find) c = Some (c1, c2) /\ transf_code rwr c = c1 ++ rwr.(repl) ++ c2) ->
        i = zlen c1 ->
        j = zlen (c1 ++ rwr.(find)) ->
        transf_range b i j.

Inductive in_transf : state_bits -> Prop :=
  | in_t :
      forall b i j rsl rsl' m m' bits rsli mi md mdi md',
        rsl PC = Values.Vint bits ->
        psur md bits = Some (b,i) ->
        transf_range b (Int.unsigned i) j ->
        step_bits (Genv.globalenv prog) (State_bits rsl m md) E0 (State_bits rsli mi mdi) ->
        in_code (Int.unsigned i) (find rwr) (Genv.globalenv prog) (State_bits rsli mi mdi) ->
        star (step_in (Int.unsigned i) (find rwr)) (Genv.globalenv prog)
             (State_bits rsli mi mdi) E0 (State_bits rsl' m' md') ->
        in_transf (State_bits rsl' m' md').

Inductive outside_range : state_bits -> Prop :=
  | out_r :
      forall rs m b i bits md,
        rs PC = Values.Vint bits ->
        psur md bits = Some (b,i) ->
        (exists x,
           Genv.find_funct_ptr (Genv.globalenv prog) b = Some x /\
           match x with
             | Internal (mkfunction s c) =>
               (exists x y, transf_range b x y /\ (Int.unsigned i < x \/ Int.unsigned i >= y)) \/ transf_code rwr c = c
             | External _ => True
           end) ->
        outside_range (State_bits rs m md).

Inductive at_entry : state_bits -> Prop :=
  | at_ent : 
      forall rs m b i k bits md,
        rs PC = Values.Vint bits ->
        psur md bits = Some (b,i) ->
        transf_range b (Int.unsigned i) k ->
        at_entry (State_bits rs m md).

Inductive match_states : state_bits -> state_bits -> Prop :=
  | outside : 
      forall rs rs' m m' b i bits md,
        rs PC = Values.Vint bits ->
        rs' PC = Values.Vint bits ->
        psur md bits = Some (b,i) ->
        outside_range (State_bits rs m md) ->
        (forall r, In r (liveness_fun_f ge b (Int.unsigned i)) -> val_eq (rs r) (rs' r)) ->
        mem_eq md m m' ->
        (no_ptr_regs rs' /\ no_ptr_mem m') ->
        match_states (State_bits rs m md) (State_bits rs' m' md)
  | entry :
      forall rs rs' m m' b i k f bits md
        (p1 : Genv.find_funct_ptr (Genv.globalenv prog) b = Some (Internal f)),
        rs PC = Values.Vint bits ->
        rs' PC = Values.Vint bits ->
        psur md bits = Some (b,i) ->
        transf_range b (Int.unsigned i) k ->
        (forall r, In r (liveness_fun_f ge b (Int.unsigned i)) -> (val_eq (rs r) (rs' r))) ->
        mem_eq md m m' ->
        (no_ptr_regs rs' /\ no_ptr_mem m') ->
        match_states (State_bits rs m md) (State_bits rs' m' md)
  | inside :
      forall rsl ml mr rsr rsl' m' b i j f bits rsli mi md mdi md'
        (p1 : Genv.find_funct_ptr (Genv.globalenv prog) b = Some (Internal f)),
        rsl PC = Values.Vint bits ->
        rsr PC = Values.Vint bits ->
        psur md bits = Some (b,i) ->
        transf_range b (Int.unsigned i) j ->
        step_bits (Genv.globalenv prog) (State_bits rsl ml md) E0 (State_bits rsli mi mdi) ->
        in_code (Int.unsigned i) (find rwr) (Genv.globalenv prog) (State_bits rsli mi mdi) ->
        star (step_in (Int.unsigned i) (find rwr)) (Genv.globalenv prog)
             (State_bits rsli mi mdi) E0 (State_bits rsl' m' md') ->
        (forall r, In r (liveness_fun_f ge b (Int.unsigned i)) -> val_eq (rsl r) (rsr r)) ->
        mem_eq md ml mr ->
        (no_ptr_regs rsr /\ no_ptr_mem mr) ->
        match_states (State_bits rsl' m' md') (State_bits rsr mr md)
  | external :
      forall rs rs' b ef m m' bits md
        (p1 : Genv.find_funct_ptr (Genv.globalenv prog) b = Some (External ef)),
        rs PC = Values.Vint bits ->
        rs' PC = Values.Vint bits ->
        psur md bits = Some (b,Int.zero) ->
        (forall r, In r (liveness_fun_f ge b 0) -> val_eq (rs r) (rs' r)) ->
        (no_ptr_regs rs' /\ no_ptr_mem m') ->
        mem_eq md m m' ->
        match_states (State_bits rs m md) (State_bits rs' m' md).


Definition transf_index (s : state_bits) (i j : Z) : Prop :=
  forall rs m md,
    s = State_bits rs m md ->
    forall bits b x,
      rs PC = Values.Vint bits ->
      psur md bits = Some (b,x) ->
      transf_range b i j.

Definition transf_idx_end (st : state_bits) : Z :=
  match st with
    | State_bits rs m md =>
      match rs PC with 
        | Values.Vint bits =>
          match psur md bits with
            | Some (b,i) =>
              match Genv.find_funct_ptr (Genv.globalenv prog) b with
                | Some (Internal (mkfunction _ c)) =>
                  match split_pat rwr.(find) c with
                    | Some(c1,c2) => 
                      if (is_proper_location_check rwr c1 rwr.(find) c2 (get_labels c1 ++ get_labels c2) rwr.(repl)) then
                        zlen c1 + zlen (find rwr)
                      else
                        0
                    | None => 0
                  end
                | _ => 0
              end
            | None => 0
          end
        | _ => 0
      end
  end.


Definition is_external_call (i : instruction) : Prop :=
  match i with
    | Pbuiltin ef args res => True 
    | _ => False
  end.

Lemma nextinstr_PC :
  forall rs v,
    rs PC = v ->
    nextinstr rs PC = Values.Val.add v Values.Vone.
Proof.
  intros. unfold nextinstr.
  rewrite Pregmap.gss. rewrite H. reflexivity.
Qed.

Lemma nextinstr_nf_PC :
  forall rs v,
    rs PC = v ->
    nextinstr_nf rs PC = Values.Val.add v Values.Vone.
Proof.
  intros. unfold nextinstr_nf.
  simpl. unfold nextinstr.
  rewrite Pregmap.gss.
  repeat rewrite Pregmap.gso by discriminate.
  rewrite H. reflexivity.
Qed.

Definition is_builtin (i : instruction) : Prop :=
  match i with
    | Pbuiltin _ _ _ => True
    | _ => False
  end.
  

Lemma external_call_pres:
  forall ef a b c d e,
    external_call ef (Genv.globalenv prog) a b c d e ->
    external_call ef (Genv.globalenv tprog) a b c d e.
Proof.
  intros. 
  eapply external_call_symbols_preserved_gen; try apply H; intros.
  unfold Senv.find_symbol. simpl.
  eapply symbols_preserved; eauto.
  unfold Senv.public_symbol. simpl.
  eapply public_symbols_preserved; eauto.
  intros. unfold Senv.block_is_volatile.
  simpl. unfold Genv.block_is_volatile. 
  erewrite varinfo_preserved; eauto.
Qed.

(* proven jointly by p92 and epdtry *)
(* Thanks guys!!!! *)
Lemma list_neq :
  forall {A} (l1 l2 l3 l4 : list A),
    l2 <> l4 ->
    l1 ++ l2 ++ l3 <> l1 ++ l4 ++ l3.
Proof.
  intros.
  Hint Resolve app_inv_tail app_inv_head. 
  eauto.
Qed.

Lemma star_step_in_same_block :
  forall rs m t rs' m' z bits b i bits' b' i' md md',
    star (step_in z (find rwr)) ge (State_bits rs m md) t (State_bits rs' m' md') ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,i) ->
    rs' PC = Values.Vint bits' ->
    psur md' bits' = Some (b',i') ->
    b' = b.
Proof.
  intros.
  app only_forward_jumps_same_block_star H.
  unfold transf_program in TRANSF.
  repeat break_match_hyp; try congruence; auto.
  eapply (forward_find rwr).
Qed.


Lemma start_transf_range_at_code :
  forall rs m bits b i j md,
    transf_range b (Int.unsigned i) j ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,i) ->
    at_code (Int.unsigned i) (find rwr) 0 ge (State_bits rs m md).
Proof.
  intros. inv H.
  rewrite H4. econstructor; eauto. omega.
  destruct (find rwr) eqn:?. app find_nonempty Heqc0. inv Heqc0.
  rewrite zlen_cons. name (zlen_nonneg _ c0) zlnc.
  omega. simpl.
  break_and. app split_pat_spec H.
Qed.

Lemma start_transf_range_at_code_tprog :
  forall rs m bits b i j md,
    transf_range b (Int.unsigned i) j ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,i) ->
    at_code (Int.unsigned i) (repl rwr) 0 tge (State_bits rs m md).
Proof.
  intros. inv H.
  rewrite H4. econstructor; eauto. omega.
  destruct (repl rwr) eqn:?. app repl_nonempty Heqc0. inv Heqc0.
  rewrite zlen_cons. name (zlen_nonneg _ c0) zlnc.
  omega.
  app functions_translated H2. simpl.
  break_and. eassumption.
Qed.

Lemma transf_range_unique :
  forall b i j i' j',
    transf_range b i j ->
    transf_range b i' j' ->
    i' = i /\ j' = j.
Proof.
  intros. inv H.
  inv H0.
  rewrite H in H1. inv H1.
  repeat break_and.
  rewrite H2 in H0. inv H0.
  split; reflexivity.
Qed.  

Lemma zlen_find :
  zlen (find rwr) > 0.
Proof.
  destruct (find rwr) eqn:?.
  app find_nonempty Heqc. inv_false.
  rewrite zlen_cons. name (zlen_nonneg _ c) zln.
  omega.
Qed.


Lemma zlen_find_rwr :
  zlen (find rwr) = zlen (repl rwr).
Proof.
  name (len_same rwr) ls. unfold zlen. rewrite ls. reflexivity.
Qed.



Lemma instrs_translated :
  forall rs m b s c x i bits md,
    outside_range (State_bits rs m md) ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,x) ->
    Genv.find_funct_ptr (Genv.globalenv prog) b = Some (Internal (mkfunction s c)) ->
    find_instr (Int.unsigned x) c = Some i ->
    find_instr (Int.unsigned x) (transf_code rwr c) = Some i.
Proof.
  intros. inv H.
  unify_PC. unify_psur.
  break_exists. break_and. unify_find_funct_ptr.
  destruct H1; repeat break_exists; repeat break_and.
  
  unfold transf_code.
  repeat break_match; auto.
  assert (transf_range b (zlen c0) (zlen c0 + zlen (find rwr))).
    econstructor; eauto.
    split. apply Heqo.
    unfold transf_code.
    find_rewrite. find_rewrite.
    reflexivity. rewrite zlen_app. reflexivity.

    eapply transf_range_unique in H; try apply H4.
    break_and. subst.
  apex in_range_find_instr H3.
  app split_pat_spec Heqo.  break_or.
  rewrite find_instr_append_tail with (c := nil) in * by omega.
  eassumption.
  replace (Int.unsigned x) with (zlen (c0 ++ repl rwr) + (Int.unsigned x - zlen (c0 ++ repl rwr))) by omega.
  rewrite <- app_ass in *.
  rewrite find_instr_append_head by (rewrite zlen_app; try rewrite <- zlen_find_rwr; omega).
  replace (Int.unsigned x) with (zlen (c0 ++ find rwr) + (Int.unsigned x - zlen (c0 ++ find rwr))) in H3 by omega.
  rewrite find_instr_append_head in H3 by (rewrite zlen_app; omega).
  rewrite zlen_app in H3. rewrite zlen_find_rwr in H3. rewrite zlen_app. assumption.

  rewrite H. eauto.
Qed.




Lemma no_trace_not_builtin :
  forall i,
    no_trace i ->
    ~ is_builtin i.
Proof.
  intros. intro. destruct i; simpl in *; try inv_false.
Qed.


Lemma in_transf_same_block :
  forall st,
    in_transf st ->
    forall t st',
      step_bits (Genv.globalenv prog) st t st' ->
      in_same_block st st'.
Proof.
  intros.
  inv H. name (conj H6 H5) Hc.
  rewrite <- st_in_eq in Hc.
  app star_step_in_in' Hc. 
  destruct st'.
  app step_in_step_t' H0. break_and.
  inv H0. inv H17. rewrite E0_right in *.
  inv H11.

  destruct fd. name (forward_find rwr) ff.
  unfold only_forward_jumps in ff. repeat break_and.
  app find_instr_in H8.
  assert (Hfi : find_instr (Int.unsigned i0) fn_code = Some x).
  simpl in H22.
  rewrite H22.
  rewrite H15.
  rewrite find_instr_append_head by omega. simpl. reflexivity.
  
  app step_PC_same_block H7. break_and.
  econstructor; eauto.

  unfold no_trace_code in H9.

  unfold transf_program in TRANSF.
  repeat (break_match_hyp; try congruence); auto.
  
  apply no_trace_not_builtin. eapply H9; eauto.
Qed.

Lemma int_add_one_range :
  forall i x,
    Int.unsigned i < x ->
    Int.unsigned (Int.add i Int.one) >= x ->
    0 <= Int.unsigned i < Int.max_unsigned ->
    Int.unsigned (Int.add i Int.one) = x.
Proof.
  intros.
  unfold Int.add in H0.
  rewrite Int.unsigned_repr in H0.
  unfold Int.add.
  rewrite Int.unsigned_repr.
  rewrite Int.unsigned_one in *.
  omega.
  rewrite Int.unsigned_one. omega.
  rewrite Int.unsigned_one. omega.
Qed.

Lemma int_add_one_range_contra :
  forall i x,
    x >= 0 ->
    Int.unsigned (Int.add i Int.one) < x  ->
    0 <= Int.unsigned i < Int.max_unsigned ->
    Int.unsigned i >= x ->
    False.
Proof.
  intros. unfold Int.add in H0.
  rewrite Int.unsigned_repr in H0.
  rewrite Int.unsigned_one in H0.
  omega.
  rewrite Int.unsigned_one. omega.
Qed.

Lemma get_labels_in :
  forall c l z,
    find_instr z c = Some (Plabel l) ->
    In l (get_labels c).
Proof.
  induction c; intros.
  * simpl in H. inv H.
  * destruct (zeq z 0).
    - rewrite e in *. simpl in H. inv H.
      simpl. left. reflexivity.
    - assert (exists i, find_instr z (a :: c) = Some i).
        eexists; eauto.
      apply in_range_find_instr in H0.
      replace z with (1 + (z - 1)) in H by omega.
      rewrite find_instr_head in H by omega.
      app IHc H. destruct a; simpl; auto.
      rewrite in_app. right. auto.
Qed.

Lemma get_labels_all :
  forall c i l z,
    find_instr z c = Some i ->
    is_label_instr i l ->
    In l (get_labels c).
Proof.
  induction c; intros.
  * simpl in H. inv H.
  * destruct (zeq z 0).
    - rewrite e in *. simpl in H. inv H.
      destruct i; simpl in H0; try inversion H0;
      simpl; try left; try reflexivity.
      rewrite in_app. left. auto.
    - assert (exists i, find_instr z (a :: c) = Some i).
        eexists; eauto. 
      apply in_range_find_instr in H1.
      replace z with (1 + (z - 1)) in H by omega.
      rewrite find_instr_head in H by omega.
      app IHc H. destruct a; simpl; auto.
      rewrite in_app. right. auto.
Qed.

Lemma no_labels_jump_out_contra_c1 :
  forall c1 c2,
    no_labels (find rwr) (get_labels c1 ++ get_labels c2) ->
    forall z l,
      label_pos l 0 (c1 ++ find rwr ++ c2) = Some z ->
      forall z' i,
        find_instr z' (c1 ++ find rwr ++ c2) = Some i ->
        is_label_instr i l ->
        z < zlen c1 ->
        z' >= zlen c1 ->
        z' < zlen (c1 ++ find rwr) ->
        False.
Proof.
  intros.
  unfold no_labels in H.
  replace z' with (zlen c1 + (z' - zlen c1)) in H1 by omega.
  rewrite find_instr_append_head in H1 by omega. 
  rewrite zlen_app in H5.
  rewrite find_instr_append_tail with (c := nil) in H1 by omega.
  rewrite app_nil_r in H1.
  specialize (H (z' - zlen c1) i H1).
  app H H2.
  apply label_pos_find_instr in H0.
  assert (exists i, find_instr (z - 1) (c1 ++ find rwr ++ c2) = Some i).
    eexists; eauto.
  apply in_range_find_instr in H7.
  rewrite find_instr_append_tail with (c := nil) in H0 by omega.
  rewrite app_nil_r in H0.
  apply get_labels_in in H0.
  app H H6.
  unfold not in H6. apply H6. apply in_app.
  left. auto.
Qed.

Lemma no_labels_jump_out_contra_c2 :
  forall c1 c2,
    no_labels (find rwr) (get_labels c1 ++ get_labels c2) ->
    forall z l,
      label_pos l 0 (c1 ++ find rwr ++ c2) = Some z ->
      forall z' i,
        find_instr z' (c1 ++ find rwr ++ c2) = Some i ->
        is_label_instr i l ->
        z >= zlen (c1 ++ find rwr) ->
        z' >= zlen c1 ->
        z' < zlen (c1 ++ find rwr) ->
        False.
Proof.
  intros.
  unfold no_labels in H.
  replace z' with (zlen c1 + (z' - zlen c1)) in H1 by omega.
  rewrite find_instr_append_head in H1 by omega.
  rewrite zlen_app in H3. rewrite zlen_app in H5.
  rewrite find_instr_append_tail with (c := nil) in H1 by omega.
  rewrite app_nil_r in H1.
  specialize (H (z' - zlen c1) i H1).
  app H H2.
  apply label_pos_find_instr in H0.
  name (no_label_out rwr) nlo.
  assert (z = zlen c1 + zlen (find rwr) \/ z > zlen c1 + zlen (find rwr)).
    omega.
  destruct H7.
  rewrite H7 in H0.
  unfold ends_in_not_label in nlo.
  replace (zlen c1 + zlen (find rwr) - 1) with (zlen c1 + (zlen (find rwr) - 1)) in H0 by omega.
  rewrite find_instr_append_head in H0 by omega.
  rewrite find_instr_append_tail with (c := nil) in H0 by omega.
  rewrite app_nil_r in H0.
  app nlo H0.
  simpl in H0.
  unfold not in H0. specialize (H0 I). inv H0.
  replace (z - 1) with (zlen (c1 ++ (find rwr)) + (z - zlen (c1 ++ (find rwr)) - 1)) in H0.
  rewrite <- app_ass in H0.
  rewrite find_instr_append_head in H0.
  unfold not in H2.
  apply get_labels_in in H0.
  rewrite in_app in H2. apply H2.
  right. auto.
  rewrite zlen_app. 
  name (zlen_nonneg instruction c1) zln.
  name (zlen_nonneg instruction (find rwr)) zlnr.
  omega.
  name (zlen_nonneg instruction c1) zln.
  name (zlen_nonneg instruction (find rwr)) zlnr.

  repeat rewrite zlen_app.
  omega.
Qed.

Lemma no_trace_step :
  forall st,
    in_transf st ->
    forall st' t,
      step_bits (Genv.globalenv prog) st t st' ->
      t = E0.
Proof.

  intros. inv H.
  name (conj H6 H5) Hc.
  rewrite <- st_in_eq in Hc.
  app star_step_in_in' Hc.
  app step_in_step_t' H0.
  break_and. app find_instr_in H8.
  inv H0. inv H18. rewrite E0_right.
  app no_trace_step_in H13.
  name (forward_find rwr) ff.
  unfold only_forward_jumps in *. repeat break_and. auto.
Qed.


Lemma label_pos_pres :
  forall c0 f r c1 l instr z z',
    label_pos l 0 (c0 ++ f ++ c1) = Some z ->
    find_instr z' (c0 ++ f ++ c1) = Some instr ->
    z' < zlen c0 \/ z' >= zlen (c0 ++ f) ->
    zlen f = zlen r ->
    is_label_instr instr l ->
    only_labels c0 (get_labels c0 ++ get_labels c1) ->
    only_labels c1 (get_labels c0 ++ get_labels c1) ->
    no_labels f (get_labels c0 ++ get_labels c1) ->
    no_labels r (get_labels c0 ++ get_labels c1) ->
    label_pos l 0 (c0 ++ r ++ c1) = Some z.
Proof.
  intros.
  name (zlen_nonneg instruction) zl.
  name (zl f) zlf. name (zl r) zlr. name (zl c0) zlc0.
  assert (forall z i, find_instr z f = Some i -> i <> Plabel l).
    assert (In l (get_labels c0 ++ get_labels c1)).
      destruct H1. app find_instr_range H0.
      rewrite find_instr_append_tail with (c := nil) in H8 by omega.
      rewrite app_nil_r in H8.
      unfold only_labels in H4. app H4 H8.
      rewrite zlen_app in H1. app find_instr_range H0.
      replace z' with (zlen c0 + (z' - zlen c0)) in H8 by omega.
      rewrite find_instr_append_head in H8 by omega.
      replace (z' - zlen c0) with (zlen f + (z' - zlen c0 - zlen f)) in H8 by omega.
      rewrite find_instr_append_head in H8 by omega.
      unfold only_labels in H5. app H5 H8.
    unfold no_labels in H6. intros.
    destruct (label_instr_other_dec i l).
    name (H6 _ _ H9 _ i0) Hlinstr. congruence. 
    destruct i; simpl in n; try congruence; auto.
  assert (forall z i, find_instr z r = Some i -> i <> Plabel l).
    assert (In l (get_labels c0 ++ get_labels c1)).
      destruct H1. app find_instr_range H0.
      rewrite find_instr_append_tail with (c := nil) in H9 by omega.
      rewrite app_nil_r in H9.
      unfold only_labels in H4. app H4 H9.
      rewrite zlen_app in H1. app find_instr_range H0.
      replace z' with (zlen c0 + (z' - zlen c0)) in H9 by omega.
      rewrite find_instr_append_head in H9 by omega.
      replace (z' - zlen c0) with (zlen f + (z' - zlen c0 - zlen f)) in H9 by omega.
      rewrite find_instr_append_head in H9 by omega.
      unfold only_labels in H5. app H5 H9.
    unfold no_labels in H7. intros.
    destruct (label_instr_other_dec i l).
    name (H7 _ _ H10 _ i0) Hlinstr. congruence.
    destruct i; simpl in n; try congruence; auto.
  app label_pos_replace H. 
Qed.

Lemma goto_label_pres :
  forall rs m md,
    outside_range (State_bits rs m md) ->
    forall b i bits,
      rs PC = Values.Vint bits ->
      psur md bits = Some (b,i) ->
      forall s c,
        Genv.find_funct_ptr (Genv.globalenv prog) b = Some (Internal (mkfunction s c)) ->
        forall instr,
          find_instr (Int.unsigned i) c = Some instr ->
          forall l, 
            is_label_instr instr l ->
            forall rs' m' md',
              goto_label_bits md (mkfunction s c) l b rs m = Nxt rs' m' md' ->
              goto_label_bits md (mkfunction s (transf_code rwr c)) l b rs m = Nxt rs' m' md'.
Proof.
  intros. inv H.
  unfold transf_code.
  repeat break_match; auto. 
  unfold goto_label_bits in H5. unify_PC. unify_psur.
  repeat break_match_hyp; try congruence;
  st_inv.
  assert (Htc : transf_code rwr c = c0 ++ repl rwr ++ c1). {
    unfold transf_code.
    rewrite Heqo. rewrite Heqb1. reflexivity.
  }
  assert (Htransf_range: transf_range b (zlen c0) (zlen (c0 ++ (find rwr)))). {
    econstructor; eauto.
  } 
  assert (c <> c0 ++ repl rwr ++ c1). {
    apply split_pat_spec in Heqo. rewrite Heqo.
    apply list_neq. apply (not_same rwr).
  } 
  unfold goto_label_bits.
  repeat collapse_match.
  app is_proper_check_sound Heqb1.
  break_and.
  unfold is_proper_rewrite_location in *.
  repeat break_and.


  unify_find_funct_ptr.
  destruct H7.
  
  repeat break_exists. break_and.
  app split_pat_spec Heqo.
  rewrite Heqo in *.
  simpl.
  erewrite label_pos_pres; eauto.
  unfold zlen.
  collapse_match. reflexivity.
  eapply transf_range_unique in H5; try apply Htransf_range.
  break_and. subst. omega.
  apply zlen_find_rwr.

  rewrite H5 in Htc. congruence.

Qed.

Lemma symbol_address_pres :
  forall id ofs v,
    Genv.symbol_address (Genv.globalenv prog) id ofs = v ->
    Genv.symbol_address (Genv.globalenv tprog) id ofs = v.
Proof.
  intros. unfold Genv.symbol_address in *.
  break_match_hyp; rewrite symbols_preserved;
  unfold ge in *;
  try rewrite Heqo; eauto. 
Qed.

Lemma eval_annot_arg_bits_pres :
  forall (rs : regset) m args vargs md,
    eval_annot_arg_bits md (Genv.globalenv prog) rs (rs ESP) m args vargs ->
    eval_annot_arg_bits md (Genv.globalenv tprog) rs (rs ESP) m args vargs.
Proof.
  induction 1; intros; econstructor; eauto.
  unfold Senv.symbol_address in *. unfold Senv.find_symbol in *.
  simpl in *.
  break_match_hyp; rewrite symbols_preserved; unfold ge; rewrite Heqo; eauto.
  unfold Senv.symbol_address in *. unfold Senv.find_symbol in *. simpl in *.
  break_match_hyp; rewrite symbols_preserved; unfold ge; rewrite Heqo0; eauto.
  unfold Senv.symbol_address in *. unfold Senv.find_symbol in *. simpl in *.
  break_match_hyp; rewrite symbols_preserved; unfold ge; rewrite Heqo; eauto.
Qed.

Lemma eval_annot_args_bits_pres :
  forall (rs : regset) m args vargs md,
    eval_annot_args_bits md (Genv.globalenv prog) rs (rs ESP) m args vargs ->
    eval_annot_args_bits md (Genv.globalenv tprog) rs (rs ESP) m args vargs.
Proof.
  induction 1; intros. econstructor; eauto.
  econstructor; eauto.
  eapply eval_annot_arg_bits_pres; eauto.
Qed.


Lemma code_transformed :
  forall c,
    code_of_prog c prog ->
    code_of_prog (transf_code rwr c) tprog.
Proof.
  intros. unfold code_of_prog in *.  
  unfold transf_program in TRANSF.
  repeat break_match_hyp; inversion TRANSF.
  unfold transform_program. simpl.
  repeat break_exists.
  eexists. eexists.
  rewrite in_map_iff. exists (x, Gfun (Internal (mkfunction x0 c))).
  split. simpl. reflexivity. auto.
Qed.


Lemma no_PC_ovf_tprog :
  no_PC_overflow_prog tprog.
Proof.
  unfold transf_program in TRANSF.
  repeat break_match_hyp; inversion TRANSF.
  unfold no_PC_overflow_prog in n.
  unfold no_PC_overflow_prog. intros.
  unfold code_of_prog in H.
  repeat break_exists.
  rename x0 into s.
  
  apply transform_program_function in H.
  break_exists. break_and.
  destruct x0. Focus 2.
  simpl in H1. inv H1.
  destruct f0 as [s0 c0]. 
  assert (code_of_prog c0 prog).
    unfold code_of_prog. eexists; eauto.
  app n H2. simpl in H1. inv H1.
  unfold no_PC_overflow in H2.
  unfold no_PC_overflow. intros. 
  assert (exists i, find_instr z (transf_code rwr c0) = Some i).
    eexists; eauto.
  apply in_range_find_instr in H1.
  name (length_pres c0) lp.
  assert (zlen c0 = zlen (transf_code rwr c0)).
    unfold zlen. rewrite lp. reflexivity.
  rewrite <- H4 in H1.
  apply in_range_find_instr in H1.
  break_exists. app H2 H1.
Qed.

Lemma at_entry_at_code :
  forall s,
    at_entry s ->
    exists z,
      at_code z (find rwr) 0 ge s.
Proof.
  intros. inv H.
  exists (Int.unsigned i).
  inv H2. break_and.
  rewrite H4. econstructor; eauto. omega.
  name (zlen_find) zl. omega.
  simpl.
  app split_pat_spec H2.
Qed.

Lemma in_transf_at_code :
  forall s,
    in_transf s ->
    exists z,
      in_code z (find rwr) ge s.
Proof.
  intros. inv H.
  exists (Int.unsigned i).
  name (conj H5 H4) Hci.
  rewrite <- st_in_eq in Hci.
  app star_step_in_in' Hci.
Qed.

Lemma transf_step_same_block :
  forall st,
    (in_transf st \/ at_entry st) ->
    forall t st',
      step_bits (Genv.globalenv prog) st t st' ->
      in_same_block st st'.
Proof.
  intros. break_or. rename H1 into H.
  inv H. name (conj H6 H5) Hc.
  rewrite <- st_in_eq in Hc.
  app star_step_in_in' Hc. 
  destruct st'.
  app step_in_step_t' H0. break_and.
  inv H0. inv H17. rewrite E0_right in *.
  inv H11.

  destruct fd. name (forward_find rwr) ff.
  unfold only_forward_jumps in ff. repeat break_and.
  app find_instr_in H8.
  assert (Hfi : find_instr (Int.unsigned i0) fn_code = Some x).
  simpl in H22.
  rewrite H22. rewrite H15.
  rewrite find_instr_append_head by omega. simpl. reflexivity.
  
  app step_PC_same_block H7. break_and.
  econstructor; eauto.

  unfold transf_program in TRANSF.
  repeat (break_match_hyp; try congruence); auto.
  
  unfold no_trace_code in H9.
  apply no_trace_not_builtin. eapply H9; eauto.


  app at_entry_at_code H1.
  inv H1.
  destruct st'.
  destruct fd. unfold fundef in *.
  assert (Hfi : exists x, find_instr (Int.unsigned i) fn_code = Some x).
  rewrite H4. simpl in H7. rewrite H7. rewrite find_instr_append_head by omega.
  destruct (find rwr) eqn:?. app find_nonempty Heqc. inv Heqc. exists i0. reflexivity.
  break_exists. name H1 Hfi.
  rewrite H4 in Hfi. simpl in H7. rewrite H7 in Hfi.
  rewrite find_instr_append_head in Hfi by omega.
  rewrite find_instr_append_tail with (c := nil) in Hfi by omega.
  rewrite app_nil_r in Hfi.
  app step_PC_same_block H0.
  break_and. econstructor; eauto.


  unfold transf_program in TRANSF.
  repeat (break_match_hyp; try congruence); auto.
  
  
  name (forward_find rwr) ff.
  unfold only_forward_jumps in ff. repeat break_and.
  unfold no_calls in H9. eapply H9; eauto.
  
  name (forward_find rwr) ff.
  unfold only_forward_jumps in ff. repeat break_and.
  unfold no_trace_code in H10.
  eapply no_trace_not_builtin. eapply H10; eauto.
Qed.  


Lemma transf_idx_end_correct :
  forall s i j,
    in_transf s ->
    transf_index s i j ->
    transf_idx_end s = j.
Proof.
  intros. unfold transf_index in H0.
  unfold transf_idx_end.
  inv H.
  
  specialize (H0 rsl' m' md' eq_refl).
  assert (at_entry (State_bits rsl m md)).
  econstructor; eauto.
  app transf_step_same_block H4.
  name (conj H6 H5) Hstin.
  rewrite <- st_in_eq in Hstin.
  app star_step_in_in Hstin.
  app star_step_in_in' H8.  
  inv Hstin. inv H8.
  inv H13. inv H11.
  app star_step_in_same_block H6.

  subst b0. inv H4.
  find_inversion. find_inversion.
  repeat unify_PC. repeat unify_psur.
  repeat unify_find_funct_ptr.

  repeat collapse_match.
  destruct fd.

  simpl in *.
  
  inv H. unify_PC. unify_psur.
  eapply transf_range_unique in H3; try apply H24.
  break_and. clear H.
  subst j0.
  name H24 Htransf_range.
  inv H24.
  break_and. unfold transf_code in *.
  unfold ge in *.
  
  unify_find_funct_ptr.
  rewrite H1.
  remember (c0 ++ find rwr ++ c1) as c.
  assert (c <> c4 ++ repl rwr ++ c5).
  apply split_pat_spec in H1. rewrite H1.
  apply list_neq. apply (not_same rwr).
  repeat break_match_hyp; try congruence.
  inv H1. rewrite Heqb.

  
  app H0 H17.
  eapply transf_range_unique in H17; try apply Htransf_range.
  break_and. subst.
  rewrite zlen_app. reflexivity.
Qed.

Lemma transf_index_unique :
  forall t s1 s2,
    step_bits (Genv.globalenv prog) s1 t s2 ->
    in_transf s1 ->
    in_transf s2 ->
    forall a b c d,
      transf_index s1 a b ->
      transf_index s2 c d ->
      (a = c /\ b = d).
Proof.
  intros. name H0 Hin_transf1. name H1 Hin_transf2.
  app transf_step_same_block H. inv H.
  unfold transf_index in *.
  specialize (H3 _ _ _ eq_refl _ _ _ H8 H10).
  specialize (H2 _ _ _ eq_refl _ _ _ H7 H9).
  eapply transf_range_unique in H3; try apply H2.
  break_and. split; congruence.
Qed.


Lemma in_transf_index :
  forall s,
    in_transf s ->
    exists i, transf_index s i (i + zlen (find rwr)).
Proof.
  intros. inv H. unfold transf_index.
  inv H4. inv H6. exists (zlen c0).
  intros. find_inversion.
  assert (at_entry (State_bits rsl m md)).
  econstructor; eauto.
  app transf_step_same_block H3. inv H3.
  find_inversion. find_inversion.
  repeat unify_PC. repeat unify_psur.
  app star_step_in_same_block H5.
  subst b1.
  rewrite <- H4 in *.
  inv H2. econstructor; eauto; try congruence.
  rewrite zlen_app. omega.
Qed.

Lemma transf_index_gen :
  forall rs m b i j k md,
    rs PC = Values.Vptr b i ->
    transf_range b j k ->
    transf_index (State_bits rs m md) j (j + zlen (find rwr)).
Proof.
  intros. inv H0.
  econstructor; eauto. inv H0.
  rewrite H3 in H. inv H.
  eauto. rewrite zlen_app. reflexivity.
  Grab Existential Variables.
  econstructor; eauto.
  exact nil. exact None.
  econstructor; eauto.
  exact false. exact false.
Qed.

Lemma no_trace_entry_step :
  forall st : state_bits,
    at_entry st ->
    forall (st' : state_bits) (t : trace),
      step_bits (Genv.globalenv prog) st t st' -> t = E0.
Proof.
  intros.
  app at_entry_at_code H.
  eapply no_trace_step_at; eauto.
  apply (no_trace_find rwr).
Qed.

End PRESERVATION.
