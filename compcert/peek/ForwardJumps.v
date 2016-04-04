Require Import Coqlib.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Asm.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Axioms.

Require Import PeekLib.
Require Import PeekTactics.
Require Import PregTactics.
Require Import SplitLib.
Require Import StepLib.
Require Import StepIn.
Require Import AsmCallingConv.
Require Import StepEquiv.
Require Import FindInstrLib.
Require Import SameBlockLib.
Require Import ProgPropDec.
Require Import MemoryAxioms.
Require Import AsmBits.
Require Import ProgPropDec.
Require Import Zlen.

Definition measure_fun (z : Z) (st : state_bits) : nat :=
  match st with
    | State_bits rs m md =>
      match rs PC with
        | Values.Vint bits =>
          match psur md bits with
            | Some (b,i) => nat_of_Z (z - Int.unsigned i)
            | None => O
          end
        | _ => O
      end
  end.

Lemma nat_of_Z_lt :
  forall z z',
    z >= 0 -> z' >= 0 ->
    z < z' ->
    (nat_of_Z z < nat_of_Z z')%nat.
Proof.
  intros. unfold nat_of_Z.
  apply Z2Nat.inj_lt; omega.
Qed.

Lemma instr_class :
  forall i,
    straightline i \/ (exists l, labeled_jump i l) \/ is_call_return i \/ trace_internal i.
Proof.
  intros.
  destruct i; 
  try solve [left; unfold straightline; exact I];
  try solve [right; left; unfold labeled_jump; eauto];
  try solve [right; unfold is_call_return; auto].  
  destruct tbl. left. simpl. reflexivity.
  right. left. unfold labeled_jump. simpl. eauto.
  right. right. right. simpl. exact I.
  right. right. right. simpl. exact I.
Qed.  

Lemma in_code_at_code :
  forall c z rs m ge md,
    in_code z c ge (State_bits rs m md) ->
    exists z' i,
      at_code z' (i :: nil) 0 ge (State_bits rs m md) /\ In i c.
Proof.
  induction c; intros.
  inv H. inv H1. simpl.
  unfold zlen in *. simpl in *.
  omega.
  inv H. inv H1.
  assert (ofs = 1 \/ ofs > 1) by omega.
  break_or. destruct c.
  rewrite zlen_cons in H11. simpl in H11. omega.
  exists (Int.unsigned i). exists i0.
  split; try solve [simpl; right; left; reflexivity].
  rewrite H6. replace (zlen c1 + 1) with (zlen (c1 ++ a :: nil)).
  econstructor; eauto.
  rewrite zlen_app. rewrite zlen_cons. simpl. omega.
  rewrite zlen_cons. simpl. omega.
  simpl. rewrite app_ass. simpl.
  rewrite H13. reflexivity.
  rewrite zlen_app. rewrite zlen_cons. simpl. reflexivity.
  assert (in_code (zlen (c1 ++ a :: nil)) c ge (State_bits rs m md)).
  econstructor. instantiate (1 := ofs - 1). omega.
  econstructor; eauto.
  rewrite H6. rewrite zlen_app.
  rewrite zlen_cons. simpl. omega.
  rewrite zlen_cons in H11. omega.
  rewrite H13. rewrite app_ass. simpl. reflexivity.
  app IHc H. exists x. exists x0. break_and.
  split; eauto. simpl. right. eauto.
Qed.
  
Lemma step_in_step_t' :
  forall z c ge st t st',
    in_code z c ge st ->
    step_bits ge st t st' ->
    exists i,
      step_t (i :: nil) ge st t st' /\ In i c.
Proof.
  intros.
  destruct st.
  app in_code_at_code H. exists x0. break_and.
  split; auto. replace t with (t ** E0) by (apply E0_right).
  econstructor; eauto. econstructor.
Qed.

Lemma step_in_step_t :
  forall z c ge st t st',
    step_in z c ge st t st' ->
    exists i,
      step_t (i :: nil) ge st t st' /\ In i c.
Proof.
  intros. inv H.
  app step_in_step_t' H2.
Qed.


Lemma step_at_step_t :
  forall z c ofs ge st t st',
    at_code z c ofs ge st ->
    step_bits ge st t st' ->
    exists i, step_t (i :: nil) ge st t st' /\ In i c.
Proof.
  intros.
  destruct (zeq ofs 0). subst ofs.
  destruct c. inv H. unfold zlen in H4. simpl in H4. omega.
  exists i. split; try solve [simpl; left; reflexivity].
  replace t with (t ** E0) by apply E0_right.
  econstructor; try solve [econstructor]; eauto.
  eapply at_code_cons; eauto.
  assert (in_code z c ge st).
  econstructor; eauto.
  inv H. omega.
  app step_in_step_t' H0.
Qed.


Lemma find_instr_in :
  forall c i,
    In i c <-> (exists z, find_instr z c = Some i).
Proof.
  induction c; split; intros.
  simpl in H. inv H.
  break_exists. simpl in H. inv H.
  simpl in H. break_or. exists 0. simpl. reflexivity.
  rewrite IHc in H0. break_exists. simpl. exists (x+1).
  apex in_range_find_instr H. break_match; try omega.
  replace (x+1-1) with x by omega. eauto.
  break_exists. simpl in H. break_match_hyp.
  inv H. simpl. left. reflexivity.
  apex IHc H. simpl. right. eauto.
Qed.

Lemma no_trace_trace :
  forall x,
    trace_internal x ->
    ~ no_trace x.
Proof.
  intros; destruct x; simpl; eauto.
Qed.

Lemma at_code_straightline_end :
  forall z x p st t st',
    no_PC_overflow_prog p ->
    straightline x ->
    at_code z (x :: nil) 0 (Genv.globalenv p) st ->
    step_bits (Genv.globalenv p) st t st' ->
    at_code_end z (x :: nil) (Genv.globalenv p) st'.
Proof.
  intros. inv H1.
  invs.
  unify_psur. unify_find_funct_ptr.
  name H16 Hfind_instr.
  rewrite H8 in H16. rewrite H5 in H16.
  rewrite find_instr_append_head in H16 by omega.
  simpl in H16. inv H16.
  app straightline_exec H17. break_and.
  Focus 2. app weak_valid_pointer_sur H12.
  break_and. eauto.
  econstructor; eauto.

  (* New stuff *)
  app md_extends_step H2.
  assert (Hadd_i : Int.unsigned (Int.add i Int.one) = Int.unsigned i + 1). {
    unfold Int.add.
    erewrite unsigned_repr_PC; eauto.
    left. rewrite Int.unsigned_one.
    replace (Int.unsigned i + 1 - 1) with (Int.unsigned i) by omega.
    eauto.
  } idtac.
  erewrite weak_valid_pointer_sur in H12; eauto.
  break_and.
  eapply pinj_add in H11.
  instantiate (1 := Int.one) in H11.
  eapply pinj_extends in H11; eauto.
  unify_pinj.
  instantiate (1 := Int.add i Int.one).
  app step_match_metadata H10.
  erewrite weak_valid_pointer_sur; eauto.
  split. eassumption.
  app step_gp H11.
  break_and.
  app global_perms_valid_globals H16.
  eapply Mem.weak_valid_pointer_spec. right.
  replace (Int.unsigned (Int.add i Int.one) - 1) with (Int.unsigned i) by omega.
  apply H16.
  unfold is_global. left.
  unfold in_code_range.
  unfold fundef in *.
  collapse_match.
  apex in_range_find_instr Hfind_instr.
  omega.
  (* end new stuff *)
  
  rewrite zlen_cons. simpl.
  replace (zlen c0 + 0) with (zlen c0) in H5 by omega.
  rewrite <- H5.
  apply add_one_no_overflow.
  unfold no_PC_overflow_prog in H.
  assert (no_PC_overflow (fn_code f)).
  apply H. unfold code_of_prog. app Genv.find_funct_ptr_inversion H7.
  destruct f. eauto.
  unfold no_PC_overflow in H10. eapply H10; eauto.
  
  unify_psur. unify_find_funct_ptr.
  rewrite H8 in H14. rewrite H5 in H14.
  rewrite find_instr_append_head in H14 by omega.
  simpl in H14. inv H14.
  simpl in H0. inv H0.

  unify_psur. unify_find_funct_ptr.
  rewrite H8 in H16. rewrite H5 in H16.
  rewrite find_instr_append_head in H16 by omega.
  simpl in H16. inv H16.
  simpl in H0. inv H0.

  unify_psur. unify_find_funct_ptr.

Qed.

Lemma at_code_label_end :
  forall z x p st t st',
    no_PC_overflow_prog p ->
    (exists l, x = Plabel l) ->
    at_code z (x :: nil) 0 (Genv.globalenv p) st ->
    step_bits (Genv.globalenv p) st t st' ->
    at_code_end z (x :: nil) (Genv.globalenv p) st'.
Proof.
  intros. inv H1.
  invs.
  unify_psur. unify_find_funct_ptr.
  name H16 Hfind_instr.
  rewrite H8 in H16. rewrite H5 in H16.
  rewrite find_instr_append_head in H16 by omega.
  simpl in H16. inv H16.
  app label_exec H17. break_and.
  econstructor; eauto.


  (* New stuff *)
  NP _app md_extends_step step_bits.
  assert (Hadd_i : Int.unsigned (Int.add i Int.one) = Int.unsigned i + 1). {
    unfold Int.add.
    erewrite unsigned_repr_PC; eauto.
    left. rewrite Int.unsigned_one.
    replace (Int.unsigned i + 1 - 1) with (Int.unsigned i) by omega.
    eauto.
  } idtac.
  erewrite weak_valid_pointer_sur in H12; eauto.
  break_and.
  eapply pinj_add in H11.
  instantiate (1 := Int.one) in H11.
  instantiate (1 := i) in H9.
  eapply pinj_extends in H11; eauto.
  unify_pinj.
  instantiate (1 := Int.add i Int.one).
  app step_match_metadata H10.
  erewrite weak_valid_pointer_sur; eauto.
  split. eassumption.
  NP _app step_gp step_bits.
  break_and.
  app global_perms_valid_globals H15.
  eapply Mem.weak_valid_pointer_spec. right.
  rewrite Hadd_i. replace (Int.unsigned i + 1 - 1) with (Int.unsigned i) by omega.
  apply H15.
  unfold is_global. left.
  unfold in_code_range.
  unfold fundef in *.
  collapse_match.
  apex in_range_find_instr Hfind_instr. omega.
  (* end new stuff *)
  
  rewrite zlen_cons. simpl.
  replace (zlen c0 + 0) with (zlen c0) in H5 by omega.
  rewrite <- H5.
  apply add_one_no_overflow.
  unfold no_PC_overflow_prog in H.
  assert (no_PC_overflow (fn_code f)).
  apply H. unfold code_of_prog. app Genv.find_funct_ptr_inversion H7.
  destruct f. eauto.
  unfold no_PC_overflow in H10. eapply H10; eauto.
  eapply weak_valid_pointer_sur in H12. break_and. eauto.
  invs; eauto. 
  
  unify_psur. unify_find_funct_ptr.
  rewrite H8 in H14. rewrite H5 in H14.
  rewrite find_instr_append_head in H14 by omega.
  simpl in H14. inv H14.
  simpl in H0. inv H0. inv H1.

  unify_psur. unify_find_funct_ptr.
  rewrite H8 in H16. rewrite H5 in H16.
  rewrite find_instr_append_head in H16 by omega.
  simpl in H16. inv H16.
  simpl in H0. inv H0. inv H1.

  unify_psur. unify_find_funct_ptr.
Qed.

Lemma step_t_to_at_code_0 :
  forall i ge st t st',
    step_t (i :: nil) ge st t st' ->        
    exists z',
      at_code z' (i :: nil) 0 ge st.
Proof.
  intros. inv H. eauto.
Qed.

Lemma Z_add_lt :
  forall (a b c : Z),
    a < b ->
    c + a < c + b.
Proof.
  intros. omega.
Qed.

Lemma step_t_labeled_jump_no_trace :
  forall i ge st t st',
    step_t (i :: nil) ge st t st' ->
    (exists l : label, labeled_jump i l) ->
    t = E0.
Proof.
  intros. break_exists.
  inv H. inv H9. inv H3.
  invs.
  reflexivity. 
  unify_stuff. find_one_instr. inv H0.
  unify_stuff. find_one_instr. inv H0.
  unify_stuff. unify_find_funct_ptr.
Qed.


Lemma is_label_instr_labeled_jump:
  forall i l l',
    is_label_instr i l ->
    labeled_jump i l' ->
    labeled_jump i l.
Proof.
  intros.
  destruct i; simpl in *; tauto.
Qed.

Lemma measure_decr_fw_j :
  forall c,
    only_forward_jumps c ->
    forall z prog st t st' ofs ofs',
      (no_PC_overflow_prog prog /\ not_after_label_in_code (Genv.globalenv prog) st z c) ->
      step_bits (Genv.globalenv prog) st t st' ->
      at_code z c ofs (Genv.globalenv prog) st ->
      at_code z c ofs' (Genv.globalenv prog) st' ->
      (* step_in z c (Genv.globalenv prog) st t st' -> *)
      lt (measure_fun (z + zlen c) st') (measure_fun (z + zlen c) st).
Proof.
  
  intros. break_and.
  unfold only_forward_jumps in *. repeat break_and.
  unfold no_calls in *. unfold no_trace_code in *.
  unfold only_forward_jumps_lab in *.
  app step_at_step_t H1. rename x into instr.
  break_and.  
  app find_instr_in H8.
  clear H8. remember True as H8. clear HeqH8.
  name (instr_class instr) Hic.
  repeat break_or.  
  - (* straightline case *)
    app step_t_to_at_code_0 H1.
    app at_code_straightline_end H7.
    destruct st as (rs, m). destruct st' as (rs', m').
    inv H1.
    inv H7.    
    simpl.
    do 7 find_rewrite.
    inv H2.
    inv H3.
    unify_stuff.
    rewrite zlen_cons.
    simpl.
    eapply Z2Nat.inj_lt.
    omega. omega. omega.  
  -   clear H8.      
      destruct st as (rs, m).
      destruct st' as (rs', m').             
      assert (t = E0) by (app step_t_labeled_jump_no_trace H11).
      subst t.            
      copy step_t_labeled_jump.      
      copy H1.
      inv H10. inv H20. inv H15.
      app H8 H11. clear H8.
      
      break_or.
      + (*jump-ish*)
        destruct H8 as (ilbl).
        destruct H8 as (l').
        repeat break_and.
        
        repeat P inv step_t.
        inv H2.
        inv H3.
        inv H23.
        unify_stuff.
        name H11 Hfind_instr.        
        find_one_instr.      
        
        simpl. 
        P rwrt_n (rs PC).
        P rwrt_n (rs' PC).
        P rwrt_n (psur a bits).
        rename bits1 into bits0.
        P rwrt_n (psur a0 bits0).

        simpl_exec.
        repeat break_match_hyp; try state_inv.
        clear H18. clear H28.
        
        P preg_simpl_hyp (Vint bits0).
        P inv (Vint bits0).

        unfold goto_label_bits in *.
        repeat break_match_hyp; try congruence.
        st_inv.
        preg_simpl_hyp H3. inv H3.

        eapply Z2Nat.inj_lt. omega. omega.
        replace (zlen c5 + zlen c - Int.unsigned i1) with
                ((zlen c5 + zlen c) + (- Int.unsigned i1)) by omega.
        replace (zlen c5 + zlen c - Int.unsigned i2) with
        ((zlen c5 + zlen c) + (- Int.unsigned i2)) by omega.
        eapply Z_add_lt.

        cut (Int.unsigned i2 < Int.unsigned i1); try omega.
        rewrite H29. rewrite H32.
        rewrite H1.
        eapply Z_add_lt.

        app label_pos_find_instr Heqo.
        rewrite H36 in H11.
        rewrite H29 in H11.
        rewrite find_instr_append_head in H11 by omega.
        erewrite find_instr_append_tail with (c := nil) in H11 by omega.
        rewrite app_nil_r in H11.

        unfold not_after_label_in_code in *.

        app step_md H7.
        break_and.
        assert (Mem.weak_valid_pointer m' b2 (Int.unsigned (Int.repr (z))) = true).
        eapply Mem.weak_valid_pointer_spec. right.
        erewrite unsigned_repr_PC; eauto.
        erewrite <- (unsigned_repr_PC _ _ (z - 1)); eauto.
        app step_gp H3.
        break_and.
        eapply global_perms_valid_globals in H20.
        unfold valid_globals in H20.
        apply H20.
        unfold is_global. left.
        unfold in_code_range. unfold fundef in *.
        collapse_match. apex in_range_find_instr Heqo.
        erewrite unsigned_repr_PC; eauto.
        omega.
        
        name (conj Heqo0 H18) Hpsur.
        erewrite <- weak_valid_pointer_sur in Hpsur.
        unify_psur.
        2: assumption.

        unify_find_funct_ptr.
        rename fd1 into f.
        destruct f.
        exploit H4.
        reflexivity. eauto. eauto. 
        eauto. eauto. eauto.
        intros.
        break_and.
        unfold ends_in_not_label_from_after_code in *.
        simpl in *. 
        clear H4.
        repeat P1 clr (0 <= 0).
        assert (zlen c1 = zlen c7) by omega.
        rewrite H26 in H47.
        Lemma cons_expand :
          forall {A} a (b : list A),
            a :: b = a :: nil ++ b.
          auto.
        Qed.
        rewrite (cons_expand ilbl c2) in H47.
        rewrite (cons_expand ilbl c8) in H47.
        copy @list_eq_middle_therefore_eq.
        specialize (H23 _ c1 (ilbl :: nil) c2 c7 c8).
        app H23 H47.
        clear H23. clear H24. break_and.
        subst.

        copy (@list_eq_middle_therefore_eq instruction).
        app H23 H36. break_and. subst. clear H23. clear H24.

        eapply is_label_instr_labeled_jump in H12; eauto.
        clear H10.

        assert (Int.unsigned (Int.repr z) = z). {
          erewrite unsigned_repr_PC; eauto.
        } idtac.

        rewrite H10 in *.
        rewrite H32 in Heqo.
        assert (ofs' = 0 \/ ofs' > 0) by omega.
        break_or.
        replace (zlen c3 + 0 - 1) with (zlen c3 - 1) in Heqo by omega.
        apex in_range_find_instr Heqo. break_and. 
        rewrite find_instr_append_tail with (c := nil) in Heqo by omega.
        rewrite app_nil_r in Heqo.
        app H20 Heqo. inv_false.
        unfold label_in_code.
        eexists; split; eassumption.
        replace (zlen c3 + ofs' - 1) with (zlen c3 + (ofs' - 1)) in Heqo by omega.
        rewrite find_instr_append_head in Heqo by omega.
        rewrite find_instr_append_tail with (c := nil) in Heqo by omega.
        rewrite app_nil_r in Heqo.

        exploit H6.
        2: eauto.
        eauto.
        eauto.
        intros. omega.

        
  (*       assert (zlen c5 = zlen c7) by omega. *)
  (*       rewrite H25 in H46. *)
  (*       copy @list_eq_middle_therefore_eq. *)
  (*       specialize (H8 _ c5 (ilbl :: nil) c6 c7 c8). *)
  (*       app H8 H46. *)
  (*       clear H8. *)
  (*       clear H13. *)
  (*       destruct H46. *)
  (*       subst c7. subst c8. *)
  (*       clear H2. *)
        
  (*       rewrite Hfh in Heqo. clear Hfh. *)
  (*       name find_instr_append_tail Hft. *)
  (*       rewrite (Hft c c2 nil) in Heqo. *)
  (*       rewrite app_nil_r in Heqo. *)
  (*       clear Hft.   *)
  (*       2: omega. *)
  (*       2: omega.         *)
  (*       assert (labeled_jump ilbl l0). { *)
  (*         destruct ilbl; simpl; try inv H12; try tauto.           *)
  (*       } *)
  (*       clear H10. clear x0. *)
  (*       rename H2 into Hjmp. *)
  (*       app H6 Hjmp. *)
  (*       clear H2. *)
  (*       Focus 2. *)
  (*       instantiate (1 := ofs). *)
  (*       rewrite <- find_instr_append_head with (a := c1) by omega. *)
  (*       P rwrtb_n (zlen c1 + ofs). *)
  (*       clear H37. clear H2. *)
  (*       P rwrt_n (zlen c5 + 0). *)
  (*       replace (c1 ++ c) with ((c1 ++ c) ++ nil). *)
  (*       Focus 2. *)
  (*       rewrite app_nil_r. reflexivity.         *)
  (*       rewrite find_instr_append_tail with (c := c2).         *)
  (*       Focus 2. *)
  (*       rewrite zlen_app. *)
  (*       copy (zlen_nonneg _ c). *)
  (*       copy (zlen_nonneg _ c1). *)
  (*       copy (zlen_nonneg _ c5). *)
  (*       omega. *)
  (*       rewrite app_ass. *)
  (*       P rwrtb_n (c1 ++ c ++ c2).    *)
  (*       P rwrt_n (c5 ++ (ilbl :: nil) ++ c6). *)
  (*       rewrite find_instr_append_head by omega. *)
  (*       simpl. *)
  (*       reflexivity. *)
        
  (*       omega. *)

      + (*straightline-ish*)
        inv H8.
        simpl.
        unfold nextinstr.
        repeat collapse_match. preg_simpl.
        simpl.

        inv H3. preg_simpl_hyp H13.
        find_rewrite. simpl in H13. inv H13.
        collapse_match.

        app step_md H18.
        app step_gp H7.
        repeat break_and.
        eapply nat_of_Z_lt; try omega.
        rewrite H19.
        repeat unify_find_funct_ptr.
        inv H2. unify_stuff. omega.

        
        cut (Int.unsigned i0 > Int.unsigned i); intros; try omega.

        assert (in_code_range (Genv.globalenv prog) b i). {
          unfold in_code_range.
          unfold fundef in *.
          rewrite H25.
          
          rewrite H26. repeat rewrite zlen_app. rewrite zlen_cons.
          replace (zlen (@nil instruction)) with 0 by (simpl; auto).
          rewrite H19. name (zlen_nonneg _ c1) zlnc1.
          name (zlen_nonneg _ c2) zlnc2.
          omega.
          
        } idtac.
        
        
        app psur_add_one H17; try solve [econstructor]. rewrite H17 in H15.
        inv H15.


        unfold Int.add.
        rewrite Int.unsigned_one.
        erewrite unsigned_repr_PC; eauto. omega.
        left. rewrite H26.
        replace (Int.unsigned i + 1 - 1) with (zlen c1 + 0) by omega.
        
        rewrite find_instr_append_head by omega.
        simpl. reflexivity.

        eapply in_range_PC.
        eassumption. unfold ge.
        apply H25. rewrite H26.
        rewrite H19. rewrite find_instr_append_head by omega.
        simpl. reflexivity.
        
  - exploit find_instr_in.
    intros.
    destruct H11.
    app H11 H9.
    clear H12.
    app H H10.
    tauto.
  - copy no_trace_trace.
    exploit find_instr_in.
    intros.
    destruct H12.
    clear H13.
    app H12 H9.
    app H11 H10.
    exploit H5.
    eauto.
    intros.
          destruct instr; simpl in *; tauto.

Qed.

Lemma z_nat_lt :
  forall z z',
    z >= 0 -> z' >= 0 ->
    (nat_of_Z z < nat_of_Z z')%nat ->
    z < z'.
Proof.
  intros.
  unfold nat_of_Z in H1.
  apply Z2Nat.inj_lt; try auto; omega.
Qed.

(* Lemma only_forward_in : *)
(*   forall c, *)
(*     only_forward_jumps c -> *)
(*     forall z prog rs m t rs' m', *)
(*       (no_PC_overflow_prog prog /\ *)
(*        not_after_label (Genv.globalenv prog) (State rs m) z c) -> *)
(*       in_code z c (Genv.globalenv prog) (State rs m) -> *)
(*       step_bits (Genv.globalenv prog) (State rs m) t (State rs' m') -> *)
(*       forall b i i' bits bits', *)
(*         rs PC = Values.Vint bits -> *)
(*         rs' PC = Values.Vint bits' -> *)
(*         psur bits = (b,i) -> *)
(*         psur bits' = (b,i') -> *)
(*         Int.unsigned i < Int.unsigned i'. *)
(* Proof. *)
(*   intros.  *)

(* TODO: what is needed here? *)
(* Used only for creating rewrites. Look at later *)

Lemma only_forward_PC_incr :
    forall c,
    only_forward_jumps c ->
    forall z prog rs m t rs' m' ofs ofs' md md',
      (no_PC_overflow_prog prog /\
       not_after_label_in_code (Genv.globalenv prog) (State_bits rs m md) z c) ->
      step_bits (Genv.globalenv prog) (State_bits rs m md) t (State_bits rs' m' md') ->
      at_code z c ofs (Genv.globalenv prog) (State_bits rs m md) ->
      at_code z c ofs' (Genv.globalenv prog) (State_bits rs' m' md') ->
      forall b i i' bits bits',
        rs PC = Values.Vint bits ->
        rs' PC = Values.Vint bits' ->
        psur md bits = Some (b,i) ->
        psur md' bits' = Some (b,i') ->
        Int.unsigned i < Int.unsigned i'.
Proof.
  intros. 
  app measure_decr_fw_j H1.  
  unfold measure_fun in H1.
  rewrite H4 in H1. 
  rewrite H5 in H1.
  rewrite H6 in H1. 
  rewrite H7 in H1.
  
  (* name (zlen_nonneg _ c1) zlnc1. *)
  name (zlen_nonneg _ c) zlnc.
  inv H2.
  inv H3.
  unify_stuff.
  app z_nat_lt H1; try omega.
Qed.

Lemma no_trace_step_at :
  forall z c ge st t st' ofs,
    no_trace_code c ->
    at_code z c ofs ge st ->
    step_bits ge st t st' ->
    t = E0.
Proof.
  intros. 

  unfold no_trace_code in H.
  inv H0. inv H3.
  invs; eauto;
  try unify_PC;
  try unify_psur;
  try unify_find_funct_ptr.


  peel_code. app H H13. simpl in *. inv_false.
  peel_code. app H H15. simpl in *. inv_false.
Qed.

  
Lemma no_trace_step_in :
  forall z c ge st t st',
    no_trace_code c ->
    in_code z c ge st ->
    step_bits ge st t st' ->
    t = E0.
Proof.
  intros. 
  inv H0. app no_trace_step_at H3.
Qed.

Lemma no_trace_star_step_in :
  forall c,
    no_trace_code c ->
    forall z ge st t st',
      star (step_in z c) ge st t st' ->
      t = E0.
Proof.
  intros. induction H0. reflexivity.
  inv H0.
  app no_trace_step_in H5. subst t1. reflexivity.
Qed.

Lemma no_trace_step_through :
  forall z c ge st t st',
    no_trace_code c ->
    at_code z c 0 ge st -> 
    step_through z c ge st t st' ->
    t = E0.
Proof.
  intros. inv H1.
  app no_trace_step_at H3.

  name H5 Hstar.
  rewrite st_in_eq in H5. break_and.
  app no_trace_step_at H4. subst t1.
  app no_trace_star_step_in H1. subst t2.
  app star_step_in_in' Hstar.
  app no_trace_step_in Hstar.
Qed.  

Lemma only_forward_jumps_same_block :
  forall rs m t rs' m' z c bits b i bits' b' i' p ofs md md',
    only_forward_jumps c ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,i) ->
    step_bits (Genv.globalenv p) (State_bits rs m md) t (State_bits rs' m' md') ->
    at_code z c ofs (Genv.globalenv p) (State_bits rs m md) ->
    rs' PC = Values.Vint bits' ->
    psur md' bits' = Some (b',i') ->
    no_PC_overflow_prog p ->    
    b' = b.
Proof.
  intros. unfold only_forward_jumps in H.
  repeat break_and.
  inv H3. unify_PC. unify_psur.
  unfold no_calls in *.
  unfold no_trace_code in *.
  invs; try unify_PC; try unify_psur; try unify_find_funct_ptr;
  match goal with
    | [ H : fn_code _ = _, H2 : find_instr ?X _ = _, H3 : ?X = _ |- _ ] =>
      rewrite H in H2; rewrite H3 in H2; 
      rewrite find_instr_append_head in H2 by omega;
      rewrite find_instr_append_tail with (c := nil) in H2 by omega;
      rewrite app_nil_r in H2;
      name H2 Hfind_instr;
      name H2 Hfi
  end;
  app H Hfind_instr;
  app H7 Hfi.

  app step_md H2.
  NP _app step_gp step_bits.

  repeat break_and.

  assert (straightline i0 \/ (exists l, labeled_jump i0 l)).  {
  name (instr_class i0) Hclass.
  repeat break_or; try congruence;
  eauto.
  app H7 H3.
  NP _app no_trace_trace trace_internal. congruence.
  } idtac.

  destruct f.

  NP _app step_PC_same_block step_bits.
  break_and. repeat unify_PC. repeat unify_psur. reflexivity.
  simpl in *.
  match goal with
    | [ H : ?X = _ , H2 : ?Y = _ |- find_instr ?X ?Y = _ ] => rewrite H; rewrite H2
  end.
  rewrite find_instr_append_head by omega.
  rewrite find_instr_append_tail with (c := nil) by omega.
  rewrite app_nil_r. assumption.
  intro. destruct i0; repeat break_or; simpl in *; try inv_false.
  
  unfold is_call_return in *; unfold no_trace in *; inv_false.
  unfold is_call_return in *; unfold no_trace in *; inv_false.
Qed.

Lemma only_forward_jumps_same_block_star :
  forall p st st' z c t,
    no_PC_overflow_prog p ->
    star (step_in z c) (Genv.globalenv p) st t st' ->
    forall rs m rs' m' md md',
      st = State_bits rs m md ->
      st' = State_bits rs' m' md' ->
      only_forward_jumps c ->
      forall bits b i bits' b' i',
        rs PC = Values.Vint bits ->
        psur md bits = Some (b,i) ->
        rs' PC = Values.Vint bits' ->
        psur md' bits' = Some (b',i') ->
        b' = b.
Proof.
  induction 2; intros.
  * subst. find_inversion. unify_PC.
    unify_psur. reflexivity.
  * destruct s1. destruct s2. destruct s3.
    repeat match goal with
               | [ H : State _ _ = State _ _ |- _ ] => inv H
           end.
    
    specialize (IHstar _ _ _ _ _ _  eq_refl eq_refl H5).
    name H Hstep_in.
    inv H0. inv H3. inv H11. inv H4.
    inv H2.
    exploit IHstar; try eauto.
    intros. subst.
    inv H10.
    app only_forward_jumps_same_block H12.
Qed.

