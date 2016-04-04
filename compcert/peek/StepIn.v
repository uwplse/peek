Require Import Coqlib.
Require Import AST.
Require Import Globalenvs.
Require Import Integers.
Require Import Smallstep.
Require Import Events.
Require Import Asm.
Require Import ProofIrrelevance.
Require Import Values.

Require Import PeekLib.
Require Import PeekTactics.
Require Import PregTactics.
Require Import FindInstrLib.
Require Import SplitLib.
Require Import StepLib.
Require Import SameBlockLib.
Require Import AsmCallingConv.
Require Import AsmBits.
Require Import MemoryAxioms.
Require Import ProgPropDec.

Require Import NoPtr.
Require Import Zlen.
Require Import GlobalPerms.



(* Maybe have 2 definitions *)
(* One like current step_in/step_through *)
(* where list is static code *)
(* Other, list index is dynamic instruction trace *)
(* prove lemmas about correspondence *)
(* peephole facts will be in terms of static code *)
(* static <-> dyn easy when straightline *)
(* Try this out and see *)


(* code c lives at offset z in entire code for function we're currently at i, within the code *)
Inductive at_code :  Z -> code -> Z -> genv -> state_bits -> Prop :=
  | at_c :
      forall rs m b i c c0 c1 fd bits ofs ge t,
        rs PC = Vint bits ->
        psur t bits = Some (b,i) ->
        Int.unsigned i = (zlen c0) + ofs ->
        0 <= ofs < zlen c ->
        Genv.find_funct_ptr ge b = Some (Internal fd) ->
        fn_code fd = c0 ++ c ++ c1 ->
        at_code (zlen c0) c ofs ge (State_bits rs m t).

Inductive at_code_end : Z -> code -> genv -> state_bits -> Prop :=
| at_end :
    forall rs m b i c c0 c1 fd ge bits t,
      rs PC = Vint bits ->
      psur t bits = Some (b,i) ->
      Int.unsigned i = (zlen c0) + (zlen c) ->
      Genv.find_funct_ptr ge b = Some (Internal fd) ->
      fn_code fd = c0 ++ c ++ c1 ->
      at_code_end (zlen c0) c ge (State_bits rs m t).

Inductive at_code_start : Z -> code -> genv -> state_bits -> Prop :=
| at_start :
    forall rs m b i c c0 c1 fd ge bits t,
      rs PC = Vint bits ->
      psur t bits = Some (b,i) ->
      Int.unsigned i = (zlen c0) ->
      Genv.find_funct_ptr ge b = Some (Internal fd) ->
      fn_code fd = c0 ++ c ++ c1 ->
      at_code_start (zlen c0) c ge (State_bits rs m t).

Inductive in_code : Z -> code -> genv -> state_bits -> Prop :=
| in_c :
    forall z c ge st ofs,
      ofs > 0 ->
      at_code z c ofs ge st ->
      in_code z c ge st.

Inductive star_step_in : Z -> code -> genv -> state_bits -> trace -> state_bits -> Prop :=
| st_st_refl :
    forall z c ge st,
      in_code z c ge st ->
      star_step_in z c ge st E0 st
| st_st_left :
    forall z c st st' st'' t t' ge,
      star_step_in z c ge st'' t st' ->
      in_code z c ge st ->
      step_bits ge st t' st'' ->
      star_step_in z c ge st (t' ** t) st'.

(* Two cases: 
    + one step through the entire region
    + step in, star step within, step to exit
*)
Inductive step_through : Z -> code -> genv -> state_bits -> trace -> state_bits -> Prop :=
| st_thru_single_step :
    forall z c ge st t st',
      at_code z c 0 ge st ->
      step_bits ge st t st' ->
      at_code_end z c ge st' ->
      step_through z c ge st t st'
| st_thru_mult_step :
    forall z c ge stA stB stC stD t1 t2 t3,
      at_code z c 0 ge stA ->
      at_code_end z c ge stD ->
      step_bits ge stA t1 stB ->
      star_step_in z c ge stB t2 stC ->
      step_bits ge stC t3 stD ->
      step_through z c ge stA (t1 ** t2 ** t3) stD.
      
Inductive step_t : code -> genv -> state_bits -> trace -> state_bits -> Prop :=
| st_t_refl :
    forall ge st,
      step_t nil ge st E0 st
| st_t_left :
    forall st st' st'' ge i c t1 t2 z,
      at_code z (i :: nil) 0 ge st ->
      step_bits ge st t1 st' ->
      step_t c ge st' t2 st'' ->
      step_t (i :: c) ge st (t1 ** t2) st''.

Lemma at_code_not_nil :
  forall z c n ge st,
    at_code z c n ge st ->
    c <> nil.
Proof.
  intros. inversion H.
  subst. destruct c. unfold zlen in H3. simpl in H3.
  omega.
  congruence.
Qed.

Inductive step_in : Z -> code -> genv -> state_bits -> trace -> state_bits -> Prop :=
| st_in :
    forall ge z c st t st',
      in_code z c ge st ->
      in_code z c ge st' ->
      step_bits ge st t st' ->
      step_in z c ge st t st'.


Lemma st_in_eq :
  forall z c ge st t st',
    star_step_in z c ge st t st' <->
    (star (step_in z c) ge st t st' /\ in_code z c ge st).
Proof.
  split. induction 1; intros.
  * split; eauto. econstructor; eauto.
  * break_and. split; eauto.
    econstructor; eauto. econstructor; eauto.
  * intros. break_and. induction H.
  - econstructor; eauto.
  - subst. econstructor; eauto. apply IHstar.
    inv H; eauto. inv H; eauto.
Qed.

Definition trace_internal (i : instruction) : Prop :=
  match i with
    | Pbuiltin _ _ _ => True
    | Pannot _ _ => True
    | _ => False
  end.

Definition straightline (i : instruction) : Prop :=
  match i with
    | Pjmp_r _ _ => False
    | Pjmp_l _ => False
    | Pjmp_s _ _ => False
    | Pjcc _ _ => False
    | Pjcc2 _ _ _ => False
    | Pcall_r _ _ => False
    | Pcall_s _ _ => False
    | Pjmptbl _ tbl => tbl = nil
    | Pbuiltin _ _ _ => False
    | Pannot _ _ => False
    | Pret _ => False
    | _ => True
  end.

Definition local_jump (i : instruction) : Prop :=
  match i with
    | Pjmp_l _ => True
    | Pjcc _ _ => True
    | Pjcc2 _ _ _ => True
    | Pjmptbl _ tbl => tbl <> nil
    | _ => False
  end.

Lemma list_destr_right :
  forall { A : Type } (l : list A),
    l = nil \/ (exists b e, l = b ++ e :: nil).
Proof.
  induction l; intros.
  left. reflexivity.
  destruct IHl. subst. right.
  exists nil. exists a. simpl. reflexivity.
  repeat break_exists. subst l.
  right.
  exists (a :: x). exists x0.
  simpl. reflexivity.
Qed.

Lemma at_code_head :
  forall z c1 c2 ofs ge cs,
    at_code z (c1 ++ c2) ofs ge cs ->
    ofs < zlen c1 ->
    at_code z c1 ofs ge cs.
Proof.
  intros. inv H.
  eapply at_c; eauto. omega.
  find_rewrite. rewrite app_ass. reflexivity.
Qed.

Lemma at_code_cons :
  forall z i c ge cs,
    at_code z (i :: c) 0 ge cs ->
    at_code z (i :: nil) 0 ge cs.
Proof.
  intros. eapply at_code_head.
  simpl. eassumption.
  unfold zlen. simpl. omega.
Qed.

Lemma straightline_exec :
  forall ge f i rs m rs' m' bits b ofs t t',
    rs PC = Vint bits ->
    exec_instr_bits ge t f i b rs m = Nxt rs' m' t' ->
    straightline i ->
    pinj t b ofs = Some bits ->
    exists bits',
      rs' PC = Vint bits' /\
      pinj t' b (Int.add ofs Int.one) = Some bits'.
Proof.
  intros.
  destruct i; simpl in H1; try subst tbl; try solve [simpl in H1; inv H1];
  simpl in *;
  simpl_exec;
  simpl in *;
  unfold exec_big_load_bits in *;
  unfold exec_big_store_bits in *;
  unfold exec_load_bits in *;
  unfold exec_store_bits in *;
  repeat break_match_hyp;
  try find_inversion;
  repeat state_inv;
  try solve [
  eexists; split; [preg_simpl; repeat break_match; preg_simpl; rewrite H;
                   simpl; eauto | apply pinj_add; eauto]].
  eexists; split.
  preg_simpl. rewrite H. simpl. eauto.
  eapply pinj_alloc. eapply pinj_add. eauto.
  eexists; split.
  preg_simpl. rewrite H. simpl. eauto.
  eapply pinj_free. eapply pinj_add. eauto.
Qed.  

Lemma label_exec :
  forall ge f i rs m rs' m' bits b ofs t t',
    rs PC = Vint bits ->
    exec_instr_bits ge t f i b rs m = Nxt rs' m' t' ->
    (exists l, i = Plabel l) ->
    pinj t b ofs = Some bits ->
    exists bits',
      rs' PC = Vint bits' /\
      pinj t' b (Int.add ofs Int.one) = Some bits'.
Proof.
  intros.
  break_exists.
  subst. 
  rename H2 into H1.
  simpl in H1; try subst tbl; try solve [simpl in H1; inv H1];
  simpl in H0. inv H0.
  eexists; split.
  preg_simpl. find_rewrite. reflexivity.
  eapply pinj_add; eauto.
Qed.  

Lemma star_step_in_at_code :
  forall z c ge st t st',
    star_step_in z c ge st t st' ->
    exists ofs,
      at_code z c ofs ge st.
Proof.
  induction 1; intros; eauto. 
  inv H. eauto.
  inv H0. eauto.
Qed.

Lemma neq_add_one :
  forall x,
    ~ Int.unsigned x = Int.unsigned (Int.add x Int.one).
Proof.
  intros. destruct x.
  simpl. unfold Int.unsigned. simpl.
  unfold Int.add. rewrite Int.unsigned_one. simpl.
  replace Int.intval with Int.unsigned by (simpl; auto).
  destruct (zeq intval Int.max_unsigned). subst.
  rewrite Int.unsigned_repr_eq.
  unfold Int.max_unsigned. unfold Int.modulus. simpl.
  unfold Int.wordsize. unfold Wordsize_32.wordsize.
  unfold two_power_nat. unfold shift_nat. simpl.
  rewrite Z_mod_same_full.
  omega.
  rewrite Int.unsigned_repr. omega. unfold Int.max_unsigned in *. omega.
Qed.


Lemma star_step_in_in :
  forall z c ge st t st',
    star_step_in z c ge st t st' ->
    in_code z c ge st.
Proof.
  induction 1; intros; eauto.
Qed.

Lemma star_step_in_in' :
  forall z c ge st t st',
    star_step_in z c ge st t st' ->
    in_code z c ge st'.
Proof.
  induction 1; intros; eauto.
Qed.


Lemma straightline_step_no_trace :
  forall z i c ge st t st',
    at_code z (i :: c) 0 ge st ->
    straightline i ->
    step_bits ge st t st' ->
    t = E0.
Proof.
  intros. inv H.
  inv_step H1; try reflexivity.


  copy H11.
  unify_psur.
  break_and; subst.
  
  unify_find_funct_ptr.
  unify_psur.
  subst.
  
  rewrite H7 in H13. 
  rewrite H4 in H13.
  rewrite find_instr_append_head in H13 by omega.
  simpl in H13. inv H13. simpl in H0. inv H0.

  copy H11.
  unify_psur.
  break_and; subst.
  unify_find_funct_ptr.
  subst.
  rewrite H7 in H15. 
  rewrite H4 in H15.
  rewrite find_instr_append_head in H15 by omega.
  simpl in H15. inv H15. simpl in H0. inv H0.

  unify_psur. unify_find_funct_ptr.

Qed.

Lemma in_code_one_instr :
  forall z i ge st,
    ~ in_code z (i :: nil) ge st.
Proof.
  intros. intro.
  inv H. inv H1.
  rewrite zlen_cons in H4. simpl in H4. omega.
Qed.

Lemma st_through_one :
  forall z st t st' i ge,
    straightline i ->
    step_through z (i :: nil) ge st t st' ->
    step_t (i :: nil) ge st t st'.
Proof.
  intros.
  
  inv H0.
  replace t with (E0 ** t) by (simpl; reflexivity).
  app straightline_step_no_trace H2. subst t.  
  econstructor; eauto.
  econstructor.


  app star_step_in_in H4.
  app in_code_one_instr H4. inv_false.
Qed.

Lemma at_code_succ :
  forall z i c ofs ge st,
    ofs > 0 ->
    at_code z (i :: c) ofs ge st ->
    at_code (z+1) c (ofs - 1) ge st.
Proof.
  intros.
  inv H0.
  replace (zlen c1 + 1) with (zlen (c1 ++ i :: nil)) by (rewrite zlen_app; rewrite zlen_cons; simpl; reflexivity).
  econstructor; eauto; 
  repeat rewrite zlen_app in *;
  repeat rewrite zlen_cons in *;
  simpl;
  try omega.
  find_rewrite. simpl. rewrite app_ass. simpl. reflexivity.
Qed.

Lemma add_one_no_overflow :
  forall i,
    0 <= Int.unsigned i < Int.max_unsigned ->
    Int.unsigned (Int.add i Int.one) = Int.unsigned i + 1.
Proof.
  intros. unfold Int.add. rewrite Int.unsigned_one.
  rewrite Int.unsigned_repr by omega. reflexivity.
Qed.


Ltac st_inv :=
  match goal with
    | [ H : Nxt _ _ _ = Nxt _ _ _ |- _ ] => inv H
    | [ H : Nxt _ _ _ = Stck |- _ ] => congruence
    | [ H : Stck = Nxt _ _ _ |- _ ] => congruence
  end.





Lemma at_code_straightline :
  forall z i x c (p : Asm.program) cs cs' t,
    no_PC_overflow_prog p ->
    at_code z (i :: x :: c) 0 (Genv.globalenv p) cs ->
    step_bits (Genv.globalenv p) cs t cs' ->
    straightline i ->
    at_code z (i :: x :: c) 1 (Genv.globalenv p) cs'.
Proof.
  intros. inv H0.

  
  inv_step H1;
    unify_psur;
    try unify_find_funct_ptr;
    subst;
    try congruence;
    try find_inversion;
    try match goal with
      | [ H : fn_code _ = _ |- _ ] => rewrite H in *
    end;
    try match goal with
      | [ H : Int.unsigned _ = _ |- _ ] => rewrite H in *
    end;
    try match goal with
      | [ H : find_instr _ _ = _ |- _ ] => rewrite find_instr_append_head in H by omega; simpl in H; inv H
        end;
    try solve [
          match goal with
            | [ H : straightline _ |- _ ] => simpl in H; inv H
          end].

  app weak_valid_pointer_sur H12. break_and.
  
  NP _app straightline_exec exec_instr_bits. break_and.
  econstructor; eauto.
  Focus 2. repeat rewrite zlen_cons. name (zlen_nonneg _ c) zln.
  instantiate (1 := (Int.add i0 Int.one)).
  

  assert (code_of_prog (fn_code f) p).
  {
    unfold code_of_prog.
    app Genv.find_funct_ptr_inversion H7.
    simpl. destruct f. simpl. exists x1. exists fn_sig.
    simpl.
    eauto.
  }

  
  unfold no_PC_overflow_prog in H.
  NP1 _app H code_of_prog. unfold no_PC_overflow in *.

  assert (find_instr (Int.unsigned i0) (fn_code f) = Some i1).
  
  rewrite H5. rewrite H8. simpl. rewrite find_instr_append_head by omega.
  simpl. reflexivity.

  NP1 _app H15 find_instr.
  rewrite add_one_no_overflow by omega. rewrite H5. omega.
  app step_match_metadata H1.

  
  erewrite weak_valid_pointer_sur; eauto.
  split; auto.
  NP _app global_perms_step step_bits.
  clear H21.
  NP _app global_perms_valid_globals global_perms.
  unfold valid_globals in *.
  eapply Memory.Mem.valid_pointer_implies.
  eapply H15.
  unfold is_global. left.
  unfold in_code_range.
  unfold fundef in *.
  collapse_match.

  name (Int.unsigned_range (Int.add i0 Int.one)) r.
  rewrite Int.unsigned_add_carry in *.
  rewrite Int.unsigned_one in *.
  split; try omega.
  unfold Int.add_carry.
  rewrite H5. rewrite H8.
  repeat rewrite zlen_app.
  repeat rewrite zlen_cons.
  name (zlen_nonneg _ c1) zlnc1.
  name (zlen_nonneg _ c2) zlnc2.
  name (zlen_nonneg _ c) zlnc.
  break_match; repeat rewrite Int.unsigned_zero;
  repeat rewrite Int.unsigned_one; try omega.
  repeat rewrite zlen_cons.
  name (zlen_nonneg _ c) zlnc.
  omega.

Qed.

Lemma at_code_end_succ :
  forall z i c ge st,
    at_code_end z (i :: c) ge st ->
    at_code_end (z+1) c ge st.
Proof.
  intros. inv H.
  replace (zlen c1 + 1) with (zlen (c1 ++ i :: nil)).
  Focus 2. rewrite zlen_app. rewrite zlen_cons.
  simpl. omega.
  econstructor; eauto.
  rewrite zlen_app. rewrite zlen_cons. simpl.
  rewrite zlen_cons in H2. omega.
  rewrite H4. simpl. rewrite app_ass. simpl.
  reflexivity.
Qed.

Ltac case_step := 
  match goal with 
    | [H : step_bits _ _ _ _ |- _ ] => inv H; [ | | | ]
  end.

Ltac same_pc_bits := 
  match goal with 
      | [ H1 : ?rs PC = Vint ?bits1, H2 : ?rs PC = Vint ?bits2 |- _ ] => 
        rewrite H1 in H2; symmetry in H2; inv H2
    end.

(* Ltac same_psur :=  *)
(*   match goal with  *)
(*       | [ H1 : psur ?bits = (_, _), H2 : psur ?bits = (_, _) |- _ ] =>  *)
(*         rewrite H1 in H2; symmetry in H2; inv H2 *)
(*     end. *)

Ltac same_find_funct_ptr := 
  match goal with
          | [ H1 : Genv.find_funct_ptr ?ge ?b = Some (Internal _),
              H2 : Genv.find_funct_ptr ?ge ?b = Some (Internal _) |- _] =>
            unfold fundef in H1, H2; rewrite H2 in H1; inv H1
  end.

Ltac same_find_instr :=
  match goal with 
    | [ H1 : find_instr ?a ?b = _,
        H2 : find_instr ?a ?b = _ |- _] =>
      rewrite H2 in H1; inv H1
  end.

Ltac trim_l_find_instr :=
  match goal with
        | [ H : find_instr (zlen ?c1 + ?ofs') (?c1 ++ ?c) = _ |- _ ] =>
          rewrite find_instr_append_head in H; [ | omega]
    end.

Ltac trim_r_find_instr :=
  match goal with
      | [ H : find_instr _ (_ ++ _) = _ |- _] =>
        rewrite (find_instr_append_tail _ _ nil _) in H; [ | omega]
  end.

Lemma find_instr_in_code :
      forall c ofs i,
        0 <= ofs < zlen c ->
        find_instr ofs c = Some i ->
        In i c.
Proof.
  induction c; simpl; intros.
  congruence.
  break_if_hyp.
  inv H0; auto.
  right.
  eapply IHc; eauto.
  rewrite zlen_cons in H.
  omega.
Qed.

Hint Resolve app_nil_end.

Definition current_fn (ge : genv) (st : state_bits) : option function := 
  match st with
    | State_bits rs m t => 
      match rs PC with
        | Vint bits =>
          match psur t bits with
            | Some (b, ofs) =>
              match Genv.find_funct_ptr ge b with
                | Some (Internal f) => Some f
                | _ => None
              end
            | None => None
          end
        | _ => None
      end                  
  end.

Definition current_code (ge : genv) (st : state_bits) : option code :=
  match current_fn ge st with
    | Some f => Some (fn_code f)
    | _ => None
  end.

Definition current_instr (ge : genv) (st : state_bits) : option instruction := 
  match st with
    | State_bits rs m t => 
      match rs PC with
        | Vint bits =>
          match psur t bits with
            | Some (b, ofs) =>
              match current_code ge st with
                | Some c => find_instr (Int.unsigned ofs) c
                | _ => None                      
              end
            | None => None
          end
        | _ => None
      end                  
  end.

Lemma in_code_instr:
  forall pad c ge st i,
    in_code pad c ge st ->
    current_instr ge st = Some i ->
    In i c.
Proof.
  intros.
  inv H.
  inv H2.
  unfold current_instr in *; 
  unfold current_code in *;
  unfold current_fn in *.
  unfold fundef in *.
  rewrite H, H3, H6, H7, H4 in H0.
  trim_l_find_instr.
  trim_r_find_instr.
  eapply find_instr_in_code. eauto.
  assert (c = c ++ nil) by apply app_nil_end.
  rewrite H2.
  eauto.   
Qed.

Lemma has_current_instr :
  forall rs m c ge i b ofs f bits pad md,
    in_code pad c ge (State_bits rs m md) ->
    rs PC = Vint bits ->
    psur md bits = Some (b, ofs) ->
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    find_instr (Int.unsigned ofs) (fn_code f) = Some i ->  
    current_fn ge (State_bits rs m md) = Some f /\
    current_instr ge (State_bits rs m md) = Some i.
Proof.
  intros.
  unfold current_instr. unfold current_code. unfold current_fn.
  rewrite H0, H1, H2, H3.
  split; trivial.
Qed.
     
Ltac case_local_jump_instr :=
  match goal with
    | [ H : local_jump ?i |- _] =>
      destruct i; try solve [inv H]
  end.

Ltac case_straightline_instr :=
  match goal with
    | [ H : straightline ?i |- _] =>
      destruct i; try solve [inv H]
  end.

Lemma in_code_is_jump_dec : 
  forall fst c ge st pad i,
    straightline fst ->
    (forall k : instruction, In k c -> straightline k \/ local_jump k) ->
    in_code pad (fst :: c) ge st ->
    current_instr ge st = Some i ->  
    straightline i \/ local_jump i.
Proof.
  intros.
  assert (In i (fst :: c)) by (eapply in_code_instr; eauto).
  assert (i = fst \/ In i c).
  simpl in *; inv H3; auto.
  inv H4.
  auto.
  apply H0.
  assumption.
Qed.

Ltac case_is_jump := 
  match goal with 
    | [ i : instruction |- _ ] =>  
      let H := fresh "H" in
      assert (straightline i \/ local_jump i) 
        as H 
          by (      
              eapply in_code_is_jump_dec; eauto;
              eapply has_current_instr; eauto
            ); inv H
  end.

Lemma val_to_int_add :
  forall z,
    Val.add (Vint z) Vone = Vint (Int.add z Int.one).
Proof.
  auto.
Qed.

Lemma nextinstr_same_block :
  forall p rs bits b ofs rs' bits' md f i i' m,
    match_metadata md m ->
    global_perms (Genv.globalenv p) m ->
    Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal f) ->
    find_instr (Int.unsigned ofs) (fn_code f) = Some i ->
    find_instr (Int.unsigned (Int.add ofs Int.one)) (fn_code f) = Some i' ->
    rs PC = Vint bits ->
    psur md bits = Some (b, ofs) ->
    rs' PC = Vint bits' ->
    Vint bits' = (nextinstr rs) PC ->
    psur md bits' = Some (b, Int.add ofs Int.one).
Proof.
  intros.
  
  (*TODO Share with PeepholeLib *)
  Lemma nextinstr_PC :
    forall rs v,
      rs PC = v ->
      nextinstr rs PC = Values.Val.add v Values.Vone.
  Proof.
    intros. unfold nextinstr.
    rewrite Pregmap.gss. rewrite H. reflexivity.
  Qed.

  
  apply nextinstr_PC in H4.
  simpl in H4. rewrite H4 in H7.
  inv H7.
  eapply weak_valid_pointer_sur in H5; eauto.
  eapply weak_valid_pointer_sur; eauto.
  break_and; split.
  eapply pinj_add; eauto.
  app global_perms_valid_globals H0.
  unfold valid_globals in H0.
  eapply Memory.Mem.valid_pointer_implies.
  eapply H0.
  unfold is_global.
  left. unfold in_code_range.
  unfold fundef in *.
  collapse_match.
  apex in_range_find_instr H3. omega.
Qed.

Ltac unify_stuff :=
  repeat (try same_pc_bits; try unify_psur; try same_find_funct_ptr; try same_find_instr).

Lemma no_PC_overflow_w_ctx (*TODO need better name*):
  forall p b f z i,
    no_PC_overflow_prog p ->
    Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal f) ->
    find_instr z (fn_code f) = Some i ->
    0 <= z < Int.max_unsigned.
Proof.
  intros.
  unfold no_PC_overflow_prog in *; unfold no_PC_overflow in *; unfold code_of_prog in *.
  destruct f.
  specialize (H fn_code).
  apply Genv.find_funct_ptr_inversion in H0.
  assert (exists id fn_sig, In (id, Gfun (Internal {| fn_sig := fn_sig; fn_code := fn_code |}))
           (prog_defs p)).
  break_exists.
  eauto.
  eapply H in H2.
  eassumption.
  eassumption.
Qed.
Hint Resolve no_PC_overflow_w_ctx.

Lemma psur_add_code :
  forall ge md bits b ofs md' m m',
    psur md bits = Some (b,ofs) ->
    md_extends md md' ->
    match_metadata md m ->
    match_metadata md' m' ->
    global_perms ge m' ->
    forall adj,
      in_code_range ge b (Int.add ofs adj) ->
      psur md' (Int.add bits adj) = Some (b,Int.add ofs adj).
Proof.
  intros.
  erewrite weak_valid_pointer_sur in *; eauto.
  break_and. app pinj_extends H.
  split.
  eapply pinj_add; eauto.
  unfold global_perms in H3.
  unfold is_global in H3.
  eapply Memory.Mem.valid_pointer_implies.
  exploit H3; eauto. intros.
  break_exists. repeat break_and.
  unfold Memory.Mem.valid_pointer.
  unfold Memory.Mem.perm_dec.
  unfold proj_sumbool. break_match; try reflexivity.
  clear Heqs. exfalso. apply n.
  unfold Memory.Mem.perm_order'.
  rewrite H7.
  econstructor.
Qed.


Lemma int_unsigned_add_one :
  forall i hi,
    0 <= Int.unsigned i < hi ->
    0 <= Int.unsigned (Int.add i Int.one) <= hi.
Proof.
  intros. unfold Int.add.
  rewrite Int.unsigned_one.
  rewrite Int.unsigned_repr_eq.
  name (Int.unsigned_range i) Hr.
  assert (Int.unsigned i + 1 < Int.modulus \/ Int.unsigned i + 1 = Int.modulus) by omega.
  break_or. rewrite Zmod_small by omega.
  omega.
  rewrite H1.
  rewrite Z_mod_same_full. omega.
Qed.  

Lemma int_unsigned_minus_range :
  forall z hi,
    0 <= z-1 < hi ->
    0 <= Int.unsigned (Int.repr z) <= hi.
Proof.
  intros. rewrite Int.unsigned_repr_eq.
  assert (z mod Int.modulus <= z). eapply Zmod_le.
  unfold Int.modulus. unfold Int.wordsize.
  unfold Wordsize_32.wordsize. unfold two_power_nat.
  unfold shift_nat. simpl. omega. omega.
  assert (0 <= z mod Int.modulus < Int.modulus). eapply Z_mod_lt.
  unfold Int.modulus. unfold Int.wordsize.
  unfold Wordsize_32.wordsize. unfold two_power_nat.
  unfold shift_nat. simpl. omega. omega.
Qed.



Lemma psur_add_one :
  forall ge md bits b ofs md' m m',
    psur md bits = Some (b,ofs) ->
    md_extends md md' ->
    match_metadata md m ->
    match_metadata md' m' ->
    global_perms ge m' ->
    in_code_range ge b ofs ->
    Int.unsigned ofs < Int.max_unsigned ->
    psur md' (Int.add bits Int.one) = Some (b,Int.add ofs Int.one).
Proof.
  intros.
  erewrite weak_valid_pointer_sur in *; eauto.
  break_and. app pinj_extends H.
  split.
  eapply pinj_add; eauto.
  unfold global_perms in H3.
  unfold is_global in H3.
  eapply Memory.Mem.weak_valid_pointer_spec.
  right.
  exploit H3; eauto. intros.
  break_exists. repeat break_and.
  unfold Memory.Mem.valid_pointer.
  unfold Memory.Mem.perm_dec.
  unfold proj_sumbool. break_match; try reflexivity.
  clear Heqs. exfalso. apply n.
  unfold Memory.Mem.perm_order'.
  replace (Int.unsigned (Int.add ofs Int.one) - 1) with (Int.unsigned ofs).
  rewrite H8.
  econstructor.
  unfold Int.add.
  rewrite Int.unsigned_one.
  name (Int.unsigned_range_2 ofs) r.
  assert (0 <= Int.unsigned ofs < Int.max_unsigned) by omega.
  cut (Int.unsigned ofs + 1 = Int.unsigned (Int.repr (Int.unsigned ofs + 1))).
  intros. omega.
  rewrite Int.unsigned_repr by omega. reflexivity.
Qed.

Lemma unsigned_repr_sub_one :
  forall z,
    z > 0 ->
    z <= Int.max_unsigned ->
    Int.unsigned (Int.repr z) - 1 = Int.unsigned (Int.repr (z - 1)).
Proof.
  intros.
  repeat rewrite Int.unsigned_repr by omega.
  reflexivity.
Qed.

Lemma unsigned_repr_range :
  forall hi z,
    0 <= z < hi ->
    0 <= Int.unsigned (Int.repr z) < hi.
Proof.
  intros.

  rewrite Int.unsigned_repr_eq.
  exploit (Z_mod_lt z Int.modulus).
  unfold Int.modulus. unfold Int.wordsize.
  unfold Wordsize_32.wordsize. unfold two_power_nat.
  unfold shift_nat. simpl. omega.
  intros.
  assert (z mod Int.modulus <= z).
  eapply Zmod_le.
  unfold Int.modulus. unfold Int.wordsize.
  unfold Wordsize_32.wordsize. unfold two_power_nat.
  unfold shift_nat. simpl. omega.
  omega. split; try omega.
Qed.

Section ST_IN.
  Variable p : program.
  Hypothesis nPC : no_PC_overflow_prog p.


  Definition ge := Genv.globalenv p.

Lemma in_range_PC :
  forall b fd z i,
    Genv.find_funct_ptr ge b = Some (Internal fd) ->
    find_instr z (fn_code fd) = Some i ->
    z < Int.max_unsigned.
Proof.
  intros. unfold ge in *.
  unfold no_PC_overflow_prog in *.
  assert (code_of_prog (fn_code fd) p). {
    unfold code_of_prog. app Genv.find_funct_ptr_inversion H.
    destruct fd. simpl. eauto.
  } idtac.
  app nPC H1.
  unfold no_PC_overflow in H1. app H1 H0.
  omega.
Qed.
  
Lemma step_PC_same_block :
  forall rs m rs' m' t b i s c instr bits md md',
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,i) ->
    Genv.find_funct_ptr ge b = Some (Internal (mkfunction s c)) ->
    find_instr (Int.unsigned i) c = Some instr ->
    ~ is_call_return instr ->
    ~ is_builtin instr ->
    step_bits ge (State_bits rs m md) t (State_bits rs' m' md') ->
    exists i' bits',
      rs' PC = Values.Vint bits' /\ psur md' bits' = Some (b,i').
Proof.
  intros.
  invs;
    repeat unify_PC;
    repeat unify_psur;
    repeat unify_find_funct_ptr;
    simpl in *;
    repeat unify_find_instr;
    simpl in *;
    try inv_false.
  
  destruct i0 eqn:?;
    simpl in H3;
    simpl in H4;
    try inv_false;
    unfold exec_instr_bits in *;
    unfold exec_load_bits in *;
    unfold exec_store_bits in *;
    unfold goto_label_bits in *;
    unfold exec_big_store_bits in *;
    unfold exec_big_load_bits in *;
    repeat break_match_hyp; try congruence;
    try st_inv;
    preg_simpl;
    try rewrite H;
    simpl;

  match goal with
    | [ |- exists _, exists _, Vint _ = Vint _ /\ _ ] => eexists; eexists; split; try reflexivity; try eapply psur_add_one
    | [ |- _ ] => idtac
  end;
  match goal with
    | [ |- match_metadata (md_alloc _ _ _ _) _ ] => eapply match_alloc
    | [ |- match_metadata (md_free _ _ _ _) _ ] => eapply match_free
    | [ |- _ ] => idtac
  end;
  try solve [econstructor];
  eauto;
  match goal with
    | [ |- match_metadata (md_alloc _ _ _ _) _ ] => eapply match_alloc
    | [ |- match_metadata (md_free _ _ _ _) _ ] => eapply match_free
    | [ |- _ ] => idtac
  end;
  eauto;
  try solve [unfold in_code_range;
              unfold fundef in *; collapse_match;
              simpl; apex in_range_find_instr H2; omega];
  try solve [
      repeat break_match; preg_simpl;
        try rewrite H;
        simpl;
        repeat break_match;
        preg_simpl;
        try rewrite H;
        match goal with
          | [ |- exists _, exists _, Vint _ = Vint _ /\ _ ] => eexists; eexists; split; try reflexivity; try eapply psur_add_one; eauto
          | [ |- _ ] => idtac
        end;
        try solve [econstructor];
        try solve [unfold in_code_range;
                    unfold fundef in *; collapse_match;
                    simpl; apex in_range_find_instr H2; try omega
                  ];
        try eapply in_range_PC; eauto
      ];
  
  try instantiate (1 := Int.repr z);
  simpl in *;
  try solve [eapply in_range_PC; eauto];
  
  
  try solve [
        erewrite weak_valid_pointer_sur in *; eauto;
        split; eauto;
        NP _app global_perms_valid_globals global_perms;
        P _eapply valid_globals;
        unfold is_global;
        left; unfold in_code_range;
        unfold fundef in *; collapse_match;
        simpl;
        simpl in Heqo;
        NP _app label_pos_find_instr label_pos;
        NP apex in_range_find_instr Plabel;
        eapply int_unsigned_minus_range; try omega;
        try eapply in_range_PC; eauto
      ];
  
  try solve [
        erewrite weak_valid_pointer_sur in *; eauto;
        split; eauto;
        NP _app global_perms_valid_globals global_perms;
        eapply Memory.Mem.weak_valid_pointer_spec; right;
        unfold valid_globals in *;
        NP _app label_pos_find_instr label_pos;
        NP apex in_range_find_instr Plabel;
        rewrite unsigned_repr_sub_one;
        try (eapply H21;
        unfold is_global;
        left; unfold in_code_range;
        unfold fundef in *;
        collapse_match; simpl;
        eapply unsigned_repr_range; try omega);
        try omega;
        cut (z - 1 < Int.max_unsigned);
        try omega;
        try eapply in_range_PC; eauto
      ].

  
  eapply psur_alloc; eauto.
  eapply GlobalPerms.global_perms_alloc; eauto.
  match goal with
    | [ |- in_code_range ge b i ] =>
      unfold in_code_range; unfold fundef in *;
      collapse_match; apex in_range_find_instr H2;
      simpl;  omega
    | [ |- _ ] => idtac
  end.

  erewrite weak_valid_pointer_sur in *; eauto. split.
  eapply pinj_free; eauto.
  repeat break_and. eauto.
  app GlobalPerms.global_perms_free Heqo3.
  app global_perms_valid_globals Heqo3.
  eapply Memory.Mem.valid_pointer_implies.
  eapply Heqo3.
  unfold is_global. left.
  unfold in_code_range.
  unfold fundef in *. collapse_match.
  simpl. apex in_range_find_instr H2. omega.
  eapply match_free; eauto.
  app GlobalPerms.global_perms_free Heqo3.
  unfold in_code_range. unfold fundef in *.
  collapse_match. simpl.
  apex in_range_find_instr H2.
  omega.

  preg_simpl. rewrite H. simpl.
  match goal with
    | [ |- exists _, exists _, Vint _ = Vint _ /\ _ ] => eexists; eexists; split; try reflexivity
    | [ |- _ ] => idtac
  end;
    try solve [econstructor];

    match goal with
      | [ |- in_code_range ge b (Int.add i Int.one) ] =>
        unfold in_code_range; unfold fundef in *;
        collapse_match; apex in_range_find_instr H2;
        simpl; eapply int_unsigned_add_one; omega
      | [ |- _ ] => idtac
    end.

  erewrite weak_valid_pointer_sur in *; eauto. break_and.
  split.

  3: eapply match_ec; eauto.
  eapply pinj_ec; eauto.
  eapply pinj_add; eauto.

  eapply Memory.Mem.weak_valid_pointer_spec. right.
  
  
  app global_perms_step H5.
  app global_perms_valid_globals H5.

  replace (Int.unsigned (Int.add i Int.one) - 1) with (Int.unsigned i).
  
  eapply H5.
  unfold is_global. left.
  unfold in_code_range.
  unfold fundef in *.
  collapse_match.
  simpl.
  apex in_range_find_instr H2.
  omega.

  unfold Int.add.
  rewrite Int.unsigned_one.

  assert (Int.unsigned i < Int.max_unsigned).
  eapply in_range_PC; eauto.
  rewrite Int.unsigned_repr. omega.
  name (Int.unsigned_range_2 i) Hrange.
  omega.
Qed.  



(* We can make this true *)
(* do later *)
Lemma in_code_straightline_succ :
  forall pad rs m bits b ofs f i rs' m' ofs' fst snd c md md',    
    (* straightline fst -> *)
    rs PC = Vint bits ->
    psur md bits = Some (b, ofs) ->
    Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal f) ->
    find_instr (Int.unsigned ofs) (fn_code f) = Some i ->
    rs' PC = (nextinstr rs) PC ->
    at_code pad (fst :: snd :: c) ofs' (Genv.globalenv p) (State_bits rs' m' md') ->
    in_code pad (fst :: snd :: c) (Genv.globalenv p) (State_bits rs m md) ->
    no_PC_overflow_prog p ->
    global_perms (Genv.globalenv p) m' ->
    md_extends md md' ->
    match_metadata md m ->
    match_metadata md' m' ->
    ofs' - 1 > 0.
Proof.
  intros.
  name H4 Hat_code.
  inv H4.
  inv H5. inv H11.
  repeat rewrite zlen_cons in *.
  unfold nextinstr in *.
  rewrite H in H3. preg_simpl_hyp H3.
  simpl in H3. rewrite H3 in H14. inv H14.
  rewrite H in H18. inv H18.
    
  erewrite psur_add_one in H15; eauto.
  inv H15.
  repeat unify_psur.
  repeat unify_find_funct_ptr.
  rewrite Int.add_unsigned in H16.
  rewrite H20 in H16. rewrite Int.unsigned_one in H16.
  rewrite Int.unsigned_repr in H16. omega.
  app no_PC_overflow_w_ctx H2. omega.
  unfold in_code_range.
  repeat unify_psur.
  unfold fundef in *.
  collapse_match.
  rewrite H20. rewrite H29.
  repeat rewrite zlen_app. repeat rewrite zlen_cons.
  name (zlen_nonneg _ c4) zln.
  name (zlen_nonneg _ c) zlnc.
  name (zlen_nonneg _ c3) zlnc3.
  omega.
  eapply in_range_PC. eapply H1.
  eapply H2.
Qed.

Hint Resolve in_code_straightline_succ.

Lemma z_split :
  forall n m,
    n <= m \/ n > m.
Proof.
  intros.
  omega.
Qed.

Lemma find_instr_range :
  forall z c i,
    find_instr z c = Some i ->
    0 <= z < zlen c.
Proof.
  intros.
  name (z_split 0 z) Hz1.
  name (z_split (zlen c) z) Hz2.
  inv Hz1; inv Hz2.
  assert (z >= zlen c) by omega.  
  apply find_instr_overflow in H2.
  congruence.
  omega.
  assert (z < 0) by omega.
  apply (find_instr_neg c) in H2.
  congruence.
  assert (z < 0) by omega.
  apply (find_instr_neg c) in H2.
  congruence.
Qed.  

Definition is_any_label (i : instruction) : Prop :=
  match i with
    | Plabel _ => True
    | _ => False
  end.

Lemma in_code_jump_succ :
  forall pad l rs m bits b ofs f i rs' m' ofs' fst snd c md md',
    straightline fst ->    
    rs PC = Vint bits ->
    psur md bits = Some (b, ofs) ->
    Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal f) ->
    find_instr (Int.unsigned ofs) (fn_code f) = Some i ->
    goto_label_bits md f l b rs m = Nxt rs' m' md' ->
    at_code pad (fst :: snd :: c) ofs' (Genv.globalenv p) (State_bits rs' m' md') ->
    ofs' > 0 ->
    in_code pad (fst :: snd :: c) (Genv.globalenv p) (State_bits rs m md) ->
    no_PC_overflow_prog p ->
    ~ (is_any_label fst) ->
    global_perms (Genv.globalenv p) m ->
    match_metadata md m ->
    ofs' - 1 > 0.
Proof.
  intros.  
  rename H6 into Hofs', H7 into H6, H8 into H7.
  unfold goto_label_bits in *.
  break_match_hyp.
  2: congruence.
  break_match_hyp; try congruence.
  apply label_pos_find_instr in Heqo.
  match goal with | [ H : at_code _ _ ofs' _ _ |- _ ] =>
                    name H Hat_code'; inv H
  end.
  st_inv. 
  match goal with | [ H : ?rs PC = _ |- _ ] => inv H end.

  assert (Hz1 : Int.unsigned (Int.repr (z - 1)) = z - 1).
  erewrite unsigned_repr_PC; try eapply H2; eauto.
  
  assert (Hz : Int.unsigned (Int.repr z) = z ).
  erewrite unsigned_repr_PC; try eapply H2; eauto.
  
  assert (Memory.Mem.weak_valid_pointer m' b z = true). {
    eapply Memory.Mem.weak_valid_pointer_spec.
    right.
    app global_perms_valid_globals H10.
    unfold valid_globals in H10.
    rewrite <- Hz1.
    eapply H10. unfold is_global.
    left. unfold in_code_range.
    unfold fundef in *.
    collapse_match. rewrite Hz1.
    NP apex in_range_find_instr Plabel.
    omega.
    
  } idtac.
  

  rewrite <- Hz in H4.
  name (conj Heqo0 H4) Hps.
  erewrite <- weak_valid_pointer_sur in Hps; eauto.

  rewrite Hps in H15. inversion H15. subst i1.
  subst b0. clear H15.

  rewrite Hz in *.
  
  assert (ofs' = 1 \/ ofs' > 1) by omega.
  break_or; try omega.

  unify_find_funct_ptr. rewrite H23 in Heqo.
  replace (zlen c1 + 1 - 1) with (zlen c1 + 0) in Heqo by omega.
  rewrite find_instr_append_head in Heqo by omega.
  simpl in Heqo.
  inv Heqo. simpl in H9. inv_false.
Qed.
  

Hint Resolve in_code_jump_succ.

Lemma in_code_succ :
  forall pad fst snd c st t st',    
    in_code pad (fst :: snd :: c) (Genv.globalenv p) st ->
    in_code pad (fst :: snd :: c) (Genv.globalenv p) st' ->    
    no_PC_overflow_prog p ->
    step_bits (Genv.globalenv p) st t st' ->    
    straightline fst ->
    (forall k, In k (snd :: c) -> straightline k \/ local_jump k) ->
    ~ (is_any_label fst) ->
    in_code (pad+1) (snd :: c) (Genv.globalenv p) st'.
Proof.
  (* This is true, because: *)
  (* if we're in a piece of code, not at the beginning *)
  (* and we take a step and stay within that piece of code *)
  (* we can't have gone back to i or even x *)
  (* as any jump to a label will go past it *)
  (* This will need absence of call/return instruction *)
  (* That will be the pain *)

  intros.
    
  match goal with 
      | [ H : in_code _ _ _ st' |- _ ] => inv H
  end.
  econstructor.
  Focus 2.
  eapply at_code_succ.
  Focus 2.
  eassumption.
  assumption.
  rename ofs into ofs'.  
  
  case_step.

  (* exec_step_internal_bits *)
  {
    case_is_jump.
    
    (* straightline *)
    {      
      case_straightline_instr;
      simpl in *;
      unfold exec_load_bits in *;
      unfold exec_store_bits in *;
      unfold exec_big_load_bits in *;
      unfold exec_big_store_bits in *;
      unfold storev_bits in *;
      repeat break_match_hyp;
      try congruence;
      assert ((rs') PC = (nextinstr rs) PC);
      try st_inv;
      subst;
      eauto;
      try eapply in_code_straightline_succ; eauto;
      try solve [econstructor; eauto];
      try solve [econstructor; try econstructor; eauto];
      try solve [eapply global_perms_store_bits; eauto];
      try solve [eapply global_perms_store_bits; try eapply global_perms_store_bits; eauto];

      
      try unfold compare_floats; try unfold compare_floats32;
      repeat break_match; preg_simpl; try reflexivity.

      simpl in Heqo. inv Heqo.

      eapply global_perms_store_bits; try eapply global_perms_store_bits;
      try eapply global_perms_alloc; eauto.

      econstructor; try econstructor; try eapply match_alloc; eauto.

      eapply global_perms_free; eauto.
      eapply match_free; eauto.
    }

    (* local jump *)
    {
      case_local_jump_instr; 
      simpl in *;
      repeat break_match_hyp; try congruence;            
      eauto;
      assert ((rs') PC = (nextinstr rs) PC);
      try st_inv;
      subst;
      try solve [eapply in_code_jump_succ; eauto];
      try solve [eapply in_code_straightline_succ; eauto; econstructor];
      eauto.
      
    }    
  }

  (*exec_step_builtin_bits*)
  remember (Pbuiltin ef args res).
  case_is_jump; inv H12.

  (*exec_step_annot_bits*)
  remember (Pannot ef args).
  case_is_jump; inv H18.

  (*exec_step_external_bits*)
  inv H6.
  inv H.
  inv H6.
  unify_stuff.
  unfold fundef in *.

  unify_find_funct_ptr.
  
Qed.   

Lemma in_code_not_nil :
  forall z c ge st,
    in_code z c ge st ->
    c <> nil.
Proof.
  intros. inv H.
  inv H1. destruct c; try congruence.
  unfold zlen in H4. simpl in H4. omega.
Qed.

Lemma star_step_in_succ :
  forall z i c st t st',        
    star_step_in z (i :: c) (Genv.globalenv p) st t st' ->
    straightline i ->
    in_code (z + 1) c (Genv.globalenv p) st ->
    (forall k, In k c -> straightline k \/ local_jump k) ->    
    no_PC_overflow_prog p ->
    ~ (is_any_label i) ->
    star_step_in (z+1) c (Genv.globalenv p) st t st'.
Proof.
  intros. 
  remember (i :: c) as c0.
  remember (Genv.globalenv p) as ge.
  induction H; subst c0.
  econstructor; eauto.
  destruct c. app in_code_not_nil H1. congruence.
  econstructor. apply IHstar_step_in. eauto.
  eauto.
  app star_step_in_in H.
  subst.
  
  eapply in_code_succ; eauto.
  eauto.
  eauto.
Qed.

(* Key lemma *)
Lemma step_through_t_straightline :
  forall z st t st' i x c,
    no_PC_overflow_prog p ->
    step_through z (i :: x :: c) (Genv.globalenv p) st t st' ->
    straightline i ->    
    (forall k, In k (x :: c) -> straightline k \/ local_jump k) ->
    ~ (is_any_label i) ->
    exists st'' t1 t2,
      step_t (i :: nil) (Genv.globalenv p) st t1 st'' /\
      step_through (z + 1) (x :: c) (Genv.globalenv p) st'' t2 st' /\
      t = t1 ** t2.
Proof.
  intros. 
  rename H3 into Hno_lb.  
  inv H0.
  * app at_code_straightline H3. 
    inv H3. inv H5. unify_PC.
    unify_psur. unify_find_funct_ptr.
    rewrite H3 in *. repeat rewrite zlen_cons in H16.
    name (zlen_nonneg _ c) zln. omega.
  * app at_code_straightline H5.
    app at_code_succ H5; try omega.
    simpl in H5. app straightline_step_no_trace H0. subst t1.
    app at_code_end_succ H4.
    exists stB. exists E0. exists (t2 ** t3).
    isplit. replace E0 with (E0 ** E0) by auto.
    econstructor; eauto. eapply at_code_head. simpl. eauto.
    rewrite zlen_cons. simpl. omega.
    econstructor. split; try reflexivity.
    
    inv H6.
    econstructor; eauto.

    rewrite Eapp_assoc.
    eapply st_thru_mult_step; eauto.
    app star_step_in_in H11.

    eapply in_code_succ in H13; eauto.
    
    eapply star_step_in_succ; eauto.
Qed.


(* (* How do we write this lemma? *) *)
(* Lemma step_through_t_straightline : *)
(*   forall z p st t st' i x c, *)
(*     no_PC_overflow_prog p -> *)
(*     step_t (i :: x :: c) (Genv.globalenv p) st t st' -> *)
(*     straightline i -> *)
(*     (forall k, In k (x :: c) -> straightline k \/ local_jump k) -> *)
(*     ~ (is_any_label i) -> *)
(*     exists st'' t1 t2, *)
(*       step_t (i :: nil) (Genv.globalenv p) st t1 st'' /\ *)
(*       step_through (z + 1) (x :: c) (Genv.globalenv p) st'' t2 st' /\ *)
(*       t = t1 ** t2. *)

  
(* Lemma test : *)
(*   forall a b c p st st' z, *)
(*     straightline a -> *)
(*     straightline b -> *)
(*     straightline c -> *)
(*     ~ is_any_label a -> *)
(*     ~ is_any_label b -> *)
(*     ~ is_any_label c -> *)
(*     no_PC_overflow_prog p -> *)
(*     step_through z (a :: b :: c :: nil) (Genv.globalenv p) st E0 st' -> *)
(*     step_t (a :: b :: c :: nil) (Genv.globalenv p) st E0 st' . *)
(* Proof. *)
(*   intros. *)
(*   app step_through_t_straightline H6. *)
(*   Focus 2. intros. simpl in H8. *)
(*   repeat break_or; subst; try inv_false; left; eauto. *)
(*   repeat break_and. *)
(*   app step_through_t_straightline H8. *)
(*   Focus 2. intros. simpl in H11. *)
(*   repeat break_or; subst; try inv_false; left; eauto. *)
(*   repeat break_and. *)
(*   app st_through_one H11. *)
(*   assert (x0 = E0). *)
(*   { *)
(*     destruct x0; auto; inv H12. inv H9. *)
(*   } *)
(*   subst x0. *)
(*   assert (x1 = E0). *)
(*   { *)
(*     destruct x1; auto; inv H9. *)
(*   } *)
(*   subst x1. *)
(*   assert (x3 = E0). *)
(*   { *)
(*     destruct x3; auto; inv H14. *)
(*   } *)
(*   subst x3. *)
(*   assert (x4 = E0). *)
(*   { *)
(*     destruct x4; auto; inv H9. *)
(*   } *)
(*   subst x4. *)
(*   replace E0 with (E0 ** E0) by auto. *)
(*   inv H6. inv H22. *)
(*   econstructor; eauto. *)
(*   rewrite E0_right. eauto. *)
(*   replace E0 with (E0 ** E0) by auto. *)
(*   inv H8. inv H24. *)
(*   assert (t1 = E0). *)
(*   { *)
(*     destruct t1; inv H16; auto. *)
(*   } *)
(*   subst t1. *)
(*   assert (t0 = E0). *)
(*   { *)
(*     destruct t0; inv H15; eauto. *)
(*   } *)
(*   subst t0. *)
(*   econstructor; eauto. *)
(* Qed. *)

(* Need other way too *)
(* step_t to step_through *)
(* TODO: make this *)

Definition ends_in_not_label (c : code) :=
  forall i,
    find_instr (zlen c - 1) c = Some i ->
    ~ is_any_label i.


Definition no_calls (c : code) :=
  forall z i,
    find_instr z c = Some i ->
    ~ is_call_return i.

Definition no_trace (i : instruction) :=
  match i with
    | Pbuiltin _ _ _ => False
    | Pannot _ _ => False
    | _ => True
  end.

Definition no_trace_code (c : code) :=
  forall z i,
    find_instr z c = Some i ->
    no_trace i.


Definition only_forward_jumps_lab (l : label) (c : code) : Prop :=
  forall z i,
    find_instr z c = Some i ->
    labeled_jump i l ->
    forall z',
      find_instr z' c = Some (Plabel l) ->
      z' > z.

Definition only_forward_jumps (c : code) : Prop :=
  no_calls c /\ no_trace_code c /\
  forall l, only_forward_jumps_lab l c .

Definition pat_at_n (pat : code) (n : nat) (c : code) : Prop :=
  c = (firstn n c) ++ pat ++ (skipn (n + length pat) c).

Lemma skipn_len :
  forall {A} (l1 l2 : list A),
    skipn (length l1) (l1 ++ l2) = l2.
Proof.
  induction l1; intros.
  * simpl. reflexivity.
  * simpl. apply IHl1.
Qed.

Lemma firstn_len :
  forall {A} (l1 l2 : list A),
    firstn (length l1) (l1 ++ l2) = l1.
Proof.
  induction l1; intros.
  * simpl. reflexivity.
  * simpl. rewrite IHl1. reflexivity.
Qed.

Lemma pat_at_n_sane :
  forall c1 c2 pat,
    pat_at_n pat (length c1) (c1 ++ pat ++ c2).
Proof.
  induction c1; intros; simpl.
  * unfold pat_at_n.
    simpl. rewrite skipn_len.
    reflexivity.
  * unfold pat_at_n. simpl.
    f_equal. rewrite <- app_length.
    rewrite <- app_ass. rewrite skipn_len.
    rewrite app_ass.
    rewrite firstn_len.
    reflexivity.
Qed.

Lemma nat_zlen :
  forall {A} (l : list A),
    nat_of_Z (zlen l) = length l.
Proof.
  induction l; intros.
  * simpl. reflexivity.
  * simpl. 
    rewrite SuccNat2Pos.id_succ.
    reflexivity.
Qed.

Definition ends_in_not_call (c : code) : Prop :=
  exists c',
    exists i,
      c = c' ++ i :: nil /\ ~ is_call_return i.

Definition is_label_instr (i : instruction) (l : label) : Prop :=
  match i with
    | Plabel l' => l = l'
    | Pjmp_l l' => l = l'
    | Pjcc _ l' => l = l'
    | Pjcc2 _ _ l' => l = l'
    | Pjmptbl _ tbl => In l tbl
    | _ => False
  end.

Definition only_labels (c : code) (labs : list label) : Prop := 
  forall z i,
    find_instr z c = Some i ->
    forall l,
      is_label_instr i l ->
      In l labs.

Definition no_labels (c : code) (labs : list label ) : Prop :=
  forall z i,
    find_instr z c = Some i ->
    forall l,
      is_label_instr i l ->
      ~ In l labs.

Fixpoint get_labels (c : code) : list label :=
  match c with
    | nil => nil
    | Plabel l :: r => l :: get_labels r
    | Pjmp_l l :: r => l :: get_labels r
    | Pjcc _ l :: r => l :: get_labels r
    | Pjcc2 _ _ l :: r => l :: get_labels r
    | Pjmptbl _ tbl :: r => tbl ++ get_labels r
    | _ :: r => get_labels r
  end.

Lemma step_t_labeled_jump :
  forall instr rs m rs' m' bits b ofs f md md',
    step_t (instr :: nil) ge (State_bits rs m md) E0 (State_bits rs' m' md') ->
    (exists l, labeled_jump instr l) ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,ofs) ->
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    (exists i l, goto_label_bits md f l b rs m = Nxt rs' m' md' /\
                 find_instr (Int.unsigned ofs) (fn_code f) = Some i /\
                 is_label_instr i l
    )
    \/ (State_bits (nextinstr rs) m md = State_bits rs' m' md').
Proof.
  intros.
  break_exists.
  destruct instr; simpl in H0; try inv_false; subst.
  * inv H. inv H11.
    inv H6. invs; repeat unify_PC; repeat unify_psur;
            unfold fundef in *;
            repeat unify_find_funct_ptr;
            find_one_instr.
    left. 
    simpl in H23.
    eexists; eexists; split; eauto.
    split. rewrite H17. rewrite H10.
    rewrite find_instr_append_head by omega.
    simpl. reflexivity. simpl. reflexivity.
  * inv H. inv H11.
    inv H6. invs; repeat unify_PC; repeat unify_psur;
            unfold fundef in *;
            repeat unify_find_funct_ptr;
            find_one_instr.
    simpl in H23.
    break_match_hyp; inv H23.
    break_match_hyp; inv H0.
    left. 
    eexists; eexists; split; eauto.
    split. rewrite H17. rewrite H10.
    rewrite find_instr_append_head by omega.
    simpl. reflexivity. simpl. reflexivity.
    right. reflexivity.
  * inv H. inv H11.
    inv H6. invs; repeat unify_PC; repeat unify_psur;
            unfold fundef in *;
            repeat unify_find_funct_ptr;
            find_one_instr.
    simpl in H23.
    break_match_hyp; inv H23.
    break_match_hyp; inv H0.
    break_match_hyp; inv H2.
    break_match_hyp; inv H0.
    left. 
    eexists; eexists; split; eauto.
    split. rewrite H17. rewrite H10.
    rewrite find_instr_append_head by omega.
    simpl. reflexivity. simpl. reflexivity.
    right. reflexivity.
    break_match_hyp; inv H2.
    right. reflexivity.    
  * inv H. inv H12.
    inv H7. invs; repeat unify_PC; repeat unify_psur;
            unfold fundef in *;
            repeat unify_find_funct_ptr;
            find_one_instr.
    simpl in H24.
    repeat break_match_hyp; try st_inv.
    left. 
    eexists; eexists; split; eauto.
    split. rewrite H11. rewrite H18.
    rewrite find_instr_append_head by omega.
    simpl. reflexivity. simpl.
    app list_nth_z_in Heqo.
Qed.

Lemma step_through_at :
  forall z c ge st t st',
    step_through z c ge st t st' ->
    at_code z c 0 ge st.
Proof.
  intros. inv H; eauto.
Qed.

Lemma step_through_at_end :
  forall ge z c st t st',
    step_through z c ge st t st' ->
    at_code_end z c ge st'.
Proof.
  intros. inv H.
  eauto. eauto.
Qed.

Lemma star_to_step :
  forall z c ge st t st',
    star (step_in z c) ge st t st' ->
    star step_bits ge st t st'.
Proof.
  induction 1; intros.
  eapply star_refl; eauto.
  inv H. eapply star_left; eauto.
Qed.

Lemma step_through_plus_step :
  forall z c ge st t st',
    step_through z c ge st t st' ->
    plus (step_bits) ge st t st'.
Proof.
  intros. inv H.
  eapply plus_one; eauto.
  rewrite st_in_eq in H3. break_and.
  app star_to_step H.
  eapply plus_left; eauto.
  eapply star_right; eauto.
Qed.

(* should this be here? Probably not *)
(* will we move it? Probably not *)
Lemma no_ptr_preserved_step_through:
  forall z c rs m t rs' m' md md',
    step_through z c (Genv.globalenv p) (State_bits rs m md) t (State_bits rs' m' md') ->
    (no_ptr_regs rs /\ no_ptr_mem m) ->
    no_ptr_regs rs' /\ no_ptr_mem m'.
Proof.
  intros. inv H.
  break_and.
  eapply NoPtr.no_ptr_regs_preserved in H2; eauto.

  rewrite st_in_eq in H4. break_and.
  app star_to_step H.
  destruct stB. destruct stC.

  clear H6.
  break_and.
  app NoPtr.no_ptr_regs_preserved H3.
  eapply NoPtr.no_ptr_regs_preserved_star in H; try reflexivity; try assumption.
  app NoPtr.no_ptr_regs_preserved H5;
    break_and; eauto.
Qed.

Lemma at_code_to_start :
  forall c z ofs rs m md,
    at_code z c ofs ge (State_bits rs m md) ->
    exists z' i,
      at_code z' (i :: nil) 0 ge (State_bits rs m md) /\ In i c.
Proof.
  induction c; intros.

  inv H.
  inv H5.
  unfold zlen in *.
  simpl in *.
  omega.

  inv H.
  assert (ofs = 0 \/ ofs > 0) by omega.
  break_or.

  exists (zlen c1).
  exists a.
  split.
  econstructor; eauto.
  simpl in *. eauto.
  simpl. left. reflexivity.

  assert (at_code (zlen (c1 ++ a :: nil)) c (ofs - 1) ge (State_bits rs m md)).
  {
    econstructor; eauto.
    rewrite zlen_app.
    rewrite zlen_cons.
    simpl.
    omega.
    rewrite zlen_cons in *.
    omega.
    
    rewrite H12.
    repeat rewrite app_ass.
    simpl.
    eauto.
  }
  
  app IHc H.
  break_and.
  eexists.
  eexists.
  split; eauto.
  simpl.
  right.
  auto.
Qed.

Lemma step_at_step_t' :
  forall z c ofs st st' t,
    at_code z c ofs ge st ->
    step_bits ge st t st' ->
    exists i,
      step_t (i :: nil) ge st t st' /\ In i c.
Proof.
  intros.
  destruct st.
  apply at_code_to_start in H.
  destruct H as (z').
  destruct H as (i).
  exists i.
  split.
  replace t with (t ** E0) by (apply E0_right).
  econstructor.
  break_and.
  eassumption.
  eassumption.
  constructor.
  break_and.
  assumption.
Qed.

Lemma straightline_step_t :
  forall ge rs m rs' m' i t bits b ofs f md md',
    step_t (i :: nil) ge (State_bits rs m md) t (State_bits rs' m' md') ->
    straightline i ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,ofs) ->
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    exec_instr_bits ge md f i b rs m = Nxt rs' m' md'.
Proof.
  intros. inv H. inv H6.
  inv H12.
  inv H7; repeat unify_PC; repeat unify_psur; repeat unify_find_funct_ptr;
  try find_one_instr; eauto; simpl in *; try inv_false.
Qed.

Lemma straightlineish_step_t :
  forall ge rs m rs' m' i t bits b ofs f md md',
    step_t (i :: nil) ge (State_bits rs m md) t (State_bits rs' m' md') ->      
    rs' PC = (nextinstr rs) PC ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,ofs) ->
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    no_trace i ->
    exec_instr_bits ge md f i b rs m = Nxt rs' m' md'.
Proof.
  intros.
  rename H4 into Hno_trace.
  inv H. inv H6.
  inv H12.
  inv H7; repeat unify_PC; repeat unify_psur; repeat unify_find_funct_ptr;
  try find_one_instr; eauto; simpl in *; try inv_false.        
Qed.  

Lemma straightlineish_step_fundef :
  forall ge rs m rs' m' i t bits b ofs md md',
    step_t (i :: nil) ge (State_bits rs m md) t (State_bits rs' m' md') ->
    rs' PC = (nextinstr rs) PC ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,ofs) ->
    exists f,
      Genv.find_funct_ptr ge b = Some (Internal f).
Proof.
  intros. inv H. inv H11.
  inv H5. unify_PC. unify_psur. eauto.
Qed.  

Lemma straightline_step_fundef :
  forall ge rs m rs' m' i t bits b ofs md md',
    step_t (i :: nil) ge (State_bits rs m md) t (State_bits rs' m' md') ->
    straightline i ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,ofs) ->
    exists f,
      Genv.find_funct_ptr ge b = Some (Internal f).
Proof.
  intros. inv H. inv H11.
  inv H5. unify_PC. unify_psur. eauto.
Qed.  

(* (* No longer true *) *)
(* Lemma straightlineish_exec : *)
(*   forall rs rs' bits b ofs md, *)
(*     rs PC = Vint bits -> *)
(*     psur md bits = (b,ofs) -> *)
(*     rs' PC = (nextinstr rs) PC -> *)
(*     exists bits', *)
(*       rs' PC = Vint bits' /\ psur bits' = (b,Int.add ofs Int.one). *)
(* Proof. *)
(*   intros. *)
(*   P preg_simpl_hyp nextinstr. *)
(*   rewrite H in H1. *)
(*   simpl in H1.     *)
(*   eexists; split; eauto. *)
(*   eapply psur_add; eauto. *)
(* Qed. *)

Lemma at_code_to_nil:
  forall z x c ge st,
    at_code z (x :: c) 0 ge st ->
    at_code z (x :: nil) 0 ge st.
Proof.
  intros.
  inv H.
  econstructor.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  instantiate (1 := (c ++ c2)).
  eauto.
Qed.
  

Lemma at_code_straightlineish_end :
  forall z x rs rs' m m' t c md md',
    True ->
    rs' PC = (nextinstr rs) PC ->
    at_code z (x :: c) 0 (Genv.globalenv p) (State_bits rs m md) ->
    step_bits (Genv.globalenv p) (State_bits rs m md) t (State_bits rs' m' md') ->
    at_code_end z (x :: nil) (Genv.globalenv p) (State_bits rs' m' md').
Proof.
  intros.
  apply at_code_to_nil in H1.
  inv H1.
  assert (Hmatch : match_metadata md m) by (invs; auto).
  assert (Hgp: global_perms (Genv.globalenv p) m) by (invs; auto).

  preg_simpl_hyp H0.
  rewrite H6 in *.
  simpl in H0.

  app md_extends_step H2.
  app step_match_metadata H1.
  app global_perms_step H3.

  assert (Hfind : exists x, find_instr (Int.unsigned i) (fn_code fd) = Some x). {
    rewrite H8. rewrite H15. rewrite find_instr_append_head by omega.
    simpl. eauto.
  }

  break_exists.
  
  assert (Hi : Int.unsigned (Int.add i Int.one) = Int.unsigned i + 1). {
    rewrite Int.add_unsigned. rewrite Int.unsigned_one.
    erewrite unsigned_repr_PC; eauto. left.
    instantiate (1 := x0).
    replace (Int.unsigned i + 1 - 1) with (Int.unsigned i) by omega.
    eauto.
  }
  idtac.  (* damnit indenting *)
  
  
  name H7 Hpsur.
  eapply psur_add_one in Hpsur; eauto.
  econstructor; eauto.

  rewrite Hi. rewrite zlen_cons in *. simpl in *. omega.
  unfold in_code_range.
  unfold fundef in *.
  collapse_match. rewrite H8.
  rewrite H15.
  repeat rewrite zlen_app.
  repeat rewrite zlen_cons.
  replace (@zlen instruction nil) with 0 by auto.
  name (zlen_nonneg _ c1) zlnc1.
  name (zlen_nonneg _ c2) zlnc2.
  
  omega.
  eapply in_range_PC; eauto.
Qed.
  
Lemma at_code_straightlineish :
  forall z x rs rs' m m' t c md md',
    True ->
    rs' PC = (nextinstr rs) PC ->
    at_code z (x :: c) 0 (Genv.globalenv p) (State_bits rs m md) ->
    step_bits (Genv.globalenv p) (State_bits rs m md) t (State_bits rs' m' md') ->
    zlen c > 0 ->
    at_code (z + 1) c 0 (Genv.globalenv p) (State_bits rs' m' md').
Proof.
  intros.
  name H1 Ha.
  apply at_code_to_nil in H1.
  rename H3 into Hz.
  inv H1.

  replace (zlen c1 + 1) with (zlen (c1 ++ x :: nil)) by (rewrite zlen_app;
                                                         rewrite zlen_cons;
                                                         simpl; omega).

  assert (Hmatch : match_metadata md m) by (invs; auto).
  assert (Hgp: global_perms (Genv.globalenv p) m) by (invs; auto).

  app md_extends_step H2.
  app step_match_metadata H1.
  app global_perms_step H3.

  assert (Hfind : exists x, find_instr (Int.unsigned i) (fn_code fd) = Some x). {
    rewrite H8. rewrite H15. rewrite find_instr_append_head by omega.
    simpl. eauto.
  }

  break_exists.
  
  assert (Hi : Int.unsigned (Int.add i Int.one) = Int.unsigned i + 1). {
    rewrite Int.add_unsigned. rewrite Int.unsigned_one.
    erewrite unsigned_repr_PC; eauto. left.
    instantiate (1 := x0).
    replace (Int.unsigned i + 1 - 1) with (Int.unsigned i) by omega.
    eauto.
  }
  idtac.  (* damnit indenting *)

  name H7 Hpsur.
  eapply psur_add_one in H7; eauto.
  
  preg_simpl_hyp H0.
  rewrite H6 in H0.
  simpl in H0.

  
  inv Ha. repeat unify_PC. repeat unify_psur.
  unify_find_funct_ptr.
  
  econstructor; eauto; try omega.
  rewrite Hi. rewrite (zlen_app). rewrite zlen_cons. simpl. omega.
  rewrite H24 in H15. replace ((x :: c) ++ c4) with ((x :: nil) ++ (c ++ c4)) in H15 by (simpl; auto).
  eapply list_eq_middle_therefore_eq in H15; eauto. break_and; subst.
  rewrite H24. simpl. repeat rewrite app_ass. simpl. reflexivity.

  unfold in_code_range. unfold fundef in *.
  collapse_match.
  
  rewrite H8. rewrite H15. repeat rewrite zlen_app. repeat rewrite zlen_cons.
  replace (@zlen instruction nil) with 0 by auto.
  name (zlen_nonneg _ c1) zlnc1.
  name (zlen_nonneg _ c2) zlnc2.
  omega.
  eapply in_range_PC; eauto.
Qed.


Lemma step_t_md_extends :
  forall l ge rs m md t rs' m' md',
    step_t l ge (State_bits rs m md) t (State_bits rs' m' md') ->
    md_extends md md'.
Proof.
  induction l; intros.
  inv H. econstructor.
  inv H. destruct st'.
  app IHl H8.
  app md_extends_step H3.
  eapply ex_trans; eauto.
Qed.
    


Lemma step_t_md :
  forall l ge rs m md t rs' m' md',
    l <> nil ->
    step_t l ge (State_bits rs m md) t (State_bits rs' m' md') ->
    match_metadata md m /\ match_metadata md' m'.
Proof.
  induction l; intros; try congruence.
  inv H0. destruct l.
  * inv H9. eapply step_md; eauto.
  * destruct st'. app IHl H9; try congruence.
    break_and. app step_md H4; intuition idtac.
Qed.


Lemma step_t_gp :
  forall l ge rs m md t rs' m' md',
    l <> nil ->
    step_t l ge (State_bits rs m md) t (State_bits rs' m' md') ->
    global_perms ge m /\ global_perms ge m'.
Proof.
  induction l; intros.
  congruence.
  inv H0. destruct l.
  * inv H9. eapply step_gp; eauto.
  * destruct st'. app IHl H9; try congruence.
    break_and.
    app step_gp H4; intuition idtac.
Qed.


End ST_IN.