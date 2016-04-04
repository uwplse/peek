Require Import Coqlib.
Require Import Asm.
Require Import Integers.
Require Import PeekTactics.
Require Import PeepsLib.
Require Import PregTactics.
Require Import StepIn.
Require Import AsmBits.
Require Import Values.
Require Import ValEq.
Require Import Integers.
Require Import PeepsTactics.
Require Import UseBasic.
Require Import StepEquiv.
Require Import ForwardJumps.
Require Import MemEq.
Require Import Globalenvs.
(* 
        movl    %eax, 56(%esp)
        movl    56(%esp), %edx
        andl    $15, %edx
        movl    0(%ecx,%edx,4), %eax

==> 
        movl    %eax, 56(%esp)
        andl    $15, %eax
        movl    0(%ecx,%eax,4), %eax

 *)

Definition example_addr : addrmode := (Addrmode None None (inl Int.zero)).

Definition peep_hmac_load_elim_example :=
        Pmov_mr example_addr EAX :: 
                Pmov_rm EAX example_addr ::
                Pand_ri EAX Int.zero ::
                Pmov_rm EAX example_addr :: nil.

Section HMAC_LOAD_ELIM.

  Variable concrete : code.

  Variable i : int.
  Variable r1 r2 : ireg.
  Variable a1 : addrmode.

  Variable r3 : ireg.

  Hypothesis neq : r3 <> r1.
  Hypothesis neq2 : r2 <> r3.
  
  Definition a2 := Addrmode (Some r3) (Some (r2, (Int.repr 4))) (inl Int.zero).
  Definition a2' := Addrmode (Some r3) (Some (r1, (Int.repr 4))) (inl Int.zero).

  Hypothesis addr_indep_1 : ~ (In (IR r1) (use_addr a1)).
  Hypothesis addr_indep_2 : ~ (In (IR r2) (use_addr a1)).
  Hypothesis addr_indep_3 : ~ (In (IR r3) (use_addr a1)).
  

  Lemma eval_a2_same :
    forall ge ge2 md (rs rs' : regset) b ofs,
      val_eq (rs r3) (rs' r3) ->
      val_eq (rs r2) (rs' r1) ->
      eval_addrmode_bits ge md a2 rs = Vptr b ofs ->
      eval_addrmode_bits ge2 md a2' rs' = Vptr b ofs.
  Proof.
    intros.
    app val_eq_or H.
    app val_eq_or H0.
    repeat break_or;
    unfold eval_addrmode_bits in *;
    unfold eval_addrmode in *;
    unfold a2 in *; unfold a2' in *;
    rewrite H4 in *; rewrite H0 in *;
    simpl in *; try congruence.
    replace (if Int.eq (Int.repr 4) Int.one then Vundef else Vundef) with Vundef in H1 by (break_match; reflexivity).
    simpl in *.
    rewrite Val.add_commut in H1. simpl in H1.
    congruence.
  Qed.
  
  Definition peep_hmac_load_elim_defs : rewrite_defs :=
    {|
      fnd := Pmov_mr a1 r1 ::
                     Pmov_rm r2 a1 ::
                     Pand_ri r2 i ::
                     Pmov_rm r1 a2 :: nil
      ; rpl := Pmov_mr a1 r1 ::
                       Pand_ri r1 i ::
                       Pmov_rm r1 a2' :: Pnop :: nil
      ; lv_in := PC :: IR r1 :: IR r3 :: use_addr a1
      ; lv_out := PC :: IR r1 :: IR r3 :: use_addr a1
      ; clobbered := IR r2 :: flags
    |}.

  Lemma eq_mem_exec_load_bits :
    forall md ml mr,
      mem_eq md ml mr ->
      forall addr rsr rsl,
        (forall reg, In reg (use_addr addr) -> val_eq (rsl reg) (rsr reg)) ->
        forall ge1 ge2 c reg rsl' ml' md',
          val_eq (rsl reg) (rsr reg) ->
          (forall id ofs, Genv.symbol_address ge1 id ofs = Genv.symbol_address ge2 id ofs) ->
          exec_load_bits ge1 md c ml addr rsl reg = Nxt rsl' ml' md' ->
          exists rsr' mr',
            exec_load_bits ge2 md c mr addr rsr reg = Nxt rsr' mr' md' /\ mem_eq md' ml' mr'.
  Proof.
    intros.
    unfold exec_load_bits in *.
    unfold Memory.Mem.loadv in *.
    repeat (break_match_hyp; try congruence); try state_inv.
    app use_addr_eval_addrmode_bits Heqv0; try congruence; try apply H0.
    erewrite eval_addrmode_bits_transf in Heqv0; eauto.
    collapse_match.
    app eq_mem_load Heqo. break_and.
    collapse_match.
    eauto.
  Qed.

  Lemma eval_addrmode_bits_nextinstr_nf :
    forall ge md a rs v,
      eval_addrmode_bits ge md a rs = v ->
      eval_addrmode_bits ge md a (nextinstr_nf rs) = v.
  Proof.
    intros.
    unfold eval_addrmode_bits in *.
    unfold eval_addrmode in *.
    destruct a; simpl in H;
    destruct base; destruct ofs; destruct const;
    simpl in H; try destruct p; simpl in H;
    try destruct (rs i0) eqn:?; simpl in *;
    unfold nextinstr_nf; unfold nextinstr;
    preg_simpl; try rewrite Heqv0; simpl; auto.
  Qed.
    

  Lemma val_eq_eval_addrmode_bits :
    forall md ge1 ge2,
      (forall id ofs,
         Genv.symbol_address ge1 id ofs = Genv.symbol_address ge2 id ofs) ->
      forall rs rs' a b ofs,
        (forall r, In r (use_addr a) -> val_eq (rs r) (rs' r)) ->
        eval_addrmode_bits ge1 md a rs = Vptr b ofs ->
        eval_addrmode_bits ge2 md a rs' = Vptr b ofs.
  Proof.
    intros.
    erewrite eval_addrmode_bits_transf in H1; eauto.
    app use_addr_eval_addrmode_bits H1; congruence.
  Qed.

  Lemma val_eq_store_load :
    forall m b ofs v m' v' vr,
      MemBits.store_bits AST.Mint32 m b ofs v = Some m' ->
      Memory.Mem.load AST.Mint32 m' b ofs = Some v' ->
      val_eq v vr ->
      val_eq v' vr.
  Proof.
    intros.
    app load_store_bits_same H0.
  Qed.

  Lemma ireg_nextinstr_nf_lookup :
    forall (r : ireg) rs,
      nextinstr_nf rs r = rs r.
  Proof.
    intros. preg_simpl. auto.
  Qed.

  Lemma use_addr_ireg :
    forall (r : preg) a,
      In r (use_addr a) ->
      exists (i : ireg),
        IR i = r.
  Proof.
    intros.
    destruct a; destruct base; destruct ofs; try destruct p;
    destruct const; simpl in H; eauto; repeat break_or; try inv_false; eauto.
  Qed.
  
  Lemma peep_hmac_load_elim_selr :
    StepEquiv.step_through_equiv_live (fnd peep_hmac_load_elim_defs) (rpl peep_hmac_load_elim_defs) (lv_in peep_hmac_load_elim_defs) (lv_out peep_hmac_load_elim_defs).
  Proof.
    prep_l.
    step_l.
    step_l.
    step_l.
    step_l.
    prep_r.

    prep_exec_instr.

    (* solve store precondition *)
    simpl in *.
    NP _app eq_mem_exec_store_bits exec_store_bits.
    break_and.
    repeat eexists; intros. eassumption.
    (* done solving store precond *)

    repeat break_exists.
    step_r.
    step_r.
    prep_exec_instr.

    (* solve load precond *)

    (* first extract mem_eq from last store *)
    simpl in H48.
    copy H48.
    eapply eq_mem_exec_store_bits in H48; try eassumption.
    repeat break_exists.
    break_and.
    simpl. 
    specialize (H4 x1).
    simpl in H4.
    erewrite H48 in H4. inv H4.
    (* done getting mem_eq *)

    (* need the fact that we loaded what we stored on the left *)
    simpl in H47. unfold exec_load_bits in H47.
    unfold Memory.Mem.loadv in H47.
    repeat (break_match_hyp; try congruence).
    assert (Hv : val_eq v (rsr r1)). {

      inv H47.
      unfold exec_store_bits in H37.
      unfold storev_bits in H37.
      repeat (break_match_hyp; try congruence).
      inv H37. inv H43.
      assert (Hptr_eq : Vptr b1 i2 = Vptr b0 i1).
      {
        app eval_addrmode_bits_nextinstr_nf Heqv1.
        rewrite Heqv1 in Heqv0. congruence.
      } idtac.

      inv Hptr_eq.

      app load_store_bits_same Heqo0.

    } idtac.

    simpl in H45. unfold exec_load_bits in H45.
    break_match_hyp; try congruence. inv H45.
    inv H43. inv H47.
    unfold Memory.Mem.loadv in Heqo0.
    break_match_hyp; try congruence.
    unfold exec_load_bits. unfold Memory.Mem.loadv.
    
    app eval_addrmode_bits_nextinstr_nf Heqv1.
    bump Heqv1.
    (* first unify a3 with prev alloc metadata *)
    unfold exec_store_bits in H48.
    unfold storev_bits in H48.
    repeat (break_match_hyp; try congruence).
    inv H48.
    bump H43.

    app eval_a2_same H45.
    rewrite H45.
    bump H37.    
    unfold exec_store_bits in H47.
    unfold storev_bits in H47.
    repeat break_match_hyp; try congruence. inv H47.
    simpl in H46.
    inv H46.
    app eq_mem_load Heqo0. break_and. collapse_match.
    eauto.


    preg_simpl.
    bump H46. simpl in H47. inv H47.
    unfold exec_store_bits in H37. unfold storev_bits in H37.
    repeat break_match_hyp; try congruence. inv H37.


    repeat (repeat rewrite ireg_nextinstr_nf_lookup; repeat rewrite Pregmap.gso by congruence).
    assumption.



    preg_simpl.
    bump H46. simpl in H47. inv H47.
    unfold exec_store_bits in H37. unfold storev_bits in H37.
    repeat break_match_hyp; try congruence. inv H37.
    repeat (repeat rewrite ireg_nextinstr_nf_lookup; repeat rewrite Pregmap.gso by congruence; repeat rewrite Pregmap.gss).
    eapply val_eq_and; eauto. simpl. reflexivity.
    
    
    repeat break_exists.
    step_r.
    step_r.
    finish_r'.
    
    prep_eq.


    repeat match goal with
             | [ H : exec_instr_bits _ _ _ _ _ _ _ = _ |- _ ] =>
               simpl in H
             | [ H : exec_store_bits _ _ _ _ _ _ _ _ = _ |- _ ] =>
               unfold exec_store_bits in H;
                 unfold storev_bits in H;
                 repeat break_match_hyp; try congruence; inv H
             | [ H : exec_load_bits _ _ _ _ _ _ _ = _ |- _ ] =>
               unfold exec_load_bits in H;
                 unfold Memory.Mem.loadv in H;
                 repeat break_match_hyp; try congruence; inv H
           end.
    state_inv.
    app val_eq_eval_addrmode_bits Heqv.
    rewrite Heqv0 in Heqv. inv Heqv.
    app eq_mem_store Heqo. break_and.
    rewrite H15 in Heqo0. inv Heqo0.
    bump Heqo1; bump Heqo2; bump Heqo3.
    bump Heqv1. bump Heqv2. bump Heqv3.

    app eval_addrmode_bits_nextinstr_nf H13.
    rewrite H45 in H13. inv H13.


    assert (Hve: val_eq v0 (rsr r1)).
    {
      app eval_a2_same H46. rewrite H46 in H43.
      Focus 2. preg_simpl. assumption.
      Focus 2. preg_simpl. eapply val_eq_and; simpl; auto.
      app val_eq_store_load H14; try apply H37; eauto. inv H43.
      app val_eq_store_load H14; try apply H37; eauto.
      
    } idtac.

    split; intros; auto.
    break_or; subst_max.
    
    (* PC *)
    preg_simpl.
    repeat eapply val_eq_add; unfold Vone; simpl; eauto.
    rewrite H2. rewrite H17.
    simpl. reflexivity.

    (* r1 *)
    break_or; subst_max.
    preg_simpl.
    app eval_a2_same H46.
    rewrite H46 in H43. inv H43.
    app eq_mem_load H38.
    break_and. congruence.

    preg_simpl. assumption.
    preg_simpl. eapply val_eq_and; preg_simpl; auto.
    
    (* r3 *)
    break_or; subst_max; try inv_false.
    preg_simpl. assumption.

    (* a1 *)
    destruct (preg_eq reg r1); try congruence.
    destruct (preg_eq reg r2); try congruence.
    destruct (preg_eq reg r3); try congruence.


    app use_addr_ireg H48.
    subst reg. preg_simpl.
    eapply H5; eauto.

    Grab Existential Variables.
    assumption. assumption.
  Qed.

  Definition peep_hmac_load_elim_proofs : rewrite_proofs :=
    {|
      defs := peep_hmac_load_elim_defs
      ; selr := peep_hmac_load_elim_selr
    |}.

      Ltac step_pres :=
        NP1 _app step_through_current_instr step_through;
        NP1 _app brk_step_through_straightline step_through;
        match goal with
          | [ |- peep_code _ ] => solve [repeat (eapply peep_code_cons; simpl; auto); try eapply peep_code_nil]
          | [ |- _ ] => try solve [simpl; eauto]
        end;
        simpl in *;        
        repeat break_and;

        try solve [
              unfold only_forward_jumps;
              split; try split;

              [ unfold no_calls; intros;
                NP1 apex find_instr_in find_instr; simpl in *; repeat break_or; try subst; try tauto |

                unfold no_trace_code; intros;
                NP1 apex find_instr_in find_instr; simpl in *; repeat break_or; try subst; simpl; try tauto | 

                intros; unfold only_forward_jumps_lab;
                intros; NP1 apex find_instr_in find_instr;
                simpl in *; repeat break_or; try inv_false; try congruence ]].


      Lemma break_not_in_cons :
        forall {A} r (x : A) f,
          ~ In x (f :: r) ->
          x <> f /\ ~ In x r.
      Proof.
        induction r; intros.
        simpl in H. split.
        intro.
        apply H. left. auto.
        intro. apply H. right. simpl in H0. auto.
        split; intro; apply H.
        subst. simpl. left. auto.
        simpl in H0. simpl.
        right. auto.
      Qed.

      Lemma break_not_in_app :
        forall {A} f r (x : A),
          ~ In x (f ++ r) ->
          ~ In x f /\ ~ In x r.
      Proof.
        induction f; intros.
        simpl in *.
        split; tauto.
        simpl in *.
        eapply Classical_Prop.not_or_and in H.
        break_and.
        use IHf; eauto. break_and.
        split; tauto.
      Qed.

      Ltac unify_current_instr :=
        match goal with
          | [ H : current_instr ?X ?Y = Some _, H2 : current_instr ?X ?Y = Some _ |- _ ] => rewrite H in H2; inv H2
        end.
      
  Definition peep_hmac_load_elim :
    concrete = fnd peep_hmac_load_elim_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite peep_hmac_load_elim_defs peep_hmac_load_elim_proofs.
    * 
      apply step_through_preserved_no_touch.
      - 
        simpl. unfold no_def. intros.
        simpl in *.

        unfold no_def_instr. intros.
        repeat break_or; subst; try inv_false;
        simpl in H1; repeat break_or;
        unfold peep_hmac_load_elim_defs; unfold preserved; simpl;
        rewrite <- Union.rem_in; intro; break_and; try apply H0;
        simpl; repeat (rewrite in_app; simpl); try tauto.
      - 
        unfold peep_hmac_load_elim_defs. simpl.
        unfold peep_code.
        intros. simpl in *.
        repeat break_or; try inv_false; subst; simpl; tauto.
    * 
      apply step_through_preserved_no_touch.
      -
        simpl. unfold no_def. intros.
        simpl in *.

        unfold no_def_instr. intros.
        repeat break_or; subst; try inv_false;
        simpl in H1; repeat break_or;
        unfold peep_hmac_load_elim_defs; unfold preserved; simpl;
        rewrite <- Union.rem_in; intro; break_and; try apply H0;
        simpl; repeat (rewrite in_app; simpl); try tauto.
      -
        unfold peep_hmac_load_elim_defs. simpl.
        unfold peep_code.
        intros. simpl in *.
        repeat break_or; try inv_false; subst; simpl; tauto.
Defined.

End HMAC_LOAD_ELIM.

Definition peep_hmac_load_elim_rewrite (c : code) : option StepEquiv.rewrite.

  name peep_hmac_load_elim p.
  unfold peep_hmac_load_elim_defs in p.
  simpl in p. 
  specialize (p c).
  do 4 set_code_cons c.
  set_code_nil c.
  set_instr_eq i 0%nat peep_hmac_load_elim_example.
  set_instr_eq i0 1%nat peep_hmac_load_elim_example.
  set_instr_eq i1 2%nat peep_hmac_load_elim_example.
  set_instr_eq i2 3%nat peep_hmac_load_elim_example.

  
  specialize (p n rs rd a).
  set_ireg_eq rd rd0.
  unfold a2 in p.
  destruct a1.
  destruct base; [ | exact None].
  specialize (p i).
  destruct ofs; [ | exact None].
  destruct p0.
  set_ireg_eq i0 rd0.
  set_int_eq i1 (Int.repr 4).
  destruct const; [ | exact None].
  set_int_eq i0 Int.zero.
  set_addrmode_eq a a0.
  simpl.
  set_ireg_eq rs rd1.
  set_ireg_neq i rd1.
  set_ireg_neq rd0 i.
  destruct (in_dec preg_eq rd1 (use_addr a0)); [ exact None | ].
  destruct (in_dec preg_eq rd0 (use_addr a0)); [ exact None | ].
  destruct (in_dec preg_eq i (use_addr a0)); [ exact None | ].
  refine (Some (p n0 n1 _ _ _ eq_refl)); eauto.
Defined.  


Definition hmac_load_elim (c : code) : list StepEquiv.rewrite :=
  collect (map peep_hmac_load_elim_rewrite (ParamSplit.matched_pat peep_hmac_load_elim_example c)).
