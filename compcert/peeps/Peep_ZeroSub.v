Require Import Coqlib.
Require Import Asm.
Require Import PeekTactics.
Require Import PeepsLib.
Require Import PregTactics.
Require Import StepIn.
Require Import AsmBits.
Require Import Values.
Require Import ValEq.
Require Import Integers.
Require Import PeepsTactics.

(* 599 hw bonus problem *)

(* 
        xorl    %eax, %eax
        subl    %esi, %eax
        leal    0(%ebx,%eax,1) %eax

==>
        subl    %esi, %ebx
        movl    %ebx, %eax

*)

Definition peep_zero_sub_example : code :=
  Pxor_r EAX :: Psub_rr EAX EAX :: Plea EAX (Addrmode None None (inl Int.one)) :: nil.

Section ZERO_SUB.

  Variable concrete : code.

  Variable r1 : ireg.
  Variable r2 : ireg.
  Variable r3 : ireg.

  Definition a1 := Addrmode (Some r3) (Some (r1, Int.one)) (inl Int.zero).
  
  Hypothesis neq12 : r1 <> r2.
  Hypothesis neq23 : r2 <> r3.
  Hypothesis neq13 : r1 <> r3.
  
  Definition peep_zero_sub_defs : rewrite_defs :=
    {|
      fnd :=
        Pxor_r r1 ::
        Psub_rr r1 r2 ::
        Plea r1 a1 ::
        nil
      ; rpl :=
          Psub_rr r3 r2 ::
          Pmov_rr r1 r3 ::
          Pnop ::
          nil
      ; lv_in := IR r2 :: IR r3 :: PC :: nil
      ; lv_out := IR r1 :: IR r2 :: PC :: nil
      ; clobbered := IR r3 :: flags
    |}.
  
  Lemma sub_no_pointer :
    forall x y,
      (forall b ofs, x <> Vptr b ofs) ->
      (forall b ofs, y <> Vptr b ofs) ->
      (forall b ofs, Val.sub x y <> Vptr b ofs).
  Proof.
    intros.
    destruct x; destruct y; simpl; congruence.
  Qed.
  
  Lemma peep_zero_sub_selr :
    StepEquiv.step_through_equiv_live (fnd peep_zero_sub_defs) (rpl peep_zero_sub_defs) (lv_in peep_zero_sub_defs) (lv_out peep_zero_sub_defs).
  Proof.
    prep_l.   
    step_l.
    step_l.
    step_l.
    prep_r.    
    step_r.
    step_r.
    step_r.
    finish_r.
    prep_eq.
    split.    
    2: eq_mem_tac.
    intros.
    simpl_and_clear.
    Focus 2. rewrite Int.eq_true in Heqb0. congruence.
    clear H39. subst.
    repeat break_or; try inv_false;
    preg_simpl.

    (* r1 *)
    * 
      clear -H0 H4.
      destruct (rsl r2) eqn:?;
               destruct (rsl r3) eqn:?;
               simpl in *;
        try solve [eapply sub_no_pointer; eauto];
        try solve [
              destruct (rsr r2) eqn:?;
               destruct (rsr r3) eqn:?;
               simpl in *;
              congruence].
      
      rewrite <- H4.
      rewrite <- H0.
      simpl. f_equal.
      ring.

    (* r2 *)
    * assumption.
    (* PC *)
    * clear -H2 H16.
      rewrite H2. rewrite H16.
      repeat (eapply val_eq_add);
        solve [simpl; auto].

  Qed.

  Definition peep_zero_sub_proofs : rewrite_proofs :=
    {|
      defs := peep_zero_sub_defs
      ; selr := peep_zero_sub_selr
    |}.

  Definition peep_zero_sub : 
    concrete = fnd peep_zero_sub_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite peep_zero_sub_defs peep_zero_sub_proofs.
  Qed.

End ZERO_SUB.

Definition peep_zero_sub_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_zero_sub p.
  unfold peep_zero_sub_defs in p.
  simpl in p. 
  specialize (p c).    
  set_code_cons c.
  set_code_cons c.
  set_code_cons c.
  set_code_nil c.
  set_instr_eq i 0%nat peep_zero_sub_example.
  set_instr_eq i0 1%nat peep_zero_sub_example.
  set_instr_eq i1 2%nat peep_zero_sub_example.
  destruct a. unfold a1 in p.
  destruct base; [ | exact None].
  destruct ofs; [ | exact None].
  destruct const; [ | exact None].
  set_int_eq i0 Int.zero.
  destruct p0.
  specialize (p rd r1 i).
  set_ireg_eq rd rd0.
  set_ireg_eq rd0 rd1.
  set_ireg_eq rd1 i0.
  set_int_eq i1 Int.one.
  set_ireg_neq i0 r1.
  set_ireg_neq r1 i.
  set_ireg_neq i0 i.
  specialize (p n n0 n1 eq_refl).
  exact (Some p).
Defined.

Definition zero_sub (c : code) : list StepEquiv.rewrite :=
  collect (map peep_zero_sub_rewrite (ParamSplit.matched_pat peep_zero_sub_example c)).

