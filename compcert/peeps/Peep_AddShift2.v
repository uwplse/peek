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


Definition peep_add_to_sal_example :=
  Padd_rr EDX EDX :: nil.

Section ADD_TO_SAL.

  Variable concrete : code.
  Variable r1 : ireg.

  Definition peep_add_to_sal_defs : rewrite_defs :=
    {|
      fnd :=
        Padd_rr r1 r1 :: nil
      ; rpl := 
          Psal_ri r1 Int.one :: nil
      ; lv_in := IR r1 :: PC :: nil
      ; lv_out := IR r1 :: PC :: nil
      ; clobbered := flags
    |}.

  Lemma peep_add_to_sal_selr :
    StepEquiv.step_through_equiv_live (fnd peep_add_to_sal_defs) (rpl peep_add_to_sal_defs) (lv_in peep_add_to_sal_defs) (lv_out peep_add_to_sal_defs).
  Proof.    
    prep_l.
    step_l.
    prep_r.
    step_r.
    finish_r.
    prep_eq'.
    - preg_simpl.
      unfold Val.shl.
      unfold Val.add.
      repeat (break_match_sm); simpl; intros; try congruence.
      f_equal.
      P0 _simpl val_eq.
      inv_vint.
      replace (Int.add i1 i1) with (Int.mul i1 (Int.repr 2)) by ring.
      eapply Int.mul_pow2.
      unfold Int.one.
      erewrite <- Int.is_power2_two_p.
      simpl.
      f_equal.      
      vm_compute.      
      split; intros; congruence.
      clear -Heqb0.
      exfalso.
      vm_compute in *.
      congruence.
    - subst.
      preg_simpl.
      repeat find_rewrite_goal.
      simpl.
      auto.
  Qed.

  Definition peep_add_to_sal_proofs : rewrite_proofs :=
    {|
      defs := peep_add_to_sal_defs
      ; selr := peep_add_to_sal_selr
    |}.

  Definition peep_add_to_sal : 
    concrete = fnd peep_add_to_sal_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite peep_add_to_sal_defs peep_add_to_sal_proofs.
  Qed.

End ADD_TO_SAL.

Definition peep_add_to_sal_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_add_to_sal p.
  unfold peep_add_to_sal_defs in p.
  simpl in p. 
  specialize (p c).
  do 1 set_code_cons c.
  set_code_nil c.  
  set_instr_eq i 0%nat peep_add_to_sal_example.
  set_ireg_eq rd r1.
  specialize (p _ eq_refl). exact (Some p).
Defined.

Definition add_to_sal (c : code) : list StepEquiv.rewrite :=
  collect (map peep_add_to_sal_rewrite (ParamSplit.matched_pat peep_add_to_sal_example c)).
