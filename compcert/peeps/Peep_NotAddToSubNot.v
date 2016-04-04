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

Definition peep_not_add_to_sub_not_example :=
  Pnot EAX ::
         Padd_rr EAX ECX ::
         nil.

Section NOT_ADD_TO_SUB_NOT.

  Variable concrete : code.

  Variable r1 : ireg.
  Variable r2 : ireg.
  Hypothesis r1_r2_neq : r1 <> r2.

  Definition peep_not_add_to_sub_not_defs : rewrite_defs :=
    {|
      fnd :=
        Pnot r1 ::
             Padd_rr r1 r2 ::
             nil
      ; rpl :=        
          Psub_rr r1 r2 ::
                  Pnot r1 ::
                  nil
      ; lv_in := PC :: IR r1 :: IR r2 :: nil
      ; lv_out := PC :: IR r1 :: nil
      ; clobbered := flags
    |}.
  
  Lemma peep_not_add_to_sub_not_selr :
    StepEquiv.step_through_equiv_live (fnd peep_not_add_to_sub_not_defs) (rpl peep_not_add_to_sub_not_defs) (lv_in peep_not_add_to_sub_not_defs) (lv_out peep_not_add_to_sub_not_defs).
  Proof.
    prep_l.
    step_l.
    step_l.
    prep_r.
    step_r.
    step_r.
    finish_r.
    prep_eq'.
    - subst_max.
      preg_simpl.
      repeat find_rewrite_goal.
      simpl.
      auto.
    - subst_max.
      preg_simpl.
      unfold Val.add.
      unfold Val.notint.
      unfold Val.sub.        
      repeat (break_match_sm); simpl; intros; try congruence; P0 _simpl val_eq;
      try inv_false.
      repeat inv_vint.
      f_equal.
      repeat rewrite Int.not_neg.
      ring.      
  Qed.

  Definition peep_not_add_to_sub_not_proofs : rewrite_proofs :=
    {|
      defs := peep_not_add_to_sub_not_defs
      ; selr := peep_not_add_to_sub_not_selr
    |}.

  Definition peep_not_add_to_sub_not :
    concrete = fnd peep_not_add_to_sub_not_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite peep_not_add_to_sub_not_defs peep_not_add_to_sub_not_proofs.   
  Qed.

End NOT_ADD_TO_SUB_NOT.

Definition peep_not_add_to_sub_not_rewrite (c : code) : option StepEquiv.rewrite.  
  name peep_not_add_to_sub_not p.
  unfold peep_not_add_to_sub_not_defs in p.
  simpl in p. 
  specialize (p c).
  do 2 set_code_cons c.
  set_code_nil c.
  set_instr_eq i 0%nat peep_not_add_to_sub_not_example.
  set_instr_eq i0 1%nat peep_not_add_to_sub_not_example.
  set_ireg_eq rd rd0.
  set_ireg_neq rd0 r1.
  specialize (p _ _ n eq_refl). exact (Some p).
Defined.

Definition not_add_to_sub_not (c : code) : list StepEquiv.rewrite :=
  collect (map peep_not_add_to_sub_not_rewrite (ParamSplit.matched_pat peep_not_add_to_sub_not_example c)).
