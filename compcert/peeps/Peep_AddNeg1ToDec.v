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

Definition peep_add_neg_1_to_dec_example :=
  Padd_ri EAX (Int.neg Int.one) :: nil.

Section ADD_NEG_1_TO_DEC.

  Variable concrete : code.
  Variable r1 : ireg.  

  Definition peep_add_neg_1_to_dec_defs : rewrite_defs :=
    {|
      fnd := 
        Padd_ri r1 (Int.neg Int.one) :: nil
      ; rpl := 
          Pdec r1 :: nil
      ; lv_in := IR r1 :: PC :: nil
      ; lv_out := IR r1 :: PC :: nil
      ; clobbered := flags
    |}.
  
  Lemma peep_add_neg_1_to_dec_selr :
    StepEquiv.step_through_equiv_live (fnd peep_add_neg_1_to_dec_defs) (rpl peep_add_neg_1_to_dec_defs) (lv_in peep_add_neg_1_to_dec_defs) (lv_out peep_add_neg_1_to_dec_defs).
  Proof.    
    prep_l.
    step_l.
    prep_r.
    step_r.
    finish_r.
    prep_eq.
    split.
    2: eq_mem_tac.
    simpl_and_clear.
    eq_reg_tac.        
    unfold_val_int.
    simpl.
    break_match.
    simpl. intros.
    break_match.
    congruence.
    congruence.
    congruence.
    congruence.
    congruence.
    no_ptr_regs_tac.
    simpl.
    P0 _simpl val_eq.
    symmetry in H0.
    find_rewrite_goal.
    f_equal.
    ring.
    simpl.
    intros.
    P0 _simpl val_eq.
    symmetry in H0.
    find_rewrite_goal.
    congruence.
    simpl.
    intros.
    P0 _simpl val_eq.
    symmetry in H0.
    find_rewrite_goal.
    congruence.
    simpl.
    intros.
    P0 _simpl val_eq.
    symmetry in H0.
    find_rewrite_goal.
    congruence.
    P0 _simpl val_eq.
    exfalso; assumption.
  Qed.

  Definition peep_add_neg_1_to_dec_proofs : rewrite_proofs :=
    {|
      defs := peep_add_neg_1_to_dec_defs
      ; selr := peep_add_neg_1_to_dec_selr
    |}.

  Definition peep_add_neg_1_to_dec :
    concrete = fnd peep_add_neg_1_to_dec_defs -> StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite peep_add_neg_1_to_dec_defs peep_add_neg_1_to_dec_proofs.
  Qed.

End ADD_NEG_1_TO_DEC.

Definition peep_add_neg_1_to_dec_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_add_neg_1_to_dec p.
  unfold peep_add_neg_1_to_dec_defs in p.
  simpl in p. 
  specialize (p c).
  set_code_cons c.
  set_code_nil c.
  set_instr_eq i 0%nat peep_add_neg_1_to_dec_example.
  set_int_eq n (Int.neg Int.one).  
  specialize (p rd eq_refl). exact (Some p).
Defined.

Definition add_neg_1_to_dec (c : code) : list StepEquiv.rewrite :=
  collect (map peep_add_neg_1_to_dec_rewrite (ParamSplit.matched_pat peep_add_neg_1_to_dec_example c)).
