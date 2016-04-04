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

Definition peep_sub_neg_1_to_inc_example := Psub_ri EAX (Int.neg Int.one) :: nil.

Section SUB_NEG_1_TO_INC.

  Variable concrete : code.
  Variable r1 : ireg.

  Definition peep_sub_neg_1_to_inc_defs : rewrite_defs := {|
    fnd := 
     Psub_ri r1 (Int.neg Int.one)
      :: nil
    ; rpl := 
      Pinc r1
      :: nil
    ; lv_in := IR r1 :: PC :: nil
    ; lv_out := IR r1 :: PC :: nil
    ; clobbered := flags
  |}.
             
  Lemma peep_sub_neg_1_to_inc_selr :
    StepEquiv.step_through_equiv_live (fnd peep_sub_neg_1_to_inc_defs) (rpl peep_sub_neg_1_to_inc_defs) (lv_in peep_sub_neg_1_to_inc_defs) (lv_out peep_sub_neg_1_to_inc_defs).
  Proof.  
    prep_l.
    step_l.
    prep_r.
    step_r.
    finish_r.
    prep_eq'.
    - subst.
      preg_simpl.
      unfold Val.sub.
      unfold Val.add.
      unfold Val.neg.
      simpl.
      repeat (break_match; P0 _simpl val_eq; repeat inv_vint; simpl; try congruence).
      f_equal.
      ring.
    - subst.
      preg_simpl.
      repeat find_rewrite_goal.
      simpl.
      f_equal.
  Qed.

  Definition peep_sub_neg_1_to_inc_proofs : rewrite_proofs :=
    {|
      defs := peep_sub_neg_1_to_inc_defs
      ; selr := peep_sub_neg_1_to_inc_selr
    |}.

  Definition peep_sub_neg_1_to_inc : 
    concrete = fnd peep_sub_neg_1_to_inc_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite peep_sub_neg_1_to_inc_defs peep_sub_neg_1_to_inc_proofs.
  Qed.

End SUB_NEG_1_TO_INC.

Definition peep_sub_neg_1_to_inc_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_sub_neg_1_to_inc p.
  unfold peep_sub_neg_1_to_inc_defs in p.
  simpl in p. 
  specialize (p c).
  do 1 set_code_cons c.
  set_code_nil c.  
  set_instr_eq i 0%nat peep_sub_neg_1_to_inc_example.
  set_int_eq n (Int.neg Int.one).  
  specialize (p _ eq_refl). exact (Some p).
Defined.

Definition sub_neg_1_to_inc (c : code) : list StepEquiv.rewrite :=
  collect (map peep_sub_neg_1_to_inc_rewrite (ParamSplit.matched_pat peep_sub_neg_1_to_inc_example c)).
