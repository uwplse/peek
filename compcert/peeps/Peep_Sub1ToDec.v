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

Definition peep_sub_1_to_dec_example := Psub_ri EAX one :: nil.

Section SUB_1_TO_DEC.

  Variable concrete : code.
  Variable r1 : ireg.

  Definition peep_sub_1_to_dec_defs : rewrite_defs := {|
    fnd := 
     Psub_ri r1 one 
      :: nil
    ; rpl := 
      Pdec r1
      :: nil
    ; lv_in := IR r1 :: PC :: nil
    ; lv_out := IR r1 :: PC :: nil
    ; clobbered := flags
  |}.
             
  Lemma peep_sub_1_to_dec_selr :
    StepEquiv.step_through_equiv_live (fnd peep_sub_1_to_dec_defs) (rpl peep_sub_1_to_dec_defs) (lv_in peep_sub_1_to_dec_defs) (lv_out peep_sub_1_to_dec_defs).
  Proof.    
    prep_l.
    step_l.
    prep_r.
    step_r.
    finish_r.
    prep_eq'.
    - subst_max.
      preg_simpl.
      eapply val_eq_sub.
      assumption.
      simpl. auto.
    - subst_max.
      preg_simpl.
      repeat find_rewrite_goal.
      simpl.
      reflexivity.
  Qed.

  Definition peep_sub_1_to_dec_proofs : rewrite_proofs :=
  {|
    defs := peep_sub_1_to_dec_defs
    ; selr := peep_sub_1_to_dec_selr
  |}.

  Definition peep_sub_1_to_dec : 
    concrete = fnd peep_sub_1_to_dec_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite peep_sub_1_to_dec_defs peep_sub_1_to_dec_proofs.
  Qed.

End SUB_1_TO_DEC.

Definition peep_sub_1_to_dec_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_sub_1_to_dec p.
  unfold peep_sub_1_to_dec_defs in p.
  simpl in p. 
  specialize (p c).
  do 1 set_code_cons c.
  set_code_nil c.  
  set_instr_eq i 0%nat peep_sub_1_to_dec_example.
  set_int_eq n (one).  
  specialize (p _ eq_refl). exact (Some p).
Defined.

Definition sub_1_to_dec (c : code) : list StepEquiv.rewrite :=
  collect (map peep_sub_1_to_dec_rewrite (ParamSplit.matched_pat peep_sub_1_to_dec_example c)).
