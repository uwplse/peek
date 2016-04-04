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

Definition peep_inc_dec_nop_example : code :=
  Pinc EAX :: Pdec EAX :: nil.

Section INC_DEC_NOP.

  Variable concrete : code.

  Variable r1 : ireg.

  Definition peep_inc_dec_nop_defs : rewrite_defs :=
    {|
      fnd :=
        Pinc r1 :: Pdec r1 :: nil
      ; rpl :=
          Pnop :: Pnop :: nil
      ; lv_in := IR r1 :: PC :: nil
      ; lv_out := IR r1 :: PC :: nil
      ; clobbered := flags                       
    |}.

  Lemma peep_inc_dec_nop_selr :
    StepEquiv.step_through_equiv_live (fnd peep_inc_dec_nop_defs) (rpl peep_inc_dec_nop_defs) (lv_in peep_inc_dec_nop_defs) (lv_out peep_inc_dec_nop_defs).
  Proof.
    prep_l.
    step_l.
    step_l.
    prep_r.
    step_r.
    step_r.
    finish_r.
    prep_eq.
    split.
    2: eq_mem_tac.
    intros.
    simpl_and_clear.
    (*r1*)
    break_or'. subst reg.
    subst_max.
    preg_simpl.
    unfold Val.add.
    unfold Val.sub.
    simpl.    
    repeat (break_match_sm; try congruence).
    simpl.
    P0 _simpl val_eq.
    rewrite <- H0.
    f_equal.
    ring.
    simpl.
    P0 _simpl val_eq.
    assumption.
    (*PC*)
    break_or'.
    2: inv_false.
    subst reg.
    preg_simpl.
    repeat find_rewrite_goal.
    simpl.
    f_equal.    
  Qed.

  Definition peep_inc_dec_nop_proofs : rewrite_proofs :=
    {|
      defs := peep_inc_dec_nop_defs
      ; selr := peep_inc_dec_nop_selr
    |}.

  Definition peep_inc_dec_nop :
    concrete = fnd peep_inc_dec_nop_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.  
    peep_tac_mk_rewrite peep_inc_dec_nop_defs peep_inc_dec_nop_proofs.
  Qed.

End INC_DEC_NOP.

Definition peep_inc_dec_nop_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_inc_dec_nop p.
  unfold peep_inc_dec_nop_defs in p.
  simpl in p. 
  specialize (p c).
  do 2 set_code_cons c.
  set_code_nil c.
  set_instr_eq i 0%nat peep_inc_dec_nop_example.
  set_instr_eq i0 1%nat peep_inc_dec_nop_example.
  set_ireg_eq rd rd0.
  specialize (p _ eq_refl). exact (Some p).
Defined.

Definition inc_dec_nop (c : code) : list StepEquiv.rewrite :=
  collect (map peep_inc_dec_nop_rewrite (ParamSplit.matched_pat peep_inc_dec_nop_example c)).
