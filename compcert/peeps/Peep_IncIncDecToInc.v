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

Definition peep_inc_inc_dec_to_inc_example :=
  Pinc EAX :: Pinc EAX :: Pdec EAX :: nil.

Section INC_INC_DEC_TO_INC.

  Variable concrete : code.

  Variable r1 : ireg.

  Definition peep_inc_inc_dec_to_inc_defs : rewrite_defs :=
    {|
      fnd :=
        Pinc r1 ::
             Pinc r1 ::
             Pdec r1 ::
             nil
      ; rpl :=        
          Pinc r1 ::
               Pnop ::
               Pnop ::
               nil
      ; lv_in := PC :: IR r1 :: nil
      ; lv_out := PC :: IR r1 :: nil
      ; clobbered := flags
    |}.
           
  Lemma peep_inc_inc_dec_to_inc_selr :
    StepEquiv.step_through_equiv_live (fnd peep_inc_inc_dec_to_inc_defs) (rpl peep_inc_inc_dec_to_inc_defs) (lv_in peep_inc_inc_dec_to_inc_defs) (lv_out peep_inc_inc_dec_to_inc_defs).
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
    (*PC*)
    break_or'.
    subst reg.
    preg_simpl.
    repeat find_rewrite_goal.
    simpl.
    f_equal. 
    (*r1*)
    break_or'. subst reg.
    2: inv_false.
    subst_max.
    preg_simpl.    
    unfold Val.add.
    unfold Val.sub.
    simpl.    
    repeat (break_match_sm; try congruence);
    simpl;
    P0 _simpl val_eq;
    try inv_vint;
    f_equal;
    try ring;
    try assumption.
  Qed.

  Definition peep_inc_inc_dec_to_inc_proofs : rewrite_proofs :=
    {|
      defs := peep_inc_inc_dec_to_inc_defs
      ; selr := peep_inc_inc_dec_to_inc_selr
    |}.

  Definition peep_inc_inc_dec_to_inc :
    concrete = fnd peep_inc_inc_dec_to_inc_defs ->
    StepEquiv.rewrite.
  Proof.
    intro.
    peep_tac_mk_rewrite peep_inc_inc_dec_to_inc_defs peep_inc_inc_dec_to_inc_proofs.
  Qed.

End INC_INC_DEC_TO_INC.

Definition peep_inc_inc_dec_to_inc_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_inc_inc_dec_to_inc p.
  unfold peep_inc_inc_dec_to_inc_defs in p.
  simpl in p. 
  specialize (p c).
  do 3 set_code_cons c.
  set_code_nil c.
  set_instr_eq i 0%nat peep_inc_inc_dec_to_inc_example.
  set_instr_eq i0 1%nat peep_inc_inc_dec_to_inc_example.
  set_instr_eq i1 2%nat peep_inc_inc_dec_to_inc_example.
  set_ireg_eq rd rd0.
  set_ireg_eq rd0 rd1.
  specialize (p _ eq_refl). exact (Some p).
Defined.

Definition inc_inc_dec_to_inc (c : code) : list StepEquiv.rewrite :=
  collect (map peep_inc_inc_dec_to_inc_rewrite (ParamSplit.matched_pat peep_inc_inc_dec_to_inc_example c)).
