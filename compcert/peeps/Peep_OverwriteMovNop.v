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

Definition peep_overwrite_mov_nop_example := 
  Pmov_rr EBX EAX
                :: Pmov_rr EBX ECX
                :: nil.

Section OVERWRITE_MOV_NOP.

  Variable concrete : code.
  Variable r1 : ireg.
  Variable r2 : ireg.
  Variable r3 : ireg.
  Hypothesis r1_r3_neq : r1 <> r3.
  Hypothesis r2_r3_neq : r2 <> r3.

  Definition peep_overwrite_mov_nop_defs : rewrite_defs :=
    {|
      fnd := 
        Pmov_rr r2 r1
                :: Pmov_rr r2 r3
                :: nil
      ; rpl :=
          Pnop
            :: Pmov_rr r2 r3
            :: nil
      ; lv_in := IR r3 :: PC :: nil
      ; lv_out := IR r2 :: IR r3 :: PC :: nil
      ; clobbered := flags
    |}.
             
  Lemma peep_overwrite_mov_nop_selr :
    StepEquiv.step_through_equiv_live (fnd peep_overwrite_mov_nop_defs) (rpl peep_overwrite_mov_nop_defs) (lv_in peep_overwrite_mov_nop_defs) (lv_out peep_overwrite_mov_nop_defs).
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
      assumption.
    - subst_max.
      preg_simpl.
      assumption.
    - subst_max.
      preg_simpl.
      repeat find_rewrite_goal.
      simpl.
      reflexivity.      
  Qed.

  Definition peep_overwrite_mov_nop_proofs : rewrite_proofs :=
    {|
      defs := peep_overwrite_mov_nop_defs
      ; selr := peep_overwrite_mov_nop_selr
    |}.

  Definition peep_overwrite_mov_nop : 
    concrete = fnd peep_overwrite_mov_nop_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite peep_overwrite_mov_nop_defs peep_overwrite_mov_nop_proofs.
  Qed.

End OVERWRITE_MOV_NOP.

Definition peep_overwrite_mov_nop_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_overwrite_mov_nop p.
  unfold peep_overwrite_mov_nop_defs in p.
  simpl in p. 
  specialize (p c).
  do 2 set_code_cons c.
  set_code_nil c.  
  set_instr_eq i 0%nat peep_overwrite_mov_nop_example.
  set_instr_eq i0 1%nat peep_overwrite_mov_nop_example.
  set_ireg_eq rd rd0.
  set_ireg_neq rd0 r0.
  specialize (p _ _ _ n eq_refl). exact (Some p).
Defined.

Definition overwrite_mov_nop (c : code) : list StepEquiv.rewrite :=
  collect (map peep_overwrite_mov_nop_rewrite (ParamSplit.matched_pat peep_overwrite_mov_nop_example c)).
