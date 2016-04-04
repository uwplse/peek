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
  
Definition peep_mov_nop_example : code :=
  Pmov_rr EAX EAX :: Pmov_rr EBX EBX :: nil.

Section MOV_NOP.

  Variable concrete : code.

  Variable r1 : ireg.
  Variable r2 : ireg.
  Hypothesis r1_r2_neq: r1 <> r2.

  Definition peep_mov_nop_defs : rewrite_defs :=
    {|
      fnd :=
        Pmov_rr r1 r1 :: 
                Pmov_rr r2 r2 :: nil
      ; rpl :=
          Pnop :: Pnop :: nil
      ; lv_in := IR r1 :: IR r2 :: PC :: nil
      ; lv_out := IR r1 :: IR r2 :: PC :: nil
      ; clobbered := nil
    |}.

  Lemma peep_mov_nop_selr :
    StepEquiv.step_through_equiv_live (fnd peep_mov_nop_defs) (rpl peep_mov_nop_defs) (lv_in peep_mov_nop_defs) (lv_out peep_mov_nop_defs).
  Proof.    
    prep_l.
    step_l.
    step_l.
    prep_r.
    step_r.
    step_r.
    finish_r.
    prep_eq'.          
    subst_max.
    preg_simpl.
    assumption.
    subst_max.
    preg_simpl.
    assumption.    
    simpl.
    preg_simpl.
    repeat find_rewrite_goal.
    reflexivity.    
  Qed.

  Definition peep_mov_nop_proofs : rewrite_proofs :=
    {|
      defs := peep_mov_nop_defs
      ; selr := peep_mov_nop_selr
    |}.

  Definition peep_mov_nop :
    concrete = fnd peep_mov_nop_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite peep_mov_nop_defs peep_mov_nop_proofs.    
  Qed.

End MOV_NOP.

Definition peep_mov_nop_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_mov_nop p.
  unfold peep_mov_nop_defs in p.
  simpl in p. 
  specialize (p c).
  do 2 set_code_cons c.
  set_code_nil c.
  set_instr_eq i 0%nat peep_mov_nop_example.
  set_instr_eq i0 1%nat peep_mov_nop_example.
  set_ireg_eq rd r1.
  set_ireg_eq rd0 r0.
  set_ireg_neq r1 r0.
  specialize (p _ _ n eq_refl). exact (Some p).
Defined.

Definition mov_nop (c : code) : list StepEquiv.rewrite :=
  collect (map peep_mov_nop_rewrite (ParamSplit.matched_pat peep_mov_nop_example c)).
