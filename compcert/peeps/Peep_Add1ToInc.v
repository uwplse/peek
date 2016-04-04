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

Definition peep_add_1_to_inc_example := Padd_ri EAX one :: nil.

Section ADD_1_TO_INC.

  Variable concrete : code.
  Variable r1 : ireg.

  Definition peep_add_1_to_inc_defs : rewrite_defs :=
    {|
      fnd := 
        Padd_ri r1 one 
                :: nil
      ; rpl := 
          Pinc r1
               :: nil
      ; lv_in := IR r1 :: PC :: nil
      ; lv_out := IR r1 :: PC :: nil
      ; clobbered := flags
    |}.
  
  Lemma peep_add_1_to_inc_selr :
    StepEquiv.step_through_equiv_live (fnd peep_add_1_to_inc_defs) (rpl peep_add_1_to_inc_defs) (lv_in peep_add_1_to_inc_defs) (lv_out peep_add_1_to_inc_defs).
  Proof.    
    prep_l.
    step_l.
    prep_r.
    step_r.
    finish_r.
    prep_eq.
    split.
    2: eq_mem_tac.
    eq_reg_tac.
    simpl_and_clear.
    unfold_val_int.
    simpl.    
    repeat (break_match; try no_ptr_regs_tac; try congruence);
      P0 _simpl val_eq;
      repeat inv_vint;
      simpl;
      try match goal with
            | [|- Vint _ = Vint _] => f_equal
          end;
      try congruence.    
  Qed.

  Definition peep_add_1_to_inc_proofs : rewrite_proofs :=
    {|
      defs := peep_add_1_to_inc_defs
      ; selr := peep_add_1_to_inc_selr
    |}.

  Definition peep_add_1_to_inc :
    concrete = fnd peep_add_1_to_inc_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite peep_add_1_to_inc_defs peep_add_1_to_inc_proofs.
  Qed.

End ADD_1_TO_INC.

Definition peep_add_1_to_inc_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_add_1_to_inc p.
  unfold peep_add_1_to_inc_defs in p.
  simpl in p. 
  specialize (p c).
  set_code_cons c.
  set_code_nil c.
  set_instr_eq i 0%nat peep_add_1_to_inc_example.
  set_int_eq n (one).      
  specialize (p rd eq_refl). exact (Some p).
Defined.

Definition add_1_to_inc (c : code) : list StepEquiv.rewrite :=
  collect (map peep_add_1_to_inc_rewrite (ParamSplit.matched_pat peep_add_1_to_inc_example c)).
