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

Definition peep_mov_0_to_xor_example := Pmov_ri EAX zero :: nil.

Section MOV_0_TO_XOR.

  Variable concrete : code.
  Variable r1 : ireg.

  Definition peep_mov_0_to_xor_defs : rewrite_defs :=
    {|
      fnd := Pmov_ri r1 zero :: nil
      ; rpl := Pxor_r r1 :: nil          
      ; lv_in := IR r1 :: PC :: nil
      ; lv_out := IR r1 :: PC :: nil
      ; clobbered := flags
    |}.

  Lemma peep_mov_0_to_xor_selr :
    StepEquiv.step_through_equiv_live (fnd peep_mov_0_to_xor_defs) (rpl peep_mov_0_to_xor_defs) (lv_in peep_mov_0_to_xor_defs) (lv_out peep_mov_0_to_xor_defs).
  Proof.    
    prep_l.
    step_l.
    prep_r.
    step_r.
    finish_r.
    prep_eq.
    split.
    intros.
    2: eq_mem_tac.
    simpl_and_clear.
    break_or'.
    subst reg.
    preg_simpl.
    unfold Vzero.
    unfold zero.
    unfold Int.zero.
    reflexivity.
    break_or'.
    subst reg.
    2: inv_false.
    preg_simpl.
    repeat find_rewrite_goal.
    reflexivity.
  Qed.

  Definition peep_mov_0_to_xor_proofs : rewrite_proofs :=
    {|
      defs := peep_mov_0_to_xor_defs
      ; selr := peep_mov_0_to_xor_selr
    |}.

  Definition peep_mov_0_to_xor : 
    concrete = fnd peep_mov_0_to_xor_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite peep_mov_0_to_xor_defs peep_mov_0_to_xor_proofs.    
  Qed.

End MOV_0_TO_XOR.

Definition peep_mov_0_to_xor_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_mov_0_to_xor p.
  unfold peep_mov_0_to_xor_defs in p.
  simpl in p. 
  specialize (p c).
  set_code_cons c.
  set_code_nil c.
  set_instr_eq i 0%nat peep_mov_0_to_xor_example.
  set_int_eq n (zero).  
  specialize (p _ eq_refl). exact (Some p).
Defined.

Definition mov_0_to_xor (c : code) : list StepEquiv.rewrite :=
  collect (map peep_mov_0_to_xor_rewrite (ParamSplit.matched_pat peep_mov_0_to_xor_example c)).
