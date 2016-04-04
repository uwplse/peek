Require Import Coqlib.
Require Import Asm.
Require Import PeekTactics.
Require Import PeepsLib.
Require Import StepIn.
Require Import MemEq.
Require Import ValEq.
Require Import PregTactics.
Require Import StepIn.
Require Import AsmBits.
Require Import Values.
Require Import ValEq.
Require Import Integers.
Require Import PeepsTactics.

Definition peep_jump_nop_example : code :=
  Pjmp_l xH :: Plabel xH :: Pnop :: nil.

Section JUMP_NOP.

  Variable concrete : code.

  Variable l1 : label.
  
  Definition peep_jump_nop_defs : rewrite_defs :=
    {|
      fnd :=            
        Pjmp_l l1 :: Plabel l1 :: Pnop :: nil
      ; rpl :=
          Pnop :: Pnop :: Pnop :: nil
      ; lv_in := PC :: nil
      ; lv_out := PC :: nil
      ; clobbered := flags
    |}.

  Lemma peep_jump_nop_selr :
    StepEquiv.step_through_equiv_live (fnd peep_jump_nop_defs) (rpl peep_jump_nop_defs) (lv_in peep_jump_nop_defs) (lv_out peep_jump_nop_defs).
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
    P0 _clear step_through.
    P0 _clear at_code.
    P0 _clear at_code_end.
    P0 _clear no_ptr_regs.
    P0 _clear no_ptr_mem.
    P0 _clear not_after_label_in_code.    
      (* unfold jumps_to_label in *.         *)
      (* collapse_match_hyp. *)
      (* repeat (break_match_hyp; try tauto). *)
      (* unfold eval_testcond in *. *)
      (* simpl_match_hyp. *)
      (* repeat inv_some. *)
    inv_state.
    split.
    {
      intros.
      repeat (break_or; try inv_false); try preg_simpl;
      repeat match goal with
               | [H: ?x ?y = _ |- context[?x ?y]] => rewrite H
             end;
      simpl.      
      f_equal.
      inv_state.
      ring.
      (* repeat (simpl_exec; break_match; try congruence); *)
      (*   repeat (state_inv); try opt_inv. *)
      (* preg_simpl. *)
      (* assumption.         *)      
    }
    {
      repeat (simpl_and_clear; break_match; try congruence);
        repeat (state_inv); try opt_inv.
    }
  Qed.

  Definition peep_jump_nop_proofs : rewrite_proofs :=
    {|
      defs := peep_jump_nop_defs
      ; selr := peep_jump_nop_selr
    |}.

  Definition peep_jump_nop :
    concrete = fnd peep_jump_nop_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite peep_jump_nop_defs peep_jump_nop_proofs.    
  Qed.

End JUMP_NOP.

Definition peep_jump_nop_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_jump_nop p.
  unfold peep_jump_nop_defs in p.
  simpl in p. 
  specialize (p c).
  do 3 set_code_cons c.
  set_code_nil c.
  set_instr_eq i 0%nat peep_jump_nop_example.
  set_instr_eq i0 1%nat peep_jump_nop_example.
  set_instr_eq i1 2%nat peep_jump_nop_example.
  set_label_eq l l0.  
  specialize (p _ eq_refl). exact (Some p).
Defined.

Definition jump_nop (c : code) : list StepEquiv.rewrite :=
  collect (map peep_jump_nop_rewrite (ParamSplit.matched_pat peep_jump_nop_example c)).
