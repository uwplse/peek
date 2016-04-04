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

Definition peep_extended_shift_example :=
  Psal_ri EAX Int.zero ::
          Pshr_ri EAX Int.zero ::
          Por_rr EAX EAX :: nil.

Section EXTENDED_SHIFT.

  Variable concrete : code.
  Variable r1 r2 : ireg.
  Variable c1 c2 : int.
  (* tweak this to maybe also include range facts  *)
  Hypothesis eq : Int.add c1 c2 = Int.repr (32).
  Variable r1_r2_neq : r1 <> r2.
  
  Definition peep_extended_shift_defs : rewrite_defs :=
    {|
      fnd :=
        Psal_ri r1 c1 ::
                Pshr_ri r2 c2 ::
                Por_rr r1 r2 :: nil
      ; rpl :=
          Pshld_ri r1 r2 c1 :: Pnop :: Pnop :: nil
      ; lv_in := PC :: IR r1 :: IR r2 :: nil
      ; lv_out := PC :: IR r1 :: nil
      ; clobbered := IR r2 :: flags
    |}.

Lemma peep_extended_shift_selr :
  StepEquiv.step_through_equiv_live (fnd peep_extended_shift_defs) (rpl peep_extended_shift_defs) (lv_in peep_extended_shift_defs) (lv_out peep_extended_shift_defs).
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
    repeat break_or_reg.
    - (*PC*)
      preg_simpl.
      repeat find_rewrite_goal.
      simpl.
      reflexivity.
    - preg_simpl.
      eapply val_eq_vor.      
      subst_max.
      preg_simpl.
      eapply val_eq_shl.
      assumption.
      simpl. auto.
      subst_max.
      preg_simpl.
      eapply val_eq_shru.
      assumption.
      simpl.
      f_equal.
      clear -eq.
      unfold Int.iwordsize in *.
      unfold Int.zwordsize in *.
      unfold Int.wordsize in *.
      unfold Wordsize_32.wordsize in *.
      simpl.
      rewrite <- eq.
      ring. 
  Qed.

  Definition peep_extended_shift_proofs : rewrite_proofs :=
    {|
      defs := peep_extended_shift_defs
      ; selr := peep_extended_shift_selr
    |}.

  Definition peep_extended_shift : 
    concrete = fnd peep_extended_shift_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite peep_extended_shift_defs peep_extended_shift_proofs.
  Qed.

End EXTENDED_SHIFT.

Definition peep_extended_shift_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_extended_shift p.
  unfold peep_extended_shift_defs in p.
  simpl in p. 
  specialize (p c).
  do 3 set_code_cons c.
  set_code_nil c.  
  set_instr_eq i 0%nat peep_extended_shift_example.
  set_instr_eq i0 1%nat peep_extended_shift_example.
  set_instr_eq i1 2%nat peep_extended_shift_example.
  set_ireg_eq rd1 rd.
  set_ireg_eq rd0 r1.
  set_ireg_neq rd r1.
  destruct (Int.eq (Int.add n n0) (Int.repr 32)) eqn:?.
  2: exact None.
  apply PtrEquiv.int_eq_true in Heqb.
  specialize (p _ _ _ _ Heqb n1 eq_refl). exact (Some p).
Defined.

Definition extended_shift (c : code) : list StepEquiv.rewrite :=
  collect (map peep_extended_shift_rewrite (ParamSplit.matched_pat peep_extended_shift_example c)).
