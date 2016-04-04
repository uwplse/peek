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
Require Import MemEq.
Require Import Integers.
Require Import PeepsTactics.

Definition peep_extended_shift_2_example :=
  Pshr_ri EAX Int.zero ::
          Pshld_ri EAX EAX Int.zero ::
          Psal_ri EAX Int.zero ::
          Por_rr EAX EAX :: nil.

Section EXTENDED_SHIFT_2.

  Variable concrete : code.
  Variable r1 r2 r3 r4 : ireg.
  Variable c1 c2 : int.
  (* tweak this to maybe also include range facts  *)
  Hypothesis eq : Int.add c1 c2 = Int.repr (32).
  Hypothesis r1_r3_neq: r1 <> r3.
  Hypothesis r1_r2_neq: r1 <> r2.
  Hypothesis r2_r4_neq: r2 <> r4.
  Hypothesis r2_r3_neq: r2 <> r3.
  Hypothesis r3_r4_neq: r3 <> r4.
  
  Definition peep_extended_shift_2_defs : rewrite_defs :=
    {|
      fnd :=
        Pshr_ri r2 c2 ::
                Pshld_ri r3 r4 c1 ::
                Psal_ri r1 c1 ::
                Por_rr r1 r2 :: nil
      ; rpl :=
          Pshld_ri r3 r4 c1 ::
          Pshld_ri r1 r2 c1 :: Pnop :: Pnop :: nil
      ; lv_in := PC :: IR r1 :: IR r2 :: IR r3 :: IR r4 :: nil
      ; lv_out := PC :: IR r1 :: IR r3 :: nil
      ; clobbered := IR r2 :: IR r4 :: flags
    |}.

    Lemma peep_extended_shift_2_selr :
    StepEquiv.step_through_equiv_live (fnd peep_extended_shift_2_defs) (rpl peep_extended_shift_2_defs) (lv_in peep_extended_shift_2_defs) (lv_out peep_extended_shift_2_defs).
  Proof.
    prep_l.
    step_l.
    step_l.
    step_l.
    step_l.
    prep_r.
    step_r.
    step_r.
    step_r.
    step_r.
    finish_r.
    prep_eq.
    split.
    2: eq_mem_tac.
    intros.
    simpl_and_clear.
    break_or'.    
    (*PC*)
    subst reg.    
    preg_simpl.
    repeat find_rewrite_goal.
    simpl.
    reflexivity.
    break_or'.
    (*r1*)
    subst reg.        
    preg_simpl.
    eapply val_eq_vor.
    subst_max.
    preg_simpl.
    eapply val_eq_shl.
    assumption.
    simpl; reflexivity.
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
    break_or'.
    (*r2*)
    subst reg.
    P0 _clear False.
    preg_simpl.
    subst_max.
    preg_simpl.
    eapply val_eq_vor.        
    eapply val_eq_shl.    
    assumption.
    simpl; reflexivity.
    eapply val_eq_shru.
    assumption.
    simpl.    
    f_equal.
    inv_false.
  Qed.

  Definition peep_extended_shift_2_proofs : rewrite_proofs :=
    {|
      defs := peep_extended_shift_2_defs
      ; selr := peep_extended_shift_2_selr
    |}.

  Definition peep_extended_shift_2 : 
    concrete = fnd peep_extended_shift_2_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite peep_extended_shift_2_defs peep_extended_shift_2_proofs.    
  Qed.

End EXTENDED_SHIFT_2.

Definition peep_extended_shift_2_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_extended_shift_2 p.
  unfold peep_extended_shift_2_defs in p.
  simpl in p. 
  specialize (p c).
  do 4 set_code_cons c.
  set_code_nil c.  
  set_instr_eq i 0%nat peep_extended_shift_2_example.
  set_instr_eq i0 1%nat peep_extended_shift_2_example.
  set_instr_eq i1 2%nat peep_extended_shift_2_example.
  set_instr_eq i2 3%nat peep_extended_shift_2_example.
  set_ireg_eq r0 rd.
  set_ireg_eq rd2 rd1.
  set_int_eq n0 n1.

  rename rd0 into l3.
  rename r1 into l4.
  rename rd into l2.
  rename rd1 into l1.
  set_ireg_neq l1 l3.
  set_ireg_neq l1 l2.
  set_ireg_neq l2 l4.
  set_ireg_neq l2 l3.
  
  destruct (Int.eq (Int.add n1 n) (Int.repr 32)) eqn:?.
  2: exact None.
  apply PtrEquiv.int_eq_true in Heqb.
  
  specialize (p _ _ _ _ _ _ Heqb n0 n2 n3 n4 eq_refl). exact (Some p).
Defined.

Definition extended_shift_2 (c : code) : list StepEquiv.rewrite :=
  collect (map peep_extended_shift_2_rewrite (ParamSplit.matched_pat peep_extended_shift_2_example c)).
