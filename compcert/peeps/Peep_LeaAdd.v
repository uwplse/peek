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

Definition peep_lea_add_example : code :=    
  Plea (EDX) (Addrmode (Some EDX) (Some (EDI, one)) (inl zero)) :: nil.

Section LEA_ADD.

  Variable concrete : code.

  Variable r1 : ireg.
  Variable r2 : ireg.

  Hypothesis neq : r1 <> r2.

  Definition peep_lea_add_defs : rewrite_defs :=
    {|
      fnd := 
        Plea r1 (Addrmode (Some r1) (Some (r2, one)) (inl zero)) 
             :: nil
      ; rpl := 
          Padd_rr r1 r2 
                  :: nil
      ; lv_in := IR r1 :: IR r2 :: PC :: nil
      ; lv_out := IR r1 :: IR r2 :: PC :: nil
      ; clobbered := flags
    |}.
  
  Lemma peep_lea_add_selr :
    StepEquiv.step_through_equiv_live (fnd peep_lea_add_defs) (rpl peep_lea_add_defs) (lv_in peep_lea_add_defs) (lv_out peep_lea_add_defs).
  Proof.
    prep_l.   
    step_l.    
    prep_r.    
    step_r.
    finish_r.
    prep_eq.
    split.    
    2: eq_mem_tac.
    intros.    
    simpl_and_clear.    
    (*r1*)
    break_or'.
    subst reg.
    preg_simpl.
    eapply val_eq_add.
    assumption.
    unfold Val.add.
    break_match; try congruence.
    simpl.    
    P0 _simpl val_eq.    
    rewrite <- H4.
    f_equal.
    unfold zero.
    ring.
    P0 _simpl val_eq.
    inv_false.
    (*r2*)
    break_or'.
    subst reg.
    preg_simpl.
    assumption.
    (*PC*)
    break_or'.
    subst reg.
    preg_simpl.
    repeat find_rewrite_goal.
    simpl.
    reflexivity.
    inv_false.
    clear -Heqb0. exfalso.
    apply PtrEquiv.int_eq_false in Heqb0.
    unfold one in *.
    unfold Int.one in *.
    congruence.    
  Qed.

  Definition peep_lea_add_proofs : rewrite_proofs :=
    {|
      defs := peep_lea_add_defs
      ; selr := peep_lea_add_selr
    |}.

  Definition peep_lea_add : 
    concrete = fnd peep_lea_add_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite peep_lea_add_defs peep_lea_add_proofs.
  Qed.

End LEA_ADD.

Definition peep_lea_add_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_lea_add p.
  unfold peep_lea_add_defs in p.
  simpl in p. 
  specialize (p c).    
  set_code_cons c.
  set_code_nil c.
  set_instr_eq i 0%nat peep_lea_add_example.
  destruct a.
  destruct base; [ | exact None].
  destruct ofs; [ | exact None].
  destruct const; [ | exact None].
  destruct p0.
  specialize (p i i1).
  set_ireg_neq i i1.
  set_ireg_eq rd i.
  specialize (p n).
  set_int_eq i2 one.
  set_int_eq i0 zero.
  exact (Some (p eq_refl)).
Defined.

Definition lea_add (c : code) : list StepEquiv.rewrite :=
  collect (map peep_lea_add_rewrite (ParamSplit.matched_pat peep_lea_add_example c)).
