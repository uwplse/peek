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

Definition aiken_2_example : code :=
  Psub_rr ECX EAX :: Pmov_rr EAX ECX :: Pdec EAX :: nil.

Section AIKEN_2.

  Variable concrete : code.
  Variable r1 : ireg.
  Variable r2 : ireg.

  Hypothesis neq : r1 <> r2.

  Definition aiken_2_defs : rewrite_defs :=
    {|
      fnd :=
        Psub_rr r2 r1 ::
                Pmov_rr r1 r2 ::
                Pdec r1 ::
                nil
      ; rpl :=
          Pnot r1 ::
               Padd_rr r1 r2 ::
               Pnop ::
               nil
      ; lv_in := PC :: IR r1 :: IR r2 :: nil
      ; lv_out := PC :: IR r1 :: nil
      ; clobbered := IR r2 :: flags
    |}.

    Lemma val_eq_sub_sub_add_not :
      forall v v' x x',
        val_eq v v' ->
        val_eq x x' ->
        val_eq (Val.sub (Val.sub v x) Vone) (Val.add (Val.notint x') v').
    Proof.
      intros. unfold val_eq in H.
      unfold val_eq in H0.
      repeat break_match_hyp; try inv_false;
      subst; simpl; try congruence;
      unfold Val.add; unfold Val.notint;
      repeat break_match;
      try congruence.
      f_equal.
      rewrite (Int.sub_add_not i0 i). ring.
    Qed.
  
  Lemma aiken_2_selr :
    StepEquiv.step_through_equiv_live (fnd aiken_2_defs) (rpl aiken_2_defs) (lv_in aiken_2_defs) (lv_out aiken_2_defs).
  Proof.    
    prep_l.
    do 3 step_l.
    prep_r.
    do 3 step_r.
    finish_r.
    prep_eq.
    split.
    2: eq_mem_tac.
    eq_reg_tac.
    subst_max.
    preg_simpl.

    eapply val_eq_sub_sub_add_not; eauto.
  Qed.
    

  Definition aiken_2_proofs : rewrite_proofs :=
    {|
      defs := aiken_2_defs
      ; selr := aiken_2_selr
    |}.

  Definition peep_aiken_2 : 
    concrete = fnd aiken_2_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite aiken_2_defs aiken_2_proofs.
  Qed.

End AIKEN_2.

Definition aiken_2_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_aiken_2 p.
  unfold aiken_2_defs in p.
  simpl in p. 
  specialize (p c).  
  do 3 (destruct c; [ exact None | ]).
  destruct c; [ | exact None].  

  set_instr_eq i 0%nat aiken_2_example.
  set_instr_eq i0 1%nat aiken_2_example.
  set_instr_eq i1 2%nat aiken_2_example.

  set_ireg_eq rd r0.
  set_ireg_eq r1 rd0.
  set_ireg_eq rd0 rd1.
  set_ireg_neq rd1 r0.
  
  specialize (p rd1 r0 n eq_refl). exact (Some p).
Defined.

Definition aiken_2 (c : code) : list StepEquiv.rewrite :=
  collect (map aiken_2_rewrite (ParamSplit.matched_pat aiken_2_example c)).
