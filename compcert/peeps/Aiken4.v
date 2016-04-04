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
Require Import StepEquiv.

Definition aiken_4_example :=
  Pmov_rr ECX EAX ::
          Pmov_rr EAX EDX ::
          Pmov_rr EDX ECX ::
          nil.

Section AIKEN_4.

  Variable concrete : code.
  Variable r1 : ireg.
  Variable r2 : ireg.
  Variable r3 : ireg.
  Hypothesis r2_r1_neq: r2 <> r1.
  Hypothesis r2_r3_neq: r2 <> r3.

  Definition aiken_4_defs : rewrite_defs :=
    {|
      fnd :=
        Pmov_rr r2 r1 ::
                Pmov_rr r1 r3 ::
                Pmov_rr r3 r2 ::
                nil
      ; rpl :=
          Pxchg_rr r1 r3 ::
                   Pnop ::
                   Pnop ::
                   nil
      ; lv_in := PC :: IR r1 :: IR r3 :: nil
      ; lv_out := PC :: IR r1 :: IR r3 :: nil
      ; clobbered := IR r2 :: nil
    |}.

  Lemma aiken_4_selr :
    StepEquiv.step_through_equiv_live (fnd aiken_4_defs) (rpl aiken_4_defs) (lv_in aiken_4_defs) (lv_out aiken_4_defs).
  Proof.    
    prep_l.
    do 3 step_l.
    prep_r.
    do 3 step_r.
    finish_r.    
    prep_eq.
    split.
    simpl_and_clear.
    subst m0 m1 a1 a0 m.
    clear_taut.
    2: eq_mem_tac.
    intros.
    P0 _clear current_block.
    P0 _clear current_instr.
    P0 _clear MemoryAxioms.match_metadata.
    P0 _clear current_PC.
    P0 _clear no_ptr_regs.
    P0 _clear no_ptr_mem.
    P0 _clear global_perms.    
    repeat break_or_reg.
    - subst.
      preg_simpl.
      repeat find_rewrite_goal.
      simpl.
      reflexivity.
    - subst.      
      preg_simpl.
      preg_case.
      rewrite e.
      preg_simpl.
      eassumption.
      assumption.
    - subst.
      preg_simpl.
      assumption.
  Qed.

  Definition aiken_4_proofs : rewrite_proofs :=
    {|
      defs := aiken_4_defs
      ; selr := aiken_4_selr
    |}.

  Definition peep_aiken_4 : 
    concrete = fnd aiken_4_defs -> StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite aiken_4_defs aiken_4_proofs.
  Qed.  

End AIKEN_4.



Definition aiken_4_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_aiken_4 p.
  unfold aiken_4_defs in p.
  simpl in p. 
  specialize (p c).  
  do 3 (destruct c; [ exact None | ]).  
  destruct c; [ | exact None].  

  set_instr_eq i 0%nat aiken_4_example.
  set_instr_eq i0 1%nat aiken_4_example.
  set_instr_eq i1 2%nat aiken_4_example.  

  rename_all ireg a.
  
  set_ireg_eq a4 a. rename a into lr2.
  set_ireg_eq a3 a2. rename a2 into lr1.
  set_ireg_eq a1 a0. rename a0 into lr3.
  set_ireg_neq lr2 lr1.
  set_ireg_neq lr2 lr3.
    
  specialize (p lr1 lr2 lr3 n n0 eq_refl). exact (Some p).
Defined.

Definition aiken_4 (c : code) : list StepEquiv.rewrite :=
  collect (map aiken_4_rewrite (ParamSplit.matched_pat aiken_4_example c)).
