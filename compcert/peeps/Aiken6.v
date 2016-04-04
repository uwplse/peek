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

Definition aiken_6_example : code :=
  Pmov_ri EAX eight ::
          Psub_rr EAX ECX ::
          Pdec EAX ::
          nil.

Section AIKEN_6.

  Variable concrete : code.
  Variable r1 : ireg.
  Variable r2 : ireg.
  Hypothesis r1_r2_neq : r1 <> r2.

  Definition aiken_6_defs : rewrite_defs :=
    {|
      fnd :=        
        (* mov $8, %eax    *)
        (* sub %ecx, %eax  *)
        (* dec %eax        *)        
        Pmov_ri r1 eight ::
                Psub_rr r1 r2 ::
                Pdec r1 ::
                nil
      ; rpl :=
          (* mov $7, %eax   *)
          (* sub %ecx, %eax *)
          Pmov_ri r1 seven ::
                  Psub_rr r1 r2 ::
                  Pnop ::
                  nil
      ; lv_in := PC :: IR r2 :: nil      
      ; lv_out := PC :: IR r2 :: nil
      ; clobbered := IR r1 :: flags
    |}.

  Lemma aiken_6_selr :
    StepEquiv.step_through_equiv_live (fnd aiken_6_defs) (rpl aiken_6_defs) (lv_in aiken_6_defs) (lv_out aiken_6_defs).
  Proof.    
    prep_l.
    do 3 step_l.
    prep_r.
    do 3 step_r.
    finish_r.
    prep_eq'.
    - subst_max.
      preg_simpl.
      repeat find_rewrite_goal.
      simpl.
      reflexivity.
    - subst_max.
      preg_simpl.
      assumption.        
  Qed.

  Definition aiken_6_proofs : rewrite_proofs :=
    {|
      defs := aiken_6_defs
      ; selr := aiken_6_selr
    |}.

  Definition peep_aiken_6 : 
    concrete = fnd aiken_6_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite aiken_6_defs aiken_6_proofs.    
  Qed.

End AIKEN_6.
  
Definition aiken_6_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_aiken_6 p.
  unfold aiken_6_defs in p.
  simpl in p.
  specialize (p c).  
  do 3 set_code_cons c.
  set_code_nil c.
  set_instr_eq i 0%nat aiken_6_example.
  set_instr_eq i0 1%nat aiken_6_example.
  set_instr_eq i1 2%nat aiken_6_example.
  set_int_eq n eight.
  set_ireg_eq rd rd0.
  set_ireg_eq rd1 rd0.
  set_ireg_neq rd0 r1.
  exact (Some (p rd0 r1 n eq_refl)).
Defined.

Definition aiken_6 (c : code) : list StepEquiv.rewrite :=
  collect (map aiken_6_rewrite (ParamSplit.matched_pat aiken_6_example c)).
