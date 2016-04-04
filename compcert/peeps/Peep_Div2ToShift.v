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

Definition peep_div_2_to_shr_example : code :=
  Pmov_ri ECX two :: Pdiv ECX :: nil.

Section DIV_2_TO_SHIFT.
  
  Variable concrete : code.

  Definition peep_div_2_to_shr_defs : rewrite_defs :=
    {|
      fnd :=
        Pmov_ri ECX two ::              
                Pdiv ECX ::
                nil
      ; rpl := 
          Pshr_ri EAX Int.one ::
                  Pnop ::
                  nil              
      ; lv_in := IR EAX :: PC :: nil
      ; lv_out := IR EAX :: PC :: nil
      ; clobbered := IR EDX :: IR ECX :: flags
    |}.

  Lemma peep_div_2_to_shr_selr :
    StepEquiv.step_through_equiv_live (fnd peep_div_2_to_shr_defs) (rpl peep_div_2_to_shr_defs) (lv_in peep_div_2_to_shr_defs) (lv_out peep_div_2_to_shr_defs).
  Proof.
    prep_l.
    step_l.
    step_l.
    prep_r.
    step_r.
    step_r.
    finish_r.
    prep_eq.
    split.
    2: eq_mem_tac.
    intros.    
    simpl_and_clear.
    (*EAX*)
    break_or'.
    {
      subst reg.
      subst_max.
      preg_simpl.      
      unfold Val.divu in *.
      simpl_match_hyp.
      repeat inv_some.
      simpl.
      unfold Val.shru.
      P0 preg_simpl_hyp nextinstr.
      inv_vint.
      rewrite Heqv1 in *.
      P0 _simpl val_eq.
      break_match; try congruence.
      break_if.
      f_equal.
      inv_vint.
      erewrite Int.divu_pow2.
      eauto.
      unfold Int.one.
      unfold two.
      cut (2 = two_p 1). intro. rewrite H0.      
      apply Int.is_power2_two_p.      
      unfold Int.zwordsize in *.
      unfold Int.wordsize in *.
      unfold Wordsize_32.wordsize in *.
      simpl.
      omega.
      vm_compute.
      reflexivity.
      inv_vint.
      clear -Heqb1.
      exfalso.
      unfold Int.ltu in *.
      break_if.
      congruence.
      clear Heqs.
      rewrite Int.unsigned_one in g.
      rewrite Int.unsigned_repr_wordsize in *.            
      unfold Int.zwordsize in *.
      unfold Int.wordsize in *.
      unfold Wordsize_32.wordsize in *.
      simpl in *.
      omega.      
    }
    (*PC*)
    break_or'.
    2: inv_false.
    subst reg.
    P0 _clear False.    
    subst_max.
    preg_simpl.
    repeat find_rewrite_goal.
    simpl.
    reflexivity.    
  Qed.

  Definition peep_div_2_to_shr_proofs : rewrite_proofs :=
    {|
      defs := peep_div_2_to_shr_defs
      ; selr := peep_div_2_to_shr_selr
    |}.

  Definition peep_div_2_to_shr :
    concrete = fnd peep_div_2_to_shr_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite peep_div_2_to_shr_defs peep_div_2_to_shr_proofs.
  Qed.

End DIV_2_TO_SHIFT.

Definition peep_div_2_to_shr_rewrite (c : code) : option StepEquiv.rewrite.  
  name peep_div_2_to_shr p.
  unfold peep_div_2_to_shr_defs in p.
  simpl in p.
  specialize (p (Pmov_ri ECX two :: Pdiv ECX :: nil)).
  specialize (p eq_refl).
  exact (Some p).  
Defined.

Definition div_2_to_shr (c : code) : list StepEquiv.rewrite :=
  collect (map peep_div_2_to_shr_rewrite (ParamSplit.matched_pat peep_div_2_to_shr_example c)).
