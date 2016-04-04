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

Definition peep_test_vec_add_example := Paddd_ff XMM0 XMM0 :: nil.

Section TEST_VEC_ADD.

  Variable concrete : code.
  Variable r1 : freg.
  Variable r2 : freg.

  Definition make_bfreg (f : freg) : bfreg :=
    match f with
      | XMM0 => xmm0
      | XMM1 => xmm1
      | XMM2 => xmm2
      | XMM3 => xmm3
      | XMM4 => xmm4
      | XMM5 => xmm5
      | XMM6 => xmm6
      | XMM7 => xmm7
    end.

  Definition get_high_reg (b : bfreg) : hfreg :=
    let (_,h) := split_big_freg b in h.

  Definition br1 := make_bfreg r1.
  Definition br2 := make_bfreg r2.
  Definition hr1 := get_high_reg br1.
  Definition hr2 := get_high_reg br2.
  
  Definition peep_test_vec_add_defs : rewrite_defs :=
    {|
      fnd :=
        Paddd_ff r1 r2 :: nil
      ; rpl :=
          Paddpd_ff (make_bfreg r1) (make_bfreg r2) :: nil
      ; lv_in := FR r1 :: FR r2 :: PC :: nil
      ; lv_out := FR r1 :: PC :: nil
      ; clobbered := FRH hr1 :: FRH hr2 :: nil
    |}.
  
  Lemma peep_test_vec_add_selr :
    StepEquiv.step_through_equiv_live (fnd peep_test_vec_add_defs) (rpl peep_test_vec_add_defs) (lv_in peep_test_vec_add_defs) (lv_out peep_test_vec_add_defs).
  Proof.
    admit.
    (* prep_l. *)
    (* step_l. *)
    (* prep_r. *)
    (* step_r. *)
    (* finish_r. *)
    (* split. *)
  Qed.

  Definition peep_test_vec_add_proofs : rewrite_proofs :=
    {|
      defs := peep_test_vec_add_defs
      ; selr := peep_test_vec_add_selr
    |}.

  Definition peep_test_vec_add :
    concrete = fnd peep_test_vec_add_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite peep_test_vec_add_defs peep_test_vec_add_proofs.
    admit. (* idk, tactic didn't work *)
  Qed.

End TEST_VEC_ADD.

Definition peep_test_vec_add_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_test_vec_add p.
  unfold peep_test_vec_add_defs in p.
  simpl in p. 
  specialize (p c).
  set_code_cons c.
  set_code_nil c.
  set_instr_eq i 0%nat peep_test_vec_add_example.
  specialize (p rd r1 eq_refl). exact (Some p).
Defined.

Definition test_vec_add (c : code) : list StepEquiv.rewrite :=
  collect (map peep_test_vec_add_rewrite (ParamSplit.matched_pat peep_test_vec_add_example c)).
