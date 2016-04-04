Require Import Coqlib.
Require Import Asm.
Require Import PeekTactics.
Require Import PeepsLib.
Require Import Integers.
Require Import PregTactics.
Require Import StepIn.
Require Import AsmBits.
Require Import Values.
Require Import ValEq.
Require Import Integers.
Require Import PeepsTactics.

Module Imp.

(* dummy addrmode *)
Definition da : addrmode := Addrmode None None (inl Int.zero).

Definition peep_vec_mull_example :=
            Pmovsd_fm XMM0 da ::
            Pmovsd_fm XMM0 da ::
            Pmuld_ff XMM0 XMM0 ::
            Pmovsd_fm XMM0 da ::
            Pmovsd_fm XMM0 da ::
            Pmuld_ff XMM0 XMM0 ::
            Pmovsd_fm XMM0 da ::
            Pmovsd_fm XMM0 da ::
            Pmuld_ff XMM0 XMM0 ::
            Pmovsd_fm XMM0 da ::
            Pmovsd_fm XMM0 da ::
            Pmuld_ff XMM0 XMM0 ::
            Pmovsd_mf da XMM0 ::
            Pmovsd_mf da XMM0 ::
            Pmovsd_mf da XMM0 ::
            Pmovsd_mf da XMM0 ::
            nil.


Section VEC_MULL.

  Variable concrete : code.
  Variable r1 r2 r3 r4 r5 r6 r7 r8 : freg.
  Variable a b c : addrmode.

  
  Definition a8 := addr_add a 8.
  Definition a16 := addr_add a 16.
  Definition a24 := addr_add a 24.

  Definition b8 := addr_add b 8.
  Definition b16 := addr_add b 16.
  Definition b24 := addr_add b 24.
  
  Definition c8 := addr_add c 8.
  Definition c16 := addr_add c 16.
  Definition c24 := addr_add c 24.
  
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
  Definition br3 := make_bfreg r3.
  Definition br4 := make_bfreg r4.
  Definition br5 := make_bfreg r5.
  Definition br6 := make_bfreg r6.
  Definition br7 := make_bfreg r7.
  Definition br8 := make_bfreg r8.
  Definition hr1 := get_high_reg br1.
  Definition hr2 := get_high_reg br2.
  Definition hr3 := get_high_reg br3.
  Definition hr4 := get_high_reg br4.
  Definition hr5 := get_high_reg br5.
  Definition hr6 := get_high_reg br6.
  Definition hr7 := get_high_reg br7.
  Definition hr8 := get_high_reg br8.

  
  Definition peep_vec_mull_defs : rewrite_defs :=
    {|
      fnd :=
            Pmovsd_fm r1 a ::
            Pmovsd_fm r2 b ::
            Pmuld_ff r1 r2 ::
            Pmovsd_fm r3 a8 ::
            Pmovsd_fm r4 b8 ::
            Pmuld_ff r3 r4 ::
            Pmovsd_fm r5 a16 ::
            Pmovsd_fm r6 b16 ::
            Pmuld_ff r5 r6 ::
            Pmovsd_fm r7 a24 ::
            Pmovsd_fm r8 b24 ::
            Pmuld_ff r7 r8 ::
            Pmovsd_mf c r1 ::
            Pmovsd_mf c8 r3 ::
            Pmovsd_mf c16 r5 ::
            Pmovsd_mf c24 r7 ::
            nil
      ; rpl :=
          Pmovups_rm br1 a ::
          Pmovups_rm br2 b ::
          Pmulpd_ff br1 br2 ::
          Pmovups_rm br3 a16 ::
          Pmovups_rm br4 b16 ::
          Pmulpd_ff br3 br4 ::
          Pmovups_mr c br1 ::
          Pmovups_mr c16 br3 ::
          Pnop :: Pnop :: Pnop :: Pnop ::
          Pnop :: Pnop :: Pnop :: Pnop :: nil
      ; lv_in :=
          PC :: nil
      ; lv_out :=
          PC :: nil
      ; clobbered :=
          nil
    |}.
  
  Lemma peep_vec_mull_selr :
    StepEquiv.step_through_equiv_live (fnd peep_vec_mull_defs) (rpl peep_vec_mull_defs) (lv_in peep_vec_mull_defs) (lv_out peep_vec_mull_defs).
  Proof.    
    prep_l.    
    step_l.
    step_l.
    step_l.
    step_l.
    step_l.
    step_l.
    step_l.
    step_l.
    step_l.
    step_l.
    step_l.
    step_l.
    step_l.
    step_l.
    step_l.
    step_l.
    prep_r.    
    (* step_r. *)
    prep_exec_instr.
    {
      clear -H.
      assert False by admit.
      exfalso.
      assumption.
    }
    repeat break_exists.
    specialize (H4 x3).

    step_r.

    prep_exec_instr.
    {
      clear -H.
      assert False by admit.
      exfalso.
      assumption.
    }
    repeat break_exists.
    specialize (H20 x3).
    step_r.

    prep_exec_instr.
    {
      clear -H.
      assert False by admit.
      exfalso.
      assumption.
    }
    repeat break_exists.
    specialize (H35 x3).
    step_r.

    prep_exec_instr.
    {
      clear -H.
      assert False by admit.
      exfalso.
      assumption.
    }
    repeat break_exists.
    specialize (H50 x3).
    step_r.

    prep_exec_instr.
    {
      clear -H.
      assert False by admit.
      exfalso.
      assumption.
    }
    repeat break_exists.
    specialize (H64 x3).
    step_r.

    prep_exec_instr.
    {
      clear -H.
      assert False by admit.
      exfalso.
      assumption.
    }
    repeat break_exists.
    specialize (H77 x3).
    step_r.

    prep_exec_instr.
    {
      clear -H.
      assert False by admit.
      exfalso.
      assumption.
    }
    repeat break_exists.
    specialize (H92 x3).
    step_r.

    prep_exec_instr.
    {
      clear -H.
      assert False by admit.
      exfalso.
      assumption.
    }
    repeat break_exists.
    specialize (H106 x3).
    step_r.

    prep_exec_instr.
    {
      clear -H.
      assert False by admit.
      exfalso.
      assumption.
    }
    repeat break_exists.
    specialize (H134 x3).
    step_r.

    step_r.
    step_r.
    step_r.
    step_r.
    step_r.
    step_r.
    step_r.

    assert (x43 = md').
    exploit step_through_md; eauto.
    unfold peep_code.
    simpl.
    intros.
    repeat break_or; simpl; tauto.
    subst x43.
    
    finish_r.
    admit.
  Qed.

  Definition peep_vec_mull_proofs : rewrite_proofs :=
    {|
      defs := peep_vec_mull_defs
      ; selr := peep_vec_mull_selr
    |}.

  Definition peep_vec_mull :
    concrete = fnd peep_vec_mull_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    peep_tac_mk_rewrite' peep_vec_mull_defs peep_vec_mull_proofs; admit.
  Qed.

End VEC_MULL.

Definition peep_vec_mull_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_vec_mull p.
  unfold peep_vec_mull_defs in p.
  simpl in p. 
  specialize (p c).
  set_code_cons c.
  set_code_cons c.
  set_code_cons c.
  set_code_cons c.
  set_code_cons c.
  set_code_cons c.
  set_code_cons c.
  set_code_cons c.
  set_code_cons c.
  set_code_cons c.
  set_code_cons c.
  set_code_cons c.
  set_code_cons c.
  set_code_cons c.
  set_code_cons c.
  set_code_cons c.
  set_code_nil c.
  set_instr_eq i 0%nat peep_vec_mull_example.
  set_instr_eq i0 1%nat peep_vec_mull_example.
  set_instr_eq i1 2%nat peep_vec_mull_example.
  set_instr_eq i2 3%nat peep_vec_mull_example.
  set_instr_eq i3 4%nat peep_vec_mull_example.
  set_instr_eq i4 5%nat peep_vec_mull_example.
  set_instr_eq i5 6%nat peep_vec_mull_example.
  set_instr_eq i6 7%nat peep_vec_mull_example.
  set_instr_eq i7 8%nat peep_vec_mull_example.
  set_instr_eq i8 9%nat peep_vec_mull_example.
  set_instr_eq i9 10%nat peep_vec_mull_example.
  set_instr_eq i10 11%nat peep_vec_mull_example.
  set_instr_eq i11 12%nat peep_vec_mull_example.
  set_instr_eq i12 13%nat peep_vec_mull_example.
  set_instr_eq i13 14%nat peep_vec_mull_example.
  set_instr_eq i14 15%nat peep_vec_mull_example.

  Require Import AddrmodeEq.
  destruct (addrmode_eq a1 (addr_add a 8)); [|exact None].
  destruct (addrmode_eq a3 (addr_add a 16)); [|exact None].
  destruct (addrmode_eq a5 (addr_add a 24)); [|exact None].
  destruct (addrmode_eq a2 (addr_add a0 8)); [|exact None].
  destruct (addrmode_eq a4 (addr_add a0 16)); [|exact None].
  destruct (addrmode_eq a6 (addr_add a0 24)); [|exact None].
  destruct (addrmode_eq a9 (addr_add a7 8)); [|exact None].
  destruct (addrmode_eq a10 (addr_add a7 16)); [|exact None].
  destruct (addrmode_eq a11 (addr_add a7 24)); [|exact None].

  subst.
  unfold a8 in *.
  unfold b8 in *.
  unfold c8 in *.
  unfold a16 in *.
  unfold b16 in *.
  unfold c16 in *.
  unfold a24 in *.
  unfold b24 in *.
  unfold c24 in *.
  destruct (preg_eq rd rd1); [|exact None]. 
  destruct (preg_eq rd0 r1); [|exact None].
  destruct (preg_eq rd2 rd4); [|exact None]. 
  destruct (preg_eq rd3 r0); [|exact None].
  destruct (preg_eq rd5 rd7); [|exact None]. 
  destruct (preg_eq rd6 r2); [|exact None].
  destruct (preg_eq rd8 rd10); [|exact None]. 
  destruct (preg_eq rd9 r3); [|exact None].
  destruct (preg_eq r4 rd1); [|exact None].
  destruct (preg_eq r5 rd4); [|exact None].
  destruct (preg_eq r6 rd7); [|exact None].
  destruct (preg_eq r7 rd10); [|exact None].
  inv e. inv e0.
  inv e1. inv e2.
  inv e3. inv e4.
  inv e5. inv e6.
  inv e7. inv e8.
  inv e9. inv e10.
  specialize (p rd1 r1).
  specialize (p rd4 r0).
  specialize (p rd7 r2).
  specialize (p rd10 r3).
  specialize (p a a0 a7).
  specialize (p eq_refl).
  exact (Some p).
Qed.

End Imp.

