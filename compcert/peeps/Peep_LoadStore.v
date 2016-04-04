Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Import Stacklayout.
Require Import Conventions.
Require Import Asm.
Require Import AsmBits.
Require Import AsmCallingConv.
Require Import MemoryAxioms.
Require Import PeekLib.
Require Import PeekTactics.
Require Import FindInstrLib.
Require Import PregTactics.
Require Import ForwardJumps.
Require Import StepIn.
Require Import StepEquiv.
Require Import ProgPropDec.
Require Import Union.
Require Import UseBasic.
Require Import PeepholeLib.
Require Import MemEq.
Require Import ValEq.
Require Import ParamSplit.
Require Import AddrmodeEq.
Require Import PeepsLib.
Require Import PeepsTactics.

Module Imp.

Definition example_addr : addrmode := (Addrmode None None (inl Int.zero)).
Definition peep_store_load_example : code :=
  Pmov_mr example_addr EAX :: Pmov_rm EAX example_addr :: nil.

Section STORE_LOAD.

  Variable concrete : code.

  Variable r : ireg.
  Variable a : addrmode.

  Definition peep_store_load_defs : rewrite_defs :=
    {|
      fnd :=
        Pmov_mr a r :: 
                Pmov_rm r a :: nil
      ; rpl :=
          Pmov_mr a r :: Pnop :: nil
      ; lv_in := PC :: IR r :: (use_addr a)
      ; lv_out := PC :: IR r ::  nil
      ; clobbered := nil
    |}.

  Lemma peep_store_load_selr :
    StepEquiv.step_through_equiv_live (fnd peep_store_load_defs) (rpl peep_store_load_defs) (lv_in peep_store_load_defs) (lv_out peep_store_load_defs).
  Proof.
    admit.
    (* assert (exists rs' m', exec_store_bits (env tprog) Mint32 mr a rsr r nil = Next rs' m'). *)
    (* { *)
    (*   assert ((forall (id : ident) (ofs : int), *)
    (*        Genv.symbol_address (env tprog) id ofs = *)
    (*        Genv.symbol_address (env prog) id ofs)) by admit. *)
    (*   simpl_exec. *)
    (*   simpl_match_hyp. *)
    (*   unfold exec_store_bits in *.     *)
    (*   erewrite eval_addrmode_bits_transf.       *)
    (*   2: eauto. *)

    (*   unfold storev_bits in *. *)
    (*   simpl_match_hyp. *)
    (*   exploit eq_mem_store. *)
    (*   eauto. *)
    (*   2: eauto. *)
    (*   eauto. *)
    (*   intros. *)
    (*   break_exists. break_and. *)
    (*   exploit use_addr_correct_bits. *)
    (*   intros. *)
    (*   specialize (H12 p). *)
    (*   conclude H12 eauto. *)
    (*   eapply H12. *)
    (*   intros. *)
    (*   instantiate (1 := (env prog)) in H15. *)
    (*   rewrite val_eq_or in H15. *)
    (*   break_or; try congruence. *)
    (*   rewrite <- H16. *)
    (*   rewrite Heqv0. *)
    (*   rewrite val_eq_or in H11. *)
    (*   rewrite H1. *)
    (*   eauto.       *)
    (* } *)
    (*Todo prove regs and mem eq*)
    (*Use: use_addr_eval_addrmode_bits*)
  Qed.

  Definition peep_store_load_proofs : rewrite_proofs :=
    {|
      defs := peep_store_load_defs
      ; selr := peep_store_load_selr
    |}.

  Definition peep_store_load :
    concrete = fnd peep_store_load_defs ->
    StepEquiv.rewrite.
  Proof.
    intros.
    
    refine (
      {|
        find := fnd peep_store_load_defs;
        repl := rpl peep_store_load_defs;
        live_in := lv_in peep_store_load_defs;
        live_out := lv_out peep_store_load_defs;
        pres := preserved peep_store_load_defs;
        not_same := _;
        PC_live_out := _;
        find_nonempty := _;
        repl_nonempty := _;
        len_same := _;
        no_trace_find := _;
        no_trace_repl := _;
        no_label_out := _;
        forward_find := _;
        steps_equiv_live := selr peep_store_load_proofs;
        steps_pres_find := _;
        steps_pres_repl := _;
        measure := measure_fun;
        measure_decr := _
      |}); admit.

  Defined.

End STORE_LOAD.


Definition peep_store_load_rewrite (c : code) : option StepEquiv.rewrite.
  name peep_store_load p.
  unfold peep_store_load_defs in p.
  simpl in p. 
  specialize (p c).
  do 2 set_code_cons c.
  set_code_nil c.
  set_instr_eq i 0%nat peep_store_load_example.
  set_instr_eq i0 1%nat peep_store_load_example.
  set_ireg_eq rs rd.
  set_addrmode_eq a a0.
  specialize (p _ _ eq_refl). exact (Some p).
Defined.

End Imp.

Module Peep.

Definition store_load (c : code) : list StepEquiv.rewrite :=
  collect (map Imp.peep_store_load_rewrite (ParamSplit.matched_pat Imp.peep_store_load_example c)).

End Peep.