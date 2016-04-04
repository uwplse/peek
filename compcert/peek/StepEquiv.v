Require Import Coqlib.
Require Import AST.
Require Import Globalenvs.
Require Import Integers.
Require Import Smallstep.
Require Import Events.
Require Import Asm.

Require Import SplitLib.
Require Import StepIn.
Require Import AsmCallingConv.
Require Import PeekLib.
Require Import ProgPropDec.
Require Import AsmBits.
Require Import SameBlockLib.
Require Import MemoryAxioms.
Require Import ValEq.
Require Import MemEq.
Require Import Zlen.
Require Import PeekTactics.

Definition not_after_label (ge : genv) (st : state_bits) (z : Z) (c : code) : Prop :=
  forall rs m b i bits md,
    st = State_bits rs m md ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,i) ->
    forall s' c' c0 c1,
      Genv.find_funct_ptr ge b = Some (Internal (mkfunction s' c')) ->
      c' = c0 ++ c ++ c1 ->
      zlen c0 = z ->
      (ends_in_not_label c0 /\ c1 <> nil).

Definition label_in_code (c : code) (l : label) :=
  exists i,
    In i c /\ labeled_jump i l.

Definition ends_in_not_label_from_after_code (c : code) (c_after : code) :=
  forall l,
    label_in_code c_after l ->
    find_instr (zlen c - 1) c = Some (Plabel l) ->
    False.

Lemma mk_ends_in_not_label_from_after_code:
  forall c c_after,
    ends_in_not_label c ->
    ends_in_not_label_from_after_code c c_after.
Proof.
  intros.
  unfold ends_in_not_label_from_after_code.
  unfold ends_in_not_label in H.
  intros.
  apply H in H1.
  simpl in H1.
  tauto.
Qed.

Definition not_after_label_in_code (ge : genv) (st : state_bits) (z : Z) (c : code) : Prop :=
  forall rs m b i bits md,
    st = State_bits rs m md ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,i) ->
    forall s' c' c0 c1,
      Genv.find_funct_ptr ge b = Some (Internal (mkfunction s' c')) ->
      c' = c0 ++ c ++ c1 ->
      zlen c0 = z ->      
      (ends_in_not_label_from_after_code c0 c /\ c1 <> nil).

Lemma mk_not_after_label_in_code:
  forall ge st z c,
    not_after_label ge st z c ->
    not_after_label_in_code ge st z c.
Proof.  
  unfold not_after_label in *.
  unfold not_after_label_in_code in *.
  intros.
  exploit H; eauto. intro.
  break_and.
  NP1 app_new mk_ends_in_not_label_from_after_code ends_in_not_label.
Qed.

Definition genv_equiv_code (z : Z) (ge ge2 : genv) (b : Values.block) (find repl : code) : Prop :=
  forall s c s' c',
    Genv.find_funct_ptr ge b = Some (Internal (mkfunction s c)) ->
    Genv.find_funct_ptr ge2 b = Some (Internal (mkfunction s' c')) ->
    pat_at_n find (nat_of_Z z) c ->
    (pat_at_n repl (nat_of_Z z) c' /\ firstn (nat_of_Z z) c' = firstn (nat_of_Z z) c).

Definition step_through_equiv_live (find repl : code) (live_in_regs live_out_regs : list preg) : Prop :=
  forall z prog rsl ml t rsl' ml' b i bits md md',
    no_PC_overflow_prog prog ->
    at_code z find 0 (Genv.globalenv prog) (State_bits rsl ml md) ->
    step_through z find (Genv.globalenv prog) (State_bits rsl ml md) t (State_bits rsl' ml' md') ->
    rsl PC = Values.Vint bits ->
    psur md bits = Some (b,i) ->
    not_after_label_in_code (Genv.globalenv prog) (State_bits rsl ml md) z find ->
    forall rsr mr,
      (forall reg, In reg live_in_regs -> val_eq (rsl reg) (rsr reg)) ->
      mem_eq md ml mr ->
      forall tprog, 
        no_PC_overflow_prog tprog ->
        no_ptr_regs rsr /\ no_ptr_mem mr ->
        genv_equiv_code z (Genv.globalenv prog) (Genv.globalenv tprog) b find repl ->        
        (forall id ofs, Genv.symbol_address (Genv.globalenv prog) id ofs =
                        Genv.symbol_address (Genv.globalenv tprog) id ofs) ->
        global_perms (Genv.globalenv tprog) mr ->
        (exists s c, Genv.find_funct_ptr (Genv.globalenv tprog) b = Some (Internal (mkfunction s c))) ->
        
        exists rsr' mr',
          step_through z repl (Genv.globalenv tprog) (State_bits rsr mr md) t (State_bits rsr' mr' md') /\ 
          (forall reg, In reg live_out_regs -> val_eq (rsl' reg) (rsr' reg)) /\
          mem_eq md' ml' mr'.

Definition step_through_preserve (c : code) (pres : list preg) : Prop :=
  forall z prog rs m t rs' m' md md',
    no_PC_overflow_prog prog ->
    at_code z c 0 (Genv.globalenv prog) (State_bits rs m md) ->
    step_through z c (Genv.globalenv prog) (State_bits rs m md) t (State_bits rs' m' md') ->
    (forall reg, In reg pres -> rs reg = rs' reg) /\ md = md'.

Record rewrite :=
  { find : code
    ; repl : code
    ; live_in : list preg
    ; live_out : list preg
    ; pres : list preg
    ; not_same : find <> repl
    ; PC_live_out : In PC live_out
    ; find_nonempty : find <> nil
    ; repl_nonempty : repl <> nil
    ; len_same : length find = length repl
    ; no_trace_find : no_trace_code find (* redundant: in forward_find *)
    ; no_trace_repl : no_trace_code repl
    ; no_label_out : ends_in_not_label find
    ; forward_find : only_forward_jumps find
    ; steps_equiv_live : step_through_equiv_live find repl live_in live_out
    ; steps_pres_find : step_through_preserve find pres
    ; steps_pres_repl : step_through_preserve repl pres
    ; measure : Z -> state_bits -> nat
    ; measure_decr :
      forall z prog st t st',
        (no_PC_overflow_prog prog /\ 
         not_after_label (Genv.globalenv prog) st z find) ->
        step_bits (Genv.globalenv prog) st t st' ->
        (exists ofs, at_code z find ofs (Genv.globalenv prog) st) ->
        (exists ofs, at_code z find ofs (Genv.globalenv prog) st') ->
        lt (measure (z + zlen find) st') (measure (z + zlen find) st)
  }.

