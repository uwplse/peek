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
Require Import SameBlockLib.
Require Import PeekTactics.
Require Import FindInstrLib.
Require Import PregTactics.
Require Import ForwardJumps.
Require Import StepIn.
Require Import StepEquiv.
Require Import ProgPropDec.
Require Import Union.
Require Import UseBasic.
Require Import MemEq.
Require Import ValEq.
Require Import ParamSplit.
Require Import AddrmodeEq.
Require Import Zlen.
Require Import StepLib.

(*TODO move out*)

Ltac bump H := copy H; clear H.

Ltac NP2 tac Hnm pat :=
  match goal with
    | [ H1 : context [ pat ], 
        H2 : context [ pat ] |- _ ] => tac Hnm H1
  end.

Ltac NP3 tac Hnm pat :=
  match goal with
    | [ H1 : context [ pat ], 
        H2 : context [ pat ], 
        H3 : context [ pat ] |- _ ] => tac Hnm H1
  end.

Ltac P3 tac pat :=
  match goal with
    | [ H1 : context [ pat ],
        H2 : context [ pat ],
        H3 : context [ pat ] |- _ ] => tac H1
  end.

Ltac P4 tac pat :=
  match goal with
    | [ H1 : context [ pat ],
        H2 : context [ pat ],
        H3 : context [ pat ],
        H4 : context [ pat ] |- _ ] => tac H1
  end.

(*TODO is this the pattern we want?*)
Ltac P2P1 tac pat1 pat2 :=
  match goal with
    | [ pat1B : context [ pat1 ],
        pat1A : context [ pat1 ] |- _] =>
      match goal with
        | [ pat2A : context [ pat2 ] |- _ ] => tac pat1B pat2A
      end
  end.

Ltac P1P2 tac pat1 pat2 :=
  match goal with
    | [ pat1A : context [ pat1 ] |- _] =>
      match goal with
        | [ pat2B : context [ pat2 ],
            pat2A : context [ pat2 ] |- _ ] => tac pat1A pat2B
      end
  end.

Ltac P1P1 tac pat1 pat2 :=
  match goal with
    | [ pat1A : context [ pat1 ] |- _] =>
      match goal with
        | [ pat2A : context [ pat2 ] |- _ ] => tac pat1A pat2A
      end
  end.

Ltac simpl_match_hyp :=
      repeat (break_match_hyp; try congruence); [].

(*TODO get rid of this slow tactic*)
Ltac discriminate_instr :=
  match goal with
    | [ i : instruction |- _ ] => destruct i
  end;
    simpl in *; auto;
    repeat break_any; discriminate || omega.

Ltac _unfold N := unfold N.
Ltac _unfoldin N H := unfold N in H.

Ltac false_or :=
  match goal with
    | [_:_|- ~ True \/ _ ] => right
    | [_:_|- False \/ _ ] => right
    | [_:_|- _ \/ ~ True ] => right
    | [_:_|- _ \/ False ] => right
  end.

Ltac collapse_match_hyp :=
  match goal with
    | [ H : ?X = _, H': context[match ?X with _ => _ end] |- _ ] => rewrite H in H'
    | [ H : _ = ?X, H': context[match ?X with _ => _ end] |- _ ] => rewrite <- H in H'
  end.

Ltac simpl_add :=
  repeat match goal with
           | [H: context [ _ + _ + _ ] |- _] =>
             rewrite Zplus_assoc_reverse in H; simpl in H
           | [_:_ |- context [ _ + _ + _ ] ] =>
             rewrite Zplus_assoc_reverse; simpl
         end.

Fixpoint collect {A : Type} (l : list (option A)) : list A :=
  match l with
    | Some x :: r => x :: collect r
    | None :: r => collect r
    | nil => nil
  end.

Lemma testcond_eq:
  forall x y : testcond,
    {x = y} + {x <> y}.
Proof.
  decide equality.
Qed.

Lemma label_eq:
  forall x y : label,
    {x = y} + {x <> y}.
Proof.
  decide equality.
Qed.

(*NOTATION*)

Notation nPC := no_PC_overflow_prog.
Notation env := Genv.globalenv.

(*DEFINITIONS*)

Definition zero := Int.repr 0.
Definition one := Int.repr 1.
Definition two := Int.repr 2.
Definition three := Int.repr 3.
Definition four := Int.repr 4.
Definition five := Int.repr 5.
Definition six := Int.repr 6.
Definition seven := Int.repr 7.
Definition eight := Int.repr 8.
Definition nine := Int.repr 9.
Definition ten := Int.repr 10.

Record rewrite_defs :=
  { fnd : code
    ; rpl : code
    ; lv_in : list preg
    ; lv_out : list preg
    ; clobbered : list preg    
  }.

Record rewrite_proofs :=
  {
    defs : rewrite_defs
    ; selr : step_through_equiv_live (fnd defs) (rpl defs) (lv_in defs) (lv_out defs)
  }.

Definition preserved (rwr: rewrite_defs) : list preg := reml preg_eq ((lv_in rwr) ++ (lv_out rwr) ++ (clobbered rwr)) all_pregs.

Definition flags : list preg :=
  (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil).

Definition no_calls' (c: code) : Prop :=
  forall i, In i c -> ~ AsmCallingConv.is_call_return i.

Definition no_trace_code' (c: code) : Prop :=
  forall i, In i c -> no_trace i.

Definition only_forward_jumps_lab' (c: code) : Prop :=
  forall i l z z',      
    In i c ->
    labeled_jump i l ->
    In (Plabel l) c ->
    find_instr z c = Some i ->
    find_instr z' c = Some (Plabel l) ->
    z' > z.

Definition no_def_instr (instr : instruction) (regs : list preg) :=       
  forall r, In r (def instr) -> ~ In r regs.

Definition no_def (code : list instruction) (regs : list preg) :=
  forall i, In i code -> no_def_instr i regs.

(* <<<<<<< HEAD *)
(* Lemma step_through_preserved_no_touch : *)
(*   forall do_code pres, *)
(*     no_def do_code pres -> *)
(*     step_through_preserve do_code pres. *)
(* Proof. *)
(*   admit. *)
(* Qed. *)

(* Lemma not_in_preserved: *)
(*   forall r ds, *)
(*     In r (lv_in ds ++ lv_out ds ++ clobbered ds) -> *)
(*     ~ In r (preserved ds). *)
(* Proof. *)
(*   intros. *)
(*   copy (in_dec preg_eq r (preserved ds)). *)
(*   destruct H0; auto. *)
(*   unfold preserved in i. *)
(*   remember (lv_in ds ++ lv_out ds ++ clobbered ds) as rs. *)
(*   copy (rem_in r rs ). *)
(*   specialize (H0 all_pregs). *)
(*   specialize (H0 preg_eq). *)
(*   destruct H0. *)
(*   specialize (H1 i). *)
(*   break_and. *)
(*   congruence. *)
(* Qed. *)

(* Ltac peep_tac_no_def := *)
(*   simpl; *)
(*   unfold no_def; *)
(*   unfold no_def_instr; *)
(*   intros; *)
(*   apply not_in_preserved; *)
(*   P0 _simpl In; *)
(*   repeat break_or; *)
(*   P0 _simpl In; *)
(*   repeat break_or;     *)
(*   simpl; auto 20. *)

(* Ltac peep_tac_pres := apply step_through_preserved_no_touch; peep_tac_no_def. *)

(* Ltac peep_tac_mk_rewrite defs proofs := *)
(*   peep_tac_mk_rewrite' defs proofs; *)
(*   try solve [ *)
(*         peep_tac_aux_proofs | *)
(*         peep_tac_only_forward defs | *)
(*         peep_tac_measure_decr defs | *)
(*         peep_tac_pres *)
(*       ]. *)

(* Definition skipz {A : Type} z (ls : list A) := *)
(*   skipn (nat_of_Z z) ls. *)

Definition no_ptr (st: state_bits) :=
  match st with
    | State_bits rs m _ => no_ptr_regs rs /\ no_ptr_mem m
  end.

Definition st_rs (st : state_bits) :=
  match st with
    | State_bits rs _ _ => rs
  end.

Definition st_m (st : state_bits) :=
  match st with
    | State_bits _ m _ => m
  end.

Definition st_md (st : state_bits) :=
  match st with
    | State_bits _ _ md => md
  end.

Definition current_block (st : state_bits) : option block :=
  match st with
    | State_bits rs m md =>
      match rs # PC with
        | Vint bits =>
          match psur md bits with
            | Some (b,_) => Some b
            | None => None
          end
        | _ => None
      end
  end.


Definition skipz {A : Type} z (ls : list A) :=
  skipn (nat_of_Z z) ls.
  
Definition firstz {A : Type} z (ls : list A) :=
  firstn (nat_of_Z z) ls.

Definition peep_instr (i : instruction) :=
  match i with
    | Pallocframe _ _ _ => False
    | Pfreeframe _ _ _ => False
    | _ => straightline i \/ local_jump i
  end.

Definition peep_code (c : list instruction) :=
  forall i, In i c -> peep_instr i.

Definition step_basic (p: program) (st: state_bits) (st': state_bits) :=
  no_ptr st /\
  nPC p /\
  match env p with
    | ge =>
      match st with
        | State_bits rs m md =>
          match_metadata md m /\ global_perms ge m /\
          match current_fn ge st, current_instr ge st,current_block st with
            | Some fn, Some instr, Some b =>
              peep_instr instr /\
              match exec_instr_bits ge md fn instr b rs m with
                | Nxt rs'' m'' md'' =>
                  match st' with
                    | State_bits rs' m' md' =>
                      rs' = rs'' /\ m' = m'' /\ md' = md''                      
                  end
                | _ => False
              end
            | _, _ , _=> False
          end
      end
  end.

Definition step_fwd (p: program) (st: state_bits) (st': state_bits) (k: Z) : Prop :=
  step_basic p st st' /\  
  (st_rs st') PC = Val.add ((st_rs st) PC) (Vint (Int.repr k)).

Inductive step_basic' : program -> state_bits -> state_bits -> Prop :=
  mk_step_basic':
    forall p ge st st' rs m rs' m' md md' fn instr b,
      no_ptr st ->
      nPC p ->
      ge = env p ->
      st = State_bits rs m md ->
      st' = State_bits rs' m' md' ->
      current_fn ge st = Some fn ->
      current_instr ge st = Some instr ->
      current_block st = Some b ->
      peep_instr instr ->
      exec_instr_bits ge md fn instr b rs m = Nxt rs' m' md' ->
      match_metadata md m ->
      global_perms ge m ->
      step_basic' p st st'.

Definition jumps_to_label (ge: genv) (st: state_bits) (l: label) : Prop :=  
  match st with
    | State_bits rs m md =>
      match current_instr ge st with
        | Some instr =>
          match instr with
            | Pjmp_l l' => l = l'
            | Pjcc cond l' =>      
              match eval_testcond cond rs with
                | Some true => l = l'
                | Some false => False
                | None => False
              end
            | Pjcc2 cond1 cond2 l' => 
              match eval_testcond cond1 rs, eval_testcond cond2 rs with
                | Some true, Some true => l = l'
                | Some _, Some _ => False
                | _, _ => False
              end
            | Pjmptbl r tbl => 
              match rs#r with
                | Vint n => 
                  match list_nth_z tbl (Int.unsigned n) with
                    | None => False
                    | Some l' => l = l'
                  end
                | _ => False
              end
            | _ => False
          end
        | _ => False          
      end
  end.

Definition current_PC (st : state_bits) :=
  match st with
    | State_bits rs _ md =>
      match rs PC with
        | Vint bits => psur md bits
        | _ => None
      end
  end.


Definition current_ofs (st : state_bits) :=  
  match current_PC st with
    | Some (_, ofs) => Some ofs
    | _ => None
  end.

(*GENERAL TACTICS*)

Ltac compute_skipz :=
  match goal with
    | [H: context[ skipz ?Z ?C ] |- _] => compute_expr (skipz Z C)
  end.

Ltac compute_firstz :=
  match goal with
    | [H: context[ firstz ?Z ?C ] |- _] => compute_expr (firstz Z C)
  end.

Lemma ls_pred:
  forall (A : Type) (P : A -> Prop) l (ls : list A),
    (forall a, In a (l :: ls) -> P a) ->
    P l /\ (forall a, In a ls -> P a).
Proof.
  intros.
  split.
  specialize (H l).
  simpl in H.
  conclude H tauto.
  auto.
  intros.
  specialize (H a).
  simpl in H.
  conclude H tauto.
  auto.
Qed.

Ltac simpl_ls_pred :=
  repeat match goal with
           | [H : (forall a, In _ (_ :: _) -> _) |- _] => apply ls_pred in H; break_and
           | [H : (forall a, In _ nil -> _) |- _] => clear H
           | [H : (forall a, In _ ?LS -> _) |- _] => simpl_expr LS
         end.

Ltac simpl_val_eq :=
  match goal with
    | [H: val_eq _ _ |- _] => apply val_eq_or in H; inv H; try (repeat break_and; congruence); [ ]
  end.

Ltac simpl_nth :=
  match goal with
    | [H: context[ nth ?A ?B ?C] |- _] => simpl_expr (nth A B C)
  end.

Ltac inv_some :=
  match goal with
    | [H: Some _ = Some _ |- _] => inv H
  end.

Ltac inv_some' :=
  match goal with
    | [H: Some _ = Some _ |- _] => inversion H
  end.

Ltac inv_vint :=
  match goal with
    | [H: Vint _ = Vint _ |- _ ] => inv H
  end.

Ltac inv_vint' :=
  match goal with
    | [H: Vint _ = Vint _ |- _ ] => inversion H
  end.

Ltac inv_state :=
  match goal with
    | [H: State_bits _ _ _ = State_bits _ _ _ |- _ ] => inv H
  end.

Ltac inv_state' :=
  match goal with
    | [H: State_bits _ _ _ = State_bits _ _ _ |- _ ] => inversion H
  end.

Ltac inv_next :=
  match goal with
    | [H : Nxt _ _ _ = Nxt _ _ _ |- _] => inv H
  end.

Ltac inv_next' :=
  match goal with
    | [H : Nxt _ _ _ = Nxt _ _ _ |- _] => inversion H
  end.

(*GENERAL LEMMAS*)

Lemma no_calls_imp:
  forall c,
    no_calls' c -> no_calls c.
Proof.
  intros.
  unfold no_calls' in *.
  unfold no_calls in *.
  intros.
  specialize (H i).
  mk_exists z in H0.
  rewrite <- find_instr_in in H0.
  specialize (H H0).
  auto.
Qed.

Lemma no_trace_code_imp:
  forall c,
    no_trace_code' c -> no_trace_code c.
Proof.
  intros.
  unfold no_trace_code' in *.
  unfold no_trace_code in *.
  intros.
  specialize (H i).
  mk_exists z in H0.
  rewrite <- find_instr_in in H0.
  specialize (H H0).
  auto.
Qed.

Lemma only_forward_jumps_lab_imp :
  forall c,
    only_forward_jumps_lab' c -> (forall l, only_forward_jumps_lab l c).
Proof.
  intros.
  unfold only_forward_jumps_lab' in *.
  unfold only_forward_jumps_lab in *.
  intros.
  specialize (H i l z z').
  copy H0.
  mk_exists z in H3.
  rewrite <- find_instr_in in H3.
  copy H2.
  mk_exists z' in H4.
  rewrite <- find_instr_in in H4.
  specialize (H H3 H1 H4 H0 H2).
  auto.
Qed.

Lemma not_in_preserved:
  forall r ds,
    In r (lv_in ds ++ lv_out ds ++ clobbered ds) ->
    ~ In r (preserved ds).
Proof.
  intros.
  copy (in_dec preg_eq r (preserved ds)).
  destruct H0; auto.
  unfold preserved in i.
  remember (lv_in ds ++ lv_out ds ++ clobbered ds) as rs.
  copy (rem_in r rs ).
  specialize (H0 all_pregs).
  specialize (H0 preg_eq).
  destruct H0.
  specialize (H1 i).
  break_and.
  congruence.
Qed. 

Lemma label_eq':
  forall (l : label) l0,
    l = l0 \/ l <> l0.
Proof.
  intros.
  copy (label_eq l l0).
  inv H; auto.
Qed.

Lemma jumps_to_label_dec:
  forall ge st l,
    jumps_to_label ge st l \/ ~jumps_to_label ge st l.
Proof.
  intros.
  unfold jumps_to_label.
  repeat break_match; auto using label_eq'.
Qed.  

Lemma mk_jumps_to_label_dec:
  forall z i c ge st t st' l,
    step_through z (i :: c) ge st t st' ->
    labeled_jump i l ->
    jumps_to_label ge st l \/ ~ jumps_to_label ge st l.
Proof.
  intros. apply jumps_to_label_dec.
Qed.

Lemma step_through_at_code:
  forall ge st t st' z c,
    step_through z c ge st t st' ->
    at_code z c 0 ge st.
Proof.
  intros.
  inv H; auto.
Qed.

Lemma at_code_find_instr:
  forall z instr c ge rs m f i b bits md,
    at_code z (instr :: c) 0 ge (State_bits rs m md) ->
    rs PC = Vint bits ->
    psur md bits = Some (b,i) ->
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    find_instr (Int.unsigned i) (fn_code f) = Some instr.
Proof.
  intros.
  inv H.
  unify_stuff.
  rewrite H8.
  rewrite H15.
  exploit find_instr_append_head.
  instantiate (1:=0). omega.
  intros.
  rewrite H.
  simpl.
  auto.
Qed.

Lemma at_code_current_instr:
  forall z instr c ge st,
    at_code z (instr :: c) 0 ge st ->
    current_instr ge st = Some instr.
Proof.
  intros.
  destruct st as (rs, m).
  copy H. inv H0.
  app_new at_code_find_instr H.
  unfold current_instr in *.
  unfold current_code in *.
  unfold current_fn in *.
  unfold fundef in *.
  repeat collapse_match.
  assumption.
Qed.

Lemma step_through_current_instr:
  forall z instr c ge st t st',
    step_through z (instr :: c) ge st t st' ->
    current_instr ge st = Some instr.
Proof.
  intros.
  inv H.
  + eapply at_code_current_instr. eauto.
  + eapply at_code_current_instr. eauto.
Qed.

Lemma current_instr_find_instr_same:
  forall ge st rs m instr1 instr2 f b i bits md,
    current_instr ge st = Some instr1 ->
    find_instr (Int.unsigned i) (fn_code f) = Some instr2 ->
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    rs PC = Vint bits ->
    psur md bits = Some (b, i) ->
    st = State_bits rs m md ->
    instr1 = instr2.
Proof.
  intros.
  unfold current_instr in *.
  unfold current_code in *.
  unfold current_fn in *.
  repeat break_match_hyp; try congruence.
Qed.

Lemma mk_current_fn:
  forall ge st rs m bits b ofs f md,
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    psur md bits = Some (b, ofs) ->
    rs PC = Vint bits ->
    st = State_bits rs m md ->
    current_fn ge st = Some f.
Proof.
  intros.
  unfold current_fn.
  unfold fundef.
  repeat collapse_match.
  auto.
Qed.

Lemma mk_current_PC:
  forall st rs m bits ofs b md,
    rs PC = Vint bits ->
    psur md bits = Some (b, ofs) ->
    st = State_bits rs m md ->
    current_PC st = Some (b, ofs).
Proof.
  intros.  
  unfold current_PC.
  repeat collapse_match.
  congruence.
Qed.


Lemma step_basic_rel:
  forall ge st st',
    step_basic ge st st' <-> step_basic' ge st st'.
Proof.
  intros.
  split; intros.
  + destruct st. destruct st'.
    inv H.
    repeat break_match; try tauto.
    repeat break_and.
    subst.
    econstructor; eauto.
  + 
    unfold step_basic.
    inv H.
    repeat (split; auto).
    repeat collapse_match.
    repeat (split; auto).    
Qed.

Lemma mk_step_basic:
  forall p ge st st' fn i rs m rs' m' b md md',
    current_fn ge st = Some fn ->
    current_instr ge st = Some i ->
    current_block st = Some b ->
    exec_instr_bits ge md fn i b rs m = Nxt rs' m' md' ->    
    no_ptr st ->
    st = State_bits rs m md ->
    st' = State_bits rs' m' md' ->
    peep_instr i ->
    match_metadata md m ->
    global_perms ge m ->
    nPC p ->
    ge = env p ->
    step_basic p st st'.
Proof.
  intros.
  exploit mk_step_basic'; eauto.
  intros. 
  apply step_basic_rel.
  auto.  
Qed.

Lemma step_bits_step_basic:
  forall ge st st' t instr p,
    step_bits ge st t st' ->
    current_instr ge st = Some instr ->
    peep_instr instr ->
    ge = env p ->
    nPC p ->
    step_basic p st st'.
Proof.
  intros.
  invs.
  + exploit current_instr_find_instr_same; eauto; intros.
    subst i.
    NP app_new mk_current_fn Genv.find_funct_ptr.
    subst st.
    exploit mk_step_basic; eauto.
    simpl. repeat collapse_match. auto.
    simpl. auto.
  + exploit current_instr_find_instr_same; eauto; intros.
    subst instr.
    simpl in *. tauto.
  + exploit current_instr_find_instr_same; eauto; intros.
    subst instr.
    simpl in *. tauto.
  + unfold current_instr in *.
    unfold current_code in *.
    unfold current_fn in *.    
    repeat break_match_hyp; try congruence.    
Qed.

Lemma step_through_c_cons:
  forall ge st t st' z c,
    step_through z c ge st t st' ->    
    exists i c',
      c = i :: c'.
Proof.
  intros.
  destruct c.
  NP app_new step_through_at_code step_through.
  inv H0.
  unfold zlen in H4.
  simpl in H4.
  omega.
  eauto.
Qed.

Lemma step_through_step_basic:
  forall z instr c ge st t st' p,
    step_through z c ge st t st' ->
    current_instr ge st = Some instr ->
    peep_instr instr ->
    ge = env p ->
    nPC p ->
    exists st'',
      step_basic p st st''.
Proof.
  intros.
  NP app_new step_through_c_cons step_through.
  subst c.
  app_new step_through_current_instr H.
  inv H.
  + eexists.
    eapply step_bits_step_basic; eauto.
    replace x with instr by congruence.
    auto.
  + replace x with instr in * by congruence.
    eexists.
    eapply step_bits_step_basic; eauto.
Qed.

Lemma mk_in_same_block:
  forall st st' b,
    current_block st = Some b ->
    current_block st' = Some b ->
    in_same_block st st'.
Proof.
  intros.
  unfold current_block in *.
  simpl_match_hyp.  
  unfold current_PC in *.
  simpl_match_hyp.
  repeat inv_some.
  econstructor; eauto.
Qed.

Lemma in_same_block_spec:
  forall st st' b,
    current_block st = Some b ->    
    in_same_block st st' ->
    current_block st' = Some b.
Proof.
  intros.
  unfold current_block in *.
  unfold current_PC in *.
  P inv in_same_block.
  simpl_match_hyp.  
  repeat inv_some.
  inv H3.
  unify_psur.
  repeat collapse_match.
  auto.
Qed.

Lemma mk_find_instr:
  forall ge st instr ofs c,
    current_instr ge st = Some instr ->
    current_ofs st = Some ofs ->
    current_code ge st = Some c ->    
    find_instr (Int.unsigned ofs) c = Some instr.
Proof.
  intros.
  unfold current_instr in *.
  collapse_match_hyp.
  simpl_match_hyp.
  unfold current_ofs in *.
  unfold current_PC in *.
  collapse_match_hyp.
  subst. find_rewrite.
  opt_inv. subst. assumption.
Qed.  

Lemma not_call_builtin:
  forall instr,
    peep_instr instr ->
    ~ is_call_return instr /\ ~ is_builtin instr.
Proof.
  intros.
  destruct instr; split; simpl in *; tauto.
Qed.

Lemma step_basic_corollaries:
  forall st st' p,    
    step_basic p st st' ->    
    exists fn instr rs m rs' m' b md md' ge,
      ge = env p /\
      nPC p /\
      current_fn ge st = Some fn /\      
      current_instr ge st = Some instr /\
      st = State_bits rs m md /\
      st' = State_bits rs' m' md' /\
      exec_instr_bits ge md fn instr b rs m = Nxt rs' m' md' /\
      step_bits ge st E0 st' /\
      no_ptr st /\
      no_ptr st' /\
      peep_instr instr /\
      current_block st = Some b /\
      current_block st' = Some b /\
      current_fn ge st' = Some fn /\
      match_metadata md' m' /\
      md' = md.
Proof.
  intros.
  unfold step_basic in *.
  repeat break_and.
  repeat break_match_hyp; repeat break_and; try congruence; try contradiction.
  subst_max.
  rename r into rs. rename r0 into rs'. rename m0 into m'.
  destruct (current_block (State_bits rs m a)) eqn:?.
  Focus 2.
  unfold current_block in *.
  congruence.
  inv_some.
  exists f. exists i. exists rs. exists m. exists rs'. exists m'. exists b.
  exists a. exists a0. exists (env p).
  P _simpl no_ptr. break_and.
  repeat isplit; auto; clear_taut.
  + unfold current_instr in *.
    unfold current_code in *.
    unfold current_fn in *.  
    repeat break_match_hyp; try congruence.
    repeat inv_some.
    eapply exec_step_internal_bits; eauto.
    unfold current_block in *.
    rewrite Heqv in Heqo2.
    rewrite Heqo1 in Heqo2.
    inv Heqo2. eauto.
  + unfold no_ptr. tauto.
  + simpl.
    eapply NoPtr.no_ptr_regs_preserved'; eauto.
  + unfold current_fn in *.
    unfold current_block in *.
    unfold current_PC in *.
    simpl_match_hyp.
    repeat inv_some.
    destruct f.    
    NP1 app_new mk_find_instr current_instr.
    Focus 2.
    unfold current_ofs.
    unfold current_PC in *.
    repeat collapse_match. reflexivity.
    Focus 2.
    unfold current_code in *.
    unfold current_fn in *.
    repeat collapse_match. reflexivity.    
    NP1 app_new not_call_builtin peep_instr.
    break_and.
    exploit step_PC_same_block; simpl; eauto.
    intros.
    repeat break_exists.
    
    break_and.
    collapse_match.
    collapse_match.
    auto.    
  + unfold current_block in *.
    unfold current_PC in *.    
    unfold current_fn in *.
    simpl_match_hyp.
    repeat inv_some.
    collapse_match.
    reflexivity.
  + NP app_new step_md step_bits.
    tauto.  
  + clear -H11 H15.
    destruct i;
      try solve[
    P1 _simpl peep_instr;
    try tauto;
    simpl in *;
    unfold exec_load_bits in *;
    unfold exec_store_bits in *;
    unfold exec_big_load_bits in *;
    unfold exec_big_store_bits in *;
    unfold goto_label_bits in *;
    repeat break_match_hyp;
    try P1 _inversion Nxt;
    try congruence].    
Qed.

Lemma step_through_current_fn:
  forall z instr c p st t st' ge,    
    step_through z c ge st t st' ->
    ge = env p ->
    nPC p ->
    current_instr ge st = Some instr ->
    peep_instr instr ->
    exists f,
      current_fn ge st = Some f.
Proof.
  intros.
  NP app_new step_through_step_basic step_through.
  NP app_new step_basic_corollaries step_basic.
  repeat break_and.
  subst x9. subst ge.
  eauto.  
Qed.

Lemma at_code_current_fn :
  forall z c ge st,    
    at_code z c 0 ge st ->
    exists f,
      current_fn ge st = Some f.
Proof.
  intros.
  inv H.
  eexists.
  eapply mk_current_fn; eauto.
Qed.

Lemma labeled_jump_is_local_jump:
  forall i l,
    labeled_jump i l ->
    local_jump i.
Proof.
  intros.
  destruct i; simpl; auto.
  unfold labeled_jump in *.
  destruct tbl; simpl in *; congruence.
Qed.

Definition non_jump_jump (i : instruction) (ge : genv) (st : state_bits) :=
  local_jump i /\ (forall l, labeled_jump i l -> ~ jumps_to_label ge st l).

Lemma non_jump_jump_local_jump:
  forall i ge st,
    non_jump_jump i ge st ->
    local_jump i.
Proof.
  intros.  
  unfold non_jump_jump in *.
  tauto.
Qed.

Lemma mk_step_fwd_straightline :
  forall p st st' i ge,    
    step_basic p st st' ->    
    current_instr ge st = Some i ->
    ge = env p ->
    straightline i \/ non_jump_jump i ge st ->
    step_fwd p st st' 1.
Proof.
  intros.
  constructor.
  eauto.
  NP app_new step_basic_corollaries step_basic.
  repeat break_and.
  subst x6. subst x8. subst ge.
  replace x0 with i in * by congruence.    
  assert (Vone = (Vint (Int.repr 1))).
  unfold Vone. unfold Int.one. reflexivity.
  destruct i;
    unfold exec_instr_bits in *;
    unfold goto_label_bits in *;
    unfold exec_load_bits in *;
    unfold exec_store_bits in *;
    unfold exec_big_load_bits in *;
    unfold exec_big_store_bits in *;
    repeat (break_match_hyp; try congruence);
    try st_inv;
    simpl;
    try preg_simpl;
    try congruence;
    try solve [P1 _simpl straightline; P1 _simpl peep_instr; repeat break_or; inv_false].  
  repeat break_match; preg_simpl; try congruence.
  repeat break_match; preg_simpl; try congruence.    
  (* JUMPS *)
  (* TODO semicolon *)
  + break_or; try tauto.
    NP app_new non_jump_jump_local_jump non_jump_jump.    
    assert (labeled_jump (Pjmp_l l) l).
    unfold labeled_jump. auto.
    unfold non_jump_jump in *.
    break_and.
    P2P1 _eapplyin labeled_jump labeled_jump.
    P2 _clear jumps_to_label.
    unfold jumps_to_label in *.
    repeat collapse_match_hyp.
    congruence.  
  + break_or; try tauto.
    NP app_new non_jump_jump_local_jump non_jump_jump.        
    assert (labeled_jump (Pjmp_l l) l).
    unfold labeled_jump. auto.
    unfold non_jump_jump in *.
    break_and.
    P2P1 _eapplyin labeled_jump labeled_jump.
    P2 _clear jumps_to_label.
    unfold jumps_to_label in *.
    repeat collapse_match_hyp.
    congruence.
  + break_or; try tauto.
    NP app_new non_jump_jump_local_jump non_jump_jump.    
    assert (labeled_jump (Pjmp_l l) l).
    unfold labeled_jump. auto.
    unfold non_jump_jump in *.
    break_and.
    P2P1 _eapplyin labeled_jump labeled_jump.
    P2 _clear jumps_to_label.
    unfold jumps_to_label in *.
    repeat collapse_match_hyp.
    congruence.  
  + break_or.
    * P1 _simpl straightline.
      simpl_exec.
      subst tbl.
      simpl_match_hyp.
      NP1 _applyin list_nth_z_in list_nth_z.
      P _simpl In.
      tauto.
    * assert (labeled_jump (Pjmptbl r tbl) l).
      unfold labeled_jump. auto.
      eapply list_nth_z_in.
      eauto.
      unfold non_jump_jump in *.
      break_and.
      P2P1 _eapplyin labeled_jump labeled_jump.
      P2 _clear jumps_to_label.
      unfold jumps_to_label in *.
      repeat collapse_match_hyp.
      congruence.
Qed.

Lemma step_basic_no_ptr:
  forall p st st',    
    step_basic p st st' ->
    no_ptr st'.
Proof.
  intros.
  app_new step_basic_corollaries H.
  tauto. 
Qed.

Lemma step_fwd_step_basic:
  forall p st st' k,
    step_fwd p st st' k ->
    step_basic p st st'.
Proof.
  intros.
  inv H.
  assumption.
Qed.

Lemma step_fwd_exec:
  forall p st st' instr f rs m rs' m' k md md' b ge,
    step_fwd p st st' k ->
    ge = env p ->
    current_fn ge st = Some f ->
    current_instr ge st = Some instr ->
    current_block st = Some b ->
    st = State_bits rs m md ->
    st' = State_bits rs' m' md' ->
    rs' PC = Val.add (rs PC) (Vint (Int.repr k)) /\
    exec_instr_bits ge md f instr b rs m = Nxt rs' m' md'.
Proof.
  intros.
  P inv step_fwd.
  split.
  auto.
  NP app_new step_basic_corollaries step_basic.
  repeat break_and.
  unfold current_fn in *.
  unfold current_code in *.
  unfold current_instr in *.
  unfold current_block in *.
  unfold current_PC in *.
  repeat (break_match; try congruence).
Qed.

Lemma zlen_nil:
  forall {A : Type},
    zlen (@nil A) = 0.
Proof.
  intros. unfold zlen. simpl.
  reflexivity.
Qed.

Lemma at_code_nil:
  forall ge st z ofs,
    at_code z nil ofs ge st ->
    False.
Proof.
  intros.
  inv H.
  copy (@zlen_nil instruction).
  rewrite H in *.
  omega.
Qed.

Lemma step_bits_no_trace :
  forall ge st t st' i,
    step_bits ge st t st' ->
    current_instr ge st = Some i ->
    no_trace i ->
    t = E0.
Proof.
  intros.
  unfold current_instr in *.
  unfold current_code in *.
  unfold current_fn in *.
  simpl_match_hyp.
  repeat inv_some.
  inv H.
  reflexivity.
  unify_stuff.
  simpl in H1.
  tauto.
  unify_stuff.
  simpl in H1.
  tauto.
  congruence.
Qed.

(*DON'T REMOVE. Might be needed for loads & stores*)
(* Lemma eval_addrmode_bits_transf: *)
(*   forall ge1 ge2 a rs, *)
(*     (forall id ofs, *)
(*        Genv.symbol_address ge1 id ofs = *)
(*        Genv.symbol_address ge2 id ofs) -> *)
(*    eval_addrmode_bits ge1 a rs = *)
(*    eval_addrmode_bits ge2 a rs. *)
(* Proof. *)
(*   (*TODO P1*) *)
(*   admit. *)
(* Qed. *)

Lemma jumps_to_label_is_labled_jump:
  forall ge st l i,
    jumps_to_label ge st l ->
    current_instr ge st = Some i ->
    labeled_jump i l.
Proof.
  intros.
  unfold jumps_to_label in *.
  repeat break_match_hyp; try contradiction;
  inv H0; simpl; auto.
  eapply list_nth_z_in.
  eauto.
Qed.

Lemma label_pos_mid:
  forall l c0 c c1 pos_f pos_c,
    label_pos l 0 (c0 ++ c ++ c1) = Some pos_f ->
    label_pos l 0 c = Some pos_c ->    
    zlen c0 < pos_f <= zlen c0 + zlen c ->    
    pos_f = zlen c0 + pos_c.
Proof.
  intros.
  eapply label_pos_append_head in H.
  2: omega.
  eapply label_pos_append_tail in H.  
  2: omega.
  instantiate (1 := nil) in H.
  replace (c ++ nil) with c in * by auto.
  rewrite H0 in H.
  inv H.
  omega.
Qed.

Lemma step_basic_current_instr:
  forall p st st' ge,    
    step_basic p st st' ->
    ge = env p ->
    exists i,
      current_instr ge st = Some i.
Proof.
  intros.
  eapply step_basic_corollaries in H; eauto.
  repeat break_exists. repeat break_and.
  subst_max.
  eauto.
Qed.

Lemma jumps_to_label_exec:
  forall ge f i rs m rs' m' l st md md' b,
    exec_instr_bits ge md f i b rs m = Nxt rs' m' md' ->
    current_instr ge st = Some i ->
    current_block st = Some b ->
    jumps_to_label ge st l ->
    st = State_bits rs m md ->
    goto_label_bits md f l b rs m = Nxt rs' m' md'.
Proof.
  intros.
  NP app_new jumps_to_label_is_labled_jump jumps_to_label.
  NP app_new labeled_jump_is_local_jump labeled_jump.
  unfold jumps_to_label in *.
  rewrite H0 in H2.
  rewrite H3 in H2.
  destruct i; try tauto.
  + subst.
    simpl in H.
    eauto.
  + repeat break_match_hyp; try tauto; subst.
    simpl in H.
    repeat break_match_hyp; try congruence.
  + repeat break_match_hyp; try tauto; subst.
    simpl in H.
    repeat break_match_hyp; try congruence.
  + repeat break_match_hyp; try tauto; subst.
    simpl in H.
    repeat break_match_hyp; try congruence.
Qed.

Lemma step_jump_exec:
  forall p st st' f l rs m rs' m' md md' b ge,    
    step_basic p st st' ->
    ge = env p ->
    current_fn ge st = Some f ->
    jumps_to_label ge st l ->
    st = State_bits rs m md ->
    st' = State_bits rs' m' md' ->
    current_block st = Some b ->
    goto_label_bits md f l b rs m = Nxt rs' m' md'.
Proof.
  intros.
  NP _app step_basic_corollaries step_basic.
  repeat break_exists. repeat break_and.
  subst_max.
  eapply jumps_to_label_exec; eauto.
  congruence.  
Qed.

Lemma current_fn_unify:
  forall ge st b i f1 f2 rs m bits md,
    current_fn ge st = Some f1 ->
    Genv.find_funct_ptr ge b = Some (Internal f2) ->
    st = State_bits rs m md ->
    rs PC = Vint bits ->
    psur md bits = Some (b, i) ->
    f1 = f2.
Proof.
  intros.
  exploit mk_current_fn; eauto.
  intros.
  congruence.
Qed.

Lemma mk_current_code:
  forall ge st rs m bits b ofs f md,
    rs PC = Vint bits ->
    psur md bits = Some (b, ofs) ->
    st = State_bits rs m md ->
    current_fn ge st = Some f ->
    current_code ge st = Some (fn_code f).
Proof.
  intros.
  unfold current_code.
  collapse_match.
  auto.
Qed.

Lemma mk_current_instr:
  forall ge st rs m bits b ofs f i md,
    rs PC = Vint bits ->
    psur md bits = Some (b, ofs) ->
    st = State_bits rs m md ->
    current_fn ge st = Some f ->
    find_instr (Int.unsigned ofs) (fn_code f) = Some i ->
    current_instr ge st = Some i.
Proof.  
  intros.
  unfold current_instr.  
  subst st.
  app_new mk_current_code H2.
  repeat collapse_match.
  auto.
Qed.

Lemma current_instr_unify:
  forall ge st b i f i1 i2 rs m bits md,
    current_instr ge st = Some i1 ->    
    find_instr (Int.unsigned i) (fn_code f) = Some i2 ->
    current_fn ge st = Some f ->
    st = State_bits rs m md ->
    rs PC = Vint bits ->
    psur md bits = Some (b, i) ->
    i1 = i2.
Proof.
  intros.
  exploit mk_current_instr; eauto.
  intros.
  congruence.
Qed.

Lemma step_basic_step_bits:
  forall p st st' ge,    
    step_basic p st st' ->
    ge = env p ->
    step_bits ge st E0 st'.
Proof.
  intros.  
  NP _app step_basic_corollaries step_basic.
  repeat break_exists; repeat break_and.
  subst_max.
  assumption.
Qed.

Lemma exec_instr_deterministic:
  forall ge f i rs m rs1 rs2 m1 m2 md md1 md2 b,
    exec_instr_bits md ge f i b rs m = Nxt rs1 m1 md1 ->
    exec_instr_bits md ge f i b rs m = Nxt rs2 m2 md2 ->
    rs1 = rs2 /\ m1 = m2 /\ md1 = md2.
Proof.
  intros.
  rewrite H in H0. inv H0.
  tauto.
Qed.

Lemma step_bits_unify:
  forall ge st t1 t2 st1 st2 i,
    step_bits ge st t1 st1 ->
    step_bits ge st t2 st2 ->
    current_instr ge st = Some i ->
    peep_instr i ->
    st1 = st2 /\ t1 = t2.
Proof.
  intros.
  inv H; inv H0;
  try solve [unify_stuff; simpl in *; congruence].
  + unify_stuff.
    split; auto.
    exploit exec_instr_deterministic.
    P1 _eapply exec_instr_bits.
    P2 _eapply exec_instr_bits.
    intros.
    congruence.
  + unify_stuff.
    unfold current_instr in *.
    unfold current_code in *.
    unfold current_fn in *.
    simpl_match_hyp.
    repeat inv_some.
    inv H3.    
    unify_stuff.
    simpl in H2. tauto.
  + unify_stuff.
    unfold current_instr in *.
    unfold current_code in *.
    unfold current_fn in *.
    simpl_match_hyp.
    repeat inv_some.
    inv H3.    
    unify_stuff.
    simpl in H2. tauto.
  + unify_stuff.
    unfold current_instr in *.
    unfold current_code in *.
    unfold current_fn in *.
    repeat break_match_hyp; try congruence.
Qed.

Lemma step_basic_bits_unify_st:
  forall p st st1 st2 t ge ,    
    step_basic p st st1 ->
    ge = env p ->
    step_bits ge st t st2 ->
    st1 = st2.
Proof.
  intros.
  NP app_new step_basic_step_bits step_basic.
  NP app_new step_basic_corollaries step_basic.
  repeat break_and.
  subst_max.
  eapply step_bits_unify; eauto.  
Qed.

Lemma at_code_ofs_unify:
  forall ge st z c ofs1 ofs2,
    at_code z c ofs1 ge st ->
    at_code z c ofs2 ge st ->
    ofs1 = ofs2.
Proof.
  intros.
  inv H.
  inv H0.
  unify_stuff.
  omega.
Qed.

Lemma at_code_end_at_code_ofs:
  forall ge st z c c' ofs,
    at_code z (c ++ c') ofs ge st ->
    at_code_end z c ge st ->
    ofs = zlen c.
Proof.
  intros.
  inv H.
  inv H0.
  unify_stuff.
  omega.
Qed.

Lemma step_through_progress:
  forall p st t st' st'' z c ofs' ge,    
    step_through z c ge st t st' ->
    step_basic p st st'' ->    
    at_code z c 0 ge st ->
    at_code z c ofs' ge st'' ->
    ge = env p ->
    0 < ofs'.
Proof.
  intros.
  NP app_new step_through_c_cons step_through.
  subst. rename x into i. rename x0 into c.
  inv H.
  + exploit step_basic_bits_unify_st; eauto. intros. subst.
    exploit at_code_end_at_code_ofs.
    2: eauto.
    instantiate (2 := nil).
    rewrite app_nil_r.
    eauto.
    intros.
    rewrite zlen_cons in *.
    copy (zlen_nonneg _ c).
    omega.
  + exploit step_basic_bits_unify_st; eauto. intros. subst stB.
    P inv star_step_in.
    - P inv in_code.
      eapply at_code_ofs_unify in H2.
      2: eapply H8.
      omega.
    - inv H8.
      eapply at_code_ofs_unify in H2.
      2: eapply H10.
      omega.
Qed.

Lemma step_through_next_at_code:
  forall p st t st' st'' z c ge,    
    step_through z c ge st t st' ->
    step_basic p st st'' ->
    ge = env p ->
    (exists ofs, at_code z c ofs ge st'' /\ 0 < ofs) \/ (at_code_end z c ge st'' /\ st' = st'').
Proof.
  intros.
  P copy step_through.
  P1 inv step_through.
  right.
  cut (st' = st'').
  intros. subst. auto.
  eapply step_basic_bits_unify_st in H0; eauto.
  left.
  NP app_new step_basic_bits_unify_st step_basic.
  subst stB.
  NP app_new star_step_in_at_code star_step_in.
  eexists. split. eauto.
  exploit step_through_progress; eauto.
Qed.

Lemma at_code_expand:
  forall ge st c ofs f c0 c1,
    at_code (zlen c0) c ofs ge st ->
    current_fn ge st = Some f ->
    fn_code f = c0 ++ c ++ c1 ->
    at_code 0 (fn_code f) (zlen c0 + ofs) ge st.
Proof.
  intros.
  assert (exists (a : list instruction), a = nil) by eauto.
  break_exists.
  replace 0 with (zlen x) by (subst; simpl; auto).
  subst.
  destruct st as (rs, m).
  inv H.
  NP app_new current_fn_unify current_fn. subst fd.
  econstructor; eauto.
  Focus 2.
  instantiate (1 := nil).      
  simpl.
  rewrite app_nil_r. auto.
  rewrite H14.
  rewrite zlen_app.
  rewrite zlen_app.
  copy (zlen_nonneg _ c4).
  copy (zlen_nonneg _ c3).
  copy (zlen_nonneg _ c).
  omega.
Qed.

Lemma at_code_end_expand:
  forall ge st c f c0 c1,
    at_code_end (zlen c0) c ge st ->
    current_fn ge st = Some f ->
    fn_code f = c0 ++ c ++ c1 ->
    at_code_end 0 (c0 ++ c) ge st.
Proof.
  intros.
  assert (exists (a : list instruction), a = nil) by eauto.
  break_exists.
  replace 0 with (zlen x) by (subst; simpl; auto).
  subst.
  destruct st as (rs, m).
  inv H.
  NP app_new current_fn_unify current_fn. subst fd.
  econstructor; eauto.
  Focus 2.
  instantiate (1 := c1).
  simpl.
  rewrite H1. rewrite app_assoc. auto.
  simpl. rewrite zlen_app.
  congruence.
Qed.

Lemma step_basic_next_current_fn:
  forall p st st' f ge,
    step_basic p st st' ->
    ge = env p ->
    current_fn ge st = Some f ->
    current_fn ge st' = Some f.
Proof.
  intros.
  eapply step_basic_corollaries in H; eauto.
  repeat break_exists; repeat break_and.    
  congruence.
Qed.

Lemma fn_code_unify:
  forall f c0 c1 c2 c3 c,
    fn_code f = c0 ++ c ++ c1 ->
    fn_code f = c2 ++ c ++ c3 ->
    zlen c0 = zlen c2 ->
    c0 = c2 /\ c1 = c3.
Proof.
  intros.
  rewrite H in H0.
  exploit (@list_eq_middle_therefore_eq instruction); eauto.
Qed.

Lemma step_jump_PC:
  forall p st st' f l pos_f ge,    
    step_basic p st st' ->
    ge = env p ->
    jumps_to_label ge st l ->
    label_pos l 0 (fn_code f) = Some pos_f ->
    current_fn ge st = Some f ->
    current_ofs st' = Some (Int.repr pos_f).
Proof.  
  intros.
  destruct st as (rs, m).
  destruct st' as (rs', m').

  app step_basic_corollaries H.
  repeat break_and.
  subst_max.  
  repeat inv_state.    
  
  NP _app step_gp step_bits.
  NP _app step_md step_bits.
  repeat break_and.

  name H15 Hcur_block.
  
  unfold current_block in *.

  repeat break_match_hyp; try congruence. subst.
  repeat opt_inv. subst x5 b0.
  
  unfold current_ofs. unfold current_PC.
  repeat collapse_match.
  erewrite weak_valid_pointer_sur in * by eauto.
  repeat break_and.  

  NP app_new step_jump_exec step_basic.
  NP app_new step_basic_current_instr step_basic.
  NP app_new jumps_to_label_is_labled_jump jumps_to_label.
  NP _applyin labeled_jump_is_local_jump labeled_jump.
  replace 0 with (zlen (@nil instruction)) by auto.
  unfold goto_label_bits in *.
  simpl_match_hyp.
  assert (z = pos_f) by congruence. subst pos_f. clear_taut.
  repeat st_inv.
  preg_simpl_hyp Heqv0. inv Heqv0.
  instantiate (1 := b) in Heqo0.
  eapply pinj_injective_within_block in Heqo0; try apply H19.
  congruence.
  unfold current_block.
  repeat collapse_match.
  name (conj H15 H16) Hpsur.
  erewrite <- weak_valid_pointer_sur in Hpsur; eauto.
  collapse_match. reflexivity.
Qed.

Lemma at_code_current_ofs:
  forall ge st z c ofs,
    at_code z c ofs ge st ->    
    current_ofs st = Some (Int.repr (z + ofs)).
Proof.
  intros.
  inv H.
  unfold current_ofs.
  simpl.
  collapse_match.
  collapse_match.
  f_equal.
  assert (Int.repr (Int.unsigned i) = Int.repr (zlen c1 + ofs)).
  f_equal.
  assumption.
  rewrite Int.repr_unsigned in H.
  assumption.
Qed.

Lemma at_code_end_current_ofs:
  forall ge st z c,
    at_code_end z c ge st ->    
    current_ofs st = Some (Int.repr (z + zlen c)).
Proof.
  intros.
  inv H.
  unfold current_ofs.
  simpl.
  collapse_match.
  collapse_match.
  f_equal.
  assert (Int.repr (Int.unsigned i) = Int.repr (zlen c1 + zlen c)).
  f_equal.
  assumption.
  rewrite Int.repr_unsigned in H.
  assumption.
Qed.

Lemma at_code_c_cons:
  forall ge st c z ofs,
    at_code z c ofs ge st ->
    exists i c',
      c = i :: c'.
Proof.
  intros.  
  destruct c.
  exploit at_code_not_nil; eauto.
  tauto.
  eauto.
Qed.

Lemma split_ls :
  forall {A : Type} (ls : list A) z,    
    ls = firstz z ls ++ skipz z ls.
Proof.  
  unfold firstz. unfold skipz.  
  auto using firstn_skipn.
Qed.

Lemma z_nat_roundtrip:
  forall z,
    0 <= z ->
    Z_of_nat' (nat_of_Z z) = z.
Proof.
  intros.
  unfold Z_of_nat'.
  rewrite nat_of_Z_max.
  rewrite Zmax_spec.
  break_if; omega.
Qed.  

Lemma zlen_firstz :
  forall {A : Type} (ls : list A) z,
    0 <= z <= zlen ls ->
    zlen (firstz z ls) = z.
Proof.
  intros.
  unfold firstz.
  unfold zlen.
  erewrite firstn_length.
  copy (Min.min_spec (nat_of_Z z) (length ls)).
  break_or; break_and.
  rewrite H1.
  rewrite z_nat_roundtrip by omega.
  auto.
  remember (nat_of_Z z) as zn.
  rewrite H1.
  assert (zlen ls = zlen ls) by omega.
  unfold zlen at 1 in H2.
  rewrite H2.
  assert (zlen ls = z \/ z < zlen ls) by omega.
  break_or.
  auto.
  copy Z2Nat.inj_le.
  assert (zlen ls = zlen ls) by omega.
  unfold zlen at 1 in H5.
  rewrite <- (Nat2Z.id (length ls)) in H0.
  unfold Z_of_nat' in H5.
  rewrite H5 in H0.
  specialize (H3 (zlen ls) z).
  forward H3.
  omega.  
  specialize (H3 H6).
  forward H3.
  omega.  
  specialize (H3 H7).
  inv H3.
  unfold nat_of_Z in H0.
  specialize (H9 H0).
  omega.  
Qed.

Lemma skipz_nil:
  forall {A : Type} k,
    skipz k (@nil A) = nil.
Proof.
  intros.  
  unfold skipz.
  unfold skipn.
  remember (nat_of_Z k) as n.
  clear Heqn.
  destruct n.
  exact eq_refl.
  exact eq_refl.
Qed.

Lemma skipz_0:
  forall {A : Type} (c : list A),
    skipz 0 c = c.
Proof.
  intros.
  vm_compute. auto.
Qed.

Lemma skipz_1:
  forall {A: Type} (i : A) c,
    skipz 1 (i :: c) = c.
Proof.
  intros.
  vm_compute. auto.
Qed.

Lemma skipz_in:
  forall {A : Type} (i : A) c' c k,
    In i c' ->
    skipz k c = c' ->
    In i c.
Proof.
  intros.
  copy (split_ls c k).
  rewrite H0 in H1.
  rewrite H1.
  rewrite in_app.
  right. auto.                  
Qed.

(* Lemma firstz_zlen': *)
(*   forall {A : Type} (c : list A) k, *)
(*     zlen c >= k -> *)
(*     zlen (firstz k c) = k. *)
(* Proof. *)
(* admit. *)  
(* Qed. *)

(* Lemma skipz_k_1: *)
(*   forall {A : Type} k (c : list A) i, *)
(*     skipz (k + 1) (i :: c) = skipz k c. *)
(* Proof. *)
(*   admit. *)
(* Qed. *)

(* Lemma skipz_skipz: *)
(*   forall {A: Type} (c : list A) a b, *)
(*     0 <= a -> *)
(*     0 <= b -> *)
(*     skipz a (skipz b c) = skipz (a + b) c. *)
(* Proof. *)
(*   admit. *)
(* Qed. *)

Lemma skipn_cons:
  forall {A : Type } n (i : A) c,
    skipn (n + 1) (i :: c) = skipn n c.
Proof.
  intros.
  replace ((n + 1)%nat) with ((1 + n)%nat) by omega.
  simpl.
  reflexivity.
Qed.

Lemma skipz_cons:
  forall {A : Type} k i (c : list A),
    0 < k ->
    skipz k (i :: c) = skipz (k - 1) c.
Proof.
  intros.  
  remember (k - 1) as k'.
  replace k with (k' + 1) by omega.
  assert (0 <= k') by omega.
  clear Heqk'. clear H.
  exploit (nat_of_Z_plus k' 1); try omega. intro.        
  unfold skipz.
  rewrite H.
  remember (nat_of_Z k') as n.
  clear H. clear Heqn. clear H0. clear k'. clear k.
  compute_expr (nat_of_Z 1).
  apply skipn_cons.
Qed.

Lemma zlen_skipz :
  forall {A : Type} (ls : list A) z,
    0 <= z <= zlen ls ->
    zlen (skipz z ls) = zlen ls - z.
Proof.
  induction ls; intros.
  simpl.
  rewrite (@zlen_nil A) in *.
  assert (z = 0) by omega.
  rewrite skipz_nil.
  rewrite (@zlen_nil A).
  omega.
  assert (z = 0 \/ 0 < z) by omega.
  break_or.
  rewrite skipz_0.
  rewrite zlen_cons. omega.
  rewrite skipz_cons by omega.
  specialize (IHls (z - 1)).
  forward IHls.
  rewrite zlen_cons in H.
  omega.
  apply IHls in H0.
  rewrite zlen_cons.
  omega.
Qed.

Lemma nat_of_Z_of_nat:
  forall n,
    nat_of_Z (Z_of_nat' n) = n.
Proof.  
  intros.  
  unfold nat_of_Z.
  unfold Z_of_nat'.
  rewrite Nat2Z.id.
  reflexivity.  
Qed.

Lemma skipz_zlen:
  forall (A : Type) (l1 l2 : list A),
    skipz (zlen l1) (l1 ++ l2) = l2.
Proof.
  intros.
  unfold skipz. unfold zlen.
  rewrite nat_of_Z_of_nat.
  eauto using skipn_len.
Qed.

Lemma firstz_zlen:
  forall {A : Type} (c : list A),
    firstz (zlen c) c = c.
Proof.
  intros.
  unfold firstz.
  rewrite nat_zlen.
  replace c with (c ++ nil) at 2 by auto.
  rewrite firstn_len.
  reflexivity.
Qed.

Lemma skipz_zlen_nil:
  forall {A : Type} (c : list A),
    skipz (zlen c) c = nil.
Proof.
  intros.
  unfold skipz.
  rewrite nat_zlen.
  replace c with (c ++ nil) at 2 by auto.
  erewrite skipn_len.
  reflexivity.
Qed.

Lemma firstz_cons:
  forall {A : Type} k (i : A) c,
    0 <= k ->
    firstz (k + 1) (i :: c) = i :: (firstz k c).
Proof.
  intros.
  unfold firstz.
  remember (nat_of_Z k) as kn.
  remember (nat_of_Z (k + 1)) as kn'.
  assert (kn' = Datatypes.S kn).
  exploit (nat_of_Z_plus k 1).
  omega. omega.
  intros.
  rewrite Heqkn'.
  rewrite H0.
  simpl.
  rewrite <- Heqkn.
  rewrite Pos2Nat.inj_1.
  rewrite NPeano.Nat.add_1_r.
  auto.
  rewrite H0.
  simpl.
  auto.
Qed.

Lemma firstz_nonnil:
  forall {A : Type} k (c : list A),
    c <> nil ->
    k > 0 ->
    firstz k c <> nil.
Proof.
  intros.
  destruct c; try tauto.
  remember (k - 1) as k'.
  replace k with (k' + 1) by omega.
  rewrite firstz_cons.
  congruence.
  omega.  
Qed.

Lemma at_code_firstz:
  forall k z c ge st,
    at_code z c 0 ge st ->
    0 < k < zlen c ->
    at_code z (firstz k c) 0 ge st.
Proof.
  intros.
  inv H.
  rewrite (split_ls c k) in H6.
  rewrite <- app_assoc in H6.
  remember (skipz k c ++ c2) as c2'.
  econstructor; eauto.
  rewrite zlen_firstz.  
  omega.
  omega.
Qed.

Lemma at_code_end_skipz:
  forall ge st z c k,
    at_code_end z c ge st ->
    0 <= k <= zlen c ->
    at_code_end (z + k) (skipz k c) ge st.
Proof.
  intros.
  rewrite (split_ls c k) in H.
  exploit (zlen_firstz c k).
  omega. intro.
  exploit (zlen_skipz c k).
  omega. intro.
  inversion H.
  rewrite <- H1 at 1.
  rewrite <- zlen_app.
  econstructor; eauto.
  rewrite zlen_app.
  rewrite zlen_app in H5.
  omega.
  rewrite <- app_assoc.
  rewrite <- app_assoc in H7.
  eauto.
Qed.

Lemma at_code_k:
  forall ge st ofs z c k,
    at_code z c (k + ofs) ge st ->
    0 <= k /\ 0 <= ofs ->                          
    at_code (z + k) (skipz k c) ofs ge st.
Proof.
  intros.
  inv H.
  copy (split_ls c k).
  assert (zlen (firstz k c) = k).
  apply zlen_firstz.
  omega.
  rewrite <- H7 at 1.
  rewrite <- zlen_app.  
  econstructor; eauto.
  rewrite zlen_app.
  omega.
  copy (zlen_skipz c k).
  omega.
  repeat rewrite <- app_assoc.
  rewrite H6.
  f_equal.
  rewrite app_assoc.
  f_equal.
  auto.
Qed.

Lemma at_code_0:
  forall ge st ofs z c,
    at_code z c ofs ge st ->
    at_code (z + ofs) (skipz ofs c) 0 ge st.
Proof.
  intros.
  inv H.
  rewrite (split_ls c ofs) in H5.
  assert (zlen (c1 ++ (firstz ofs c)) = zlen c1 + ofs).
  rewrite zlen_app.
  f_equal.
  exploit (zlen_firstz c ofs).
  omega.
  intros.
  auto.
  remember (c1 ++ firstz ofs c) as c'.
  rewrite app_assoc in H5.
  rewrite app_assoc in H5.  
  rewrite <- Heqc' in H5.
  rewrite <- app_assoc in H5.
  rewrite <- H.
  econstructor.
  eauto.
  eauto.  
  omega.
  2: eauto.
  exploit (zlen_skipz c ofs).
  omega.
  intros.
  omega.
  eauto.
Qed.

Lemma at_code_find_instr':
  forall ge st ofs z c f instr,
    at_code z c ofs ge st ->
    current_instr ge st = Some instr ->
    current_fn ge st = Some f ->
    find_instr (z + ofs) (fn_code f) = Some instr.
Proof.
  intros.
  NP _applyin at_code_0 at_code.
  NP app_new at_code_c_cons at_code.
  rewrite H2 in H. rename x0 into c'. rename x into i.
  NP app_new at_code_current_instr at_code.
  destruct st as (rs, m).
  P copy at_code.
  P1 inv at_code.  
  NP app_new at_code_find_instr at_code.
  rewrite H11 in H4.
  rewrite Z.add_0_r in H4.
  assert (i = instr) by congruence. subst i.
  assert (f = fd) by (eauto using current_fn_unify). subst fd.
  assumption.
Qed.

Lemma mk_find_funct_ptr:
  forall ge st f b,
    current_fn ge st = Some f ->
    current_block st = Some b ->
    Genv.find_funct_ptr ge b = Some (Internal f).
Proof.
  intros.
  unfold current_fn in *; unfold current_block in *.
  simpl_match_hyp.  
  unfold current_PC in *.
  simpl_match_hyp.
  repeat inv_some.
  inv Heqv.
  assumption.
Qed.

Lemma mk_current_block:
  forall st rs m bits ofs b md,
    rs PC = Vint bits ->
    psur md bits = Some (b, ofs) ->
    st = State_bits rs m md ->
    current_block st = Some b.
Proof.
  intros.
  unfold current_block.
  unfold current_PC.
  repeat collapse_match.
  reflexivity.
Qed.

Lemma at_code_current_block:
  forall ge st z c ofs,
    at_code z c ofs ge st ->
    exists b,
      current_block st = Some b.
Proof.
  intros.
  inv H.
  exploit mk_current_block; eauto.
Qed.         

Lemma at_code_nPC:
  forall p ge st c z ofs,
    at_code z c ofs ge st ->
    ge = env p ->
    nPC p ->
    Int.unsigned (Int.repr (z + ofs)) = z + ofs.
Proof.
  intros.  
  NP _applyin at_code_0 at_code.
  NP app_new at_code_c_cons at_code.
  rename x into c'. rename x0 into i.
  rewrite H2 in H.
  destruct st as (rs, m).
  NP app_new at_code_current_instr at_code.
  NP app_new at_code_current_fn at_code.
  rename x into f.
  NP app_new at_code_find_instr' at_code.
  NP app_new at_code_current_block at_code.
  exploit unsigned_repr_PC.
  eauto.
  eapply mk_find_funct_ptr; eauto.
  P _rewriteb (env p). eauto.
  right. eauto.
  intros.
  rewrite Z.add_0_r in H7.
  assumption.
Qed.

Lemma last_is_in:
  forall {A: Type} (c : list A) i i',
    i = last c i' ->
    c <> nil ->
    In i c.
Proof.
  induction c; intros.  
  tauto.
  simpl in H.
  break_match_hyp.
  subst. simpl. auto.
  apply IHc in H.
  simpl. simpl in H.
  break_or; auto.
  congruence.
Qed.  

Lemma at_code_end_find_instr:
  forall ge st z c f,
    at_code_end z c ge st ->
    0 < z + zlen c ->
    current_fn ge st = Some f ->
    exists instr,
      find_instr (z + zlen c - 1) (fn_code f) = Some instr.
Proof.
  intros.    
  inv H.
  assert (f = fd) by (eauto using current_fn_unify). subst fd.
  rewrite H6.
  rewrite app_assoc.
  remember (c1 ++ c) as c'.
  assert (0 < zlen c').
  rewrite Heqc'.
  rewrite zlen_app. auto.
  replace (zlen c1 + zlen c) with (zlen c').
  Focus 2.
  rewrite Heqc'.
  rewrite zlen_app. auto.
  erewrite find_instr_append_tail.
  2: omega.
  instantiate (1 := nil).
  rewrite app_nil_r.
  eapply in_range_find_instr.
  omega.
Qed.

Lemma at_code_end_current_fn:
  forall ge st z c,
    at_code_end z c ge st ->
    exists f,
      current_fn ge st = Some f.
Proof.
  intros.
  inv H.
  eexists.
  eapply mk_current_fn; eauto.
Qed.

Lemma at_code_end_current_block:
  forall ge st z c,
    at_code_end z c ge st ->
    exists b,
      current_block st = Some b.
Proof.
  intros.
  inv H.
  exploit mk_current_block; eauto.
Qed.

Lemma at_code_end_nPC:
  forall p ge st c z,
    at_code_end z c ge st ->    
    ge = env p ->
    nPC p ->    
    Int.unsigned (Int.repr (z + zlen c)) = z + zlen c.
Proof.
  intros.
  assert (0 < z + zlen c \/ (z = 0 /\ zlen c = 0)).
  inv H.
  copy (zlen_nonneg _ c).
  copy (zlen_nonneg _ c1).
  omega.
  break_or.
  + NP app_new at_code_end_current_fn at_code_end.
    NP app_new at_code_end_find_instr at_code_end.
    NP app_new at_code_end_current_block at_code_end.
    exploit unsigned_repr_PC.
    eauto.
    unfold current_fn in *.
    simpl_match_hyp.
    unfold current_block in *.
    unfold current_PC in *.
    simpl_match_hyp.
    repeat inv_some.
    inv Heqv.        
    unify_stuff.
    eauto.
    left.
    eauto.
    intros.
    assumption.
  + break_and. subst. rewrite H2. simpl.
    vm_compute.
    reflexivity.
Qed.

Lemma step_basic_nPC:
  forall p st st',
    step_basic p st st' ->
    nPC p.
Proof.
  intros.
  unfold step_basic in *.
  tauto.
Qed.
  
Lemma step_through_PC_bounds:
  forall st t st' st'' c z pc p ge,
    step_through z c ge st t st' ->
    step_basic p st st'' ->
    current_ofs st'' = Some pc ->
    ge = env p ->    
    z < Int.unsigned pc <= z + zlen c.
Proof.
  intros.  
  NP app_new step_through_at_code step_through.
  NP app_new step_through_next_at_code step_through.
  break_or.
  + break_exists. break_and.
    NP1 app_new at_code_current_ofs at_code.    
    assert (pc = (Int.repr (z + x))) by congruence.
    subst pc.
    NP1 app_new at_code_nPC at_code.
    P _rewrite Int.unsigned.
    P1 inv at_code.
    cut (0 < x). intros. omega.
    omega.
    eapply step_basic_nPC; eauto.
  + break_and. subst st''.
    NP app_new at_code_end_current_ofs at_code_end.
    assert (pc = (Int.repr (z + zlen c))) by congruence.
    subst pc.
    NP app_new at_code_end_nPC at_code_end.
    P1 _rewrite z.
    P1 inv at_code.
    omega.
    eapply step_basic_nPC; eauto.
Qed.

Lemma step_through_current_instr':
  forall ge st st' z c t,
    step_through z c ge st t st' ->
    exists instr,
      current_instr ge st = Some instr /\ head c = Some instr.
Proof.
  intros.
  NP app_new step_through_c_cons step_through.
  subst.
  NP app_new step_through_current_instr step_through.
Qed.

Lemma label_pos_nPC:
  forall ge st p c l pos_f f,
    label_pos l 0 c = Some pos_f ->
    c = fn_code f ->
    current_fn ge st = Some f ->
    ge = env p ->
    nPC p ->
    Int.unsigned (Int.repr pos_f) = pos_f.
Proof.
  intros.
  NP app_new label_pos_find_instr label_pos.
  unfold current_fn in *.
  simpl_match_hyp.
  inv H1. subst. 
  NP app_new unsigned_repr_PC nPC.
Qed.

Lemma local_jump_peep_instr:
  forall i,
    local_jump i ->
    peep_instr i.
Proof.
  destruct i; simpl in *; tauto.
Qed.

Lemma step_through_jump_pos:
  forall z c ge st t st' l f pos_f pos_c p,
    step_through z c ge st t st' ->      
    jumps_to_label ge st l ->
    current_fn ge st = Some f ->
    label_pos l 0 (fn_code f) = Some pos_f ->
    label_pos l 0 c = Some pos_c ->
    ge = env p ->
    nPC p ->
    pos_f = z + pos_c.
Proof.
  intros.
  cut (z < pos_f <= z + zlen c).
  {
    intros.
    NP app_new step_through_at_code step_through.
    P inv at_code.
    assert (f = fd) by (eauto using current_fn_unify).
    subst.
    rewrite H13 in H2.
    eapply label_pos_mid; eauto.
  }
  NP1 app_new step_through_current_instr' step_through.
  break_and.
  NP app_new step_through_step_basic step_through.
  rename x0 into st''.
  
  NP app_new step_jump_PC step_basic; try solve [subst ge; eauto].
  NP app_new step_through_PC_bounds step_through.
  NP2 app_new label_pos_nPC label_pos.
  rewrite H11 in H10. omega.

  NP app_new jumps_to_label_is_labled_jump jumps_to_label;
    try solve [subst ge; eauto].
  NP app_new labeled_jump_is_local_jump labeled_jump.
  eapply local_jump_peep_instr; eauto.
Qed.

(* WON'T WORK WITHOUT EVIDENCE THE LABEL IN C IS THE FIRST LABEL IN THE FN *)
(* Lemma mk_step_fwd_jump : *)
(*   forall ge st st' i, *)
(*     step_basic ge st st' -> *)
(*     at_code z c 0 ge st -> *)
(*     jumps_to_label ge st l -> *)
(*     label_pos l 0 c = Some pos -> *)
(*     step_fwd ge st st' pos. *)
(* Proof. *)
(*   (* Use: step_through_jump_pos *) *)
(*   admit. *)
(* Qed. *)

Lemma label_pos_none_ofs:
  forall c l a b,
    label_pos l a c = None ->
    label_pos l b c = None.
Proof.
  induction c; intros.
  simpl. auto.
  simpl in H.
  simpl_match_hyp.
  simpl.
  collapse_match.
  exploit IHc.
  eapply H.
  intros.
  instantiate (1 := b + 1) in H0.
  auto.
Qed.

Lemma label_pos_none_cons:
  forall l i c,    
    label_pos l 0 (i :: c) = None ->
    is_label l i = false /\ label_pos l 0 c = None.
Proof.
  intros.
  unfold label_pos in *.
  simpl_match_hyp.
  split; auto.
  fold label_pos in *.
  eapply label_pos_none_ofs. eauto.
Qed.
    
Lemma label_pos_compose:
  forall c1 c2 l pos,
    label_pos l 0 c1 = None ->
    label_pos l 0 c2 = Some pos ->
    label_pos l 0 (c1 ++ c2) = Some (zlen c1 + pos).
Proof.
  induction c1; intros.
  simpl. auto.
  NP2 app_new label_pos_none_cons label_pos.
  break_and.
  exploit IHc1.
  eauto.
  eauto.
  intros.
  simpl_expr (label_pos l 0 ((a :: c1) ++ c2)).  
  collapse_match.
  NP1 app_new label_pos_1 label_pos.
  simpl in H4.
  rewrite zlen_cons.
  rewrite H4.
  f_equal.
  omega.
Qed.

Lemma step_through_label_pos_f:
  forall ge st t st' z c l f pos_c,
    step_through z c ge st t st' ->
    label_pos l 0 c = Some pos_c ->
    current_fn ge st = Some f ->
    exists pos_f,
      label_pos l 0 (fn_code f) = Some pos_f.
Proof.
  intros.
  NP app_new step_through_at_code step_through.
  P inv at_code.
  assert (f = fd) by (eauto using current_fn_unify). subst fd.
  P _rewrite fn_code.
  destruct (label_pos l 0 c1) eqn:?.
  + NP1 app_new label_pos_lt label_pos.
    rewrite <- (app_nil_r c1) in Heqo.
    eapply label_pos_append_tail in Heqo; eauto.
  + exploit label_pos_compose; eauto. intros.
    rewrite <- (app_nil_r (c1 ++ c)) in H2.    
    exploit label_pos_append_tail.
    2: eapply H2.
    rewrite zlen_app.
    NP app_new label_pos_lt (Some pos_c).
    omega.
    intros.
    instantiate (1 := c2) in H9.
    rewrite <- app_assoc in H9.
    eauto.
Qed.

Lemma step_through_current_ofs:
  forall ge st t st' z c,
    step_through z c ge st t st' ->
    current_ofs st = Some (Int.repr z).
Proof.
  intros.
  NP app_new step_through_at_code step_through.
  NP app_new at_code_current_ofs at_code.
  find_rewrite. f_equal. f_equal. omega.
Qed.

Lemma at_code_current_code:
  forall ge st z c ofs,
    at_code z c ofs ge st ->
    exists c0 c1,
      current_code ge st = Some (c0 ++ c ++ c1) /\
      z = zlen c0.
Proof.
  intros.
  inv H.
  exploit mk_current_fn; eauto. intro.
  exploit mk_current_code; eauto. intro.
  rewrite H5 in H6.
  eauto.
Qed.

Lemma at_code_end_current_code:
  forall ge st z c,
    at_code_end z c ge st ->
    exists c0 c1,
      current_code ge st = Some (c0 ++ c ++ c1) /\
      z = zlen c0.
Proof.
  intros.
  inv H.
  exploit mk_current_fn; eauto. intro.
  exploit mk_current_code; eauto. intro.
  rewrite H4 in H5.
  eauto.
Qed.

(*BEGIN SMALL_Z*)

Inductive small_z (z : Z) :=
  mk_small_z:
    z = Int.unsigned (Int.repr z) ->
    small_z z.

Lemma small_z_sub:
  forall z1 z2,
    small_z z1 ->
    small_z z2 ->
    z2 <= z1 ->
    small_z (z1 - z2).
Proof.
  intros.
  inversion H.
  inversion H0.
  constructor.
  rewrite Int.unsigned_repr.
  omega.
  split; try omega.
  copy (Int.unsigned_range_2 (Int.repr z1)).
  copy (Int.unsigned_range_2 (Int.repr z2)).
  omega.
Qed.

Lemma small_z_int_sub:
  forall z1 z2,
    small_z z1 ->
    small_z z2 ->
    z2 <= z1 ->
    Int.unsigned (Int.sub (Int.repr z1) (Int.repr z2)) = z1 - z2.
Proof.
  intros.
  NP app_new small_z_sub (z2 <= z1).
  inv H2.
  rewrite Int.unsigned_sub_borrow.
  unfold Int.sub_borrow.
  inversion H. inversion H0.
  break_match.
  + clear Heqs.
    rewrite Int.unsigned_zero in l.
    omega.
  + rewrite Int.unsigned_zero.
    omega.
Qed.

Lemma label_pos_small_z:
  forall ge st l c pos_f f p,
    label_pos l 0 c = Some pos_f ->
    c = fn_code f ->
    current_fn ge st = Some f ->
    ge = env p -> nPC p ->
    small_z pos_f.
Proof.
  intros.
  exploit label_pos_nPC; eauto. intros.
  constructor. auto.
Qed.

Lemma step_through_small_z:
  forall p ge st st' z c t,
    step_through z c ge st t st' ->
    ge = env p ->
    nPC p ->
    small_z z.
Proof.
  intros.
  NP app_new step_through_at_code step_through.
  NP app_new at_code_nPC at_code.
  constructor.
  replace (z + 0) with z in * by omega.
  auto.
Qed.

(* Lemma at_code_small_z':   *)
(*   forall z c ofs ge st p, *)
(*     at_code z c ofs ge st -> *)
(*     ge = env p -> *)
(*     nPC p -> *)
(*     small_z (z + zlen c). *)
(* Proof. *)
(*   admit. *)
(* Qed. *)

Lemma current_code_code_of_prog:
  forall st c ge p,
    current_code ge st = Some c ->
    ge = env p ->
    code_of_prog c p.
Proof.
  intros.
  unfold code_of_prog.
  unfold current_code in *.
  unfold current_fn in *.
  simpl_match_hyp.
  repeat inv_some.
  destruct f.
  simpl.  
  NP app_new Genv.find_funct_ptr_inversion Genv.find_funct_ptr.
  eauto.
Qed.

Lemma no_PC_overflow_small_z:
  forall c,
    no_PC_overflow c ->
    small_z (zlen c).
Proof.
  intros.
  constructor.
  unfold no_PC_overflow in *.
  copy (zlen_nonneg _ c).
  assert (zlen c = 0 \/ 0 < zlen c) by omega.
  break_or.
  rewrite H2.
  vm_compute.
  reflexivity.
  copy (in_range_find_instr c (zlen c - 1)).  
  assert (zlen c - 1 >= 0 /\ zlen c - 1 < zlen c) by omega.
  apply H1 in H3.
  break_exists.
  apply H in H3.
  assert (0 < zlen c <= Int.max_unsigned) by omega.
  clear -H4.
  symmetry.
  apply Int.unsigned_repr.
  omega.
Qed.

Lemma current_code_small_z:
  forall st c ge p,
    current_code ge st = Some c ->
    ge = env p ->
    nPC p ->
    small_z (zlen c).
Proof.
  intros.
  unfold nPC in *.
  NP app_new current_code_code_of_prog current_code.
  apply H1 in H2.
  apply no_PC_overflow_small_z; eauto.  
Qed.

Lemma small_z_range:
  forall z,
    small_z z ->
    0 <= z <= Int.max_unsigned.
Proof.
  intros.
  inversion H.
  copy (Int.unsigned_range (Int.repr z)).
  rewrite <- H0 in H1.    
  unfold Int.max_unsigned.
  omega.
Qed.
  
Lemma small_z_lt:
  forall z z',
    small_z z ->
    0 <= z' <= z ->
    small_z z'.
Proof.  
  intros.
  NP app_new small_z_range small_z.  
  constructor.
  symmetry.
  apply Int.unsigned_repr.
  omega.
Qed.

Lemma at_code_small_z:  
  forall z c ofs ge st p,
    at_code z c ofs ge st ->
    ge = env p ->
    nPC p ->
    small_z z /\
    small_z ofs /\
    small_z (zlen c) /\
    small_z (z + ofs) /\
    small_z (z + zlen c).
Proof.
  intros.  
  cut (small_z (z + zlen c)). intro.
  copy (zlen_nonneg _ c).  
  repeat (split;
          try (eapply small_z_lt; eauto; P inv at_code;
               copy (zlen_nonneg _ c1); omega)).
  NP app_new at_code_current_code at_code. break_and.
  NP app_new current_code_small_z current_code.
  repeat rewrite zlen_app in H4.
  eapply small_z_lt.
  eauto.
  copy (zlen_nonneg _ x).
  copy (zlen_nonneg _ c).
  copy (zlen_nonneg _ x0).
  omega.
Qed.

Lemma at_code_end_small_z:  
  forall z c ge st p,
    at_code_end z c ge st ->
    ge = env p ->
    nPC p ->
    small_z z /\
    small_z (zlen c) /\    
    small_z (z + zlen c).
Proof.
  intros.  
  cut (small_z (z + zlen c)). intro.
  copy (zlen_nonneg _ c).  
  repeat (split;
          try (eapply small_z_lt; eauto; P inv at_code_end;
               copy (zlen_nonneg _ c1); omega)).
  NP app_new at_code_end_current_code at_code_end. break_and.
  NP app_new current_code_small_z current_code.
  repeat rewrite zlen_app in H4.
  eapply small_z_lt.
  eauto.
  copy (zlen_nonneg _ x).
  copy (zlen_nonneg _ c).
  copy (zlen_nonneg _ x0).
  omega.  
Qed.

(*END SMALL_Z*)

Lemma mk_step_fwd:
  forall p st st' ofs1 ofs2,    
    step_basic p st st' ->
    current_ofs st = Some ofs1 ->
    current_ofs st' = Some ofs2 ->    
    step_fwd p st st' (Int.unsigned (Int.sub ofs2 ofs1)).
Proof.
  intros.
  unfold step_fwd.
  split; auto.
  unfold current_ofs in *.
  unfold current_PC in *.
  simpl_match_hyp.
  repeat inv_some.
  simpl.
  rewrite Heqv.
  rewrite Heqv0.
  simpl.
  f_equal.
  rewrite Int.repr_unsigned.
  assert (b = b0).
  {
    (*TODO: Make a nice lemma for this*)
    NP app_new step_basic_corollaries step_basic.
    repeat break_and.
    subst_max.    
    repeat inv_state.
    unfold current_block in *.
    unfold current_PC in *.
    repeat collapse_match_hyp.
    repeat inv_some.
    auto.
  }
  subst b0.
  repeat inv_some.
  NP _app step_basic_corollaries step_basic.
  repeat break_and.
  subst_max.
  repeat inv_state.
  app step_md H7.
  repeat break_and.
  app md_extends_step H.

  erewrite weak_valid_pointer_sur in *; eauto.
  repeat break_and.
  app pinj_extends H17.
  
  exploit pinj_sub_ptr_diff.
  eapply H15. eapply H19.
  intros.
  
  rewrite H20.
  ring.
Qed.

Lemma step_basic_fns:
  forall p st st' ge,    
    step_basic p st st' ->
    ge = env p ->
    exists f,
      current_fn ge st = Some f /\
      current_fn ge st' = Some f.
Proof.
  intros.
  NP app_new step_basic_corollaries step_basic.
  repeat break_and.
  subst_max.
  eauto.
Qed.

Lemma step_basic_blocks:
  forall p st st',    
    step_basic p st st' ->
    exists b,
      current_block st = Some b /\
      current_block st' = Some b.
Proof.
  intros.
  NP app_new step_basic_corollaries step_basic.
  repeat break_and.
  eauto.
Qed.

Lemma step_fwd_ofs:
  forall p st st' k,    
    step_fwd p st st' k ->
    exists ofs ofs',
      current_ofs st = Some ofs /\
      current_ofs st' = Some ofs'.
Proof.
  intros.
  inv H.
  NP app_new step_basic_corollaries step_basic.
  repeat break_and.
  unfold current_block in *.
  unfold current_ofs in *.
  unfold current_PC in *.
  simpl_match_hyp.
  eauto.
Qed.

Lemma step_fwd_k_ofs:
  forall p st st' k ofs ofs',    
    step_fwd p st st' k ->
    current_ofs st = Some ofs ->
    current_ofs st' = Some ofs' ->
    small_z k ->
    small_z (Int.unsigned ofs + k) ->
    Int.unsigned ofs' = Int.unsigned ofs + k.
Proof.
  intros.
  unfold current_ofs in *.
  unfold current_PC in *.
  P inv step_fwd.
  simpl_match_hyp.
  repeat inv_some.
  P _simpl st_rs.
  P2P1 _rewritein (r0 PC) (r0 PC).
  P2P1 _rewritein (r PC) (r PC).
  P1 _simpl Vint.
  P1 inv Vint.

  NP _app step_basic_corollaries step_basic.
  repeat break_and.
  subst_max.
  repeat inv_state.  
  NP _app step_md step_bits.
  NP _app md_extends_step step_bits.
  break_and.

  unfold current_block in *.
  rewrite Heqv0 in *.
  rewrite Heqo0 in *.
  rewrite Heqv in *.
  rewrite Heqo in *.
  repeat opt_inv. subst.
  
  erewrite weak_valid_pointer_sur in * by eauto.
  repeat break_and.
  eapply pinj_extends in H17; eauto.
  eapply pinj_add in H17; eauto.
  eapply pinj_injective_within_block in H17; try eapply H13.
  rewrite H17.

  P0 _inversion small_z.
  rewrite Int.add_unsigned.
  congruence.
Qed.
  
Lemma mk_step_through:
  forall p ge st st' k z c,
    step_fwd p st st' k ->
    at_code z c 0 ge st ->
    ge = env p ->
    nPC p ->
    0 < k <= zlen c ->
    step_through z (firstz k c) ge st E0 st' /\
    match skipz k c with
      | nil => at_code_end z c ge st'
      | c' => at_code (z + k) c' 0 ge st'            
    end.
Proof.
  intros.
  assert (k = zlen c \/ k < zlen c) by omega.
  NP app_new step_fwd_ofs step_fwd.
  break_and. rename x into ofs. rename x0 into ofs'.  
  NP app_new step_fwd_k_ofs step_fwd.
  Focus 2.
  NP app_new at_code_small_z at_code. repeat break_and.
  eapply small_z_lt.
  eapply H10.
  omega.
  Focus 2.
  NP app_new at_code_current_ofs at_code.
  rewrite H5 in H8.
  inv_some.
  rewrite Z.add_0_r.
  NP app_new at_code_small_z at_code. repeat break_and.
  inversion H1.
  rewrite <- H13.
  app_new small_z_range H1.  
  eapply small_z_lt.
  2: assert (0 <= z + k <= z + zlen c) by omega; eauto.
  auto.
  break_or.
  - rewrite firstz_zlen.
    rewrite skipz_zlen_nil.
    isplit.
    + constructor.
      * assumption.
      * inv H.
        NP app_new step_basic_corollaries step_basic.
        repeat break_and.
        congruence.        
      * P inv at_code.
        destruct st' as (rs', m').        
        unfold current_ofs in *.
        unfold current_PC in *.
        simpl_match_hyp.
        repeat inv_some.
        P inv (Vint i1 = Vint bits).
        repeat unify_psur.
        NP app_new mk_current_fn (Internal fd).
        instantiate (1 := m) in H0.        
        econstructor; eauto.
        P _rewrite (Int.unsigned ofs').
        omega.
        P inv step_fwd.
        NP _app step_basic_corollaries step_basic.
        repeat break_and.
        repeat match goal with
                 | [ H : State_bits _ _ _ = State_bits _ _ _ |- _ ] => inv H
               end.
        unfold current_block in *.
        rewrite Heqv in *. rewrite Heqv0 in *.
        rewrite Heqo0 in *. rewrite H4 in *.
        repeat opt_inv; subst.
        eauto.

        
    + P inv step_through; eauto.
  - isplit.
    + econstructor.
      * NP _eapplyin (at_code_firstz k) at_code.
        2: omega.
        auto.
      * inv H.
        NP app_new step_basic_corollaries step_basic.
        repeat break_and.
        congruence.
      * P inv at_code.
        destruct st' as (rs', m').                

        unfold current_ofs in *.
        unfold current_PC in *.
        simpl_match_hyp.
        repeat inv_some.
        P inv (Vint i1 = Vint bits).
        repeat unify_psur.
        NP app_new mk_current_fn (Internal fd).
        instantiate (1 := m) in H0.        
        econstructor; eauto.
        P _rewrite (Int.unsigned ofs').
        f_equal.
        omega.
        rewrite zlen_firstz by omega. reflexivity.
        exploit step_basic_next_current_fn;
          P inv step_fwd;
          eauto.
        intros.
        NP _app step_basic_corollaries step_basic.
        repeat break_and.
        repeat match goal with
                 | [ H : State_bits _ _ _ = State_bits _ _ _ |- _ ] => inv H
               end.
        unfold current_block in *.
        rewrite Heqv in *. rewrite Heqv0 in *.
        rewrite Heqo0 in *. rewrite H4 in *.
        repeat opt_inv; subst.
        eauto.

        copy (split_ls c k).
        instantiate (1 := skipz k c ++ c2).        
        P1P2 _rewritein c c.        
        repeat rewrite app_assoc in *.
        assumption.
    + break_match.
      * copy (split_ls c k).
        P2P1 _rewritein @skipz @skipz.        
        rewrite app_nil_r in *.
        exploit (zlen_firstz c k).
        omega.
        intros.
        P2P1 _rewritebin c c.        
        omega.
      * assert (at_code_end z (firstz k c) (env p) st').
        inv H1; auto.
        copy (split_ls c k).
        inversion H0.
        subst c0. subst ge. subst ofs0.
        assert (zlen (firstz k c) = k).
        apply zlen_firstz. omega.
        assert (z + k = zlen (c1 ++ firstz k c)).
        rewrite zlen_app.
        omega.
        P1 _rewrite (zlen c1).
        P1 _rewrite (z + k).
        P1 _inversion at_code_end.        
        econstructor; eauto.
        rewrite zlen_app.
        omega.
        rewrite zlen_cons.
        copy (zlen_nonneg _ l).
        omega.
        instantiate (1 := c2).
        P1P1 _rewritein (firstz k c ++ skipz k c) (fn_code fd).        
        rewrite <- Heql.
        cut (fd0 = fd). intros.
        subst fd0.
        repeat rewrite app_assoc in *.
        assumption.
        P _clear (zlen (firstz k c) = k).        
        P _inversion step_fwd.
        NP app_new step_basic_corollaries step_basic.
        repeat break_and.
        P2 _clear (firstz k c ++ skipz k c).        
        subst.
        unfold current_fn in *.
        unfold current_block in *.
        unfold current_PC in *.
        P2 inv no_ptr.
        repeat match goal with
                 | [ H : State_bits _ _ _ = State_bits _ _ _ |- _ ] => inv H
               end.
        repeat (break_match_hyp; try congruence).
Qed.

Lemma step_basic_md:
  forall st st' p,
    step_basic p st st' ->    
    match_metadata (st_md st') (st_m st').
Proof.
  intros.
  app_new step_basic_corollaries H.
  repeat break_and.
  subst st'.
  simpl in *.
  tauto.
Qed.

Lemma step_basic_gp:
  forall st st' p,
    step_basic p st st' ->    
    global_perms (env p) (st_m st').
Proof.
  intros.  
  app_new step_basic_corollaries H.
  repeat break_and.
  subst.  
  exploit step_gp; eauto.
  intros.
  simpl.
  tauto.
Qed.

Lemma mk_step_through_straightline:
  forall ge st i c z rs m p rs' m' st' md md' b,
    at_code z (i :: c) 0 ge st ->
    peep_instr i ->
    straightline i \/ non_jump_jump i ge st ->
    (forall fn, exec_instr_bits ge md fn i b rs m = Nxt rs' m' md') ->
    no_ptr st ->
    ge = env p ->
    nPC p ->
    st = State_bits rs m md ->       
    st' = State_bits rs' m' md' ->
    current_block st = Some b ->
    match_metadata md m ->
    global_perms ge m ->
    step_through z (i :: nil) ge st E0 st' /\
    match c with
      | nil => at_code_end z (i :: nil) ge st'
      | i' :: c' => at_code (z + 1) (i' :: c') 0 ge st'
    end /\
    no_ptr st' /\
    match_metadata md' m' /\
    global_perms ge m'.
Proof.
  intros.
  NP1 app_new at_code_current_instr at_code.
  NP1 app_new at_code_current_fn at_code.
  specialize (H2 x).
  exploit mk_step_basic; eauto.
  intros.
  (* intros. *)
  (* break_or. auto. *)
  (* right. *)
  (* eapply non_jump_jump_local_jump; eauto.   *)
  (* intros. subst ge. *)
  exploit mk_step_fwd_straightline; eauto; simpl; eauto; intros.
  exploit mk_step_through; eauto; intros.  
  
  rewrite zlen_cons.
  copy (zlen_nonneg _ c).
  omega.  
  break_and.
  split.
  auto.
  split.
  break_match; auto.
  split.
  eapply step_basic_no_ptr.
  eassumption.
  NP app_new step_basic_md step_basic.
  subst st'. simpl in *.
  split.
  assumption.
  NP app_new step_basic_gp step_basic.
  subst. simpl in *.
  assumption.
 Qed.

(* Lemma step_through_deterministic: *)
(*   forall z c ge st t1 t2 st1 st2, *)
(*     step_through z c ge st t1 st1 -> *)
(*     step_through z c ge st t2 st2 -> *)
(*     (forall i : instruction, In i c -> straightline i \/ local_jump i) -> *)
(*     t1 = t2 /\ st1 = st2. *)
(* Proof. *)
(*   (*TODO P0*) *)
(*   admit. *)
(* Qed. *)

(* Lemma step_fwd_in_code_at_code: *)
(*   forall ge st st' k c z p, *)
(*     step_fwd ge st st' k -> *)
(*     at_code z c 0 ge st -> *)
(*     in_code z c ge st' -> *)
(*     ge = env p -> *)
(*     nPC p -> *)
(*     at_code z c k ge st'. *)
(* Proof. *)
(*   intros. *)
(*   P inv in_code. *)
(*   cut (k = ofs). *)
(*   intro. subst. auto. *)
(*   NP app_new step_fwd_ofs step_fwd. *)
(*   break_and. *)
(*   NP app_new step_fwd_k_ofs step_fwd. *)
(*   NP2 app_new at_code_current_ofs at_code. *)
(*   NP1 app_new at_code_current_ofs at_code. *)
(*   rewrite H1 in H7. *)
(*   rewrite H2 in H8. *)
(*   repeat inv_some. *)
(*   admit. *)
(* Qed. *)

Lemma mk_no_trace:
  forall a,
    peep_instr a ->
    no_trace a.
Proof.
  destruct a; simpl in *; tauto.
Qed.

Lemma no_trace_code_in:
  forall c,
    (forall i, In i c -> no_trace i) ->
    no_trace_code c.
Proof.
  intros.
  unfold no_trace_code.
  intros.
  apply H.
  rewrite find_instr_in.
  eauto.
Qed.

Lemma step_fwd_at_code_in_code:
  forall ge st st' k z c p,
    step_fwd p st st' k ->
    at_code z c 0 ge st ->
    in_code z c ge st' ->
    0 < k <= zlen c ->
    ge = env p ->
    nPC p ->
    at_code z c k ge st'.
Proof.
  intros.
  NP app_new at_code_current_ofs at_code.
  P inv in_code.
  NP0 app_new at_code_small_z at_code. repeat break_and.  
  P0 inv at_code.  
  NP app_new step_fwd_ofs step_fwd. break_and. 
  NP app_new step_fwd_k_ofs step_fwd.
  Focus 2.
  eapply small_z_lt.
  P1 _eapply (small_z (zlen c)).
  omega.
  Focus 2. (*TODO nice lemma for this subgoal*)
  unfold current_ofs in *.
  unfold current_PC in *.
  simpl_match_hyp.
  repeat inv_some.
  repeat inv_vint.
  inv H14.
  rewrite <- H5.
  rewrite Z.add_0_r.
  assert (zlen c1 + k <= zlen c1 + zlen c) by omega.
  eapply small_z_lt.
  P1 _eapply (small_z (zlen c1 + zlen c)).
  copy (zlen_nonneg _ c1).
  omega.
  NP app_new step_fwd_step_basic step_fwd.
  NP app_new step_basic_blocks step_basic. break_and.
  unfold current_block in *.  
  unfold current_ofs in *.
  unfold current_PC in *.
  simpl_match_hyp.
  repeat inv_some.
  repeat inv_vint.  
  unify_stuff.
  econstructor; eauto.
  omega.
  omega.
Qed.

(* Lemma at_code_at_end: *)
(*   forall ge st z c k, *)
(*     at_code z c k ge st -> *)
(*     at_code_end z (firstz k c) ge st. *)
(* Proof. *)
(*   admit. *)
(* Qed. *)

(* Lemma step_through_k_bounds: *)
(*   forall ge st t st' st'' c z k p, *)
(*     step_through z c ge st t st' -> *)
(*     step_fwd ge st st'' k ->     *)
(*     ge = env p -> *)
(*     nPC p -> *)
(*     0 < k <= zlen c. *)
(* Proof. *)
(*   intros. *)
(*   inv H. *)
(*   inv H0. *)
(*   exploit step_basic_bits_unify_st; eauto. intros. subst st''. *)
(*   (*TODO P0*) *)
(*   admit. *)
(* Qed. *)

Lemma star_step_in_in_code:
  forall ge st z c t st',
    star_step_in z c ge st t st' ->
    in_code z c ge st.
Proof.
  intros.
  P inv star_step_in; eauto.
Qed.

(* Lemma step_fwd_at_code_ofs_k: *)
(*   forall ge st st' k z c ofs, *)
(*     step_fwd ge st st' k -> *)
(*     at_code z c 0 ge st -> *)
(*     at_code z c ofs ge st' -> *)
(*     ofs = k. *)
(* Admitted. *)

(* Lemma at_code_end_skipz: *)
(*   forall ge st z c k, *)
(*     at_code_end z c ge st -> *)
(*     0 < k <= zlen c -> *)
(*     at_code_end (z + k) (skipz k c) ge st. *)
(* Admitted. *)

Lemma step_through_nil:
  forall ge st st' t z,
    step_through z nil ge st t st' ->
    False.
Proof.
  intros.
  P inv step_through.
  P inv at_code.
  copy (@zlen_nil instruction).
  omega.
  P inv at_code.
  copy (@zlen_nil instruction).
  omega.
Qed.

Lemma step_bits_step_basic':
  forall p st t st' z c ofs ge,
    step_bits ge st t st' ->            
    at_code z c ofs ge st ->
    peep_code c ->
    ge = env p ->
    nPC p ->
    step_basic p st st'.
Proof.
  intros.
  NP _eapplyin at_code_0 at_code.
  destruct (skipz ofs c) eqn:?.
  + NP _applyin at_code_nil at_code.
    exfalso; assumption.
  + NP app_new at_code_current_instr at_code.    
    assert (In i (i :: l)) by (simpl; auto).    
    NP1 app_new (@skipz_in instruction) In.
    unfold peep_code in *.
    P exploit peep_instr; eauto. intro.    
    eapply step_bits_step_basic; eauto.    
Qed.

(* Definition at_code' (z : Z) (c : code) (ofs : Z) (ge: genv) (st: state) : Prop := *)
(*   let (rs, m) := st in *)
(*   match rs PC with *)
(*     | Vint bits => *)
(*       let (b, i) := psur bits in *)
(*       match Genv.find_funct_ptr ge b with *)
(*         | Some (Internal fd) => *)
(*           match fn_code fd with *)
(*             | c0 ++ c ++ c1 => *)
(*               Int.unsigned i = zlen c0 + ofs /\ *)
(*               0 <= ofs < zlen c *)
(*             | _ => False *)
(*           end *)
(*         | _ => False *)
(*       end *)
(*     | _ => False *)
(*   end. *)

Lemma at_code_fwd:
  forall st st' ofs ofs' z c p ge,
    at_code z c ofs ge st ->
    at_code z c ofs' ge st' ->
    step_basic p st st' ->
    only_forward_jumps c ->
    not_after_label_in_code ge st z c ->
    ge = env p ->    
    ofs < ofs'.
Proof.
  intros.
  NP app_new step_basic_corollaries step_basic.
  repeat break_and.
  subst.
  unfold current_block in *.
  unfold current_instr in *.
  unfold current_code in *.
  unfold current_fn in *.
  unfold current_PC in *.
  simpl_match_hyp.
  repeat inv_some.  
  exploit only_forward_PC_incr; eauto.
  intros.
  P0 copy at_code.
  P1 inv at_code.
  P2 inv at_code.
  unify_stuff.
  omega.
Qed.

Lemma find_instr_nonneg:
  forall z c i,
    find_instr z c = Some i ->
    0 <= z.
Proof.
  intros.
  assert (exists i : instruction, find_instr z c = Some i) by eauto.
  rewrite <- in_range_find_instr in H0.
  omega.
Qed.

Lemma only_forward_jumps_skipz:
  forall c k,
    only_forward_jumps c ->
    only_forward_jumps (skipz k c).
Proof.
  intros.
  unfold only_forward_jumps in *.
  repeat break_and.
  repeat split.
  + unfold no_calls in *.
    intros.
    copy (find_instr_nonneg z _ _ H2).
    erewrite <- find_instr_append_head in H2.
    instantiate (1 := firstz k c) in H2.
    rewrite <- split_ls in H2.
    2: omega.
    eapply H.
    eauto.
  + unfold no_trace_code in *.
    intros.
    copy (find_instr_nonneg z _ _ H2).
    erewrite <- find_instr_append_head in H2.
    instantiate (1 := firstz k c) in H2.
    rewrite <- split_ls in H2.
    2: omega.
    eapply H0.
    eauto.
  + intros.
    unfold only_forward_jumps_lab in *.
    intros.
    copy (find_instr_nonneg _ _ _ H2).
    copy (find_instr_nonneg _ _ _ H4).
    erewrite <- find_instr_append_head in H2.
    instantiate (1 := firstz k c) in H2.
    rewrite <- split_ls in H2.
    erewrite <- find_instr_append_head in H4.
    instantiate (1 := firstz k c) in H4.
    rewrite <- split_ls in H4.
    2: omega.
    2: omega.
    exploit H1.
    2: eauto.
    eauto.
    eauto.
    intros.
    omega.    
Qed.

Lemma not_after_label_in_code_step:
  forall p st st' z c ge,    
    not_after_label_in_code ge st z c ->
    step_basic p st st' ->
    ge = env p ->
    not_after_label_in_code ge st' z c.
Proof.
  intros.
  NP app_new step_basic_corollaries step_basic.
  repeat break_and.
  subst.            
  unfold not_after_label_in_code in *.
  intros.
  repeat inv_state.  
  unfold current_instr in *.
  unfold current_code in *.
  unfold current_fn in *.
  unfold current_block in *.            
  unfold current_PC in *.
  repeat (break_match_hyp; try congruence).            
  repeat inv_some.
  repeat inv_vint.  
  unify_stuff.
  eauto.
Qed.

Lemma list_head_eq :
  forall {A} (a b c c' : list A),    
    a ++ c = b ++ c' ->
    zlen a = zlen b ->
    a = b.
Proof.
  intros. app (@list_eq_middle_therefore_eq A) H0.
  break_and. auto.
  instantiate (4 := nil). instantiate (1 := c').
  instantiate (1 := c).
  simpl.
  assumption.
Qed.

Lemma not_after_label_in_code_skipz:
  forall k ge st z c ofs,
    not_after_label_in_code ge st z c ->
    only_forward_jumps c ->
    at_code z c ofs ge st ->
    0 < k <= zlen c ->
    not_after_label_in_code ge st (z + k) (skipz k c).
Proof.
  intros.
  rename H into H_.
  rename H0 into H.
  rename H1 into H0.
  rename H2 into H1.
  unfold not_after_label_in_code.
  intros.
  split.
  + unfold ends_in_not_label_from_after_code.
    intros.
    unfold only_forward_jumps in *.
    repeat break_and.
    P bump only_forward_jumps_lab.
    specialize (H13 l).
    unfold only_forward_jumps_lab in *.
    P inv label_in_code.
    break_and.
    NP app_new find_instr_in In.
    copy (split_ls c k).
    NP1 app_new find_instr_nonneg find_instr.
    erewrite <- (find_instr_append_head (firstz k c)) in H8.
    2: omega.
    rewrite <- H12 in H8.    
    clear H12.
    inv H0.
    unify_stuff.
    simpl in H26.
    copy (split_ls c k).
    replace (c3 ++ c ++ c4) with (c3 ++ firstz k c ++ skipz k c ++ c4) in H26.
    Focus 2.
    f_equal.
    rewrite app_assoc.
    f_equal.
    auto.
    copy (zlen_firstz c k).
    forward H12. omega.
    specialize (H13 _ _ H8).
    exploit (@list_head_eq instruction).
    instantiate (1 := (skipz k c ++ c4)).
    instantiate (1 := c3 ++ firstz k c).
    instantiate (1 := (skipz k c ++ c1)).
    instantiate (1 := c0).
    repeat rewrite <- app_assoc.
    assumption.
    rewrite zlen_app.
    omega.
    intros.
    subst c0.
    replace (c3 ++ firstz k c) with ((c3 ++ firstz k c) ++ nil) in H9 by auto.
    erewrite find_instr_append_tail in H9.
    instantiate (1 := skipz k c) in H9.
    Focus 2.
    repeat rewrite <- app_assoc.
    repeat rewrite zlen_app.
    simpl.
    rewrite zlen_app in H7.
    rewrite H7.
    rewrite (@zlen_nil instruction).
    copy (zlen_nonneg _ c3).
    omega.
    repeat rewrite <- app_assoc in H9.
    rewrite <- H0 in H9.
    repeat rewrite zlen_app in H9.
    rewrite (@zlen_nil instruction) in *.
    replace (zlen c3 + (zlen (firstz k c) + 0) - 1)
            with (zlen c3 + (zlen (firstz k c) - 1)) in * by omega.
    rewrite find_instr_append_head in H9.
    exploit H13.
    2: eauto.
    2: eauto.
    eauto.
    intros.
    omega.
    omega.
  + unfold not_after_label_in_code in *.
    inv H0.
    inv H18.
    unify_stuff.
    exploit H_; eauto.    
    clear H_.
    intro.
    break_and.
    cut (c4 = c1).
    intro. congruence.
    simpl in *.
    replace (c3 ++ c ++ c4) with (c3 ++ (firstz k c ++ skipz k c) ++ c4) in H13.
    rewrite <- app_assoc in H13.
    replace (c3 ++ firstz k c ++ skipz k c ++ c4)
    with ((c3 ++ firstz k c) ++ skipz k c ++ c4) in H13.
    apply list_eq_middle_therefore_eq in H13.
    break_and. auto.
    rewrite zlen_app.
    copy (zlen_firstz c k).
    omega.    
    repeat rewrite <- app_assoc.
    auto.
    f_equal.
    f_equal.
    copy (split_ls c k).
    auto.
Qed.

(* Lemma mk_straightline_local_jump: *)
(*   forall c, *)
(*     no_calls c -> *)
(*     no_trace_code c -> *)
(*     forall i : instruction, In i c -> straightline i \/ local_jump i. *)
(* Proof. *)
(*   intros. *)
(*   unfold no_calls in *. *)
(*   unfold no_trace_code in *. *)
(*   rewrite find_instr_in in H1. *)
(*   break_exists. *)
(*   copy H1. *)
(*   apply H in H1. *)
(*   apply H0 in H2. *)
(*   destruct i; simpl; tauto. *)
(* Qed. *)

Lemma at_code_ofs_unify':
  forall ge st z c c' ofs1 ofs2 k,
    at_code z c ofs1 ge st ->
    at_code (z + k) c' ofs2 ge st ->
    ofs1 = k + ofs2.
Proof.
  intros.
  P0 inv at_code.
  unify_stuff.
  omega.
Qed.

Lemma step_fwd_star_step_in:
  forall ge st st' k z c t p,    
    star_step_in z c ge st t st' ->
    in_code (z + k) (skipz k c) ge st ->
    only_forward_jumps c ->
    not_after_label_in_code ge st z c ->
    peep_code c ->
    ge = env p ->
    nPC p ->
    0 <= k ->
    star_step_in (z + k) (skipz k c) ge st t st'.
Proof.
  intros.
  generalize dependent k.  
  induction H.
  intros.
  constructor.
  assumption.
  intros.
  P3 copy in_code.
  P1 inv in_code.
  NP app_new step_bits_step_basic' step_bits.  
  NP2 app_new not_after_label_in_code_step not_after_label_in_code.  
  econstructor 2; eauto.  
  apply IHstar_step_in; auto.
  rename st'' into ST.  
  NP2 app_new star_step_in_in_code star_step_in.
  P1 inv in_code.
  exploit at_code_fwd.
  P2 _eapply at_code.
  P1 _eapply at_code.
  auto.
  auto.
  auto.
  eauto.
  auto.
  auto.
  auto.
  intros.
  P1 inv in_code.
  P3 bump at_code.  
  NP1 app_new at_code_ofs_unify' at_code.  
  replace (ofs0) with (k + (ofs0 - k)) in H14 by omega.  
  NP3 app_new at_code_k at_code.
  econstructor.
  2: eauto.
  omega.
  split; try omega.  
Qed.

Inductive star_step_basic : program -> state_bits -> state_bits -> Prop :=
  | st_basic_refl:
    forall p st,
      star_step_basic p st st
  | st_basic_left:
      forall p st st'' st',
        star_step_basic p st'' st' ->
        step_basic p st st'' ->
        star_step_basic p st st'.

Lemma star_step_in_star_step_basic:
  forall ge st st' z c t p,
    star_step_in z c ge st t st' ->
    peep_code c ->
    ge = env p ->
    nPC p ->
    star_step_basic p st st'.
Proof.
  induction 1; intros.
  constructor.
  econstructor.
  eapply IHstar_step_in; auto.
  P inv in_code.
  eapply step_bits_step_basic'; eauto.
Qed.

Lemma star_step_basic_same_block:
  forall p st st' b,    
    star_step_basic p st st' ->    
    current_block st = Some b ->
    current_block st' = Some b.
Proof.
  induction 1; intros.
  congruence.
  NP app_new step_basic_corollaries step_basic.
  repeat break_and.
  exploit IHstar_step_basic; eauto.
  congruence.
Qed.

Lemma star_step_in_same_block:
  forall z c p st st' b t ge,
    star_step_in z c ge st t st' ->
    ge = env p ->
    nPC p ->    
    peep_code c ->
    current_block st = Some b ->
    current_block st' = Some b.
Proof.
  intros.
  NP app_new star_step_in_star_step_basic star_step_in.
  eapply star_step_basic_same_block; eauto.
Qed.

Lemma star_step_in_in_code':
  forall z c ge st t st',
    star_step_in z c ge st t st' ->
    in_code z c ge st /\ in_code z c ge st'.
Proof.  
  induction 1; intros.
  eauto.
  break_and.
  auto.
Qed.

Lemma in_code_at_code':
  forall st c z ge,
    in_code z c ge st ->
    exists z' i,
      at_code z' (i :: nil) 0 ge st /\ In i c.
Proof.
  intros.
  destruct st.
  eapply in_code_at_code; eauto.
Qed.

Lemma star_step_in_no_trace:
  forall st c z ge st' t,
    star_step_in z c ge st t st' ->
    (forall a : instruction, In a c -> no_trace a) ->
    t = E0.
Proof.
  induction 1; intros.
  auto.
  NP app_new in_code_at_code' in_code. break_and.
  NP app_new at_code_current_instr at_code.
  NP app_new step_bits_no_trace step_bits.
  subst.
  simpl.
  apply IHstar_step_in.
  auto.
Qed.

Lemma E0_3:
  E0 = E0 ** E0 ** E0.
Proof.
  auto.
Qed.

Lemma E0_2:
  E0 = E0 ** E0.
Proof.
  auto.
Qed.

Lemma E0_3':
  forall t1 t2 t3,
    t1 ** t2 ** t3 = E0 ->
    t1 = E0 /\ t2 = E0 /\ t3 = E0.
Proof.
  intros.
  apply Eapp_E0_inv in H. break_and.  
  apply Eapp_E0_inv in H0. break_and.
  auto.
Qed.

Lemma E0_2':
  forall t1 t2,
    t1 ** t2 = E0 ->
    t1 = E0 /\ t2 = E0.
Proof.
  intros.
  apply Eapp_E0_inv in H. break_and.  
  auto.
Qed.

Lemma step_through_no_trace :
  forall z c ge st t st',
    step_through z c ge st t st' ->
    (forall a : instruction, In a c -> no_trace a) ->
    t = E0.
Proof.
  intros.
  inv H.
  - destruct c.
    exploit (at_code_nil); eauto. tauto.
    NP app_new at_code_current_instr at_code.
    eapply step_bits_no_trace; eauto.
    apply H0; simpl; auto.
  - NP app_new star_step_in_in_code' star_step_in. break_and.
    NP0 app_new in_code_at_code' in_code. repeat break_and.
    destruct c.
    exploit (at_code_nil); eauto. tauto.
    NP0 app_new at_code_current_instr at_code.
    NP0 app_new step_bits_no_trace step_bits.
    2: apply H0; simpl; auto.
    subst.
    simpl.
    rewrite E0_2 at 2.
    f_equal.        
    eapply star_step_in_no_trace; eauto.
Qed.

Lemma step_through_same_block:
  forall c ge p st st' z b,    
    step_through z c ge st E0 st' ->    
    peep_code c ->
    ge = (env p) ->
    nPC p ->
    current_block st = Some b ->
    current_block st' = Some b.
Proof.
  induction 1; intros.
  + NP app_new step_bits_step_basic' step_bits.
    NP app_new step_basic_corollaries step_basic.
    repeat break_and.
    subst.
    congruence.    
  + NP app_new star_step_in_in_code' star_step_in.
    break_and.
    P0 inv in_code.    
    NP0 app_new step_bits_step_basic' step_bits.
    NP0 app_new step_basic_corollaries step_basic.
    repeat break_and.    
    NP app_new star_step_in_same_block star_step_in.
    congruence.
Qed.

Lemma step_through_same_block':
  forall z c ge p st t st',
    step_through z c ge st t st' ->
    ge = env p ->
    nPC p ->    
    peep_code c ->
    exists b,
      current_block st = Some b /\
      current_block st' = Some b.
Proof.
  intros.
  P copy step_through.
  P1 inv step_through.
  - NP app_new step_bits_step_basic' step_bits.
    NP app_new step_basic_corollaries step_basic.
    repeat break_and.
    NP app_new step_through_no_trace step_through.
    intros.
    eapply mk_no_trace; eauto.
  - NP2 app_new step_bits_step_basic' step_bits.
    NP app_new step_basic_corollaries step_basic.
    repeat break_and.
    subst.
    NP app_new step_through_no_trace step_through.
    rewrite H3 in H.    
    NP app_new step_through_same_block step_through.
    intros.
    unfold peep_code in *.
    eapply mk_no_trace; eauto.
Qed.

Lemma same_block_same_code:
  forall ge st st' b c,
    current_block st = Some b ->
    current_block st' = Some b ->
    current_code ge st = Some c ->
    current_code ge st' = Some c.
Proof.
  intros.
  unfold current_code in *.
  unfold current_fn in *.
  unfold current_block in *.
  unfold current_PC in *.
  simpl_match_hyp.
  subst.
  repeat inv_some.
  repeat collapse_match.
  trivial.
Qed.

Lemma same_block_same_fn:
  forall st1 st2 b1 b2 fn1 fn2 ge,
    current_block st1 = Some b1 ->
    current_block st2 = Some b2 ->
    b1 = b2 ->
    current_fn ge st1 = Some fn1 ->
    current_fn ge st2 = Some fn2 ->
    fn1 = fn2.
Proof.
  intros.
  unfold current_fn in *.
  unfold current_block in *.
  unfold current_PC in *.
  repeat (break_match; try congruence).
Qed.

Lemma same_block_same_fn':
  forall st1 st2 b1 b2 fn ge,
    current_block st1 = Some b1 ->
    current_block st2 = Some b2 ->
    b1 = b2 ->
    current_fn ge st1 = Some fn ->
    current_fn ge st2 = Some fn.    
Proof.
  intros.
  unfold current_fn in *.
  unfold current_block in *.
  unfold current_PC in *.
  repeat (break_match; try congruence).
Qed.

Lemma list_adj_middle:
  forall {A: Type} c1 c2 p1 p2 s1 s2 (x : list A),
    x = p1 ++ c1 ++ s1 ->
    x = p2 ++ c2 ++ s2 ->
    zlen p2 = zlen p1 + zlen c1 ->
    x = p1 ++ c1 ++ c2 ++ s2.
Proof.
  intros.
  subst x.
  rewrite app_assoc in H0.
  app_new @list_head_eq H0.
  2: rewrite zlen_app; auto.
  rewrite app_assoc.
  rewrite app_assoc.
  rewrite H in *.
  f_equal.
  eauto.
Qed.

Lemma current_code_current_fn:
  forall ge st c,
    current_code ge st = Some c ->
    exists fn,
      current_fn ge st = Some fn /\
      fn_code fn = c.
Proof.
  intros.
  unfold current_code in *.
  simpl_match_hyp.
  inv_some.
  eauto.
Qed.

Lemma fn_code_current_code:
  forall fn st c ge,
    fn_code fn = c ->
    current_fn ge st = Some fn ->
    current_code ge st = Some c.
Proof.
  intros.
  unfold current_code.
  collapse_match.
  f_equal.
  trivial.
Qed.

Lemma step_through_nonnil:
  forall c ge st t st' z,
    step_through z c ge st t st' ->
    0 < zlen c.
Proof.
  intros.
  destruct c.
  apply step_through_nil in H. tauto.
  rewrite zlen_cons.
  copy (zlen_nonneg _ c).
  omega.
Qed.

Lemma at_code_right_ext:
  forall ge st z c0 c c' c1 ofs,
    at_code z c ofs ge st ->
    current_code ge st = Some (c0 ++ c ++ c' ++ c1) ->
    z = zlen c0 ->
    at_code z (c ++ c') ofs ge st.
Proof.
  intros.
  inv H.
  econstructor; eauto.
  rewrite zlen_app.
  copy (zlen_nonneg _ c').
  omega.
  unfold current_code in *.
  simpl_match_hyp.
  inv_some.
  rewrite <- app_assoc.  
  unfold current_fn in *.
  simpl_match_hyp.
  repeat inv_some.
  inv H2.
  unify_stuff.
  rewrite H1 in H7.
  exploit @list_head_eq.
  eauto.
  omega.
  intro.
  subst.
  eauto.  
Qed.

Lemma at_code_left_ext:
  forall z c ge st c' c0 c1 ofs,
    at_code z c ofs ge st ->
    current_code ge st = Some (c0 ++ c' ++ c ++ c1) ->
    z = zlen c0 + zlen c' ->
    at_code (zlen c0) (c' ++ c) (zlen c' + ofs) ge st.
Proof.
  intros.
  inv H.
  econstructor; eauto.
  omega.
  rewrite zlen_app.
  copy (zlen_nonneg _ c').
  omega.
  unfold current_code in *.
  unfold current_fn in *.
  simpl_match_hyp.
  repeat inv_some.
  inv H2.
  unify_stuff.
  rewrite H1 in H7.
  rewrite app_assoc in H7.
  exploit @list_head_eq; eauto.
  rewrite zlen_app.
  omega.
  intro.
  rewrite <- app_assoc.
  eauto.
Qed.

Lemma at_code_end_left_ext:
  forall z c ge st c' c0 c1,
    at_code_end z c ge st ->
    current_code ge st = Some (c0 ++ c' ++ c ++ c1) ->
    z = zlen c0 + zlen c' ->
    at_code_end (zlen c0) (c' ++ c) ge st.
Proof.
  intros.
  inv H.
  econstructor; eauto.
  rewrite zlen_app.
  omega.      
  unfold current_code in *.
  unfold current_fn in *.
  simpl_match_hyp.
  repeat inv_some.
  inv H2.
  unify_stuff.
  rewrite H1 in H6.
  rewrite app_assoc in H6.
  exploit @list_head_eq; eauto.
  rewrite zlen_app.
  omega.
  intro.
  rewrite <- app_assoc.
  eauto.
Qed.

Lemma star_step_in_left_ext:
  forall c c' ge p st st' z c0 c1,    
    star_step_in z c ge st E0 st' ->
    current_code ge st = Some (c0 ++ c' ++ c ++ c1) ->
    z = zlen c0 + zlen c' ->
    ge = env p ->
    nPC p ->
    peep_code c ->
    star_step_in (zlen c0) (c' ++ c) ge st E0 st'.
Proof.
  remember E0 as t.
  induction 1; intros; subst.
  - P inv in_code.
    NP _eapplyin at_code_left_ext at_code; eauto.
    econstructor 1.
    econstructor.
    2: eauto.
    copy (zlen_nonneg _ c').
    omega.
  - exploit E0_2'; eauto; intro. break_and. auto.
    subst.    
    P inv in_code.
    exploit IHstar_step_in; eauto.    
    NP app_new step_bits_step_basic' step_bits.
    NP app_new step_basic_blocks step_basic. break_and.
    NP1 app_new same_block_same_code current_code.
    intros.    
    NP1 _eapplyin at_code_left_ext at_code.
    2: eauto.
    2: trivial.
    econstructor 2.
    eauto.
    econstructor.
    2: eauto.
    copy (zlen_nonneg _ c').
    omega.
    auto.    
Qed.

Lemma star_step_in_right_ext:
  forall c c' p ge st st' z c0 c1,    
    star_step_in z c ge st E0 st' ->
    current_code ge st = Some (c0 ++ c ++ c' ++ c1) ->
    z = zlen c0 ->
    nPC p ->
    ge = env p ->
    peep_code c ->
    star_step_in z (c ++ c') ge st E0 st'.
Proof.
  remember E0 as t.
  induction 1; intros; subst.
  - P inv in_code.
    NP _eapplyin at_code_right_ext at_code; eauto.
    econstructor 1.
    econstructor.
    2: eauto.
    copy (zlen_nonneg _ c').
    omega.
  - exploit E0_2'; eauto; intro. break_and. auto.
    subst.    
    P inv in_code.
    exploit IHstar_step_in; eauto.    
    NP app_new step_bits_step_basic' step_bits.
    NP app_new step_basic_blocks step_basic. break_and.
    NP1 app_new same_block_same_code current_code.
    intros.    
    NP1 _eapplyin at_code_right_ext at_code.
    2: eauto.
    2: trivial.
    econstructor 2.
    eauto.
    econstructor.
    2: eauto.
    copy (zlen_nonneg _ c').
    omega.
    auto.
Qed.

Lemma star_step_in_chain:
  forall st1 st2 st3 c z ge,
    star_step_in z c ge st1 E0 st2 ->
    star_step_in z c ge st2 E0 st3 ->
    star_step_in z c ge st1 E0 st3.
Proof.
  intros.
  generalize dependent H0.
  generalize dependent st3.
  remember E0 as t.
  induction H; intros.
  eauto.
  apply E0_2' in Heqt. repeat break_and. subst.
  exploit IHstar_step_in; eauto.
  intros.
  econstructor 2.
  eauto.
  eauto.
  eauto.
Qed.

Lemma step_through_chain_E0:
  forall z1 c1 c2 p st1 st2 st3 ge,    
    step_through z1 c1 ge st1 E0 st2 ->
    step_through (z1 + zlen c1) c2 ge st2 E0 st3 ->
    ge = env p ->
    nPC p ->
    peep_code c1 ->
    peep_code c2 ->
    step_through z1 (c1 ++ c2) ge st1 E0 st3.
Proof.
  intros.
  NP0 app_new step_through_same_block' step_through. repeat break_and.
  replace x0 with x in * by congruence. rename x into b.  
  NP0 app_new step_through_nonnil step_through.
  P0 inv step_through.
  - NP0 app_new at_code_current_code at_code. repeat break_and.
    NP0 app_new current_code_current_fn current_code. repeat break_and.
    rename_all function fn.
    rename_all (list instruction) c.
    exploit (same_block_same_fn st1 st2); eauto; intro. subst.
    exploit (list_adj_middle c1 c2); eauto; intro.
    exploit (same_block_same_fn' st1 st3); eauto. intro.
    
    NP2 _eapplyin at_code_right_ext at_code.
    2: eauto using (fn_code_current_code fn).
    2: trivial.    
    NP1 _eapplyin at_code_end_left_ext at_code_end.
    2: eauto using (fn_code_current_code fn).
    2: trivial.
    NP2 _eapplyin at_code_left_ext at_code.
    2: eauto using (fn_code_current_code fn).
    2: trivial.
    
    rewrite E0_3.
    econstructor 2; eauto.
    constructor.
    econstructor.
    2: eauto.
    omega.
  - NP1 _eapplyin E0_3' E0. repeat break_and. subst.
    NP app_new star_step_in_in_code star_step_in.
    P inv in_code.
    NP0 app_new at_code_current_code at_code. repeat break_and.
    NP0 app_new current_code_current_fn current_code. repeat break_and.
    rename_all function fn.
    rename_all (list instruction) c.
    exploit (same_block_same_fn st1 st2); eauto; intro. subst.
    exploit (list_adj_middle c1 c2); eauto; intro. 
    NP1 app_new step_bits_step_basic' step_bits; eauto.
    NP1 app_new step_basic_blocks step_basic. break_and.
    replace x with b in * by congruence.
    exploit (same_block_same_fn st2 stB); eauto; intro. subst.
    exploit (same_block_same_fn' st1 st3); eauto. intro.
    NP app_new star_step_in_same_block star_step_in.
    
    NP3 _eapplyin at_code_right_ext at_code.
    2: eauto using (fn_code_current_code fn).
    2: trivial.    
    NP1 _eapplyin at_code_end_left_ext at_code_end.
    2: eauto using (fn_code_current_code fn).
    2: trivial.
    NP3 _eapplyin at_code_left_ext at_code.
    2: eauto using (fn_code_current_code fn).
    2: trivial.    
    NP1 _eapplyin in_c at_code.
    2: omega.

    econstructor 2; eauto.
    
    rewrite E0_2.
    econstructor 2; eauto.
    eapply star_step_in_left_ext; eauto.
    exploit (fn_code_current_code fn stB).
    P1 _eapply fn_code.
    eauto.
    intros. 
    eauto.    
  - NP1 _eapplyin E0_3' E0. repeat break_and. subst.    
    NP0 app_new at_code_current_code at_code. repeat break_and.
    NP0 app_new current_code_current_fn current_code. repeat break_and.
    rename_all function fn.
    rename_all (list instruction) c.    
    NP1 app_new step_bits_step_basic' step_bits; eauto.
    NP1 app_new step_basic_blocks step_basic. break_and.
    replace x with b in * by congruence.
    NP app_new star_step_in_same_block star_step_in.
    exploit (same_block_same_fn' st1 st3); eauto; intro. subst.
    exploit (same_block_same_fn st1 st2); eauto; intro. subst.     
    exploit (same_block_same_fn' st1 stB); eauto. intro. subst.
    exploit (same_block_same_fn' st1 stC); eauto. intro. subst.
    exploit (list_adj_middle c1 c2); eauto; intro.
    
    NP2 _eapplyin at_code_right_ext at_code.
    2: eauto using (fn_code_current_code fn).
    2: trivial.
    NP1 _eapplyin at_code_end_left_ext at_code_end.
    2: eauto using (fn_code_current_code fn).
    2: trivial.

    econstructor 2; eauto.

    NP _eapplyin star_step_in_right_ext star_step_in; eauto.
    2: eauto using (fn_code_current_code fn).

    NP2 _eapplyin at_code_left_ext at_code.
    2: eauto using (fn_code_current_code fn).
    2: trivial.

    NP app_new star_step_in_in_code' star_step_in. break_and.

    eapply star_step_in_chain; eauto.
    
    rewrite E0_2.
    econstructor 2; eauto.
    econstructor.
    econstructor.
    2: eauto.
    omega.
  - NP0 _eapplyin E0_3' E0. repeat break_and. subst.    
    NP0 app_new at_code_current_code at_code. repeat break_and.
    NP0 app_new current_code_current_fn current_code. repeat break_and.
    rename_all function fn.
    rename_all (list instruction) c.
    NP1 app_new step_bits_step_basic' step_bits; eauto.
    NP1 app_new step_basic_blocks step_basic. break_and.
    replace x with b in * by congruence.
    P3 bump step_bits.
    NP1 app_new step_bits_step_basic' step_bits; eauto.
    NP1 app_new step_basic_blocks step_basic. break_and.
    replace x1 with b in * by congruence.
    NP0 app_new star_step_in_same_block star_step_in.    
    exploit (same_block_same_fn st1 st2); eauto; intro. subst.
    exploit (same_block_same_fn' st1 st3); eauto; intro. subst.
    exploit (same_block_same_fn' st1 stB); eauto. intro. subst.
    exploit (same_block_same_fn' st1 stC); eauto. intro. subst.
    exploit (same_block_same_fn' st1 stB0); eauto. intro. subst.
    exploit (same_block_same_fn' st1 stC0); eauto. intro. subst.
    exploit (list_adj_middle c1 c2); eauto; intro.
    
    NP2 _eapplyin at_code_right_ext at_code.
    2: eauto using (fn_code_current_code fn).
    2: trivial.
    NP1 _eapplyin at_code_end_left_ext at_code_end.
    2: eauto using (fn_code_current_code fn).
    2: trivial.

    econstructor 2; eauto.
    
    NP1 _eapplyin star_step_in_right_ext star_step_in; eauto.
    2: eauto using (fn_code_current_code fn).
    NP2 _eapplyin star_step_in_left_ext star_step_in; eauto.
    2: eauto using (fn_code_current_code fn).

    eapply star_step_in_chain.
    2: eauto.    
    eapply star_step_in_chain.
    eauto.

    NP2 _eapplyin at_code_left_ext at_code.
    2: eauto using (fn_code_current_code fn).
    2: trivial.

    NP0 app_new star_step_in_in_code' star_step_in. repeat break_and.

    rewrite E0_2.
    econstructor 2; eauto.
    rewrite E0_2.
    econstructor 2; eauto.
    constructor.
    eauto.
    econstructor.
    2: eauto.
    omega.
Qed.

Lemma brk_step_through:
  forall p ge st st' st'' z c k,
    step_through z c ge st E0 st' ->
    step_fwd p st st'' k ->
    peep_code c ->
    only_forward_jumps c ->
    not_after_label_in_code ge st z c ->    
    ge = env p ->
    nPC p ->
    0 < k <= zlen c ->
    match skipz k c with
      | nil => st' = st''
      | c' => step_through (z + k) c' ge st'' E0 st' /\
              not_after_label_in_code ge st'' (z + k) c'
    end.
Proof.
  intros.  
  P inv step_through.
  - (*CASE A*)
    NP app_new step_fwd_step_basic step_fwd.
    NP app_new step_basic_bits_unify_st step_basic.
    subst st''.
    cut (k = zlen c). intros.
    copy (skipz_zlen_nil c).
    P1 _rewrite k.
    P1 _rewrite (skipz (zlen c) c).
    exact eq_refl.    
    NP app_new at_code_current_ofs at_code.
    NP app_new at_code_end_current_ofs at_code_end.
    NP app_new step_fwd_k_ofs step_fwd.
    Focus 2.
    NP app_new at_code_small_z at_code. repeat break_and.
    eapply small_z_lt.
    eapply H14.
    omega.
    Focus 2.
    NP app_new at_code_small_z at_code. repeat break_and.
    inv H15.
    rewrite <- H18.
    eapply small_z_lt.
    eapply H16.
    app_new small_z_range H12.
    omega.    
    cut (small_z (z + zlen c)). intro.
    cut (small_z (z + 0)). intro.
    P0 inv small_z.
    rewrite <- H14 in H11.
    rewrite <- H12 in H11.
    omega.
    NP app_new at_code_small_z at_code. repeat break_and. auto.
    NP app_new at_code_end_small_z at_code_end. repeat break_and. auto.
  - assert (stB = st'').
    {
      NP app_new step_fwd_step_basic step_fwd.
      NP app_new step_basic_bits_unify_st step_basic.
    }
    subst.
    P1 inv star_step_in.
    + (*CASE C*)
      NP app_new step_fwd_at_code_in_code step_fwd.
      assert (k < zlen c).
      P1 inv at_code.
      omega.
      assert (0 < zlen (skipz k c)).
      {
        rewrite zlen_skipz.
        omega.
        omega.
      }
      break_match.
      * exfalso.
        copy (@zlen_nil instruction).
        omega.
      * simpl.
        isplit.
        constructor.
        replace (k) with (k + 0) in H4 by omega.
        NP1 app_new at_code_k at_code.
        2: omega.
        P2 _rewriteb k.
        assumption.
        assert (t1 = E0 /\ t3 = E0).        
        P _simpl E0.
        NP app_new Eapp_E0_inv E0.
        break_and. subst.
        simpl.
        assumption.
        NP app_new at_code_end_skipz at_code_end.
        rewrite <- Heql.
        eauto.
        omega.
        {
          NP app_new step_fwd_step_basic step_fwd.
          NP app_new not_after_label_in_code_step not_after_label_in_code.
          P2 _rewriteb (i :: l).
          NP1 app_new not_after_label_in_code_skipz not_after_label_in_code.          
        }
    + (*CASE B*)
      rename st into st0.
      rename st'' into st1.
      rename st''0 into st2.
      rename stC into st3.
      rename st' into st4.
      NP app_new step_fwd_at_code_in_code step_fwd.
      NP1 app_new at_code_0 at_code.      
      assert (at_code_end (z + k) (skipz k c) (env p) st4).
      {
        eapply at_code_end_skipz.
        assumption.
        omega.
      }
      NP app_new star_step_in_in_code star_step_in.
      P1 copy in_code.
      P1 inv in_code.
      P1 copy step_bits.
      NP1 _eapplyin step_bits_step_basic' step_bits.
      2: P3 _eapply at_code.
      2: assumption.
      2: eauto.
      2: eauto.      
      P2 copy step_bits.
      NP1 _eapplyin step_bits_step_basic' step_bits; eauto.
      NP app_new not_after_label_in_code_step not_after_label_in_code.
      NP1 app_new not_after_label_in_code_step not_after_label_in_code. 
      assert (in_code (z + k) (skipz k c) (env p) st2).
      {
        P3 bump at_code.
        P2 copy at_code.
        NP1 _eapplyin at_code_fwd at_code.
        2: P2 _eapply at_code.
        2: eassumption.
        2: assumption.
        2: assumption.        
        2: eauto.        
        P2 bump at_code.
        replace (ofs) with (k + (ofs - k)) in * by omega.
        NP1 app_new at_code_k at_code.
        2: omega.        
        econstructor.
        2: eauto.
        omega.
      }
      NP app_new step_fwd_star_step_in star_step_in.
      2: omega.
      exploit st_thru_mult_step.
      4: P1 _eapply star_step_in.
      3: eauto.
      3: eauto.
      eauto.
      eauto.
      intros.
      break_match.
      * exploit step_through_nil; eauto; tauto.
      * repeat match goal with
                 | [H: _ = E0 |- _ ] => apply Eapp_E0_inv in H; try break_and
               end.
        subst.
        P0 _simpl E0.
        simpl.
        split.
        assumption.
        {           
          P _rewriteb (skipz k c = i :: l).
          eapply not_after_label_in_code_skipz; eauto.
        }        
Qed.

Lemma brk_step_through_straightline :
  forall ge p st st' i c z t,    
    step_through z c ge st t st' ->
    current_instr ge st = Some i ->
    straightline i \/ non_jump_jump i ge st ->
    (~ is_any_label i \/ (exists l, i = Plabel l /\ forall a, In a c -> ~ labeled_jump a l)) ->
    peep_instr i ->
    peep_code c ->
    only_forward_jumps c ->
    not_after_label_in_code ge st z c ->
    ge = env p ->
    nPC p ->
    exists st'',
      step_fwd p st st'' 1 /\
      match skipz 1 c with
        | nil => st' = st''
        | c' => step_through (z + 1) c' ge st'' E0 st' /\
                not_after_label_in_code ge st'' (z + 1) c'
      end.
Proof.
  intros; subst ge.
  unfold peep_code in *.
  NP app_new step_through_step_basic step_through.
  rename x into st''. exists st''.
  isplit.
  eapply mk_step_fwd_straightline; eauto.
  NP app_new step_through_no_trace step_through.
  subst t.
  eapply brk_step_through; eauto.
  copy (zlen_nonneg _ c).
  assert (zlen c = 0 \/ 0 < zlen c) by omega.
  break_or.
  destruct c.
  exploit step_through_nil; eauto. intros.
  inv_false.

  rewrite zlen_cons in *.
  copy (zlen_nonneg _ c).
  omega.
  omega.
  intros.  
  PP1 _applyin peep_instr (In a c).  
  apply mk_no_trace; auto.  
Qed.

Lemma brk_step_through_jump :
  forall ge p st st' c z t l pos,
    step_through z c ge st t st' ->    
    jumps_to_label ge st l ->
    label_pos l 0 c = Some pos ->
    peep_code c ->
    only_forward_jumps c ->
    not_after_label_in_code ge st z c ->
    ge = env p ->
    nPC p ->
    exists st'',      
      step_fwd p st st'' pos /\
      match skipz pos c with
        | nil => st' = st''
        | c' => step_through (z + pos) c' ge st'' E0 st' /\
                not_after_label_in_code ge st'' (z + pos) c'
      end.
Proof.
  intros.
  unfold peep_code in *.
  NP app_new step_through_c_cons step_through.
  subst c. rename x0 into c. rename x into i.
  NP app_new step_through_current_instr step_through.
  NP app_new jumps_to_label_is_labled_jump jumps_to_label.
  NP app_new labeled_jump_is_local_jump labeled_jump.
  subst ge.
  NP app_new step_through_current_fn step_through.  
  rename x into f.
  NP app_new step_through_step_basic step_through.
  rename x into st''.
  exists st''.
  NP app_new step_through_label_pos_f step_through.
  rename x into f_pos.
  exploit step_jump_PC; eauto. intros.  
  exploit step_through_jump_pos; eauto. intros.
  NP app_new step_through_current_ofs step_through.
  isplit.
  + exploit mk_step_fwd; eauto. intros.
    exploit (small_z_int_sub f_pos z); eauto.
    NP1 app_new label_pos_small_z label_pos.
    NP app_new step_through_small_z step_through.
    NP2 app_new label_pos_in_range label_pos. omega.
    intros.    
    replace (f_pos - z) with pos in * by omega.
    P1 _rewriteb pos.
    assumption.
  + NP app_new label_pos_answer_valid (Some pos).
    eapply brk_step_through; eauto.    
    NP app_new step_through_no_trace step_through.
    subst t.
    assumption.
    intros.    
    P exploit (peep_instr); eauto. intro.
    apply mk_no_trace; auto.
    rewrite zlen_cons.
    copy (zlen_nonneg _ c).
    apply label_pos_lt in H1.
    rewrite zlen_cons in H1.
    omega.
  + apply H2. simpl. auto.
  + apply H2. simpl. auto.
Qed.

Lemma preg_dec:
  forall (p q : preg),
    { p <> q } + { p = q }.
Proof.  
  repeat decide equality.
Qed.

Lemma in_regset_dec:
  forall (reg : preg) rs,
    In reg rs \/ ~ In reg rs.
Proof.
  intros.
  
  tauto.
Qed.

Lemma no_touch_reg:
  forall r1 r2 (v : val) rs,
    r1 <> r2 ->
    (rs # r2 <- v) r1 = rs r1.
Proof.
  intros.
  destruct r1; preg_simpl; tauto.
Qed.

Lemma no_touch_nextinstr_nf:
  forall reg rs,
    ~ In reg flags ->
    reg <> PC ->
    (nextinstr_nf rs) reg = rs reg.
Proof.
  intros.
  preg_simpl.
  destruct reg; simpl in *; try tauto.
  destruct c; simpl in *; try tauto.
Qed.

Lemma mk_not_is_call_return:
  forall i,
    peep_instr i -> ~ is_call_return i.
Proof.
  intros.
  destruct i; simpl in *; tauto.
Qed.

Lemma exec_instr_preserved_no_touch :
  forall rs i pres ge rs' m m' f md' md b,
    exec_instr_bits ge md f i b rs m = Nxt rs' m' md' ->    
    no_def_instr i pres ->
    peep_instr i ->
    (forall reg, In reg pres -> rs reg = rs' reg) /\
    md = md'.
Proof.
  intros.
  split.
  - intros.
    exploit def_spec; eauto.
    apply mk_not_is_call_return; eauto.
    instantiate (1 := reg).
    intros.
    break_or.
    unfold no_def_instr in *.
    exploit H0; eauto.
    tauto.
    auto.
  - destruct i;
      try solve[
    P1 _simpl peep_instr;
    try tauto;
    simpl in *;
    unfold exec_load_bits in *;
    unfold exec_store_bits in *;
    unfold exec_big_load_bits in *;
    unfold exec_big_store_bits in *;
    unfold goto_label_bits in *;
    repeat break_match_hyp;
    try P1 _inversion Nxt;
    try congruence].    
Qed.

Lemma step_bits_preserved_no_touch :
  forall st i pres ge st' t,
    step_bits ge st t st' ->    
    current_instr ge st = Some i ->
    no_def_instr i pres ->
    peep_instr i ->
    (forall reg, In reg pres -> (st_rs st) reg = (st_rs st') reg) /\
    st_md st = st_md st'.
Proof.
  intros.  
  unfold current_instr in *.
  unfold current_code in *.
  unfold current_fn in *.  
  simpl_match_hyp.
  subst.
  unfold peep_instr in *.
  repeat inv_some.  
  inv H; unify_stuff; simpl.
  - eapply exec_instr_preserved_no_touch; eauto.
  - simpl in *.
    tauto.
  - simpl in *.
    tauto.
  - congruence.
Qed.

Lemma star_step_in_preserved_no_touch :
  forall st pres ge st' t c z,
    star_step_in z c ge st t st' ->    
    no_def c pres ->
    peep_code c ->
    (forall reg, In reg pres -> (st_rs st) reg = (st_rs st') reg) /\
    st_md st = st_md st'.
Proof.
  induction 1; intros.
  split.
  reflexivity.
  reflexivity.  
  NP app_new in_code_at_code' in_code. break_and.
  NP app_new at_code_current_instr at_code.
  exploit step_bits_preserved_no_touch; eauto.  
  intros.
  break_and.    
  exploit IHstar_step_in; eauto.
  intros.
  break_and.
  split.
  intros.
  specialize (H7 reg H11).
  specialize (H9 reg H11).
  congruence.
  congruence.
Qed.

Lemma step_through_preserved_no_touch :
  forall c pres,
    no_def c pres ->
    peep_code c ->
    step_through_preserve c pres.
Proof.
  intros.
  unfold step_through_preserve.
  intros.  
  P _clear at_code.  
  P inv step_through.    
  - destruct c.
    exploit at_code_nil; eauto; simpl; tauto.

    NP app_new at_code_current_instr at_code.
    exploit step_bits_preserved_no_touch; eauto.
    unfold no_def in *.
    apply H.
    simpl; auto.
    unfold peep_code in *.
    P1 _apply peep_instr.
    simpl. auto.
  - NP app_new star_step_in_in_code' star_step_in. break_and.
    NP0 app_new in_code_at_code' in_code. repeat break_and.    
    destruct c.
    exploit (at_code_nil); eauto. tauto.
    NP0 app_new at_code_current_instr at_code.
    NP0 app_new step_bits_preserved_no_touch step_bits.
    2: unfold no_def in *; apply H; simpl; auto.
    exploit star_step_in_preserved_no_touch; eauto.
    intros.
    destruct stB.
    destruct stC.
    P0 _simpl st_rs.
    split.
    intros.
    repeat break_and.
    specialize (H16 reg H19).
    specialize (H17 reg H19).
    specialize (H18 reg H19).
    congruence.
    repeat break_and.
    congruence.
    unfold peep_code in *.
    P1 _apply peep_instr.
    simpl. auto.
Qed.

Lemma at_code_transf:
  forall z ge1 ge2 st1 st2 c1 c2 b ofs f2,
    genv_equiv_code z ge1 ge2 b c1 c2 ->
    at_code z c1 0 ge1 st1 ->
    zlen c1 = zlen c2 ->    
    current_PC st1 = Some (b, ofs) ->
    current_PC st2 = Some (b, ofs) ->    
    current_fn ge2 st2 = Some f2 ->    
    at_code z c2 0 ge2 st2.
Proof.
  intros.
  P inv at_code.
  unfold genv_equiv_code in *.
  unfold current_fn in *.  
  unfold current_PC in *.
  simpl_match_hyp.
  repeat inv_some.
  repeat inv_vint.
  unify_stuff.
  destruct fd. destruct f2.
  exploit H; eauto.
  - simpl in *.
    P1 _rewrite fn_code.
    rewrite nat_zlen.
    apply pat_at_n_sane.
  - intros.
    break_and.
    clear H.
    simpl in *.
    rewrite nat_zlen in H2.
    rewrite nat_zlen in H0.
    rewrite H10 in H2.
    rewrite firstn_len in H2.
    unfold pat_at_n in H0.
    rewrite H2 in H0.
    econstructor; eauto.
    omega.
Qed.

