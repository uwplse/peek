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
Require Import PeekLivenessProof.
Require Import PeepsLib.
Require Import StepLib.
Require Import GlobalPerms.

Lemma current_PC_current_block:
forall st b i,
  current_PC st = Some (b, i) ->
  current_block st = Some b.
Proof.
intros.
unfold current_PC in *.
simpl_match_hyp.
eapply mk_current_block; eauto.
Qed.

Lemma mem_eq_match_metadata_l:
  forall md ml mr,
    mem_eq md ml mr ->      
    match_metadata md ml.
Proof.
  intros.
  unfold mem_eq in *.
  tauto.
Qed.

Lemma mem_eq_match_metadata_r:
  forall md ml mr,
    mem_eq md ml mr ->      
    match_metadata md mr.
Proof.
  intros.
  unfold mem_eq in *.
  tauto.
Qed.

Lemma star_step_basic_md:
forall p st st',
star_step_basic p st st' ->    
st_md st = st_md st'.
Proof.
induction 1; intros.
reflexivity.
NP app_new step_basic_corollaries step_basic.
repeat break_and.
subst.
simpl.
auto.
Qed.  

Lemma step_through_md:
forall ge st t st' z c p,
step_through z c ge st t st' ->
peep_code c ->
ge = env p ->
nPC p ->
st_md st = st_md st'.
Proof.
induction 1; intros.
- NP app_new step_bits_step_basic' step_bits.
NP app_new step_basic_corollaries step_basic.
repeat break_and.
subst.
simpl.
tauto.
- NP app_new star_step_in_in_code' star_step_in.
break_and.
P0 inv in_code.
NP app_new star_step_in_star_step_basic star_step_in.    
NP0 app_new step_bits_step_basic' step_bits.
NP0 app_new step_basic_corollaries step_basic.
repeat break_and.
subst.
simpl.
NP app_new star_step_basic_md star_step_basic.
Qed.  


Lemma step_fwd_transf_block:
  forall p st st' b k,
    step_fwd p st st' k ->
    current_block st = Some b ->
    current_block st' = Some b.
Proof.
  intros.
  unfold step_fwd in *.
  break_and.
  NP app_new step_basic_corollaries step_basic.
  repeat break_and.
  congruence.
Qed.

Lemma star_step_basic_transf_block:
  forall p st st' b,
    star_step_basic p st st' ->   
    current_block st = Some b ->
    current_block st' = Some b.    
Proof.
  induction 1; intros.
  assumption.
  NP app_new step_basic_corollaries step_basic.
  repeat break_and.
  subst.
  apply IHstar_step_basic.
  congruence.
Qed.

Lemma step_through_transf_block:
  forall ge st t st' z c p b,
    step_through z c ge st t st' ->
    peep_code c ->
    ge = env p ->
    nPC p ->
    current_block st = Some b ->
    current_block st' = Some b.    
Proof.
  induction 1; intros.
  - NP app_new step_bits_step_basic' step_bits.
    NP app_new step_basic_corollaries step_basic.
    repeat break_and.
    subst.
    congruence.
  - NP app_new star_step_in_in_code' star_step_in.
    break_and.
    P0 inv in_code.
    NP app_new star_step_in_star_step_basic star_step_in.    
    NP0 app_new step_bits_step_basic' step_bits.
    NP0 app_new step_basic_corollaries step_basic.
    repeat break_and.
    subst.
    NP app_new star_step_basic_transf_block star_step_basic.
    congruence.
Qed.

Lemma peep_code_cons:
  forall i c,
    peep_instr i ->
    peep_code c ->
    peep_code (i :: c).
Proof.
  intros.
  unfold peep_code in *.
  simpl.
  intros.
  repeat break_or.
  assumption.
  apply H0.
  auto.
Qed.

Lemma peep_code_hd:
  forall i,
    peep_instr i ->    
    peep_code (i :: nil).
Proof.
  intros.
  apply peep_code_cons; auto.
  unfold peep_code. simpl. intros. inv_false.
Qed.

Lemma peep_code_nil:
    peep_code nil.
Proof.
  unfold peep_code.
  simpl.
  intros.
  inv_false.
Qed.

Lemma peep_code_cons':
  forall i c,
    peep_code (i :: c) ->
    peep_instr i /\
    peep_code c.
Proof.
  intros.
  unfold peep_code in *.
  split.
  apply H.
  simpl. auto.
  intros.
  apply (in_cons i) in H0.
  apply H.
  assumption.
Qed.

Lemma no_calls'_cons:
  forall i c,
    no_calls' (i :: nil) ->
    no_calls' c ->
    no_calls' (i :: c).
Proof.
  intros.
  unfold no_calls' in *.
  intros.
  simpl in H1.
  break_or.
  apply H.
  simpl. auto.
  apply H0.
  auto.
Qed.

Lemma peep_instr_no_calls:
  forall i,
    peep_instr i ->
    no_calls' (i :: nil).
Proof.
  intros.
  unfold no_calls'.
  unfold not.
  intros.
  simpl in *. break_or; auto.
  destruct i0 eqn:?; simpl in *; tauto.
Qed.

Lemma peep_code_no_calls:
  forall c,
    peep_code c ->
    no_calls' c.
Proof.
  induction c; intros.
  vm_compute.
  intros.
  assumption.  
  apply peep_code_cons' in H.
  break_and.
  specialize (IHc H0).
  apply no_calls'_cons.
  apply peep_instr_no_calls; auto.
  auto.  
Qed.

Lemma no_trace_code'_cons:
  forall i c,
    no_trace_code' (i :: nil) ->
    no_trace_code' c ->
    no_trace_code' (i :: c).
Proof.
  intros.
  unfold no_trace_code' in *.
  intros.
  simpl in H1.
  break_or.
  apply H.
  simpl. auto.
  apply H0.
  auto.
Qed.

Lemma peep_instr_no_trace_code:
  forall i,
    peep_instr i ->
    no_trace_code' (i :: nil).
Proof.
  intros.
  unfold no_trace_code'.  
  intros.
  simpl in *. break_or; auto.
  destruct i0 eqn:?; simpl in *; tauto.
  tauto.
Qed.

Lemma peep_code_no_trace_code:
  forall c,
    peep_code c ->
    no_trace_code' c.
Proof.
  induction c; intros.
  vm_compute.
  intros.
  tauto.
  apply peep_code_cons' in H.
  break_and.
  specialize (IHc H0).
  apply no_trace_code'_cons; auto.
  apply peep_instr_no_trace_code; auto.
Qed.

Lemma only_forward_jumps_no_labels:
  forall c,
    peep_code c ->
    (forall i, In i c -> ~ is_any_label i) ->
    only_forward_jumps c.
Proof.
  intros.
  unfold only_forward_jumps.  
  split.
  apply no_calls_imp.
  apply peep_code_no_calls; auto.
  split.
  apply no_trace_code_imp.
  apply peep_code_no_trace_code; auto.
  apply only_forward_jumps_lab_imp.
  unfold only_forward_jumps_lab'.
  intros.
  specialize (H0 _ H3).
  simpl in *.
  tauto.
Qed.

Lemma skipz_neg:
  forall {A : Type} (c : list A) k,
    k < 0 ->
    skipz k c = c.
Proof.
  intros.
  destruct k.
  omega.
  copy (Pos2Z.is_pos p).
  omega.
  unfold skipz.
  unfold nat_of_Z.
  rewrite Z2Nat.inj_neg.
  simpl.
  reflexivity.
Qed.

Lemma skipz_crunch:
  forall {A: Type} k (i : A) c,
    skipz k (i :: c) =
    match k with
      | Zpos _ => skipz (k - 1) c
      | _ => (i :: c)
    end.
Proof.
  intros.
  break_match.
  apply skipz_0.  
  copy (Pos2Z.is_pos p).
  rewrite <- Heqz in *.
  apply skipz_cons; auto.
  copy (Pos2Z.neg_is_neg p).
  rewrite <- Heqz in *.
  apply skipz_neg; auto.
Qed.

Ltac crunch_skipz :=
  match goal with
    | [H: context[ skipz ?Z ?C ] |- _] =>
      repeat (rewrite skipz_crunch in H; simpl in H)
  end.  

(* TODO out *)

Ltac find_rewrite_goal :=
  match goal with
    | [H: ?X = _ |- context[?X]] => rewrite H
  end.

(*PEEP TACS*)

(*TODO replace with peep_tac_only_forward'*)
Ltac peep_tac_only_forward defs :=
    unfold only_forward_jumps;
    repeat split;
    [ cut (no_calls' (fnd defs)); try apply no_calls_imp;
      unfold no_calls'; simpl; intros;
      repeat break_or; tauto
    | cut (no_trace_code' (fnd defs)); try apply no_trace_code_imp;
      unfold no_trace_code'; simpl; intros;
      repeat break_or; simpl; tauto
    | cut (only_forward_jumps_lab' (fnd defs)); try apply only_forward_jumps_lab_imp;
      unfold only_forward_jumps_lab'; simpl; intros;
      repeat break_or; simpl; try tauto; repeat break_if; try congruence;
      omega
    ].

Ltac peep_tac_only_forward' :=
  try solve [
        apply only_forward_jumps_no_labels;
        unfold peep_code; simpl; intros; repeat break_or; simpl; tauto
        ];
  unfold only_forward_jumps;
  repeat split;
  match goal with
    | [|- no_calls ?C] =>
      cut (no_calls' C); try apply no_calls_imp;
      unfold no_calls'; simpl; intros;
      repeat break_or; tauto
    | [|- no_trace_code ?C] =>
      cut (no_trace_code' C); try apply no_trace_code_imp;
      unfold no_trace_code'; simpl; intros;
      repeat break_or; simpl; tauto
    | [|- context [ only_forward_jumps_lab _ ?C ] ] =>
      cut (only_forward_jumps_lab' C);
        try apply only_forward_jumps_lab_imp;
        unfold only_forward_jumps_lab'; simpl; intros;
        repeat (break_or; try tauto); simpl; repeat (break_if; try congruence);
        omega
  end.
    
Ltac peep_tac_measure_decr defs :=  
  intros;
  repeat break_exists;
  repeat break_and;
  NP app_new mk_not_after_label_in_code not_after_label;
  eapply measure_decr_fw_j; eauto;
  peep_tac_only_forward defs.

Ltac peep_tac_aux_proofs :=
  solve [
      simpl in *;
      unfold no_trace_code;
      unfold peep_code;
      unfold ends_in_not_label;
      intros;
      congruence || tauto || discriminate_instr].

Ltac peep_tac_no_def :=
  simpl;
  unfold no_def;
  unfold no_def_instr;
  intros;
  apply not_in_preserved;
  P0 _simpl In;
  repeat break_or;
  P0 _simpl In;
  repeat break_or;    
  simpl; auto 20.

Ltac peep_tac_pres := apply step_through_preserved_no_touch; (peep_tac_no_def || peep_tac_aux_proofs).

Ltac peep_tac_mk_rewrite' defs proofs :=
  refine (
      {|
        find := fnd defs;
        repl := rpl defs;
        live_in := lv_in defs;
        live_out := lv_out defs;
        pres := preserved defs;
        not_same := _;
        PC_live_out := _;
        find_nonempty := _;
        repl_nonempty := _;
        len_same := _;
        no_trace_find := _;
        no_trace_repl := _;
        no_label_out := _;
        forward_find := _;
        steps_equiv_live := selr proofs;
        steps_pres_find := _;
        steps_pres_repl := _;
        measure := measure_fun;
        measure_decr := _
      |}).

Ltac peep_tac_mk_rewrite defs proofs :=
  peep_tac_mk_rewrite' defs proofs;
  try solve [
        peep_tac_aux_proofs |
        peep_tac_only_forward defs |
        peep_tac_measure_decr defs |
        peep_tac_pres
      ].

(*STEP TACTICS*)

(*TODO: this won't handle jump tables*)
Ltac mk_non_jump_jump_tac :=
    match goal with
      | [Hc: current_instr ?ge ?st = Some ?i,
             Hj: ~ jumps_to_label ?ge ?st ?l |- _ ] =>
        assert (non_jump_jump i ge st)
          by (unfold non_jump_jump; simpl; split; auto; intros; subst; congruence)
    end.

Ltac step_l_str :=   
    NP1 app_new brk_step_through_straightline step_through;
    simpl; eauto;
    try (false_or; eexists; split; [ eauto | ]);
    try solve [unfold peep_code; simpl; intros; repeat break_or; simpl; tauto];
    try solve [peep_tac_only_forward'];
    [ ].

Ltac step_l_jmp :=
    NP1 app_new mk_jumps_to_label_dec step_through; [ |simpl; eauto];
    break_or; [
      try solve [
            NP1 _unfoldin jumps_to_label jumps_to_label;
            break_match_hyp; collapse_match_hyp; tauto
          ]
    | try solve [
            NP1 _unfoldin jumps_to_label jumps_to_label;
            collapse_match_hyp; congruence
          ]]; 
    match goal with
      | [_: jumps_to_label _ _ _ |- _] =>
        NP1 app_new brk_step_through_jump step_through; [
          | solve [simpl; auto; rewrite peq_true; eauto]
          | unfold peep_code; simpl; intros; repeat break_or; simpl; tauto
          | peep_tac_only_forward'
          ]
      | [_: ~ jumps_to_label _ _ _ |- _] =>
        mk_non_jump_jump_tac;
          step_l_str
    end.

Ltac step_l :=
    NP1 app_new step_through_current_instr step_through;
    NP1 app_new step_through_current_fn step_through; [ | simpl; eauto ];
    (step_l_str || step_l_jmp);
    break_and; crunch_skipz; P1 _simpl step_through; try break_and;
    NP1 app_new step_fwd_transf_block step_fwd.

Ltac step_r :=
    exploit mk_step_through_straightline;    
  try reflexivity; eauto; simpl; eauto;
  intros; repeat break_and;

  NP1 app_new step_through_transf_block step_through;
  try solve [apply peep_code_hd; simpl; auto];

  simpl_add;
  try (exploit step_through_chain_E0; [
         P2 _eapply step_through |
         repeat rewrite PeekLib.zlen_cons; simpl; simpl_add; P1 _eapply step_through |
         reflexivity |
         assumption |
         repeat (apply peep_code_cons; simpl; auto); apply peep_code_nil |
         apply peep_code_hd; simpl; auto |
         idtac
       ]; [];
       intros;
       repeat P2 _clear step_through;
       P _simpl step_through);
  P0 bump step_through.

Ltac prep_r :=
  repeat match goal with
         | [H: state_bits |- _] => destruct H
       end;
  repeat match goal with
           | [H : step_fwd _ _ _ _ |- _] => eapply step_fwd_exec in H;
               try eassumption;
               try reflexivity;
               break_and
         end;    
  P0 _clear step_through;
  P0 _clear current_fn;
  P0 _clear StepEquiv.not_after_label_in_code;
  NP app_new mem_eq_match_metadata_r MemEq.mem_eq.

Ltac finish_r :=
  eexists; eexists; split;
  [P _eapply step_through | ].

Lemma exec_load_bits_md :
  forall ge md c m addr rs reg rs' m' md',
    exec_load_bits ge md c m addr rs reg = Nxt rs' m' md' ->
    md = md'.
Proof.
  intros. unfold exec_load_bits in H.
  break_match_hyp; congruence.
Qed.

Lemma exec_store_bits_md :
  forall ge md c m addr rs reg rs' m' md' clob,
    exec_store_bits ge md c m addr rs reg clob = Nxt rs' m' md' ->
    md = md'.
Proof.
  intros. unfold exec_store_bits in H.
  break_match_hyp; congruence.
Qed.

Ltac finish_r' :=
  repeat match goal with
           | [ H : State_bits _ _ _ = State_bits _ _ _ |- _ ] => inv H
         end;
  repeat match goal with
           | [ H : forall fn : function, _ = Nxt _ _ ?X |- _ ] => uespecialize H;
               simpl in H;
               try app exec_load_bits_md H;
               try app exec_store_bits_md H
         end;
  subst;
  finish_r.

Ltac prep_l :=
  unfold StepEquiv.step_through_equiv_live;
  intros;
  (let H' := fresh "Hsym" in
   rename_all Globalenvs.Genv.symbol_address H');
  break_and; repeat break_exists;
  
  NP app_new step_through_no_trace step_through;
  try solve[ simpl; intros; repeat break_or; simpl; tauto ];
  subst;
  
  simpl_ls_pred;
  repeat simpl_val_eq;

  match goal with
    | [ _: MemEq.mem_eq ?md ?ml ?mr, _: ?rsl PC = ?rsr PC, _: _ PC = Vint ?bits |- _] =>
      assert (st_rs (State_bits rsl ml md) PC = st_rs (State_bits rsr mr md) PC) by auto;
        assert (rsr PC = Vint bits) by congruence
  end;
  NP0 app_new mk_current_PC Vint;
  NP _eapplyin at_code_transf at_code;
  eauto using mk_current_fn;
  
  P _simpl at_code;
  P _simpl step_through;

  NP app_new step_through_md step_through;
    try solve [unfold peep_code; simpl; intros;
             repeat break_or; simpl; auto; inv_false];    
  P1 _simpl st_md;
  subst;

  NP0 app_new current_PC_current_block current_PC.

(*MATCHER TACS*)

Ltac set_instr_eq i n ex :=
  destruct (same_opcode i (nth n ex Pnop)) eqn:?; [ | exact None];
  simpl_nth; destruct i; unfold same_opcode in *; try congruence; [ ]; clear_taut.
Ltac set_ireg_eq r1 r2 :=
  destruct (ireg_eq r1 r2); [ | exact None]; subst r1.
Ltac set_ireg_neq r1 r2 :=
  destruct (ireg_eq r1 r2); [exact None | ].
Ltac set_testcond_eq c1 c2 :=    
  destruct (testcond_eq c1 c2); [ | exact None]; subst c1.
Ltac set_label_eq l1 l2 :=    
  destruct (label_eq l1 l2); [ | exact None]; subst l1.
Ltac set_int_eq i1 i2 :=    
  destruct (Int.eq i1 i2) eqn:?; [ | exact None]; [];
  NP _applyin PtrEquiv.int_eq_true Int.eq; subst i1.
Ltac set_addrmode_eq a1 a2 :=
  destruct (addrmode_eq a1 a2); [ | exact None]; subst a1.
Ltac set_code_cons c := destruct c; [exact None | ].
Ltac set_code_nil c := destruct c; [ | exact None].

(*REG EQ TACTICS*)

Lemma no_ptr_regs_spec:
  forall rs r b i,
    no_ptr_regs rs ->
    rs r = Vptr b i ->
    False.
Proof.
  intros.
  unfold no_ptr_regs in *.
  unfold not in *.
  eapply H; eauto.
Qed.

Ltac no_ptr_regs_tac :=
  match goal with
    | [H1 : no_ptr_regs ?rs,
            H2: ?rs ?r = Vptr ?b ?i
       |- _] => apply (no_ptr_regs_spec rs r b i H1) in H2; exfalso; exact H2
  end.

Ltac prep_eq :=
  P0 _clear step_through;
  P0 _clear at_code;
  P0 _clear at_code_end;
  P0 _clear not_after_label_in_code;
  P0 _clear st_rs;
  subst;
  try inv_state;
  P0 bump val_eq;
  P0 bump exec_instr_bits.

Ltac case_reg_tac :=
  preg_case;
  repeat find_rewrite_goal;
  preg_simpl;
  try assumption.

Ltac unfold_val_int :=
  unfold Val.add;
  unfold Val.notint;
  unfold Val.sub.
Ltac val_or_tac :=      
  NP0 _applyin val_eq_or val_eq;
  repeat break_or; repeat break_and;
  repeat find_rewrite_goal; simpl; intros.
Ltac val_int_tac :=      
  unfold_val_int;
  simpl;
  repeat (break_match; try no_ptr_regs_tac; try congruence);
  repeat inv_vint;
  simpl;
  try match goal with
    | [|- Vint _ = Vint _] => f_equal
  end.

Lemma val_eq_compare_ints :
  forall a b x y md m m',
    val_eq a b ->
    val_eq x y ->
    mem_eq md m m' ->
    forall f rs rs',
      In f flags ->          
      val_eq (compare_ints a x rs m f)
             (compare_ints b y rs' m' f).
Proof.
  intros.
  unfold compare_ints.      
  unfold flags in *; simpl in *; repeat break_or; try inv_false; subst;
  preg_simpl; repeat break_match; preg_simpl; simpl; eauto; intros; try congruence;
  unfold Val.of_bool.
  eapply val_eq_cmpu; eauto.
  eapply val_eq_cmpu; eauto.
Qed.

Lemma nextinstr_flags :
  forall rs reg,
    In reg flags ->
    nextinstr rs reg = rs reg.
Proof.
  intros.
  simpl in *.
  repeat break_or; try inv_false; simpl; reflexivity.
Qed.

Ltac simpl_exec_hyp H :=
  match type of H with
    | exec_instr_bits _ _ _ _ _ _ _ = Nxt _ _ _ => simpl in H
    | exec_load_bits _ _ _ _ _ _ _ = Nxt _ _ _ => unfold exec_load_bits in H
    | exec_store_bits _ _ _ _ _ _ _ _ = Nxt _ _ _ => unfold exec_store_bits in H
    | goto_label_bits _ _ _ _ _ _ = Nxt _ _ _ => unfold goto_label_bits in H
  end.

Ltac state_inv' :=
  match goal with
    | [ H : Stck = Nxt _ _ _ |- _ ] => inversion H
    | [ H : Nxt _ _ _ = Stck |- _ ] => inversion H
    | [ H : Nxt _ _ _ = Nxt _ _ _ |- _ ] => inversion H
  end.
    
Ltac break_match_lem H :=
  match type of H with
    | context [ match ?X with _ => _ end ] => destruct X eqn:?
  end.
Ltac break_match_sm_lem H :=
  match type of H with
    | context [ match ?X with _ => _ end ] => break_match_sm' X
  end.
Ltac simpl_and_clear_hyp H :=
  repeat (simpl_exec_hyp H; repeat (break_match_sm_lem H; try congruence)); state_inv'; clear H.
Ltac simpl_and_clear :=
  P0 simpl_and_clear_hyp exec_instr_bits;
  P0 simpl_and_clear_hyp exec_load_bits;
  P0 simpl_and_clear_hyp goto_label_bits.

Ltac break_or' :=
  match goal with
    | [ H : _ \/ _ |- _ ] => inversion H
  end.

Ltac break_or_reg :=
  match goal with
    | [ H : ?A \/ ?B |- _ ] => inversion H;
        [
          match goal with
            | [_: ?r = ?reg, H2: ?r = ?reg \/ _ |- _] => subst reg; clear H2
          end
        | try inv_false; clear H
        ]
  end.    

Ltac eq_mem_tac :=
  repeat (simpl_and_clear; try break_match; try congruence).

Ltac eq_reg_tac :=
  intros;
  repeat (break_or; try inv_false); try preg_simpl;
  repeat find_rewrite_goal; simpl;
  match goal with
    | [|- Vint _ = Vint _] => f_equal
    | [|- val_eq _ _] =>
      repeat (simpl_and_clear; try break_match; try congruence);
        repeat (state_inv); try opt_inv; preg_simpl
  end;
  try assumption.

(*TODO merge with prep_eq*)
Ltac prep_eq' :=
  P0 _clear step_through;
  P0 _clear at_code;
  P0 _clear at_code_end;
  P0 _clear not_after_label_in_code;
  P0 _clear st_rs;
  subst;
  try inv_state;
  P0 bump val_eq;
  P0 bump exec_instr_bits;
  split;
  [
    intros; simpl_and_clear; repeat break_or_reg
    | eq_mem_tac
  ].

Ltac prep_exec_instr :=
  match goal with
    |[H: at_code ?z (?i :: _) 0 ?ge (State_bits ?rs ?m ?md),
      H2: current_block (State_bits ?rs ?m ?md) = Some ?b |- _] =>
     assert (exists rs' m' md',
               (forall fn : function, exec_instr_bits ge md fn i b rs m = Nxt rs' m' md'))
  end.

(*TODO move to a PeepsLib*)

Lemma eval_addrmode_bits_transf:
  forall md ge1 ge2 a rs,
    (forall id ofs,
       Genv.symbol_address ge1 id ofs =
       Genv.symbol_address ge2 id ofs) ->
   eval_addrmode_bits ge1 md a rs =
   eval_addrmode_bits ge2 md a rs.
Proof.
  intros.
  unfold eval_addrmode_bits in *.
  unfold eval_addrmode in *.
  repeat (break_match; try congruence).
Qed.

Lemma eq_mem_exec_store_bits :
  forall md ml mr,
    mem_eq md ml mr ->
    forall addr rsr rsl,
      (forall reg, In reg (use_addr addr) -> val_eq (rsl reg) (rsr reg)) ->
      forall ge1 ge2 c reg l rsl' ml' md',
        val_eq (rsl reg) (rsr reg) ->
        (forall id ofs, Genv.symbol_address ge1 id ofs = Genv.symbol_address ge2 id ofs) ->
        exec_store_bits ge1 md c ml addr rsl reg l = Nxt rsl' ml' md' ->
        exists rsr' mr',
          exec_store_bits ge2 md c mr addr rsr reg l = Nxt rsr' mr' md' /\ mem_eq md' ml' mr'.
Proof.
  intros.
  unfold exec_store_bits in *.
  unfold storev_bits in *.
  repeat (break_match_hyp; try congruence); repeat state_inv.
  app use_addr_eval_addrmode_bits Heqv; try congruence; try apply H0.
  erewrite eval_addrmode_bits_transf in Heqv; eauto.
  collapse_match.
  app eq_mem_store Heqo; try apply H0; eauto.
  break_and.
  collapse_match.
  eexists; eexists; split; auto.
Qed.    


Require Import Memory.
Require Import MemBits.

Lemma load_store_bits_same:          
  forall (m1 : mem) 
         (b : block) (ofs : Z) (v v' : val) (m2 : mem),
    store_bits AST.Mint32 m1 b ofs v = Some m2 ->
    val_eq v v' ->
    forall res,
      Mem.load AST.Mint32 m2 b ofs = Some res ->
      val_eq res v'.
Proof.          
  intros. unfold store_bits in *.
  break_match_hyp; try congruence; opt_inv; subst.
  app Mem.load_result H1.
  subst. unfold Mem.mem_contents.
  clear H. rewrite Maps.PMap.gss.
  erewrite <- encode_val_bits_length.
  rewrite Mem.getN_setN_same.
  unfold val_eq in H0.
  break_match_hyp; try inv_false; simpl; try congruence.
  unfold decode_val.
  rewrite proj_inj_bytes.
  rewrite decode_encode_int_4.
  subst. simpl. reflexivity.
Qed.

Lemma val_eq_use_addr_nextinstr_nf:
  forall p a rs,
    In p (use_addr a) ->
    no_ptr_regs rs ->
    val_eq (nextinstr_nf rs p) (rs p).
Proof.
  intros.
  unfold use_addr in *.
  repeat break_match;          
    simpl in *;
    repeat break_or_reg;
    preg_simpl;
    apply Use.val_eq_refl;
    unfold no_ptr_regs in *;
    auto.
Qed.

Ltac clear_dup :=
  match goal with
    |[H : ?A, H2: ?A |- _] => clear H
  end.
      
Lemma eval_testcond_e_neg:
  forall st b,
    eval_testcond Cond_e st = Some b ->
    (st ZF = Vtrue \/ st ZF = Vfalse) ->          
    eval_testcond Cond_ne st = Some (negb b).
Proof.
  intros.
  unfold eval_testcond in *.
  break_or.
  collapse_match.
  collapse_match_hyp.
  simpl in *.
  f_equal.
  inv_some.
  vm_compute.
  auto.
  collapse_match.
  collapse_match_hyp.
  simpl in *.
  f_equal.
  inv_some.
  vm_compute.
  auto.
Qed.

Lemma eval_testcond_ne_neg:
  forall st b,
    eval_testcond Cond_ne st = Some b ->
    (st ZF = Vtrue \/ st ZF = Vfalse) ->          
    eval_testcond Cond_e st = Some (negb b).
Proof.
  intros.
  unfold eval_testcond in *.
  break_or.
  collapse_match.
  collapse_match_hyp.
  simpl in *.
  f_equal.
  inv_some.
  vm_compute.
  auto.
  collapse_match.
  collapse_match_hyp.
  simpl in *.
  f_equal.
  inv_some.
  vm_compute.
  auto.
Qed.

Ltac find_subst :=
        match goal with
          | [H : ?a = ?b |- _] => subst a
        end.

Ltac gentle_inv_next :=
  match goal with
    | [H: Nxt _ _ _ = Nxt _ _ _ |- _] => inversion H; clear H
  end.

(*Stuart's Ring Magic *)

Lemma int_ring : ring_theory Int.zero Int.one Int.add Int.mul Int.sub Int.neg eq.
constructor; intros;
eauto using
  Int.add_zero_l, Int.add_assoc, Int.add_commut,
  Int.mul_one, Int.mul_assoc, Int.mul_commut,
  Int.mul_add_distr_l, Int.sub_add_opp, Int.add_neg_zero.
- (* 1 * x = x -- doesn't quite go through on its own *)
  rewrite Int.mul_commut. apply Int.mul_one.
Qed.

Definition eq_dec_bool x y := Coqlib.proj_sumbool (Int.eq_dec x y).

Lemma int_ring_dec : forall x y, eq_dec_bool x y = true -> x = y.
intros.
unfold eq_dec_bool, Coqlib.proj_sumbool in *.
destruct (Int.eq_dec _ _); congruence.
Qed.

Ltac int_ring_constants t :=
    match t with
    | Int.zero => constr:(Int.repr 0)
    | Int.one => constr:(Int.repr 1)
    | Int.repr _ => t
    | _ => constr:NotConstant
    end.

Add Ring IntRing : int_ring (decidable int_ring_dec, constants [int_ring_constants]).

(*end ring magic*)
