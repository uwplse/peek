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
Require Import Memory.
Require Import Asm.

Require Import PeekLib.
Require Import PeekTactics.
Require Import FindInstrLib.
Require Import PregTactics.
Require Import ProgPropDec.

Require Import Zlen.
Require Import AsmBits.
Require Import MemoryAxioms.
Require Import PtrEquiv.
Require Import PtrEquivMem.
Require Import PtrEquivMemInit.


Definition instr_of_prog (i : instruction) (p : program) :=
  exists z c,
    code_of_prog c p /\ find_instr z c = Some i.

Fixpoint lookup_global {F V : Type} (id : ident) (l : list (ident * globdef F V)) : option (globdef F V) :=
  match l with
    | nil => None
    | (id',gd) :: r => if peq id id' then Some gd else lookup_global id r
  end.

Definition global_size (id : ident) (p : program) : Z :=
  match lookup_global id (prog_defs p) with
    | Some (Gfun (Internal f)) => zlen (fn_code f)
    | Some (Gfun (External e)) => 1
    | Some (Gvar v) => Genv.init_data_list_size (gvar_init v)
    | None => 0
  end.


(* Fixpoint lookup_global {F V : Type} (id : ident) (l : list (ident * globdef F V)) : option (globdef F V) := *)
(*   match l with *)
(*     | nil => None *)
(*     | (id',gd) :: r => if peq id id' then Some gd else lookup_global id r *)
(*   end. *)

(* Definition global_size (id : ident) (p : program) : Z := *)
(*   match lookup_global id (prog_defs p) with *)
(*     | Some (Gfun (Internal f)) => zlen (fn_code f) *)
(*     | Some (Gfun (External e)) => 0 *)
(*     | Some (Gvar v) => Genv.init_data_list_size (gvar_init v) *)
(*     | None => 0 *)
(*   end. *)



Lemma lookup_norepet :
  forall {F V : Type} l (id : ident) (x : globdef F V),
    list_norepet (map fst l) ->
    In (id,x) l ->
    lookup_global id l = Some x.
Proof.
  induction l; intros.
  simpl in H0. inv H0.
  simpl in H0. break_or.
  simpl. destruct (peq id id); congruence.
  simpl in H. inv H.
  app IHl H1.
  simpl. rewrite H1.
  destruct a. simpl in H3.
  eapply in_map with (f := fst) in H. simpl in H.
  break_match; auto. subst. congruence.
Qed.

Fixpoint well_formed_annot_arg {A : Type} (aa : annot_arg A) (p : program) : Prop :=
  match aa with
    | AA_addrglobal id ofs =>
      In id (prog_defs_names p) ->
      0 <= Int.unsigned ofs < global_size id p
    | AA_longofwords hi lo => well_formed_annot_arg hi p /\ well_formed_annot_arg lo p
    | _ => True
  end.

Definition well_formed_addrmode (a : addrmode) (p : program) : Prop :=
  match a with
    | Addrmode _ _ (inr (id,ofs)) =>
      In id (prog_defs_names p) ->
      0 <= Int.unsigned ofs <= global_size id p
    | _ => True
  end.

Definition all_lea_well_formed (p : program) : Prop :=
  forall r a,
    instr_of_prog (Plea r a) p ->
    well_formed_addrmode a p.

Definition all_annot_well_formed (p : program) : Prop :=
  forall e l,
    instr_of_prog (Pannot e l) p ->
    forall aa,
      In aa l -> well_formed_annot_arg aa p.

Definition is_nonempty_fun (id : ident) (p : program) : Prop :=
  forall x,
    In (id,x) (prog_defs p) ->
    exists fd,
      x = Gfun fd /\ match fd with
                       | Internal f => (fn_code f <> nil)
                       | External _ => True
                     end.


Definition global_nonempty (gd : globdef fundef unit) : Prop :=
  match gd with
    | Gvar v => Genv.init_data_list_size (gvar_init v) > 0
    | Gfun (Internal fd) => zlen (fn_code fd) > 0
    | Gfun (External _) => True
  end.

Definition globals_nonempty (p : program) : Prop :=
  forall id gd,
    In (id,gd) (prog_defs p) -> global_nonempty gd.

Section FSIM.


  Variable p : program.
  Definition ge := Genv.globalenv p.
  (* All of these are well formedness hypotheses that we will carry down from higher levels *)
  Hypothesis palloc : all_allocframes_positive p.
  Hypothesis norep : list_norepet (prog_defs_names p).
  Hypothesis main_fn_is_fn : is_nonempty_fun (prog_main p) p.
  (* Hypothesis all_addrmode_wf : all_lea_well_formed p. *)
  Hypothesis all_annot_wf : all_annot_well_formed p.
  Hypothesis no_PC : no_PC_overflow_prog p.
  (* Hypothesis nonempty : globals_nonempty p. *)
  (* Hypothesis all_defs_wf : wf_defs p (prog_defs p). *)


  
  Definition alloc_inj (t : allocator_metadata) : Prop :=
    forall b,
      allocated t b ->
      pinj t b Int.zero <> None.

  Definition reachable (s : state) : Prop :=
    exists start_state tr,
      initial_state p start_state /\
      star step ge start_state tr s.
  
  (* This is what we have to assume about the program *)
  (* TODO: change allocated to be just about blocks *)
  (* just say the first thing in the block injects *)
  (* pinj_add takes care of the rest *)
  Hypothesis prog_well_behaved :
    forall rs m t,
      reachable (State rs m) ->
      match_metadata t m ->
      alloc_inj t.

  (* Hypothesis global_base_inj : *)
  (*   forall rs m t b, *)
  (*     reachable (State rs m) -> *)
  (*     match_metadata t m -> *)
  (*     is_global_block b -> *)
  (*     pinj t b (Int.zero) <> None. *)
  
  Definition reachable_bits (s : state_bits) : Prop :=
    exists start_state tr,
      initial_state_bits p start_state /\
      star step_bits ge start_state tr s.

  Definition globals_alloc (t : allocator_metadata) : Prop := 
    forall b,
      is_global_block (Genv.globalenv p) b ->
      allocated t b.

  
  Inductive match_states : state -> state_bits -> Prop :=
  | internal :
      forall t rs m rs' m',
        ptr_equiv_rs t rs rs' ->
        ptr_equiv_mem (Genv.globalenv p) t m m' ->
        globals_alloc t ->
        reachable (State rs m) ->
        reachable_bits (State_bits rs' m' t) ->
        match_states (State rs m) (State_bits rs' m' t).


  (* Lemma within_global_size_in_range : *)
  (*   forall id ofs b, *)
  (*     Genv.find_symbol ge id = Some b -> *)
  (*     0 <= Int.unsigned ofs < global_size id p -> *)
  (*     (in_var_range ge b ofs \/ in_code_range ge b ofs). *)
  (* Proof. *)
  (*   intros. app Genv.find_symbol_inversion H. *)
  (*   unfold prog_defs_names in H. *)
  (*   app list_in_map_inv H. repeat break_and. destruct x. *)
  (*   simpl in H. subst i. *)
  (*   destruct g. right. *)
  (*   app Genv.find_funct_ptr_exists H4. break_and. *)
  (*   unfold ge in H1. rewrite H1 in H4. inv H4. *)
  (*   unfold in_code_range. unfold global_size in H3. *)
  (*   app (@lookup_norepet fundef unit) H. rewrite H in H3. *)
  (*   unfold ge. rewrite H5. *)
  (*   break_match; simpl. *)
    
  (*   omega. *)

  (*   omega. *)

  (*   left. *)
  (*   app (@lookup_norepet fundef unit) H4. *)
  (*   unfold global_size in H3. rewrite H4 in H3. *)
  (*   unfold in_var_range. app Genv.find_var_exists H. *)
  (*   repeat break_and. unfold ge in *. rewrite H1 in H. *)
  (*   inv H. rewrite H6. omega. *)
  (* Qed. *)

  (* Lemma inj_init_defs: *)
  (*   forall rs m t, *)
  (*     initial_state p (State rs m) -> *)
  (*     match_metadata t m -> *)
  (*     injectable_defs ge t (prog_defs p). *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold wf_defs in *. unfold wf_idg in *. *)
  (*   unfold wf_globdef in *. unfold wf_gvar in *. *)
  (*   unfold injectable_defs. unfold injectable_idg. *)
  (*   unfold injectable_globdef. unfold injectable_gvar. *)
  (*   intros. break_let. break_match; auto. *)
  (*   intros. *)
  (*   subst. *)
  (*   app all_defs_wf H1. simpl. *)
  (*   app H1 H2. *)
  (*   unfold wf_init_data in H2. *)
  (*   unfold injectable_init_data. *)
  (*   break_match; auto. *)
  (*   intros. *)
  (*   eapply prog_well_behaved; eauto. *)
  (*   unfold reachable.  *)
  (*   exists (State rs m). exists E0. *)
  (*   split; auto. *)
  (*   eapply star_refl. *)

  (*   inv H. *)
  (*   app ptr_equiv_init H7. *)
  (*   break_and. unfold ptr_equiv_mem in H8. *)
  (*   repeat break_and. *)
  (*   unfold PtrEquivMem.globals_allocated in H11. *)
    
  (*   eapply ptr_equiv_init_find_symbol. *)
  (*   inv H. eauto. eauto. *)
  (*   eapply within_global_size_in_range. eauto. *)
  (*   eauto. *)
    
    
  (* Qed. *)

  Lemma goto_label_same_mem :
    forall f l rs m rs' m',
      goto_label f l rs m = Next rs' m' ->
      m = m'.
  Proof.
    intros. unfold goto_label in H.
    repeat break_match_hyp; congruence.
  Qed.

  (* Definition more_allocated (md md' : allocator_metadata) : Prop := *)
  (*   forall b ofs, *)
  (*     allocated md b ofs -> *)
  (*     allocated md' b ofs. *)

  (* This is the wrong approach *)
  (* Probably not useful, as has existential in conclusion *)
  (* Move this lemma to MemoryAxioms.v *)
  (* Lemma step_match_metadata : *)
  (*   forall ge rs m t rs' m' md, *)
  (*     match_metadata md m -> *)
  (*     step ge (State rs m) t (State rs' m') -> *)
  (*     exists md', *)
  (*       match_metadata md' m' /\ more_allocated md md'. *)
  (* Proof. *)
  (*   intros. inv_step H0. *)
  (*   subst. *)
  (*   * destruct i; simpl_exec; *)
  (*     simpl in H9; *)
  (*     repeat break_match_hyp; *)
  (*     inv H9; *)
  (*     unfold exec_load in *; *)
  (*     unfold exec_big_load in *; *)
  (*     repeat (break_match_hyp; try congruence); *)
  (*     try find_inversion; *)

  (*     try solve [eexists; split; try eassumption; *)
  (*                unfold more_allocated; intros; assumption]; *)
      
  (*     unfold exec_store in *; unfold Mem.storev in *; *)
  (*     repeat (break_match_hyp; try congruence); *)
  (*     try find_inversion; *)

  (*     try solve [eexists; split; try eapply match_store; eauto; *)
  (*                unfold more_allocated; intros; assumption]; *)
      
  (*     try solve [match goal with *)
  (*                  | [ H : goto_label _ _ _ _ = Next _ _ |- _ ] => *)
  (*                    app goto_label_same_mem H; *)
  (*                      subst; *)
  (*                      solve [eexists; split; try eassumption; *)
  (*                             unfold more_allocated; intros; assumption] *)
  (*                end]; *)
            
  (*     try solve [unfold exec_big_store in *; *)
  (*                 unfold Mem.storev in *; *)
  (*                 repeat (break_match_hyp; try congruence); *)
  (*                 find_inversion; *)
  (*                 eexists; split; try eapply match_store; *)
  (*                 try eapply match_store; eauto; *)
  (*                 unfold more_allocated; intros; assumption]. *)

  (*     (* alloc frame *) *)
  (*     eexists. split. *)
  (*     eapply match_store. eapply match_store. *)
  (*     eapply match_alloc. eassumption. *)
  (*     eauto. eauto. eauto. *)
  (*     econstructor; eauto. *)


  (*     (* free frame *) *)
  (*     eexists. split. eapply match_free; eauto. *)
  (*     econstructor; eauto. *)
      
  (*   * subst. *)
  (*     eexists. split. *)
  (*     eapply match_ec'; eauto. *)
  (*     econstructor; eauto. *)
  (*   * subst. *)
  (*     eexists. split. *)
  (*     eapply match_ec; eauto. *)
  (*     econstructor; eauto. *)
  (*   * subst. *)
  (*     eexists. split. *)
  (*     eapply match_ec'; eauto. *)
  (*     econstructor; eauto. *)
  (* Qed. *)

  (* Lemma star_step_match_metadata : *)
  (*   forall st st' t, *)
  (*     star step ge st t st' -> *)
  (*     forall rs m, *)
  (*       st = State rs m -> *)
  (*       forall rs' m', *)
  (*         st' = State rs' m' -> *)
  (*         forall md, *)
  (*           match_metadata md m -> *)
  (*           exists md', *)
  (*             match_metadata md' m' /\ more_allocated md md'. *)
  (* Proof. *)
  (*   induction 1; intros. *)
  (*   subst. inv H0. *)
  (*   eexists. split. eauto. *)
  (*   unfold more_allocated. intros. eauto. *)
  (*   subst. destruct s2. *)
  (*   specialize (IHstar _ _ eq_refl _ _ eq_refl). *)
  (*   app step_match_metadata H. break_and. *)
  (*   specialize (IHstar x H). *)
  (*   break_exists. break_and. *)
  (*   exists x0. split. auto. *)
  (*   unfold more_allocated in *. *)
  (*   intros. apply H5. *)
  (*   apply H2. assumption. *)
  (* Qed. *)
  
  (* Lemma reachable_injectable : *)
  (*   forall rs m, *)
  (*     reachable (State rs m) -> *)
  (*     exists md, *)
  (*       injectable_defs ge md (prog_defs p) /\ *)
  (*       match_metadata md m. *)
  (* Proof. *)
  (*   intros. unfold reachable in *. *)
  (*   repeat break_exists. *)
  (*   break_and. *)
  (*   destruct x. *)
  (*   app init_state_match_metadata H. *)

  (*   app star_step_match_metadata H0. break_and. *)
  (*   exists x1. split; auto. *)
  (*   unfold injectable_defs. intros. *)
  (*   unfold injectable_idg. break_let. *)
  (*   unfold injectable_globdef. break_match; auto. *)
  (*   unfold injectable_gvar. intros. *)
  (*   unfold injectable_init_data. break_match; auto. intros. *)
  (*   unfold alloc_inj in *. *)
  (*   eapply prog_well_behaved; eauto. *)
  (*   apply H3. *)

  (*   eapply ptr_equiv_init_find_symbol; eauto. *)
  (*   inv H1; auto. *)

  (*   eapply within_global_size_in_range. eauto. *)
  (*   unfold wf_defs in *. *)
  (*   unfold wf_idg in *. *)
  (*   subst. specialize (all_defs_wf (i, Gvar v) H4). *)
  (*   break_let. inv Heqp0. *)
  (*   unfold wf_globdef in *. *)
  (*   unfold wf_gvar in *. *)
  (*   specialize (all_defs_wf _ H5). *)
  (*   unfold wf_init_data in *. auto. *)
  (* Qed. *)
  
  Fixpoint injectable_annot_arg {A : Type} (t : allocator_metadata) (aa : annot_arg A) : Prop :=
    match aa with
      | AA_addrglobal id ofs =>
        match Genv.find_symbol ge id with
          | Some b => pinj t b ofs <> None
          | None => True
        end
      | AA_longofwords hi lo => injectable_annot_arg t hi /\ injectable_annot_arg t lo
      | _ => True
    end.
  
  Lemma well_formed_inj :
    forall {A : Type} t rs m (aa : annot_arg A),
      well_formed_annot_arg aa p ->
      globals_alloc t ->
      reachable (State rs m) ->
      match_metadata t m ->
      injectable_annot_arg t aa.
  Proof.
    induction aa; intros; simpl; auto.
    unfold well_formed_annot_arg in H.
    break_match; auto.
    unfold globals_alloc in H0.
    unfold alloc_inj in prog_well_behaved.
    destruct (pinj t b ofs) eqn:?; try congruence.
    exploit prog_well_behaved; try eapply H0; eauto.

    app Genv.find_symbol_inversion Heqo.
    unfold prog_defs_names in Heqo.
    app list_in_map_inv Heqo.
    destruct x. break_and. subst.
    unfold is_global_block. eauto.

    destruct (pinj t b Int.zero) eqn:?; try congruence.
    eapply pinj_add in Heqo1.
    instantiate (1 := ofs) in Heqo1.
    rewrite Int.add_zero_l in Heqo1.
    congruence.
    
    simpl in H. break_and.
    eauto.

  Qed.

  Lemma all_annot_arg_injectable :
    forall e l,
      instr_of_prog (Pannot e l) p ->
      forall aa t rs m,
        In aa l ->
        globals_alloc t ->
        reachable (State rs m) ->
        match_metadata t m ->
        injectable_annot_arg t aa.
  Proof.
    intros.
    unfold all_annot_well_formed in *.
    app all_annot_wf H0.
    eapply well_formed_inj; eauto.
  Qed.

(*   Lemma all_addrmode_injectable : *)
(*     forall r a, *)
(*       instr_of_prog (Plea r a) p -> *)
(*       injectable_addrmode a. *)
(*   Proof. *)
(*     intros. unfold all_lea_well_formed in all_addrmode_wf. *)
(*     app all_addrmode_wf H. *)
(*     unfold well_formed_addrmode in H. *)
(*     unfold injectable_addrmode. *)
(*     destruct a; auto. destruct const; auto. *)
(*     destruct p0. break_match; auto. *)
(*     app Genv.find_symbol_inversion Heqo. *)
(*     app H Heqo. *)
(*     apply globals_valid. *)
(*     unfold prog_defs_names in H2. *)
(*     app list_in_map_inv H2. break_and. subst i. *)
(*     destruct x. destruct g. *)
(*     right. unfold in_code_range. *)
(*     app Genv.find_funct_ptr_exists H4. repeat break_and. *)
(*     unfold ge. simpl in H1. unfold ge in H1. *)
(*     rewrite H1 in H4. inv H4. *)
(*     rewrite H7. simpl in H6. *)
(*     unfold global_size in H6. *)
(*     app (@lookup_norepet fundef unit) H2. *)
(*     rewrite H2 in H6. *)
(*     break_match; try omega. *)
(*     assert (Int.unsigned i0 = 0) by omega. *)
(*     rewrite H8 in *. *)
(*     destruct i0. simpl in H8. subst. unfold Int.zero. *)
(*     symmetry. apply Int.eqm_repr_eq. simpl. *)
(*     apply Int.eqm_refl. *)
(*     left. unfold in_var_range. *)
(*     app Genv.find_var_exists H4. repeat break_and. *)
(*     unfold ge in *. simpl in H1. *)
(*     rewrite H4 in H1. inv H1. *)
(*     rewrite H7. simpl in H6. unfold global_size in H6. *)
(*     app (@lookup_norepet fundef unit) H2. rewrite H2 in H6. *)
(*     omega. *)
(*   Qed. *)

  
(* Lemma pinj_main_exists : *)
(*     match Genv.symbol_address (Genv.globalenv p) (prog_main p) Int.zero with *)
(*       | Vptr b i => pinj b i <> None *)
(*       | _ => True *)
(*     end. *)
(* Proof. *)
(*   unfold Genv.symbol_address. break_match_sm; auto. *)
(*   app Genv.find_symbol_inversion Heqo. *)
(*   eapply globals_valid. right. unfold in_code_range. *)
(*   unfold prog_defs_names in Heqo. *)
(*   app list_in_map_inv Heqo. break_and. *)
(*   destruct x. simpl in H1. subst i. *)
(*   destruct g. *)
(*   app Genv.find_funct_ptr_exists H2. break_and. rewrite H2 in H. inv H. *)
(*   unfold ge. rewrite H3. rewrite Int.unsigned_zero. *)
(*   break_match. *)
(*   name (zlen_nonneg _ (fn_code f0)) zln. omega. reflexivity. *)
(*   app main_fn_is_fn H2. specialize (H2 v). congruence. *)
(* Qed. *)

(* Lemma pinj_symbol_exists : *)
(*   forall id, *)
(*     match Genv.find_symbol (Genv.globalenv p) id with *)
(*       | Some b => *)
(*         pinj b Int.zero <> None *)
(*       | None => True *)
(*     end. *)
(* Proof. *)
(*   intros. break_match; auto. *)
(*   eapply globals_valid; eauto. *)
(*   app Genv.find_symbol_inversion Heqo. *)
(*   unfold prog_defs_names in Heqo. app list_in_map_inv Heqo. *)
(*   break_and. destruct x. simpl in H1. subst id. destruct g. *)
(*   right. app Genv.find_funct_ptr_exists H2. break_and. *)
(*   rewrite H in H2. inv H2. unfold in_code_range. *)
(*   unfold ge. rewrite H3. break_match. *)
(*   name (zlen_nonneg _ (fn_code f0)) zln. rewrite Int.unsigned_zero. omega. *)
(*   reflexivity. *)
(*   left. unfold in_var_range. app Genv.find_var_exists H2. break_and. *)
(*   rewrite H2 in H. inv H. *)
(*   unfold ge. find_rewrite. *)
(*   rewrite Int.unsigned_zero. split; try omega. *)
(*   name (Genv.init_data_list_size_pos (gvar_init v)) lsp. omega. *)
(* Qed. *)
  
(* Lemma pinj_alloc_exists : *)
(*   forall rs m', *)
(*     reachable (State rs m') -> *)
(*     forall lo hi m b, *)
(*       lo < hi -> *)
(*       Mem.alloc m lo hi = (m',b) -> *)
(*       forall i, *)
(*         lo <= Int.unsigned i -> *)
(*         Int.unsigned i <= hi -> (* pointers to just after block are also valid *) *)
(*         pinj b i <> None. *)
(* Proof. *)
(*   intros. *)
(*   eapply reachable_ptr_valid; eauto. *)
(*   rewrite orb_true_iff. *)
(*   assert (Int.unsigned i < hi \/ Int.unsigned i = hi) by omega. destruct H4. *)
(*   left. *)
(*   rewrite Mem.valid_pointer_nonempty_perm. *)
(*   app Mem.perm_alloc_2 H1. *)
(*   eapply Mem.perm_implies; eauto. econstructor. *)
(*   right. *)
(*   rewrite H4 in *. clear H4. *)
(*   rewrite Mem.valid_pointer_nonempty_perm. *)
(*   app Mem.perm_alloc_2 H1. *)
(*   eapply Mem.perm_implies; eauto. econstructor. *)
(*   split; try omega. *)
(* Qed. *)

  
  
Lemma eval_addrmode_pres :
  forall a rs rs' m m' t b i,
    match_states (State rs m) (State_bits rs' m' t) ->
    eval_addrmode ge a rs = Vptr b i ->
    Mem.valid_pointer m b (Int.unsigned i) = true ->
    eval_addrmode_bits ge t a rs' = Vptr b i.
Proof.

  intros a rs rs' m m' t b i H Hev Hvp.
  inversion H as [ x y c d e Hptr_rs Hptr_mem Hreach Hreach_bits ].
  subst.
  unfold eval_addrmode in *.
  unfold eval_addrmode_bits.
  unfold ptr_equiv_rs in *.
  unfold ptr_equiv_val in *.
  destruct a. 
  repeat break_match_hyp; subst;
  try name (Hptr_rs i0) Hi0;
    try name (Hptr_rs i1) Hi1;
    try name (Hptr_rs i2) Hi2;
    clear Hptr_rs;
    repeat break_match_hyp;
    repeat break_or;
    repeat break_exists;
    repeat break_and;
    simpl;
    try rewrite H0;
    try rewrite H1;
    try rewrite H2;
    unfold Val.add in *;
    unfold Val.mul in *;
    simpl in *;
    try congruence;
    try rewrite <- Hi0;
    try rewrite <- Hi1;
    inversion Hev;
    subst;
    try rewrite Heqb0;
    repeat (break_match_hyp; try congruence);

    match goal with
      | [ H : pinj t _ _ = Some ?X
          |-
          match psur t (Int.add ?X _ ) with
              _ => _
          end = _
        ] => idtac
      | [ |- _ ] => try rewrite Int.add_permut
    end;
  
  
  name (pinj_add _ _ _ _ H2) Hpinj;
  match goal with
    | [ |- match psur _ (Int.add _ ?X) with
               _ => _ end = _ ] =>
      specialize (Hpinj X)
  end;

  try find_inversion;
  try find_inversion;
  try inv Heqv1;
  try inv Heqv0;
  
  try solve [
        app Mem.valid_pointer_implies Hvp;
        name (conj Hpinj Hvp) Hp;
        erewrite <- weak_valid_pointer_sur in Hp;
        try collapse_match; try f_equal; try ring;
        eapply ptr_equiv_match_metadata_l; eauto];

  try solve [
        rewrite Int.add_assoc in Hvp;
        match goal with
          | [ H : Mem.valid_pointer _ _ (Int.unsigned (Int.add ?Z (Int.add ?X ?Y))) = true |- _ ] => 
            rewrite (Int.add_commut X Y) in H;
              app Mem.valid_pointer_implies H
        end;
        try solve [  name (conj Hpinj Hvp) Hp;
                    erewrite <- weak_valid_pointer_sur in Hp;
                    try collapse_match; try f_equal; try ring;
                    eapply ptr_equiv_match_metadata_l; eauto]].
  
Qed.


  Lemma ptr_equiv_rs_val :
    forall t rs rs',
      ptr_equiv_rs t rs rs' ->
      forall reg v,
        rs reg = v ->
        exists v',
          rs' reg = v' /\ ptr_equiv_val t v v'.
  Proof.
    intros. unfold ptr_equiv_rs in H. specialize (H reg).
    rewrite H0 in H. exists (rs' reg). eauto.
  Qed.

  
  Definition injectable_addrmode (t : allocator_metadata) (a : addrmode) : Prop :=
    match a with
      | Addrmode _ _ (inr (id,ofs)) =>
        match Genv.find_symbol ge id with
          | Some b => pinj t b ofs <> None
          | None => True
        end
      | _ => True
    end.

  
Lemma ptr_equiv_eval_addrmode :
  forall t rs rs',
    ptr_equiv_rs t rs rs' ->
    forall a,
      injectable_addrmode t a ->
      ptr_equiv_val t (eval_addrmode ge a rs) (eval_addrmode_no_ptr ge t a rs').
Proof.
  intros.
  name ptr_equiv_add pea.
  name ptr_equiv_mul pem.
  unfold ptr_equiv_binop in *.
  destruct a; destruct base; destruct ofs; destruct const; try destruct p0;
  simpl; repeat apply pea;
  try destruct p1;
  unfold Genv.symbol_address;
  match goal with
    | [ |- context[Genv.find_symbol ?X ?Y ] ] => destruct (Genv.find_symbol X Y) eqn:?
    | [ |- _ ] => idtac
  end;
    repeat match goal with
             | [ |- context[Int.eq ?X ?Y] ] => destruct (Int.eq X Y) eqn:?
           end;
    repeat apply pem;
    unfold injectable_addrmode in *;
    repeat find_rewrite;
  try solve [apply ptr_equiv_self; assumption];
  try solve [apply ptr_equiv_nonpointers; (intros; discriminate)];
  try solve [
        try apply ptr_equiv_undef_int;
        try apply ptr_equiv_bits;
        try apply ptr_equiv_init_undef;
        try apply psur_add; assumption];
  try solve [
        break_match_sm;
        try congruence;
        match goal with
          | [ H : pinj _ _ = Some _ |- _ ] => app pinj_psur_inverse H
          | [ |- _ ] => idtac
        end;
        try solve [apply ptr_equiv_self; assumption];
        try solve [apply ptr_equiv_nonpointers; (intros; discriminate)];
        try solve [
              try apply ptr_equiv_undef_int;
              try apply ptr_equiv_bits;
              try apply ptr_equiv_init_undef;
              try apply psur_add; assumption] ];
  try solve [break_match_sm; try congruence; apply ptr_equiv_bits;
             try eapply pinj_add; eauto;
             symmetry; rewrite Int.add_commut; symmetry;
             eapply pinj_add; eauto];
  try reflexivity;
  clear pea;
  clear pem;
  unfold Val.add;
  unfold Val.mul;
  break_match_sm;
  
  match goal with
    | [ H : rs _ = _ |- _ ] => app ptr_equiv_rs_val H; repeat break_and
    | [ |- _ ] => idtac
  end;
  match goal with
    | [ H : ptr_equiv_val _ _ _ |- _ ] => unfold ptr_equiv_val in H
    | [ |- _ ] => idtac
  end;
  try break_match_hyp;
  repeat break_or;
  repeat break_exists;
  repeat break_and;
  subst;
  repeat collapse_match;
  match goal with
    | [ |- context[pinj ?T ?X ?Y] ] => destruct (pinj T X Y) eqn:?; try congruence
    | [ |- _ ] => idtac
  end;
  
  try solve [apply ptr_equiv_self; assumption];
  try solve [apply ptr_equiv_nonpointers; (intros; discriminate)];
  try solve [
        try apply ptr_equiv_undef_int;
        try apply ptr_equiv_bits;
        try apply ptr_equiv_init_undef;
        try apply psur_add; assumption];
  try congruence;
  apply ptr_equiv_bits;
  repeat eapply pinj_add;
  symmetry; rewrite Int.add_commut; symmetry;
  repeat eapply pinj_add;
  try (symmetry; rewrite Int.add_commut; symmetry;
       repeat eapply pinj_add);
  eauto.
Qed.


Lemma globals_inj_addrmode :
  forall t a rs m,
    globals_alloc t ->
    reachable (State rs m) ->
    match_metadata t m ->
    injectable_addrmode t a.
Proof.
  unfold injectable_addrmode.
  unfold globals_alloc. intros.
  repeat break_match; try solve [exact I].
  subst.


  destruct (pinj t b Int.zero) eqn:?.
  intro.
  eapply pinj_add in Heqo0.
  instantiate (1 := i0) in Heqo0.
  rewrite Int.add_commut in Heqo0.
  erewrite Int.add_zero in Heqo0.
  congruence.
  intro.

  exploit H. unfold is_global_block. eauto.
  intros.
  exploit prog_well_behaved; eauto.
Qed.

Ltac ptr_equiv :=
  try apply ptr_equiv_nextinstr_nf;
  try apply ptr_equiv_nextinstr;
  try apply ptr_equiv_undef_regs;
  try apply ptr_equiv_set_regs;
  try apply ptr_equiv_map_args;
  try apply ptr_equiv_compare_ints;
  try apply ptr_equiv_compare_floats;
  try apply ptr_equiv_compare_floats32;
  repeat apply ptr_equiv_update;
  ptr_equiv_ops;
  try apply ptr_equiv_sext;
  try apply ptr_equiv_zext;
  try apply ptr_equiv_encode_long;
  try apply ptr_equiv_decode_longs;
  ptr_equiv_conversion;
  try apply ptr_equiv_self;
  try eapply ptr_equiv_undef_self;
  try solve [apply ptr_equiv_nonpointers; (intros; discriminate)];
  try apply ptr_equiv_undef_int;
  try apply ptr_equiv_bits;
  try apply ptr_equiv_init_undef;
  try apply ptr_equiv_eval_addrmode;
  try apply ptr_equiv_of_optbool;
  ptr_equiv_ops;
  try eapply globals_inj_addrmode;
  try eapply ptr_equiv_match_metadata_l; 
  eassumption.


Lemma in_range_unsigned_repr :
  forall x y,
    0 <= x < y ->
    0 <= Int.unsigned (Int.repr x) < y.
Proof.
  intros. 
  name (Int.unsigned_range (Int.repr x)) H1.
  split. omega.
  assert (y < Int.modulus \/ y >= Int.modulus) by omega.
  destruct H0. assert (x < Int.modulus) by omega.
  rewrite Int.unsigned_repr. omega.
  unfold Int.max_unsigned.
  omega.
  omega.
Qed.

Lemma ints_can_add :
  forall x y,
  exists z, (Int.add x z) = y.
Proof.
  intros. exists (Int.sub y x). ring.
Qed.

Lemma goto_label_pres :
  forall t rs rs' m m',
    match_states (State rs m) (State_bits rs' m' t) ->
    forall b i,
      rs PC = Vptr b i ->
      forall f,
        Genv.find_funct_ptr ge b = Some (Internal f) ->
        forall l rs'' m'',
          goto_label f l rs m = Next rs'' m'' ->
          exists rs''' m''',
            goto_label_bits t f l b rs' m' = Nxt rs''' m''' t  /\
            ptr_equiv_rs t rs'' rs''' /\ ptr_equiv_mem (Genv.globalenv p) t m'' m'''.
Proof.
  intros.
  P inv match_states.
  unfold goto_label in *. unfold goto_label_bits.
  break_match_hyp; try congruence.
  break_match_hyp; try congruence.
  app ptr_equiv_PC Heqv. break_and.
  match goal with
    | [ H : Vptr _ _ = Vptr _ _ |- _ ] => inv H
  end.

  match goal with
    | [ H : Next _ _ = Next _ _ |- _ ] => inv H
  end.
  break_match.

  eexists. eexists. split; try reflexivity.
  split; ptr_equiv.

  exfalso.
  generalize Heqo0.
  cut (pinj t b (Int.repr z) <> None). auto.
  clear Heqo0.
  
  app label_pos_find_instr Heqo.
  apex in_range_find_instr Heqo.

  use pinj_add; try eapply H4.
  use (ints_can_add i (Int.repr z)).
  break_exists. rewrite <- H7.
  intro. rewrite H5 in H13. congruence.
Qed.

Lemma valid_access_any_chunk :
  forall m c b ofs p,
    Mem.valid_access m c b ofs p ->
    Mem.valid_access m Mint8unsigned b ofs p.
Proof.
  intros.
  unfold Mem.valid_access in *.

  break_and.


  destruct c; simpl in *; eauto;
  split;

  try solve [unfold Mem.range_perm in *;
              intros; apply H; omega];

  eapply Z.divide_1_l.
  
Qed.

Lemma load_valid_pointer :
  forall c m b ofs v,
    Mem.load c m b ofs = Some v ->
    Mem.valid_pointer m b ofs = true.
Proof.
  intros.
  app Mem.load_valid_access H.
  eapply Mem.valid_pointer_valid_access.
  eapply Mem.valid_access_implies;
    try instantiate (1 := Readable);
    try solve [econstructor].
  eapply valid_access_any_chunk; eauto.
Qed.
  
Lemma exec_load_pres :
  forall rs rs' m m' t,
    match_states (State rs m) (State_bits rs' m' t) ->
    forall c a r rs'' m'',
      exec_load ge c m a rs r = Next rs'' m'' ->
      exists rs''' m''',
        exec_load_bits ge t c m' a rs' r = Nxt rs''' m''' t /\
        ptr_equiv_rs t rs'' rs''' /\
        ptr_equiv_mem (Genv.globalenv p) t m'' m'''.
Proof.
  intros. inversion H. unfold exec_load_bits in *.
  unfold exec_load in *.
  unfold Mem.loadv in *.
  destruct (eval_addrmode ge a rs) eqn:?; P inv Next.
  break_match_hyp; P inv Next.
  NP _app load_valid_pointer Mem.load.
  
  NP _eapplyin eval_addrmode_pres eval_addrmode; eauto.


  unfold ge in *. unfold ge.
  collapse_match.
  NP _app ptr_equiv_mem_load Mem.load.
  break_and.
  collapse_match.
  eexists. eexists. split. reflexivity.
  econstructor; eauto; subst; try ptr_equiv.
Qed.


Lemma store_valid_pointer :
  forall c m b ofs d m',
    Mem.store c m b ofs d = Some m' ->
    Mem.valid_pointer m b ofs = true.
Proof.
  intros.
  app Mem.store_valid_access_3 H.
  eapply Mem.valid_pointer_valid_access.
  eapply Mem.valid_access_implies;
    try instantiate (1 := Writable);
    try solve [econstructor].
  eapply valid_access_any_chunk; eauto.
Qed.

Lemma exec_store_pres :
  forall rs rs' m m' t,
    match_states (State rs m) (State_bits rs' m' t) ->
    forall c a r rs'' m'' d,
      exec_store ge c m a rs r d = Next rs'' m'' ->
      exists rs''' m''',
        exec_store_bits ge t c m' a rs' r d = Nxt rs''' m''' t /\
        ptr_equiv_rs t rs'' rs''' /\
        ptr_equiv_mem (Genv.globalenv p) t m'' m'''.
Proof.
  intros. name H Hmatch.
  inversion H. unfold exec_store_bits in *.
  unfold exec_store in *.
  unfold Mem.storev in *.
  destruct (eval_addrmode ge a rs) eqn:?; P inv Next.
  break_match_hyp; P inv Next.
  NP _app store_valid_pointer Mem.store.
  NP _eapplyin eval_addrmode_pres eval_addrmode; eauto.
  unfold ge in *. unfold ge.
  P _rewrite eval_addrmode_bits.
  NP _app ptr_equiv_mem_store Mem.store. break_and.
  eexists. eexists.
  unfold storev_bits. collapse_match.
  split. reflexivity.
  econstructor; eauto.
  ptr_equiv.
Qed.



Lemma eval_annot_arg_pres :
  forall t rs rs' m m' sp sp',
    ptr_equiv_rs t rs rs' ->
    ptr_equiv_mem (Genv.globalenv p) t m m' ->
    ptr_equiv_val t sp sp' ->
    forall aa v,
      injectable_annot_arg t aa ->
      eval_annot_arg ge rs sp m aa v ->
      exists v',
        eval_annot_arg_bits t ge rs' sp' m' aa v' /\ ptr_equiv_val t v v'.
Proof.
  intros.
  induction H3;
  try solve [eexists; split; [ econstructor; eauto | ptr_equiv]].
  * unfold Mem.loadv in H3. unfold Val.add in H3.
    destruct sp; simpl in H3; inversion H3.
    simpl in H1. break_exists. break_and.
    app ptr_equiv_mem_load H3. break_and.
    eexists; split; try econstructor; eauto.
    instantiate (2 := b). instantiate (1 := i).
    erewrite weak_valid_pointer_sur.
    split. eapply pinj_add; eauto.
    app load_valid_pointer H5.
    eapply Mem.valid_pointer_implies; eauto.
    eapply ptr_equiv_match_metadata_l; eauto.
    simpl. eauto.
  * unfold Mem.loadv in *.
    break_match_hyp; try congruence.
    app ptr_equiv_mem_load H3.
    break_and.
    eexists; split; try econstructor.
    unfold Mem.loadv. collapse_match. eauto. assumption.
  * remember (Senv.symbol_address ge id ofs) as se.
    unfold Senv.symbol_address in Heqse.
    break_match_hyp; subst.

    
    unfold injectable_annot_arg in H2. unfold Senv.find_symbol in Heqo.
    unfold Genv.to_senv in Heqo. rewrite Heqo in H2.
    destruct (pinj t b ofs) eqn:?; try congruence.
    eexists; split. econstructor; eauto.
    unfold Senv.symbol_address. unfold Senv.find_symbol.
    unfold ge. simpl. unfold ge in Heqo. rewrite Heqo. reflexivity.
    ptr_equiv. 
    
    exists Vundef. split; try ptr_equiv.
    eapply eval_AA_addrglobal_undef.
    unfold Senv.symbol_address.
    collapse_match. reflexivity.
    
  * repeat break_exists; repeat break_and.
    simpl in H2. break_and.
    app IHeval_annot_arg1 H2.
    app IHeval_annot_arg2 H3.
    repeat break_and.
    eexists; split. econstructor; eauto.
    ptr_equiv.
Qed.

Lemma eval_annot_args_pres :
  forall t rs rs' m m' sp sp',
    ptr_equiv_rs t rs rs' ->
    ptr_equiv_mem (Genv.globalenv p) t m m' ->
    ptr_equiv_val t sp sp' ->
    forall args vargs,
      (forall x, In x args -> injectable_annot_arg t x) ->
      eval_annot_args ge rs sp m args vargs ->
      exists vargs',
        (eval_annot_args_bits t ge rs' sp' m' args vargs' /\
         ptr_equiv_list t vargs vargs').
Proof.
  intros. unfold eval_annot_args in H3.
  induction H3.
  * eexists.
    split; econstructor; eauto.
  * destruct IHlist_forall2. intros.
    apply H2. simpl.  right. assumption.
    app eval_annot_arg_pres H3; try apply H2; simpl;
    try left; try reflexivity;
    repeat break_and.
    eexists; split; econstructor; eauto.

Qed.

Lemma extcall_arg_pres :
  forall t rs rs' m m',
    ptr_equiv_rs t rs rs' ->
    ptr_equiv_mem (Genv.globalenv p) t m m' ->
    forall a b,
      extcall_arg rs m a b ->
      exists b',
        extcall_arg_bits t rs' m' a b' /\ ptr_equiv_val t b b'.
Proof.
  intros. inv H1.
  * eexists; split.
    econstructor; eauto.
    ptr_equiv.
  * unfold Mem.loadv in H3.
    break_match_hyp; try congruence.
    app ptr_equiv_mem_load H3. break_and.
    unfold Val.add in Heqv.
    break_match_hyp; try solve [inv Heqv].
    unfold ptr_equiv_rs in H.
    specialize (H ESP). unfold ptr_equiv_val in H.
    rewrite Heqv0 in H.
    break_exists; break_and.
    
    eexists; split; try econstructor; try reflexivity; eauto.

    rewrite H. reflexivity.

    erewrite weak_valid_pointer_sur;
      try solve [eapply ptr_equiv_match_metadata_l; eauto].
    split. inv Heqv.
    eapply pinj_add; eauto.

    app load_valid_pointer H1.
    eapply Mem.valid_pointer_implies; eauto.
Qed.  

Lemma extcall_arguments_pres :
  forall t rs m sg args,
    extcall_arguments rs m sg args ->
    forall rs' m',
      ptr_equiv_rs t rs rs' ->
      ptr_equiv_mem (Genv.globalenv p) t m m' ->
      exists args',
        extcall_arguments_bits t rs' m' sg args' /\
        ptr_equiv_list t args args'.
Proof.
  intros. unfold extcall_arguments in *.
  unfold extcall_arguments_bits.
  induction H.
  * eexists. split; try econstructor; eauto.
  * break_exists; break_and.
    app extcall_arg_pres H. break_and.
    eexists; split; econstructor; eauto.
Qed.

(* We guarantee our simulation only when *)
(* a valid pointer into the current memory implies pinj works *)
(* for current memory reached from start state *)

(* TODO: maybe build sample pinj-psur functions that satisfy these axioms *)


(* We need an axiom for external calls *)
(* We provide slightly different arguments to external calls *)
(* Thus we need the fact that external calls play nicely with our conversion *)
(* Thus this needs to be an axiom *)
Axiom ext_call_pres :
  forall md rs rs' m m',
    ptr_equiv_rs md rs rs' ->
    ptr_equiv_mem (Genv.globalenv p) md m m' ->
    forall ef vargs t v m'0,
      external_call ef ge vargs m t v m'0 ->
      forall vargs',
        ptr_equiv_list md vargs vargs' ->
        exists m'' v',
          (external_call ef ge vargs' m' t v' m'' /\
           ptr_equiv_val (md_ec md ef ge vargs' m' t v' m'') v v' /\
           ptr_equiv_mem (Genv.globalenv p) (md_ec md ef ge vargs' m' t v' m'') m'0 m'').

Axiom ext_call'_pres :
  forall md rs rs' m m',
    ptr_equiv_rs md rs rs' ->
    ptr_equiv_mem (Genv.globalenv p) md m m' ->
    forall ef vargs t v m'0,
      external_call' ef ge vargs m t v m'0 ->
      forall vargs',
        ptr_equiv_list md vargs vargs' ->
        exists m'' v',
          (external_call' ef ge vargs' m' t v' m'' /\
           ptr_equiv_list (md_ec' md ef ge vargs' m' t v' m'') v v' /\
           ptr_equiv_mem (Genv.globalenv p) (md_ec' md ef ge vargs' m' t v' m'') m'0 m'').
(* Proof. *)
(*   intros. inversion H1. *)
(*   name H3 Hec; eapply ext_call_pres in Hec; *)
(*   try apply ptr_equiv_decode_longs; *)
(*   try apply H2. *)
(*   repeat break_exists. repeat break_and. *)
(*   do 2 eexists; split; *)
(*   try eapply external_call'_intro. *)
(*   eapply H5. reflexivity. split. *)
(*   subst. ptr_equiv. eauto. *)
(*   eassumption. assumption. *)
(* Qed. *)

(* Lemma global_size_nonzero : *)
(*   forall id b, *)
(*     Genv.find_symbol (Genv.globalenv p) id = Some b -> *)
(*     global_size id p > 0. *)
(* Proof. *)
(*   intros. app Genv.find_symbol_inversion H. *)
(*   unfold global_size. *)
(*   unfold prog_defs_names in H. *)
(*   app list_in_map_inv H. *)
(*   break_and. destruct x. *)
(*   subst. *)
(*   erewrite lookup_norepet; eauto. *)
(*   unfold globals_nonempty in nonempty. *)
(*   app nonempty H2. *)
(*   unfold global_nonempty in *. *)
(*   destruct g; try destruct f; omega. *)
(* Qed. *)

Lemma find_sym_pinj_exists :
  forall rs m t id b,
    reachable (State rs m) ->
    match_metadata t m ->
    globals_alloc t ->
    Genv.find_symbol (Genv.globalenv p) id = Some b ->
    exists bits,
      pinj t b Int.zero = Some bits.
Proof.
  intros.
  destruct (pinj t b Int.zero) eqn:?; eauto.
  unfold globals_alloc in *.
  exploit prog_well_behaved; try eapply H1; eauto.
  unfold is_global_block. eauto.
  intros. inv_false.
Qed.

Lemma reachable_step :
  forall s,
    reachable s ->
    forall t s',
      step ge s t s' ->
      reachable s'.
Proof.
  intros. unfold reachable in H.
  repeat break_exists.
  repeat break_and.
  unfold reachable.
  exists x. eexists.
  split. auto.
  eapply star_right. eassumption.
  eassumption. reflexivity.
Qed.

Lemma reachable_step_bits :
  forall s,
    reachable_bits s ->
    forall t s',
      step_bits ge s t s' ->
      reachable_bits s'.
Proof.
  intros. unfold reachable_bits in H.
  repeat break_exists.
  repeat break_and.
  unfold reachable.
  exists x. eexists.
  split. auto.
  eapply star_right. eassumption.
  eassumption. reflexivity.
Qed.

Lemma no_pointer_no_ptr :
  forall m,
    (forall b ofs, no_pointer (Mem.mem_contents m) !! b ofs) ->
    no_ptr_mem m.
Proof.
  intros. unfold no_pointer in *.
  unfold no_ptr_mem.
  intros.
  apply H.
Qed.

Lemma ptr_equiv_no_ptr_mem :
  forall t m m',
    ptr_equiv_mem (Genv.globalenv p) t m m' ->
    no_ptr_mem m'.
Proof.
  intros. unfold ptr_equiv_mem in *.
  repeat break_and.
  unfold mem_contents_equiv in H1.
  unfold contents_equiv in *.
  eapply no_pointer_no_ptr.
  intros. repeat break_and.
  specialize (H5 b ofs).
  break_and; eauto.
Qed.

Lemma psur_valid_code :
  forall t b ofs bits f i,
    pinj t b ofs = Some bits ->
    Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal f) ->
    find_instr (Int.unsigned ofs) (fn_code f) = Some i ->
    forall m m',
      ptr_equiv_mem (Genv.globalenv p) t m m' ->
      psur t bits = Some (b,ofs).
Proof.
  intros.
  name H2 Hptr_equiv.
  unfold ptr_equiv_mem in H2.
  repeat break_and.
  app global_perms_valid_globals H6.
  unfold valid_globals in *.
  exploit (H6 b ofs); intros.
  unfold is_global. left.
  unfold in_code_range.
  collapse_match.
  apex in_range_find_instr H1. omega.

  eapply valid_pointer_sur; eauto.
  eapply ptr_equiv_match_metadata_r; eauto.
Qed.


Lemma store_valid_commute :
  forall m m' c b ofs v,
    Mem.store c m b ofs v = Some m' ->
    forall b ofs,
      Mem.valid_pointer m b ofs = Mem.valid_pointer m' b ofs.
Proof.
  intros. app Mem.store_access H.
  unfold Mem.valid_pointer.
  unfold Mem.perm_dec.
  unfold proj_sumbool.
  repeat break_match; try congruence;
  clear Heqs; clear Heqs0;
  rewrite H in *;
  congruence.
Qed.



Lemma ptr_equiv_rs_alloc :
  forall t rs rs',
    ptr_equiv_rs t rs rs' ->
    forall lo hi b,
      ptr_equiv_rs (md_alloc t lo hi b) rs rs'.
Proof.
  intros. unfold ptr_equiv_rs in *.
  intros. eapply ptr_equiv_md_alloc; eauto.
Qed.

Lemma globals_inj_alloc :
  forall t,
    globals_alloc t ->
    forall lo hi b,
      globals_alloc (md_alloc t lo hi b).
Proof.
  intros. unfold globals_alloc in *.
  intros. app H H0.
  econstructor; eauto.
Qed.



Lemma ptr_equiv_rs_free :
  forall t rs rs',
    ptr_equiv_rs t rs rs' ->
    forall lo hi b,
      ptr_equiv_rs (md_free t lo hi b) rs rs'.
Proof.
  intros. unfold ptr_equiv_rs in *.
  intros. eapply ptr_equiv_md_free; eauto.
Qed.


Lemma globals_inj_free :
  forall t,
    globals_alloc t ->
    forall lo hi b,
      globals_alloc (md_free t lo hi b).
Proof.
  intros. unfold globals_alloc in *.
  intros. app H H0.
  econstructor; eauto.
Qed.


Lemma ptr_equiv_md_ec' :
  forall rs rs' md,
    ptr_equiv_rs md rs rs' ->
    forall ef ge args m t m' res,
      ptr_equiv_rs (md_ec' md ef ge args m t m' res) rs rs'.
Proof.
  intros.
  unfold ptr_equiv_rs in *.
  intros. specialize (H r).
  unfold ptr_equiv_val in *.
  break_match_hyp; try assumption.
  repeat break_exists. break_and.
  eexists; split; try eassumption.
  eapply pinj_ec'; eauto.
Qed.

Lemma globals_inj_ec :
  forall md,
    globals_alloc md ->
    forall ef ge args m t m' res,
      globals_alloc (md_ec md ef ge args m t m' res).
Proof.
  intros. unfold globals_alloc in *.
  intros. app H H0.
  econstructor; eauto.
Qed.

Lemma ptr_equiv_md_ec :
  forall rs rs' md,
    ptr_equiv_rs md rs rs' ->
    forall ef ge args m t m' res,
      ptr_equiv_rs (md_ec md ef ge args m t m' res) rs rs'.
Proof.
  intros.
  unfold ptr_equiv_rs in *.
  intros. specialize (H r).
  unfold ptr_equiv_val in *.
  break_match_hyp; try assumption.
  repeat break_exists. break_and.
  eexists; split; try eassumption.
  eapply pinj_ec; eauto.
Qed.

Lemma globals_inj_ec' :
  forall md,
    globals_alloc md ->
    forall ef ge args m t m' res,
      globals_alloc (md_ec' md ef ge args m t m' res).
Proof.
  intros. unfold globals_alloc in *.
  intros. app H H0.
  econstructor; eauto.
Qed.

Lemma as_bits_fsim_step :
  forall (s1 : state) (t : trace) (s1' : state),
    step ge s1 t s1' ->
    forall s2 : state_bits,
      match_states s1 s2 ->
      exists s2', step_bits ge s2 t s2' /\ match_states s1' s2'.
Proof.
  intros. inversion H0.
  inversion H. subst.
  inv H12.

  * assert (Hiop : instr_of_prog i p). {
      unfold instr_of_prog. eexists. eexists. split; try eauto.
      unfold code_of_prog.
      app Genv.find_funct_ptr_inversion H9.
      exists x. exists (fn_sig f). destruct f. simpl. apply H7.
    }

                                       
    destruct i eqn:Hinstr;
      try solve [P _simpl exec_instr; P inv exec_instr];
      P _simpl exec_instr;

      match goal with
        | [ H : exec_load _ _ _ _ _ _ = _ |- _ ] => app exec_load_pres H
        | [ H : exec_store _ _ _ _ _ _ _ = _ |- _ ] => app exec_store_pres H
        | [ H : goto_label _ _ _ _ = _ |- _ ] => app goto_label_pres H
        | [ |- _ ] => idtac
      end;
    name (H1 PC) HPC;
    rewrite H8 in HPC;
    unfold ptr_equiv_val in HPC;
    repeat break_exists; repeat break_and;
    try unfold Genv.symbol_address in *;
    try destruct (Genv.find_symbol ge id) eqn:Hfindsym;
    try unfold Genv.symbol_address in *;
    try rewrite Hfindsym;
    repeat break_match_hyp;
    try congruence;
    match goal with
      | [ H : Val.divu _ _ = Some _ |- _ ] => app ptr_equiv_divu_pres H
      | [ H : Val.divs _ _ = Some _ |- _ ] => app ptr_equiv_divs_pres H
      | [ |- _ ] => idtac
    end;
    match goal with
      | [ H : Val.modu _ _ = Some _ |- _ ] => app ptr_equiv_modu_pres H
      | [ H : Val.mods _ _ = Some _ |- _ ] => app ptr_equiv_mods_pres H
      | [ |- _ ] => idtac
    end;
    repeat break_and;
    repeat match goal with
             | [ H : State _ _ = State _ _ |- _ ] => inv H
             | [ H : Next _ _ = Next _ _ |- _ ] => inv H
    end;
    match goal with
      | [ |- ptr_equiv_val _ _ ] => try ptr_equiv
      | [ |- _ ] => idtac
    end;
    (*try app all_addrmode_injectable Hiop; *)

    try solve [

    (* Normal cases *)
          unfold Genv.symbol_address in *;
          match goal with
            | [ H : Genv.find_symbol _ _ = Some _ |- _ ] => app find_sym_pinj_exists H
            | [ |- _ ] => idtac
          end;
          try (eexists; isplit; econstructor);
          simpl;
          match goal with
            | [ |- find_instr _ _ = _ ] => eassumption
            | [ |- _ ] => idtac
          end;
          match goal with
            | [ |- exec_instr_bits _ _ _ _ _ _ _ = _ ] => reflexivity
            | [ |- _ ] => idtac
          end;
          match goal with
            | [ |- exec_instr_bits _ _ _ _ _ _ _ = _ ] => simpl; unfold Genv.symbol_address; repeat collapse_match; reflexivity
            | [ |- _ ] => idtac
          end;
          eauto;
          match goal with
            | [ H : pinj _ _ = Some _ |- _ ] => app pinj_psur_inverse H
            | [ |- _ ] => idtac
          end;
          match goal with
            | [ H : reachable _ |- _ ] => app reachable_ptr_valid H
            | [ |- _ ] => idtac
          end;
          match goal with
            | [ |- ptr_equiv_val _ _ _ ] => ptr_equiv
            | [ |- ptr_equiv_rs _ _ _ ] => ptr_equiv
            | [ |- _ ] => idtac
          end;
          match goal with
            | [ |- no_ptr_regs _ ] => eapply ptr_equiv_no_ptr; eassumption
            | [ |- reachable _ ] => eapply reachable_step; eauto
            | [ |- reachable_bits _ ] => eapply reachable_step_bits; eauto
            | [ |- _ ] => idtac
          end;
          instantiate;
          try eapply ptr_equiv_no_ptr_mem; eauto;
          try solve [eapply ptr_equiv_match_metadata_r; eauto];
          try solve [eapply ptr_equiv_match_metadata_l; eauto];
          try solve [eapply ptr_equiv_global_perms_r; eauto];
          try solve [eapply psur_valid_code; eauto];
          instantiate

        | 

          (* cmov *)
          match goal with
            | [ H : eval_testcond _ _ = _ |- _ ] => app ptr_equiv_eval_testcond H
            | [ |- _ ] => idtac
          end;
          eexists; isplit; econstructor;
          match goal with
            | [ |- find_instr _ _ = _ ] => eassumption
            | [ |- _ ] => idtac
          end;
          simpl;
          repeat match goal with
                   | [ H : eval_testcond _ _ = _ |- _ ] => try rewrite H; clear H
                 end;
          match goal with
            | [ H : Next _ _ = Next _ _ |- _ ] => inv H
            | [ |- _ ] => idtac
          end;
          try reflexivity;
          eauto;
          match goal with
            | [ |- ptr_equiv_val _ _ _ ] => ptr_equiv
            | [ |- ptr_equiv_rs _ _ _ ] => ptr_equiv
            | [ |- _ ] => idtac
          end;
          match goal with
            | [ |- no_ptr_regs _ ] => eapply ptr_equiv_no_ptr; eassumption
            | [ |- reachable _ ] => eapply reachable_step; eauto
            | [ |- reachable_bits _ ] => eapply reachable_step_bits; eauto
            | [ |- _ ] => idtac
          end;
          try eapply ptr_equiv_no_ptr_mem; eauto;
          try solve [eapply ptr_equiv_match_metadata_r; eauto];
          try solve [eapply ptr_equiv_match_metadata_l; eauto];
          try solve [eapply ptr_equiv_global_perms_r; eauto];
          try solve [eapply psur_valid_code; eauto]

        |
    
          (* Conditional Jumps *)
          match goal with
            | [ H : _ = Some (Pjcc ?X _), H2 : eval_testcond ?X _ = _ |- _ ] => app ptr_equiv_eval_testcond H2
            | [ H : _ = Some (Pjcc2 ?X ?Y _), H2 : eval_testcond ?X _ = _, H3 : eval_testcond ?Y _ = _ |- _ ] => app ptr_equiv_eval_testcond H2; app ptr_equiv_eval_testcond H3
          end;
          match goal with
            | [ H : goto_label _ _ _ _ = _ |- _ ] => app goto_label_pres H
            | [ |- _ ] => idtac
          end;
          repeat break_and;
          eexists; isplit; econstructor;
          simpl;
          match goal with
            | [ |- find_instr _ _ = _ ] => eassumption
            | [ |- _ ] => idtac
          end;
          match goal with
            | [ H : Next _ _ = Next _ _ |- _ ] => inv H
            | [ |- _ ] => idtac
          end;
          try reflexivity;
          try ptr_equiv;
          try solve [eapply ptr_equiv_no_ptr; eassumption];
          try solve [eapply reachable_step; eauto];
          try solve [eapply reachable_step_bits; eauto];
          simpl;
          repeat match goal with
                   | [ H : eval_testcond _ rs' = _ |- _ ] => rewrite H
                 end;
          try reflexivity;
          eauto;
          try eapply ptr_equiv_no_ptr_mem; eauto;
          try solve [eapply ptr_equiv_match_metadata_r; eauto];
          try solve [eapply ptr_equiv_match_metadata_l; eauto];
          try solve [eapply ptr_equiv_global_perms_r; eauto];
          try solve [eapply psur_valid_code; eauto]
          
          |

          (* jump table *)
          match goal with
            | [ H : goto_label _ _ _ _ = Next _ _ |- _ ] => app goto_label_pres H
          end; repeat break_and;
          eexists; isplit; econstructor;
          match goal with
            | [ |- find_instr _ _ = _ ] => eassumption
            | [ |- _ ] => idtac
          end;
          match goal with
            | [ H : Next _ _ = Next _ _ |- _ ] => inv H
            | [ |- _ ] => idtac
          end;
          simpl;
          match goal with
            | [ H : rs _ = _ |- _ ] => app ptr_equiv_val_exists H
            | [ |- _ ] => idtac
          end;
          repeat break_and;
          simpl in *;
          repeat collapse_match;
          eauto;
          match goal with
            | [ |- no_ptr_regs _ ] => eapply ptr_equiv_no_ptr; eassumption
            | [ |- reachable _ ] => eapply reachable_step; eauto
            | [ |- reachable_bits _ ] => eapply reachable_step_bits; eauto
            | [ |- _ ] => idtac
          end;
          try eapply ptr_equiv_no_ptr_mem; eauto;
          try solve [eapply ptr_equiv_match_metadata_r; eauto];
          try solve [eapply ptr_equiv_match_metadata_l; eauto];
          try solve [eapply ptr_equiv_global_perms_r; eauto];
          try solve [eapply psur_valid_code; eauto]
          
        ].

    
    (*mov_mi*)
    unfold Mem.storev in Heqo.
    break_match_hyp; try congruence.
    app eval_addrmode_pres Heqv.
    app ptr_equiv_mem_store Heqo.
    eexists. isplit.
    econstructor; eauto.
    eapply psur_valid_code; eauto.
    eapply ptr_equiv_no_ptr; eassumption.
    eapply ptr_equiv_no_ptr_mem; eauto.
    simpl.
    unfold storev_bits.
    break_and. collapse_match.
    rewrite H13. reflexivity.
    eapply ptr_equiv_match_metadata_r; eauto.
    repeat break_and.
    eapply ptr_equiv_global_perms_r; eauto.
    econstructor; eauto.
    ptr_equiv.
    break_and. assumption.
    eapply reachable_step; eauto.
    eapply reachable_step_bits; eauto.
    ptr_equiv.
    app store_valid_pointer Heqo.

    (* Pmovups_rm *)
    unfold exec_big_load in *.
    repeat break_let;
      repeat break_match_hyp; try congruence;
      state_inv.
    unfold Mem.loadv in *. repeat break_match_hyp; try congruence.
    app ptr_equiv_mem_load Heqo.
    app ptr_equiv_mem_load Heqo0.
    repeat break_and.
    app eval_addrmode_pres Heqv0.
    app eval_addrmode_pres Heqv1.
    eexists; isplit; econstructor.
    Focus 6. eauto.
    Focus 6.
    simpl. unfold exec_big_load_bits.
    collapse_match. find_rewrite. find_rewrite.
    simpl. repeat collapse_match.
    reflexivity.
    eauto. eauto.
    eapply psur_valid_code; eauto.
    eapply ptr_equiv_no_ptr; eauto.
    eapply ptr_equiv_no_ptr_mem; eauto.
    eauto.
    eapply ptr_equiv_match_metadata_r; eauto.
    eapply ptr_equiv_global_perms_r; eauto.
    ptr_equiv. eauto.
    eauto.
    eapply reachable_step; eauto.
    eapply reachable_step_bits; eauto.
    eapply load_valid_pointer; eauto.
    eapply load_valid_pointer; eauto.   

    (* Pmovups_mr *)
    unfold exec_big_store in *.
    repeat break_match; try congruence; state_inv.
    unfold Mem.storev in *.
    repeat break_match; try congruence.
    app eval_addrmode_pres Heqv0.
    app eval_addrmode_pres Heqv.
    app ptr_equiv_mem_store Heqo. break_and.
    app ptr_equiv_mem_store Heqo0. break_and.
    eexists; isplit; econstructor; try eapply H10;
    simpl; unfold exec_big_store_bits; try collapse_match;
    try find_rewrite; try find_rewrite; simpl;
    repeat collapse_match; try reflexivity; eauto.
    eapply psur_valid_code; eauto.
    eapply ptr_equiv_no_ptr; eauto.
    eapply ptr_equiv_no_ptr_mem; eauto.
    eapply ptr_equiv_match_metadata_r; eauto.
    eapply ptr_equiv_global_perms_r; eauto.
    ptr_equiv.
    eapply reachable_step; eauto.
    eapply reachable_step_bits; eauto.


    app store_valid_commute Heqo.
    rewrite Heqo.
    
    eapply store_valid_pointer; eauto.
    eapply store_valid_pointer; eauto.


    (* div *)
    unfold Genv.symbol_address in *;
      match goal with
        | [ H : Genv.find_symbol _ _ = Some _ |- _ ] => app find_sym_pinj_exists H
        | [ |- _ ] => idtac
      end;
      try (eexists; isplit; econstructor);
      simpl;
      match goal with
        | [ |- find_instr _ _ = _ ] => eassumption
        | [ |- _ ] => idtac
      end;
      match goal with
        | [ |- exec_instr_bits _ _ _ _ _ _ _ = _ ] => reflexivity
        | [ |- _ ] => idtac
      end;
      match goal with
        | [ |- exec_instr_bits _ _ _ _ _ _ _ = _ ] => simpl; unfold Genv.symbol_address; repeat collapse_match; reflexivity
        | [ |- _ ] => idtac
      end;
      eauto;
      match goal with
        | [ H : pinj _ _ = Some _ |- _ ] => app pinj_psur_inverse H
        | [ |- _ ] => idtac
      end;
      match goal with
        | [ H : reachable _ |- _ ] => app reachable_ptr_valid H
        | [ |- _ ] => idtac
      end;
      match goal with
        | [ |- ptr_equiv_val _ _ _ ] => ptr_equiv
        | [ |- ptr_equiv_rs _ _ _ ] => ptr_equiv
        | [ |- _ ] => idtac
      end;
      match goal with
        | [ |- no_ptr_regs _ ] => eapply ptr_equiv_no_ptr; eassumption
        | [ |- reachable _ ] => eapply reachable_step; eauto
        | [ |- reachable_bits _ ] => eapply reachable_step_bits; eauto
        | [ |- _ ] => idtac
      end;
      try eapply ptr_equiv_no_ptr_mem; eauto;
      try solve [eapply ptr_equiv_match_metadata_r; eauto];
      try solve [eapply ptr_equiv_match_metadata_l; eauto];
      try solve [eapply ptr_equiv_global_perms_r; eauto];
      try solve [eapply psur_valid_code; eauto];
      instantiate.

    (* idiv *)
    unfold Genv.symbol_address in *;
      match goal with
        | [ H : Genv.find_symbol _ _ = Some _ |- _ ] => app find_sym_pinj_exists H
        | [ |- _ ] => idtac
      end;
      try (eexists; isplit; econstructor);
      simpl;
      match goal with
        | [ |- find_instr _ _ = _ ] => eassumption
        | [ |- _ ] => idtac
      end;
      match goal with
        | [ |- exec_instr_bits _ _ _ _ _ _ _ = _ ] => reflexivity
        | [ |- _ ] => idtac
      end;
      match goal with
        | [ |- exec_instr_bits _ _ _ _ _ _ _ = _ ] => simpl; unfold Genv.symbol_address; repeat collapse_match; reflexivity
        | [ |- _ ] => idtac
      end;
      eauto;
      match goal with
        | [ H : pinj _ _ = Some _ |- _ ] => app pinj_psur_inverse H
        | [ |- _ ] => idtac
      end;
      match goal with
        | [ H : reachable _ |- _ ] => app reachable_ptr_valid H
        | [ |- _ ] => idtac
      end;
      match goal with
        | [ |- ptr_equiv_val _ _ _ ] => ptr_equiv
        | [ |- ptr_equiv_rs _ _ _ ] => ptr_equiv
        | [ |- _ ] => idtac
      end;
      match goal with
        | [ |- no_ptr_regs _ ] => eapply ptr_equiv_no_ptr; eassumption
        | [ |- reachable _ ] => eapply reachable_step; eauto
        | [ |- reachable_bits _ ] => eapply reachable_step_bits; eauto
        | [ |- _ ] => idtac
      end;
      try eapply ptr_equiv_no_ptr_mem; eauto;
      try solve [eapply ptr_equiv_match_metadata_r; eauto];
      try solve [eapply ptr_equiv_match_metadata_l; eauto];
      try solve [eapply ptr_equiv_global_perms_r; eauto];
      try solve [eapply psur_valid_code; eauto].

    
    (* cmov (left eval to None) *)
    destruct (eval_testcond c rs') eqn:?;
             try destruct b0;

    unfold Genv.symbol_address in *;
      match goal with
        | [ H : Genv.find_symbol _ _ = Some _ |- _ ] => app find_sym_pinj_exists H
        | [ |- _ ] => idtac
      end;
      try (eexists; isplit; econstructor);
      simpl;
      match goal with
        | [ |- find_instr _ _ = _ ] => eassumption
        | [ |- _ ] => idtac
      end;
      match goal with
        | [ |- exec_instr_bits _ _ _ _ _ _ _ = _ ] => reflexivity
        | [ |- _ ] => idtac
      end;
      match goal with
        | [ |- exec_instr_bits _ _ _ _ _ _ _ = _ ] => simpl; unfold Genv.symbol_address; repeat collapse_match; reflexivity
        | [ |- _ ] => idtac
      end;
      eauto;
      match goal with
        | [ H : pinj _ _ = Some _ |- _ ] => app pinj_psur_inverse H
        | [ |- _ ] => idtac
      end;
      match goal with
        | [ H : reachable _ |- _ ] => app reachable_ptr_valid H
        | [ |- _ ] => idtac
      end;
      match goal with
        | [ |- ptr_equiv_val _ _ _ ] => ptr_equiv
        | [ |- ptr_equiv_rs _ _ _ ] => ptr_equiv
        | [ |- _ ] => idtac
      end;
      match goal with
        | [ |- no_ptr_regs _ ] => eapply ptr_equiv_no_ptr; eassumption
        | [ |- reachable _ ] => eapply reachable_step; eauto
        | [ |- reachable_bits _ ] => eapply reachable_step_bits; eauto
        | [ |- _ ] => idtac
      end;
      try eapply ptr_equiv_no_ptr_mem; eauto;
      try solve [eapply ptr_equiv_match_metadata_r; eauto];
      try solve [eapply ptr_equiv_match_metadata_l; eauto];
      try solve [eapply ptr_equiv_global_perms_r; eauto];
      try solve [eapply psur_valid_code; eauto].

    eapply ptr_equiv_nextinstr.
    unfold ptr_equiv_rs.
    intros. preg_case.
    ptr_equiv. ptr_equiv.
    

    (* allocframe *)
    app ptr_equiv_mem_alloc Heqp0. repeat break_and.
    destruct (pinj (md_alloc t0 0 sz b0) b0 Int.zero) eqn:Hpinj_zero.

    app ptr_equiv_mem_store Heqo. repeat break_and.
    app ptr_equiv_mem_store Heqo0. repeat break_and.
    
    eexists; isplit; econstructor;
    try solve [eapply ptr_equiv_no_ptr; eassumption];
    match goal with
      | [ H : Next _ _ = Next _ _ |- _ ] => inv H
      | [ |- _ ] => idtac
    end;
    match goal with
      | [ |- find_instr _ _ = _ ] => eassumption
      | [ |- _ ] => idtac
    end;
    eauto.
    eapply psur_valid_code; eauto.
    eapply ptr_equiv_no_ptr_mem; eauto.
    simpl.
    break_let.
    match goal with
      | [ H : (_,_) = (_,_) |- _ ] => inv H
    end.
    repeat collapse_match.
    rewrite H15. rewrite H18.
    reflexivity.
    eapply ptr_equiv_match_metadata_r; eauto.
    eapply ptr_equiv_global_perms_r; eauto.


    eapply ptr_equiv_update;
      try solve [preg_simpl; find_rewrite; find_rewrite;
                 eapply ptr_equiv_md_alloc; ptr_equiv];
      eapply ptr_equiv_update;
      try eapply ptr_equiv_update;
      try solve [eapply ptr_equiv_rs_alloc; eauto];
    ptr_equiv.

    eapply globals_inj_alloc; eauto.
    eapply reachable_step; eauto.
    eapply reachable_step_bits; eauto.

    eapply ptr_equiv_md_alloc; ptr_equiv.
    eapply ptr_equiv_md_alloc; ptr_equiv.
    

    assert (code_of_prog (fn_code f) p). {
      unfold code_of_prog.
      app Genv.find_funct_ptr_inversion H9.
    exists x1. exists (fn_sig f). destruct f. simpl. auto.
    }       
      
    NP _app palloc code_of_prog.

    unfold all_allocframes_positive_code in *.
    NP1 _app H14 find_instr.

    assert (allocated (md_alloc t0 0 sz b0) b0). {
      econstructor; eauto.
    } 
    eapply prog_well_behaved in H17.
    congruence.
    instantiate (1 := m'0).
    eapply reachable_step; eauto.
    eapply match_store; try solve [eauto].
    eapply match_store; try solve [eauto].
    eapply ptr_equiv_match_metadata_l; eauto.
                                                          
    (* freeframe *)
    unfold Mem.loadv in *. unfold Val.add in *.
    app ptr_equiv_mem_load Heqo. break_and.
    app ptr_equiv_mem_load Heqo0. break_and.
    name (H1 ESP) HESP.
    rewrite Heqv1 in HESP.
    simpl in HESP. break_exists; break_and.
    app ptr_equiv_mem_free Heqo1; break_and.
    eexists; isplit; econstructor;
    try solve [eapply ptr_equiv_no_ptr; eassumption];
    match goal with
      | [ H : Next _ _ = Next _ _ |- _ ] => inv H
      | [ |- _ ] => idtac
    end;
    match goal with
      | [ H : find_instr _ _ = _ |- _ ] => try apply H
    end; eauto. simpl.
    eapply psur_valid_code; eauto.
    eapply ptr_equiv_no_ptr_mem; eauto.
    simpl.
    match goal with
      | [ H : rs' _ = _ |- _ ] => rewrite H
    end.

    app load_valid_pointer H11.
    app load_valid_pointer H14.
    copy H18.
    eapply pinj_add in H24. instantiate (1 := ofs_ra) in H24.
    copy H18.
    eapply pinj_add in H25. instantiate (1 := ofs_link) in H25.
    app Mem.valid_pointer_implies H11.
    app Mem.valid_pointer_implies H14.
    name (conj H24 H11) Hora.
    name (conj H25 H14) Holink.
    erewrite <- weak_valid_pointer_sur in Hora.
    erewrite <- weak_valid_pointer_sur in Holink.
    repeat collapse_match.
    reflexivity.
    eapply ptr_equiv_match_metadata_l; eauto.
    eapply ptr_equiv_match_metadata_l; eauto.
    eapply ptr_equiv_match_metadata_r; eauto.

    eapply ptr_equiv_global_perms_r; eauto.
    
    eapply ptr_equiv_rs_free; ptr_equiv.

    eapply globals_inj_free; eauto.
    
    eapply reachable_step; eauto.
    eapply reachable_step_bits; eauto.
    
  *
    

    subst.
    match goal with
      | [ H : State _ _ = State _ _ |- _ ] => inv H
    end.
    
    match goal with
      | [ H : external_call' _ _ _ _ _ _ _ |- _ ] => app ext_call'_pres H
    end; eauto.
    match goal with
      | [ H : rs PC = _ |- _ ] => app ptr_equiv_PC H
    end.
    repeat break_and.

    Focus 2.
    apply ptr_equiv_map_args.
    apply H1.
    
    
    assert (ptr_equiv_rs (md_ec' t0 ef ge (map rs' args) m' t x0 x) (nextinstr_nf
              (set_regs res vl
                 (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)))
                         (nextinstr_nf (set_regs res x0 (undef_regs (map preg_of (destroyed_by_builtin ef)) rs')))).
    {
      apply ptr_equiv_nextinstr_nf;
      try apply ptr_equiv_set_regs;
      try apply ptr_equiv_undef_regs;
      try ptr_equiv;
      try eapply ptr_equiv_md_ec';
      eauto.
    }

    eexists; isplit; econstructor; eauto.

    erewrite weak_valid_pointer_sur; try eapply ptr_equiv_match_metadata_r; eauto.
    split; try assumption.
    eapply ptr_equiv_valid_globals_r in H2; eauto.
    unfold valid_globals in *.
    eapply Mem.valid_pointer_implies.
    eapply H2.
    unfold is_global.
    left.
    unfold in_code_range.
    unfold ge in *.
    unfold fundef in *.
    collapse_match.
    apex in_range_find_instr H10.
    omega.
    
    eapply ptr_equiv_no_ptr; eauto.
    eapply ptr_equiv_no_ptr_mem; eauto.

    eapply ptr_equiv_match_metadata_r; eauto.
    eapply ptr_equiv_global_perms_r; eauto.

    eapply globals_inj_ec'; eauto.
    
    eapply reachable_step; eauto.
    eapply reachable_step_bits; eauto.
          
  * 
    subst.
    match goal with
      | [ H : State _ _ = State _ _ |- _ ] => inv H
    end.
    match goal with
      | [ H : rs PC = _ |- _ ] => app ptr_equiv_PC H
    end.
    break_and.

    match goal with
      | [ H : eval_annot_args _ _ _ _ _ _ |- _ ] => app eval_annot_args_pres H; repeat break_and
    end.
    match goal with
      | [ H : external_call _ _ _ _ _ _ _ |- _ ] => app ext_call_pres H; repeat break_and
    end.

    eexists; isplit.
    try eapply exec_step_annot_bits;
      try eassumption.

    erewrite weak_valid_pointer_sur; try eapply ptr_equiv_match_metadata_r; eauto.
    split; try assumption.
    eapply ptr_equiv_valid_globals_r in H2; eauto.
    unfold valid_globals in *.
    eapply Mem.valid_pointer_implies.
    eapply H2.
    unfold is_global.
    left.
    unfold in_code_range.
    unfold ge in *.
    unfold fundef in *.
    collapse_match.
    apex in_range_find_instr H10.
    omega.
    
    eapply ptr_equiv_no_ptr; eauto.
    eapply ptr_equiv_no_ptr_mem; eauto.
    eapply ptr_equiv_no_ptr_mem; eauto.

    eapply ptr_equiv_match_metadata_r; eauto.

    eapply ptr_equiv_global_perms_r; eauto.

    econstructor; try ptr_equiv.

    eapply ptr_equiv_md_ec; ptr_equiv.
    
    eapply globals_inj_ec; eauto.
    eapply reachable_step; eauto.
    eapply reachable_step_bits; eauto.
    intros.
    eapply all_annot_arg_injectable; eauto. 
    unfold instr_of_prog. destruct f.
    match goal with
      | [ H : Genv.find_funct_ptr _ _ = _ |- _ ] => app Genv.find_funct_ptr_inversion H
    end.
    repeat eexists; eauto.
    eapply ptr_equiv_match_metadata_l; eauto.

  * 
    subst.
    match goal with
      | [ H : State _ _ = State _ _ |- _ ] => inv H
    end.

    match goal with
      | [ H : extcall_arguments _ _ _ _ |- _ ] => app extcall_arguments_pres H
    end.
    break_and.

    match goal with
      | [ H : external_call' _ _ _ _ _ _ _ |- _ ] => app ext_call'_pres H
    end; eauto; repeat break_and.

    match goal with
      | [ H : rs PC = _ |- _ ] => app ptr_equiv_PC H
    end; eauto; repeat break_and.

    
    
    eexists; isplit;
    try eapply exec_step_external_bits;
    try eapply ptr_equiv_no_ptr;
    eauto.
    6: econstructor; eauto.

    erewrite weak_valid_pointer_sur; try eapply ptr_equiv_match_metadata_r; eauto.
    split; try assumption.
    eapply ptr_equiv_valid_globals_r in H2; eauto.
    unfold valid_globals in *.
    eapply Mem.valid_pointer_implies.
    eapply H2.
    unfold is_global.
    left.
    unfold in_code_range.
    unfold ge in *.
    unfold fundef in *.
    collapse_match.
    rewrite Int.unsigned_zero.
    omega.

    eapply ptr_equiv_update. eapply ptr_equiv_set_regs.
    2: eassumption. eapply ptr_equiv_md_ec'. eassumption.
    assert (ptr_equiv_val t0 (rs RA) (rs' RA)).
    eapply H1.
    unfold ptr_equiv_val. unfold ptr_equiv_val in H17.
    instantiate (1 := rs RA). break_match_hyp; try assumption.
    break_exists. break_and. eexists; split; try eassumption.
                             eapply pinj_ec'; eauto.

    eapply ptr_equiv_no_ptr_mem; eauto.

    eapply ptr_equiv_match_metadata_r; eauto.

    eapply ptr_equiv_global_perms_r; eauto.
    
    eapply ptr_equiv_update; try eapply ptr_equiv_set_regs; try ptr_equiv.
    eapply ptr_equiv_md_ec'; eauto.
    eapply ptr_equiv_md_ec'; eauto.

    eapply globals_inj_ec'; eauto.
    
    eapply reachable_step; eauto.
    eapply reachable_step_bits; eauto.

    Grab Existential Variables.
    exact PC. exact PC.
    exact PC. exact PC.
    exact PC. exact PC.

Qed.

Lemma public_symbols_preserved :
     forall id : ident,
   Senv.public_symbol (symbolenv (semantics_bits p)) id =
   Senv.public_symbol (symbolenv (semantics p)) id.
Proof.
  intros. unfold Senv.public_symbol. simpl.
  reflexivity.
Qed.


Lemma initial_states_match :
  forall s1 : state,
    initial_state p s1 ->
    exists s2,
      initial_state_bits p s2 /\ match_states s1 s2.
Proof.

  intros. inversion H. subst.
  app ptr_equiv_init H0. repeat break_and.

  destruct (Genv.find_symbol (Genv.globalenv p) (prog_main p)) eqn:?.
  
  Focus 2.
  eexists; isplit; econstructor; eauto.
  unfold Genv.symbol_address. rewrite Heqo.
  reflexivity.
  subst rs0. repeat eapply ptr_equiv_update; try ptr_equiv.
  unfold Genv.symbol_address. unfold ge0. rewrite Heqo.
  ptr_equiv. unfold globals_alloc. intros.
  app globals_allocated_init H0.
  unfold reachable. eexists; eexists; isplit.
  eauto. eapply star_refl.
  unfold reachable_bits. eexists. eexists.
  isplit. eauto. eapply star_refl.

  assert (pinj x0 b Int.zero <> None). {

    unfold alloc_inj in *.
    eapply prog_well_behaved; eauto.

    unfold reachable.
    eexists; eexists; split; try eapply star_refl; eauto.
    eapply ptr_equiv_match_metadata_l; eauto.
    unfold is_global_block.
    app globals_allocated_init H0.
    eapply H0.
    unfold is_global_block. eauto.
    
  } idtac.
  
  destruct (pinj x0 b Int.zero) eqn:?; try congruence.

  eexists; isplit; try econstructor; eauto.
  unfold Genv.symbol_address. unfold fundef in *.
  repeat collapse_match.
  instantiate (1 := i). app ptr_equiv_match_metadata_r H2.
  erewrite weak_valid_pointer_sur; eauto. split; auto.
  eapply Mem.valid_pointer_implies.
  app ptr_equiv_global_perms_r H4; eauto.
  eapply global_perms_valid_globals in H4.
  
  eapply H4. app Genv.find_symbol_inversion Heqo.
  unfold prog_defs_names in Heqo.
  app list_in_map_inv Heqo. destruct x1.
  break_and.
  simpl in H8. subst i0.
  app main_fn_is_fn H9.
  destruct g.
  * break_and.
    
    unfold is_global. left. unfold in_code_range.
    inv H9.
    app Genv.find_funct_ptr_exists H8.
    repeat break_and. unfold fundef in *.
    rewrite H8 in H6. inv H6.
    collapse_match.
    rewrite Int.unsigned_zero.
    break_match; split; try omega.
    destruct (fn_code f); try congruence.
    rewrite zlen_cons. name (zlen_nonneg _ c) zlnc.
    omega.
    
  * break_and. congruence.
  * 
  subst rs0.
  repeat eapply ptr_equiv_update; eauto.
  unfold ptr_equiv_rs. intros. rewrite Pregmap.gi. simpl. left. reflexivity.
  unfold Genv.symbol_address. unfold ge0. unfold fundef in *. collapse_match.
  simpl. eauto. simpl. eauto. simpl. eauto.
  * unfold globals_alloc. intros.
    app globals_allocated_init H0.
  * 
  unfold reachable. eexists; eexists; isplit.
  eauto. eapply star_refl.
  * unfold reachable_bits. eexists. eexists.
  isplit. eauto. eapply star_refl.

Qed.  

Lemma final_states_match :
  forall s1 s2 x,
    match_states s1 s2 ->
    final_state s1 x ->
    final_state_bits s2 x.
Proof.
  intros. inversion H0. subst.
  inversion H. subst.
  unfold ptr_equiv_rs in H5.
  unfold ptr_equiv_val in H5.
  econstructor.
  specialize (H5 PC). rewrite H1 in H5. simpl in H5. auto.
  specialize (H5 EAX). rewrite H2 in H5. auto.
Qed.

Lemma as_bits_fsim :
  forward_simulation (semantics p) (semantics_bits p).
Proof.
  intros.
  eapply forward_simulation_step;
    try eapply as_bits_fsim_step;
    try eapply public_symbols_preserved;
    try eapply initial_states_match;
    try eapply final_states_match.
Qed.

End FSIM.

Lemma eval_annot_arg_bits_determ:
  forall (ge : Senv.t) (e : preg -> val)
         (sp : val) (m : mem) (a : annot_arg preg) (v : val) md,
    eval_annot_arg_bits md ge e sp m a v ->
    forall v' : val, eval_annot_arg_bits md ge e sp m a v' -> v' = v.
Proof.
  induction 1; intros v' EV; inv EV; try congruence.
  f_equal; eauto.
  inv H4. rewrite H0 in H5.
  assert (Int.add o ofs = Int.add o0 ofs) by congruence.
  rewrite H in *.
  assert (o = o0). {
    assert (Int.add (Int.add o ofs) (Int.neg ofs) = Int.add (Int.add o ofs) (Int.neg ofs)) by reflexivity.
    rewrite H in H2 at 1. repeat rewrite Int.add_assoc in H2.
    rewrite Int.add_neg_zero in H2.
    repeat rewrite Int.add_zero in H2. congruence.
  } idtac.
  subst o.
  assert (b = b0) by congruence.
  subst b.
  rewrite H1 in H7. congruence.
  f_equal; eauto.
  
Qed.

Lemma eval_annot_args_bits_determ:
  forall (ge : Senv.t) (e : preg -> val)
         (sp : val) (m : mem) (al : list (annot_arg preg))
         (vl : list val) md,
    eval_annot_args_bits md ge e sp m al vl ->
    forall vl' : list val, eval_annot_args_bits md ge e sp m al vl' -> vl' = vl.
Proof.
  induction 1; intros v' EV; inv EV; f_equal; eauto using eval_annot_arg_bits_determ.
Qed.

Remark extcall_arguments_bits_determ:
  forall rs md m sg args1 args2,
    extcall_arguments_bits md rs m sg args1 ->
    extcall_arguments_bits md rs m sg args2 ->
    args1 = args2.
Proof.
  intros until m.
  
  assert (forall ll vl1, list_forall2 (extcall_arg_bits md rs m) ll vl1 ->
          forall vl2, list_forall2 (extcall_arg_bits md rs m) ll vl2 -> vl1 = vl2).
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; auto.
    inv H; inv H3; congruence.
  intros. red in H0; red in H1. eauto.
Qed.


Lemma alloc_only_globals_bits_match :
  forall l md ge m m' md' l',
    alloc_only_globals_bits md ge m l = Some (m',md',l') ->
    match_metadata md m ->
    match_metadata md' m'.
Proof.
  induction l; intros;
  simpl in *; try congruence.
  repeat break_match_hyp; try congruence.
  subst. opt_inv. subst.
  app IHl Heqo0.
  destruct a; simpl in Heqo.
  repeat break_match_hyp; try congruence;
  opt_inv; subst;
  try solve [
  eapply match_drop_perm; try eapply match_alloc; eauto].
Qed.

Lemma store_zeros_bits_match :
  forall l m b ofs m',
    store_zeros_bits m b ofs l = Some m' ->
    forall md,
      match_metadata md m ->
      match_metadata md m'.
Proof.
  induction l using Z_nat_ind; eauto; intros;
  rewrite store_zeros_bits_equation in *;
  try break_match_hyp; try omega; try congruence.
  break_match_hyp; try congruence.
  rewrite store_zeros_bits_equation in *.
  break_match_hyp; try omega. opt_inv. subst.
  eapply match_store_bits; eauto.
  break_match_hyp; try congruence.
  replace (l + 1 - 1) with l in * by omega.
  app IHl H0.
  eapply match_store_bits; eauto.
Qed.

Lemma store_init_data_list_bits_match :
  forall l md ge m b ofs m',
    store_init_data_list_bits md ge m b ofs l = Some m' ->
    match_metadata md m ->
    match_metadata md m'.
Proof.
  induction l; intros;
  simpl in *. congruence.
  repeat break_match_hyp; try congruence.
  app IHl H.
  unfold store_init_data_bits in Heqo.
  repeat break_match_hyp; try congruence;
  eapply match_store_bits; eauto.
Qed.

Lemma store_globals_bits_match :
  forall l md m ge m' md',
    store_globals_bits md ge m l = Some (m',md') ->
    match_metadata md m ->
    match_metadata md' m'.
Proof.
  induction l; intros;
  simpl in *; try congruence.
  repeat break_let; repeat break_match_hyp; try congruence.
  subst. app IHl H.
  unfold store_global_bits in Heqo.
  repeat break_match_hyp; try congruence;
  opt_inv; subst.
  eapply match_set_perm; eauto.
  eapply match_set_perm; eauto.
  eapply match_set_perm; try eapply Heqo2.
  eapply store_init_data_list_bits_match;
    try eapply store_zeros_bits_match;
    eauto.
Qed.

Lemma init_mem_bits_match :
  forall p m md,
    init_mem_bits p = Some (m,md) ->
    match_metadata md m.
Proof.
  unfold init_mem_bits in *.
  unfold alloc_globals_bits in *.
  intros.
  repeat break_match_hyp; try congruence.
  subst.
  app alloc_only_globals_bits_match Heqo;
    try solve [econstructor].
  eapply store_globals_bits_match; eauto.
Qed.


Lemma semantics_determinate:
  forall p, determinate (semantics_bits p).
Proof.

Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  intros; constructor; simpl; intros.
- (* determ *)
  inv H; inv H0; Equalities.
  + split. constructor. auto.
  + discriminate.
  + discriminate.
  + discriminate.
  + exploit external_call_determ'. eexact H5.
    eexact H16. intros [A B].
    split. auto. intros. destruct B; auto. subst. auto.
  + discriminate.
  + assert (vargs0 = vargs) by (eapply eval_annot_args_bits_determ; eauto). subst vargs0.
    exploit external_call_determ.
    eexact H8. eassumption.
    intros [A B].
    split. auto. intros. destruct B; auto. subst. auto.
  + assert (args0 = args) by (eapply extcall_arguments_bits_determ; eauto). subst args0.
    exploit external_call_determ'. eexact H5. eexact H16. intros [A B].
    split. auto. intros. destruct B; auto. subst. auto.
- (* trace length *)
  red; intros; inv H; simpl.
  omega.
  inv H4. eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
  inv H4. eapply external_call_trace_length; eauto.
- (* initial states *)
  inv H; inv H0. f_equal.
  + unfold rs0, rs1.
    repeat break_match_hyp; subst_max; auto.
    rewrite H1 in H. inv H.
    app init_mem_bits_match H1.
    erewrite weak_valid_pointer_sur in *; eauto.
    repeat break_and.
    unify_pinj. auto.
  + congruence.
  + congruence.
- (* final no step *)
  inv H. unfold Vzero in H0.
  red; intros; red; intros.
  inv H; replace bits with Int.zero in * by congruence.
  + erewrite weak_valid_pointer_sur in *; eauto.
    break_and. eapply null_always_invalid in H; eauto.
    break_and. app Mem.weak_valid_pointer_spec H2.
    break_or; try congruence.
  + erewrite weak_valid_pointer_sur in *; eauto.
    break_and. eapply null_always_invalid in H; eauto.
    break_and. app Mem.weak_valid_pointer_spec H2.
    break_or; try congruence.
  + erewrite weak_valid_pointer_sur in *; eauto.
    break_and. eapply null_always_invalid in H; eauto.
    break_and. app Mem.weak_valid_pointer_spec H2.
    break_or; try congruence.
  + erewrite weak_valid_pointer_sur in *; eauto.
    break_and. eapply null_always_invalid in H; eauto.
    break_and. app Mem.weak_valid_pointer_spec H2.
    break_or; try congruence.
- (* final states *)
  inv H; inv H0. congruence.
Qed.

