Require Import Coqlib.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Asm.
Require Import Integers.
Require Import Maps.
Require Import Errors.
Require Import Machregs.

Require Import ProofIrrelevance.

Require Import PeekLiveness.
Require Import SplitLib.
Require Import FindInstrLib.
Require Import SameBlockLib.
Require Import PeekTactics.
Require Import PregTactics.
Require Import AsmCallingConv. 
Require Import Union.
Require Import StepIn. 
Require Import StepLib.
Require Import PeekLivenessProof.
Require Import Use.
Require Import PeekLib. 
Require Import StepEquiv. (* Where rewrite is defined *)
Require Import ProgPropDec. 
Require Import ForwardJumps. 
Require Import Zlen.

Require Import AsmBits.
Require Import MemoryAxioms.
Require Import NoPtr.

Require Import Peephole.
Require Import PeepholeLib.
Require Import PeepholeDec.
Require Import PeepholeMatch.

Require Import MemEq.
Require Import Memory.


(* Lemma alloc_only_global_bits_result : *)
(*   forall md ge m a m' md' i b g, *)
(*     alloc_only_global_bits md ge m a = Some (m',md',i,b,g) -> *)
(*     b = Memory.Mem.nextblock m /\ a = (i,g) /\ Memory.Mem.nextblock m' = Pos.succ (Memory.Mem.nextblock m). *)
(* Proof. *)
(*   intros. unfold alloc_only_global_bits in *. *)
(*   repeat break_match_hyp; try congruence; *)
(*   NP _app Memory.Mem.alloc_result Memory.Mem.alloc; *)
(*   NP _app Memory.Mem.nextblock_alloc Memory.Mem.alloc; *)
(*   opt_inv; repeat split; *)
(*   try congruence; *)
(*   unfold Memory.Mem.drop_perm in *; *)
(*   repeat break_match_hyp; *)
(*   try congruence; *)
(*   opt_inv; *)
(*   subst; *)
(*   subst m'; *)
(*   simpl; *)
(*   assumption. *)
  
(* Qed. *)

(* Definition gd_size (gd : globdef fundef unit) : Z := *)
(*   match gd with *)
(*     | Gfun (Internal f) => zlen (fn_code f) *)
(*     | Gfun (External _) => 1 *)
(*     | Gvar v => Genv.init_data_list_size (gvar_init v) *)
(*   end. *)

(* Definition list_of_globals (l : list (ident * Values.block * globdef fundef unit)) (ge : Genv.t fundef unit) : Prop := *)
(*   forall b ofs, *)
(*     is_global ge b ofs -> exists id gd,(In (id,b,gd) l /\ 0 <= Int.unsigned ofs < gd_size gd). *)

(* Lemma list_of_globals_permut : *)
(*   forall b a c ge, *)
(*     list_of_globals (b ++ a :: c) ge -> *)
(*     list_of_globals (a :: b ++ c) ge. *)
(* Proof. *)
(*   unfold list_of_globals in *. *)
(*   intros. app H H0. *)
(*   exists x. exists x0. *)
(*   break_and; split; try assumption. *)
(*   rewrite in_app in *. *)
(*   simpl. rewrite in_app. simpl in H0. *)
(*   tauto. *)
(* Qed. *)

(* Lemma in_var_range_add_fun : *)
(*   forall ge id f b ofs, *)
(*     in_var_range (Genv.add_global ge (id, Gfun f)) b ofs -> *)
(*     in_var_range ge b ofs. *)
(* Proof. *)
(*   intros. unfold in_var_range in *. *)
(*   unfold Genv.add_global in *. *)
(*   unfold Genv.find_var_info in *. simpl in *. *)
(*   assumption. *)
(* Qed. *)

(* Lemma in_code_range_add_var : *)
(*   forall ge id v b ofs, *)
(*     in_code_range (Genv.add_global ge (id, Gvar v)) b ofs -> *)
(*     in_code_range ge b ofs. *)
(* Proof. *)
(*   intros. unfold in_code_range in *. *)
(*   unfold Genv.add_global in *. *)
(*   unfold Genv.find_funct_ptr in *. simpl in *. *)
(*   assumption. *)
(* Qed. *)

(* Lemma in_code_range_not_next : *)
(*   forall ge id gd b ofs, *)
(*     in_code_range (Genv.add_global ge (id,gd)) b ofs -> *)
(*     b <> Genv.genv_next ge -> *)
(*     in_code_range ge b ofs. *)
(* Proof. *)
(*   intros. unfold in_code_range in *. *)
(*   destruct gd; unfold Genv.find_funct_ptr in *; *)
(*   unfold Genv.add_global in *; simpl in *; *)
(*   try rewrite PTree.gso in * by congruence; *)
(*   eauto. *)
(* Qed. *)

(* Lemma in_var_range_not_next : *)
(*   forall ge id gd b ofs, *)
(*     in_var_range (Genv.add_global ge (id,gd)) b ofs -> *)
(*     b <> Genv.genv_next ge -> *)
(*     in_var_range ge b ofs. *)
(* Proof. *)
(*   intros. unfold in_var_range in *. *)
(*   destruct gd; unfold Genv.find_var_info in *; *)
(*   unfold Genv.add_global in *; simpl in *; *)
(*   try rewrite PTree.gso in * by congruence; *)
(*   eauto. *)
(* Qed. *)



(* Lemma list_of_globals_cons : *)
(*   forall l ge, *)
(*     list_of_globals l ge -> *)
(*     forall id gd, *)
(*       list_of_globals ((id,Genv.genv_next ge,gd)::l) (Genv.add_global ge (id,gd)). *)
(* Proof. *)
(*   intros. *)
(*   unfold list_of_globals in *. *)
(*   intros. unfold is_global in H0. *)
(*   destruct gd; break_or; *)
(*   try ( *)
(*         try eapply in_var_range_add_fun in H1; *)
(*         try eapply in_code_range_add_var in H1; *)
(*         exploit H; unfold is_global; try solve [right; eassumption]; *)
(*         try solve [left; eassumption]; *)
(*         intros; repeat break_exists; *)
(*         break_and; eexists; eexists; simpl; *)
(*         split; try right; eauto); *)

(*   destruct (peq b (Genv.genv_next ge)); *)
(*   try subst; *)
(*   try ( *)
(*       try eapply in_var_range_not_next in H1; *)
(*       try eapply in_code_range_not_next in H1; *)
(*       try congruence; *)
(*       exploit H; unfold is_global; try solve [right; eassumption]; *)
(*       try solve [left; eassumption]; *)
(*       intros; repeat break_exists; *)
(*       break_and; eexists; eexists; simpl; *)
(*       split; try right; eauto). *)

(*   unfold in_code_range in *. *)
(*   unfold Genv.find_funct_ptr in *. *)
(*   unfold Genv.add_global in *. *)
(*   simpl in *. *)
(*   rewrite Maps.PTree.gss in *. *)
(*   eexists; eexists; split; try left; try reflexivity;  *)
(*   unfold gd_size; destruct f; try omega. *)
  
(*   unfold in_var_range in *. *)
(*   unfold Genv.find_var_info in *. *)
(*   unfold Genv.add_global in *. *)
(*   simpl in *. *)
  
(*   rewrite PTree.gss in *. *)
(*   eexists; eexists; split; try left; try reflexivity;  *)
(*   unfold gd_size; try omega. *)
(* Qed. *)


(* Lemma alloc_only_globals_list_ind : *)
(*   forall l n ge m md m' md' l', *)
(*     Memory.Mem.nextblock m = Genv.genv_next ge -> *)
(*     list_of_globals n ge -> *)
(*     alloc_only_globals_bits md (Genv.add_globals ge l) m l = Some (m',md',l') -> *)
(*     list_of_globals (l' ++ n) (Genv.add_globals ge l). *)
(* Proof. *)
(*   induction l; intros. *)
(*   simpl in H1. inv H1. simpl. assumption. *)
(*   simpl in H1. repeat break_match_hyp; try congruence. subst. *)
(*   opt_inv. subst. *)
(*   app alloc_only_global_bits_result Heqo. repeat break_and. subst. *)
(*   rewrite H. simpl. *)
(*   app IHl Heqo0; try solve [simpl; congruence]; *)
(*   try solve [eapply list_of_globals_cons; eauto]. *)
(*   eapply list_of_globals_permut; eauto. *)
  
(* Qed. *)
  

(* Lemma list_of_globals_empty : *)
(*   forall (p : program), *)
(*     list_of_globals nil (Genv.empty_genv fundef unit (prog_public p)). *)
(* Proof. *)
(*   unfold list_of_globals. intros. *)
(*   unfold is_global in H. *)
(*   break_or. *)

(*   unfold in_code_range in H0. *)
(*   unfold Genv.find_funct_ptr in H0. *)
(*   unfold Genv.empty_genv in H0. *)
(*   simpl in H0. *)
(*   rewrite PTree.gempty in H0. inv_false. *)

(*   unfold in_var_range in H0. *)
(*   unfold Genv.find_var_info in H0. *)
(*   unfold Genv.empty_genv in H0. *)
(*   simpl in H0. *)
(*   rewrite PTree.gempty in H0. inv_false. *)
(* Qed. *)

(* Lemma alloc_only_globals_list : *)
(*   forall l' md p m' md', *)
(*     alloc_only_globals_bits md (Genv.globalenv p) Memory.Mem.empty (prog_defs p) = Some (m',md',l') -> *)
(*     list_of_globals l' (Genv.globalenv p). *)
(* Proof. *)
(*   intros. *)
(*   unfold Genv.globalenv in *. *)
(*   replace l' with (l' ++ nil) by eapply app_nil_r; eauto. *)
(*   eapply alloc_only_globals_list_ind; eauto. *)
(*   simpl. reflexivity. *)
(*   eapply list_of_globals_empty. *)
(* Qed. *)

(* Definition addr_in_list (b : Values.block) (ofs : int) (l : list (ident * Values.block * globdef fundef unit)) : Prop := *)
(*   exists id gd, *)
(*     In (id,b,gd) l /\ 0 <= Int.unsigned ofs < gd_size gd. *)

(* Lemma store_zeros_bits_access : *)
(*   forall l m b ofs m', *)
(*     store_zeros_bits m b ofs l = Some m' -> *)
(*     Mem.mem_access m = Mem.mem_access m'. *)
(* Proof. *)
(*   induction l using Z_nat_ind; *)
(*   intros; *)
(*   rewrite store_zeros_bits_equation in *; *)
(*   intros. *)
(*   * break_match_hyp; try omega. inv H. reflexivity. *)
(*   * break_match_hyp; try omega. break_match_hyp; try congruence. *)
(*     rewrite store_zeros_bits_equation in *. *)
(*     break_match_hyp; try omega. inv H. *)
(*     unfold MemBits.store_bits in *. *)
(*     repeat break_match_hyp; try congruence. *)
(*     inv Heqo. simpl. reflexivity. *)
(*   * break_match_hyp; try omega. inv H0. reflexivity. *)
(*   * break_match_hyp; try omega. *)
(*     break_match_hyp; try congruence. *)
(*     replace (l + 1 - 1) with l in * by omega. *)
(*     app IHl H0. *)
(*     rewrite <- H0. *)
(*     unfold MemBits.store_bits in *. *)
(*     break_match_hyp; try congruence. *)
(*     inv Heqo. simpl. reflexivity. *)
(* Qed. *)

(* Lemma store_init_data_list_bits_access : *)
(*   forall l a ge m b ofs m', *)
(*     store_init_data_list_bits a ge m b ofs l = Some m' -> *)
(*     Mem.mem_access m = Mem.mem_access m'. *)
(* Proof. *)
(*   induction l; intros. simpl in H. inv H. reflexivity. *)
(*   simpl in H. break_match_hyp; try congruence. *)
(*   app IHl H. rewrite <- H. *)
(*   unfold store_init_data_bits in *. *)
(*   repeat break_match_hyp; try congruence; *)
(*   try solve [unfold MemBits.store_bits in *; *)
(*               break_match_hyp; *)
(*               try congruence; *)
(*               try opt_inv; *)
(*               simpl; *)
(*               reflexivity]. *)
(* Qed. *)


(* Lemma store_globals_bits_untouched : *)
(*   forall l b, *)
(*     ~ In b (map snd (map fst l)) -> *)
(*     forall md ge m m' md', *)
(*       store_globals_bits md ge m l = Some (m',md') -> *)
(*       (Mem.mem_access m) !! b = (Mem.mem_access m') !! b. *)
(* Proof. *)
(*   induction l; intros. *)
(*   simpl in H0. inv H0. reflexivity. *)
(*   simpl in H0. repeat break_match_hyp; try congruence; subst. *)
(*   simpl in H. *)
(*   eapply Decidable.not_or in H. *)
(*   break_and. *)
(*   cut ((Mem.mem_access m0) !! b = (Mem.mem_access m') !! b); *)
(*     try solve [eapply IHl; eauto]. *)
(*   intros. rewrite <- H2. clear H2. clear IHl. *)
(*   clear H0. *)
  
(*   unfold store_global_bits in *. *)
(*   repeat break_match_hyp; try congruence; *)
(*   opt_inv; subst; *)
(*   unfold MemBits.set_perm in *; *)
(*   repeat break_match_hyp; try congruence; *)
(*   opt_inv; subst; simpl; *)
(*   rewrite PMap.gso by congruence; try reflexivity. *)
  
(*   app store_zeros_bits_access Heqo0. *)
(*   app store_init_data_list_bits_access Heqo1. *)
(*   congruence. *)
(* Qed. *)


(* Lemma store_globals_perms : *)
(*   forall l ge md m m' md', *)
(*     list_norepet (map snd (map fst l)) -> *)
(*     store_globals_bits md ge m l = Some (m',md') -> *)
(*     forall b ofs, *)
(*       addr_in_list b ofs l -> *)
(*       exists p, *)
(*         (Memory.Mem.mem_access m') !! b (Int.unsigned ofs) Cur = Some p /\ p <> Freeable. *)
(* Proof. *)
(*   induction l; intros; *)
(*   unfold addr_in_list in *; *)
(*   intros; *)
(*   repeat break_exists; repeat break_and. *)
(*   simpl in H1. inv_false. *)
(*   simpl in H1. break_or. *)
(*   * simpl in H0. *)
(*     break_match_hyp; try congruence. *)
(*     break_let. subst. *)
(*     simpl in H. inv H. *)
(*     app store_globals_bits_untouched H0. *)
(*     rewrite <- H0. *)
(*     unfold store_global_bits in Heqo. *)
(*     repeat break_match_hyp; try congruence; *)
(*     opt_inv; subst; simpl in *; *)
(*     unfold MemBits.set_perm in *; break_match_hyp; try congruence; opt_inv; subst; *)
(*     simpl; rewrite PMap.gss; unfold andb; unfold proj_sumbool; *)
(*     break_match; try omega; eexists; split; try reflexivity; try congruence; *)
(*     repeat break_if; try congruence; try omega. *)

(*     unfold Genv.perm_globvar. *)
(*     repeat break_match; try congruence. *)
    
    

(*   * simpl in H. inv H. *)
(*     destruct a. destruct p. *)
(*     simpl in H6. *)
(*     simpl in H0. repeat break_match_hyp; try congruence. *)
(*     subst. *)
(*     eapply IHl; eauto. *)

(*     Grab Existential Variables. *)
(*     exact Freeable. *)
(*     exact Freeable. *)
(*     exact Freeable. *)
    
(* Qed. *)


(* Lemma store_globals_perms' : *)
(*   forall l ge md m m' md', *)
(*     store_globals_bits md ge m l = Some (m',md') -> *)
(*     list_of_globals l ge -> *)
(*     list_norepet (map snd (map fst l)) -> *)
(*     global_perms ge m'. *)
(* Proof. *)
(*   unfold global_perms. *)
(*   intros. *)
(*   eapply store_globals_perms; eauto. *)
(*   unfold list_of_globals in *. *)
(*   unfold addr_in_list. *)
  
(*   solve [eauto]. *)
(* Qed. *)

(* Lemma alloc_only_globals_bits_nextblock : *)
(*   forall l md ge m m' md' l', *)
(*     alloc_only_globals_bits md ge m l = Some (m',md',l') -> *)
(*     forall b, *)
(*       In b (map snd (map fst l')) -> ~ Plt b (Mem.nextblock m). *)
(* Proof. *)
(*   induction l; intros. *)
(*   simpl in H. inv H. *)
(*   simpl in H0. inv_false. *)
(*   simpl in H. repeat break_match_hyp; try congruence. *)
(*   subst. inv H. *)
(*   simpl in H0. break_or. *)
(*   * clear -Heqo. *)
(*     unfold alloc_only_global_bits in Heqo. *)
(*     destruct a. *)
(*     repeat break_match_hyp; try congruence; *)
(*     inv Heqo; *)
(*     NP _app Mem.alloc_result Mem.alloc; *)
(*     subst; *)
(*     eapply Plt_strict. *)
(*   * app IHl Heqo0. *)
(*     unfold alloc_only_global_bits in Heqo. *)
(*     destruct a. *)
(*     repeat break_match_hyp; try congruence; *)
(*     inv Heqo; *)
(*     NP _app Mem.nextblock_alloc Mem.alloc; *)
(*     subst; *)
(*     unfold Mem.drop_perm in *; *)
(*     repeat break_match_hyp; try congruence; *)
(*     opt_inv; subst; simpl in *; *)
(*     rewrite Heqp in *; *)
(*     intro; apply Heqo0; *)
(*     eapply Plt_trans_succ; eauto. *)
(* Qed. *)


(* Lemma alloc_only_globals_bits_list_norepet : *)
(*   forall l md ge m m' md' l', *)
(*     alloc_only_globals_bits md ge m l = Some (m',md',l') -> *)
(*     list_norepet (map snd (map fst l')). *)
(* Proof. *)
(*   induction l; intros. *)
(*   * simpl in H. inv H. simpl. econstructor. *)

(*   * simpl in H. repeat break_match_hyp; try congruence. *)
(*     subst. inv H. simpl. econstructor. *)

(*     name (alloc_only_globals_bits_nextblock _ _ _ _ _ _ _ Heqo0) Hb. *)
(*     intro. app Hb H. *)

(*   unfold alloc_only_global_bits in Heqo. *)
(*   destruct a. *)
(*   repeat break_match_hyp; try congruence; *)
(*   inv Heqo; *)
(*   NP _app Mem.nextblock_alloc Mem.alloc; *)
(*   NP _app Mem.alloc_result Mem.alloc; *)
(*   subst; try rewrite Heqp in *; *)
(*   unfold Mem.drop_perm in *; *)
(*     repeat break_match_hyp; try congruence; *)
(*     opt_inv; subst; simpl in *; *)
(*     try rewrite Heqp in *; *)
(*     apply H; *)
(*     eapply Plt_succ. *)
(*   eapply IHl; eauto. *)
(* Qed. *)

Section PRESERVATION.

Variable rwr: rewrite.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSF: transf_program rwr prog = OK tprog.
Hypothesis CALLING_CONV : calling_conv_correct_bits prog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Definition outside_range := PeepholeDec.outside_range rwr prog.
Definition in_transf := PeepholeDec.in_transf rwr prog.
Definition at_entry := PeepholeDec.at_entry rwr prog.
Definition match_states := PeepholeDec.match_states rwr prog.
Definition transf_index := PeepholeLib.transf_index rwr prog.
Definition transf_idx_end := PeepholeLib.transf_idx_end rwr prog.

Lemma step_simulation:
  forall s1 t s1', step_bits (Genv.globalenv prog) s1 t s1' ->
  forall s2, match_states s1 s2 ->
  ((exists s2', plus step_bits (Genv.globalenv tprog) s2 t s2' /\ match_states s1' s2') \/
   (((measure rwr) (transf_idx_end s1')) s1' < ((measure rwr) (transf_idx_end s1)) s1)%nat /\ t = E0 /\ match_states s1' s2).
Proof.

  intros.
  app in_transf_dec H0.
  repeat break_or.
  * (* started in region *)
    app in_transf_step_dec H.
    break_or.
    - (* stayed in region *)
      simpl.
      
      right. app no_trace_step H2.
      subst t.
      split.

      app in_transf_index H3.
      app in_transf_index H.

      
      repeat (erewrite (transf_idx_end_correct rwr prog); eauto).

      assert (x = x0).
      eapply transf_index_unique in H2; eauto.
      break_and. congruence.
      
      subst x0.

      eapply measure_decr_rewr; eauto.
      split; auto.
      
      eapply in_transf_step_match; eauto. 
    - (* stepped out *)
      app no_trace_step H2. subst t.
      left.
      eapply step_out; eauto.
  * (* started outside *)
    app outside_step_dec H. break_or.
    - (* stayed outside *)
      
      name TRANSF Htransf.
      unfold transf_program in TRANSF.
      repeat break_match_hyp; inversion TRANSF.
      app match_states_match_live H1.
      destruct u.
      app liveness_analysis_correct Heqr.
      unfold liveness_fun_correct in Heqr.
      unfold exec_preserved in Heqr.
      app Heqr H1. break_and.
      inversion TRANSF.
      rewrite H9.

      assert (match_states s1' x).
        eapply match_not_in; try apply H1; try apply H2; eauto.

      left. exists x. split.
      apply plus_one.       
      eapply step_outside; auto.
      eauto.  eauto.
      eapply outside_range_match; eauto.
      auto.
      
    - (* stepped to entry *)
      name TRANSF Htransf.
      unfold transf_program in TRANSF.
      repeat break_match_hyp; inversion TRANSF.
      app match_states_match_live H1.
      destruct u.
      app liveness_analysis_correct Heqr.
      unfold liveness_fun_correct in Heqr.
      unfold exec_preserved in Heqr.
      app Heqr H1. break_and.
      inversion TRANSF.
      rewrite H9.

      assert (match_states s1' x).
        eapply match_at_entry; eauto.
      left. exists x. split.
      apply plus_one.
      
      eapply step_outside; auto.
      eauto. eauto.
      eapply outside_range_match; eauto.
      auto.

  * (* at entry *)
    app at_entry_step_dec H. break_or.
    - (* stayed in transformed region *)
      right.
      (* This case should be its own lemma *)

      split. eapply measure_decr_entry_in; eauto.
                    
      app at_entry_at_code H0.
      name (no_trace_find rwr) ntf.
      app no_trace_step_at H2. split; eauto.
      subst t.

      eapply entry_step_in; eauto.
      
      
    - left.
      
      app no_trace_entry_step H0.
      subst t.
      eapply step_out_at_entry; eauto.

Qed.

Lemma prog_defs_tprog :
  prog_defs tprog = map (transform_program_globdef (transf_fundef rwr)) (prog_defs prog).
Proof.
  unfold transf_program in TRANSF.
  repeat break_match_hyp; inversion TRANSF.
  unfold transform_program. simpl.
  reflexivity.
Qed.

Lemma store_init_data_bits_pres :
  forall m b k a m' md,
    store_init_data_bits md ge m b k a = Some m' ->
    store_init_data_bits md tge m b k a = Some m'.
Proof.
  intros. destruct a; simpl in *; eauto. 
  break_match_hyp; try solve [inversion H].
  unfold tge. erewrite symbols_preserved by eauto.
  unfold ge in *. find_rewrite. assumption.
Qed.

Lemma store_init_data_list_bits_pres :
  forall l m b k m' md,
    store_init_data_list_bits md ge m b k l = Some m' ->
    store_init_data_list_bits md tge m b k l = Some m'.
Proof.
  induction l; intros.
  simpl in *. eauto.
  simpl in H.
  break_match_hyp; try solve [inversion H].
  app store_init_data_bits_pres Heqo.
  simpl. find_rewrite. eauto.
Qed.

Lemma alloc_global_pres :
  forall m a m0 md' id b g md,
    alloc_only_global_bits md ge m a = Some (m0,md',id,b,g) ->
    let tidg := transform_program_globdef (transf_fundef rwr) (id,g) in
    alloc_only_global_bits md tge m (transform_program_globdef (transf_fundef rwr) a) = Some (m0,md',id,b,snd tidg).
Proof.
  intros. destruct a. simpl in *. 
  repeat break_match_hyp; try congruence; simpl;
  repeat opt_inv.
  destruct f0. simpl.
  simpl in *.
  assert (zlen fn_code = zlen (transf_code rwr fn_code)).
  unfold zlen. rewrite length_pres. reflexivity.
  repeat rewrite <- H. simpl.
  repeat collapse_match. simpl.
  destruct g; simpl in *. inversion H5.
  simpl. congruence. congruence.
  
  repeat collapse_match.
  destruct g; try congruence. inversion H5.
  subst tidg. simpl. subst f0. simpl. congruence.
  repeat collapse_match.
  destruct g; try congruence. inversion H5.
  subst tidg. simpl. congruence. 
Qed.

Definition mgd (x : (ident * Values.block * globdef fundef unit)) : (ident * Values.block * globdef fundef unit) :=
  let (idb,g) := x in
  let (id,b) := idb in
  let (id',g') := transform_program_globdef (transf_fundef rwr) (id,g) in
  (id,b,g').

Lemma alloc_globals_pres :
  forall l m m' md md' l',
    alloc_only_globals_bits md ge m l = Some (m',md',l') ->
    alloc_only_globals_bits md tge m (map (transform_program_globdef (transf_fundef rwr)) l) = Some (m',md',map mgd l').
Proof.
  induction l; intros.
  simpl in H. inv H. simpl. reflexivity.
  simpl in H. simpl. break_match_hyp; inv H.
  repeat break_let. subst.
  break_match_hyp; try congruence.
  repeat break_let. subst. opt_inv. subst.
  app IHl Heqo0.
  
  app alloc_global_pres Heqo. collapse_match.
  collapse_match. simpl.
  f_equal. f_equal. f_equal. f_equal.
  break_let. simpl. reflexivity.
Qed.

Lemma store_globals_bits_pres :
  forall l md m m' md',
    store_globals_bits md (Genv.globalenv prog) m l = Some (m',md') ->
    store_globals_bits md (Genv.globalenv tprog) m (map mgd l) = Some (m',md').
Proof.
  induction l; intros.
  simpl in *. congruence.
  simpl in *. repeat break_let; subst.
  repeat break_match_hyp; try congruence.
  simpl in Heqp1.
  repeat break_let; subst.
  inv Heqp1.
  break_match_hyp. subst g. inv Heqp2.
  unfold store_global_bits in *.
  destruct f.
  assert (zlen (fn_code f) = zlen (transf_code rwr (fn_code f))).
  unfold zlen. rewrite length_pres. reflexivity.
  simpl. destruct f. simpl in *.
  break_match_hyp; try congruence. inv Heqo.
  rewrite <- H0.
  collapse_match.
  eapply IHl; eauto.
  simpl. collapse_match.
  eapply IHl; eauto.
  inv Heqp2.
  unfold store_global_bits in *.
  repeat break_match_hyp; try congruence;
  repeat opt_inv; subst.
  erewrite store_init_data_list_bits_pres; eauto.
  collapse_match.
  eapply IHl; eauto.
Qed.

Lemma init_mem_bits_pres :
  forall m,
    init_mem_bits prog = Some m ->
    init_mem_bits tprog = Some m.
Proof.
  intros. unfold init_mem_bits in *.
  rewrite prog_defs_tprog.
  destruct m.
  unfold alloc_globals_bits in *.
  repeat break_match_hyp; try congruence.
  subst.
  erewrite alloc_globals_pres; eauto.
  eapply store_globals_bits_pres; eauto.
Qed.

Lemma prog_main_pres :
  prog_main tprog = prog_main prog.
Proof.
  intros. unfold transf_program in TRANSF.
  repeat break_match_hyp; inversion TRANSF.
  destruct prog. simpl. reflexivity.
Qed.

Definition symbols_preserved := PeepholeLib.symbols_preserved rwr prog tprog.



Lemma transf_initial_states:
  forall st1, AsmBits.initial_state_bits prog st1 ->
              exists st2, AsmBits.initial_state_bits (tprog) st2 /\ match_states st1 st2.
Proof.
  name TRANSF Htransf.
  intros. inv H.
  unfold Genv.symbol_address in *.
  exists (State_bits rs0 m0 md).
  destruct (Genv.find_symbol (Genv.globalenv prog) (prog_main prog)) eqn:?;
  rewrite <- symbols_preserved in Heqo. 
  *
    split. econstructor; eauto.
    eapply init_mem_bits_pres; eauto.
    rewrite prog_main_pres. unfold Genv.symbol_address. rewrite Heqo. eauto.
    eapply outside; eauto; subst rs0; preg_simpl; eauto.

    econstructor; preg_simpl; eauto.
    
    unfold transf_program in TRANSF.
    repeat break_match_hyp; inversion TRANSF.
    unfold symbol_offset in Heqv.
    rewrite symbols_preserved in Heqo. unfold ge in *.
    rewrite Heqo in Heqv. inv Heqv. rewrite Heqo0.
    eexists; split; eauto.
    break_match; eauto.
    destruct f0. subst.
    unfold transf_code. repeat break_match; try solve [right; reflexivity].
    left.

    exists (zlen c). exists (zlen (c ++ find rwr)).
    split. econstructor; eauto. split; eauto.
    unfold transf_code. find_rewrite. find_rewrite.
    reflexivity.
    destruct c; try solve [inversion Heqb].
    rewrite zlen_app. repeat rewrite zlen_cons.
    name (zlen_nonneg _ c) zln. name zlen_find zlnf.
    rewrite Int.unsigned_zero. omega.
    eauto.
    intros. repeat preg_case; preg_simpl;
                                unfold Values.Vzero;
                                try congruence.
    rewrite Pregmap.gi.
    simpl. eauto.
    congruence.
    eapply eq_mem_init; eauto.
    
    split; try eapply no_ptr_mem_init; eauto.
    unfold no_ptr_regs. intros.
    repeat preg_case; preg_simpl; unfold Values.Vzero; try congruence.
    rewrite Pregmap.gi. congruence.
  * eauto.
  * split. econstructor; eauto.
    eapply init_mem_bits_pres; eauto.
    rewrite prog_main_pres. unfold Genv.symbol_address. rewrite Heqo. eauto.

    unfold transf_program in TRANSF.
    unfold symbol_offset in TRANSF.
    rewrite symbols_preserved in Heqo. unfold ge in *.
    rewrite Heqo in TRANSF.
    inv TRANSF. eauto.
  * eauto.
Qed.

Lemma star_step_match_metadata :
  forall ge st st' t,
    star step_bits ge st t st' ->
    forall rs m md rs' m' md',
      st = State_bits rs m md ->
      st' = State_bits rs' m' md' ->
      match_metadata md m ->
      match_metadata md' m'.
Proof.
  induction 1; intros.
  subst. congruence.
  subst. destruct s2.
  exploit IHstar; intros; try reflexivity;
  app step_md H.
  break_and. assumption.
Qed.

Lemma transf_final_states:
  forall s1 s2 r,
   match_states s1 s2 ->
   Smallstep.final_state (semantics_bits prog) s1 r ->
   Smallstep.final_state (semantics_bits tprog) s2 r.
Proof.
  
  intros. simpl in *.
  inv H0. inv H; try unify_PC.
  inv H8; unify_PC.

  unfold mem_eq in H11.
  repeat break_and.
  erewrite weak_valid_pointer_sur in *; eauto.
  repeat break_and.
  app null_always_invalid H5.
  break_and. app Memory.Mem.weak_valid_pointer_spec H14.
  destruct H14; congruence.

  unfold mem_eq in H11.
  repeat break_and.
  erewrite weak_valid_pointer_sur in *; eauto.
  repeat break_and.
  app null_always_invalid H7.
  break_and. app Memory.Mem.weak_valid_pointer_spec H12.
  destruct H12; congruence.

  
  name (conj H11 H10) Hstin.
  rewrite <- st_in_eq in Hstin.
  app star_step_in_in' Hstin.
  inv Hstin. inv H3. unify_PC.

  assert (match_metadata md m). {
    app step_md H9. repeat break_and.
    rewrite st_in_eq in H. repeat break_and.
    app star_to_step H.
    app star_step_match_metadata H.
  } idtac.
  erewrite weak_valid_pointer_sur in H19; eauto.
  repeat break_and.
  app null_always_invalid H13.
  break_and. app Memory.Mem.weak_valid_pointer_spec H16.
  destruct H16; congruence.


  unfold mem_eq in *.
  repeat break_and.
  erewrite weak_valid_pointer_sur in *; eauto.
  break_and.
  app null_always_invalid H7.
  break_and.
  rewrite Memory.Mem.weak_valid_pointer_spec in H11.
  destruct H11; congruence.
Qed.  

Lemma transf_program_correct:
  forward_simulation (AsmBits.semantics_bits prog) (AsmBits.semantics_bits (tprog)).
Proof.
  eapply forward_simulation_star.
  unfold Senv.public_symbol. simpl.
  eapply public_symbols_preserved; eauto.
  eexact transf_initial_states.
  eexact transf_final_states.
  eapply step_simulation.
Qed.

End PRESERVATION.
