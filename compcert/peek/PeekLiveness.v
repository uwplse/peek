Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Asm.
Require Import Axioms.
Require Import Floats.
Require Import Values.
Require Import Maps.
Require Import Errors.
(* Require Import Lattice. *)
(* Require Import ListSet. *)
(* Require Import Iteration. *)

Require Import PeekTactics.
Require Import SplitLib.
Require Import FindInstrLib.
Require Import Pred.
Require Import PeekLib.
Require Import Use.
Require Import UseBasic.
Require Import Union.
Require Import AsmCallingConv.
Require Import ProgPropDec.
Require Import AsmBits.
Require Import MemoryAxioms.
Require Import ValEq.
Require Import MemEq.
Require Import Zlen.

Definition exec_preserved(p : Asm.program)(P : Asm.program -> state_bits -> state_bits -> Prop) : Prop :=
  forall sl sr sl' t,
    P p sl sr ->
    step_bits (Genv.globalenv p) sl t sl' ->
    exists sr',
      (step_bits (Genv.globalenv p) sr t sr' /\ P p sl' sr').

Definition match_live
           (live_fun : genv -> Values.block -> Z -> list preg)
           (prog : Asm.program)
           (sl sr : state_bits) : Prop :=
  match sl,sr with
    | State_bits lrs lm md,State_bits rrs rm md' =>
      forall bits b i,
        psur md bits = Some (b, i) ->
        forall (p1 : lrs PC = Values.Vint bits),
        no_ptr_regs rrs /\ no_ptr_mem rm /\ md = md' /\
        (forall p, In p (live_fun (Genv.globalenv prog) b (Int.unsigned i)) ->
                   val_eq (lrs p) (rrs p)) /\ (mem_eq md lm rm)
  end.

Definition liveness_fun_correct(p : Asm.program)(live_fun : genv -> Values.block -> Z -> list preg):Prop :=
  exec_preserved p (match_live live_fun).

(* current liveness results *)
Definition liveness_map_t := ZMap.t (list preg).

(* worklist of locations to process *)
Definition worklist_t := list Z.

Inductive iter_state := 
  | mkstate : liveness_map_t -> worklist_t -> iter_state.

(* given a current liveness map, make a liveness function *)
(* Definition curr_liveness (lm : liveness_map_t) : Z -> list preg := fun z => ZMap.get z lm. *)

(* given a piece of code, create an initial state for the iterative liveness solver *)
Definition init_state (c : code) : iter_state :=
  mkstate (ZMap.init (PC :: nil)) (range (Z.of_nat (length c))).

Definition transfer (i : instruction) (l : list preg) : list preg :=
  addl preg_eq (use i) (reml preg_eq (def i) l).

(* How should liveness work around calls/returns: *)
(*  * When making a call: *)
(*    - at the call site, caller save regs must be dead *)
(*    - at the call site, callee save regs may be live *)
(*      + currently we approximate that by making all callee save regs live *)
(*      + this works? *)
(*      + all callee save regs that are live at return site are live here *)
(*      + data must flow from call site to return site *)
(*      + this is hard, is there a nice way around it? *)
(*    - at the call target, caller save regs must be dead *)
(*    - at the call target, callee save regs must be live, or not change at all in the function (we have to take care of them) *)
(*      + they're used by the return function, so they will be live if not changed, thus must be live is ok *)
(*      + currently we don't force them all to be live *)
(*      + allowed to not use params, but must preserve all these regs *)
(*      + check at fun entry must thus be exact set equality, not subset *)
(*  * When making a return: *)
(*    - at the return site, callee save regs must be live *)
(*    - at the return site, caller save regs must be dead *)
(*    - at the return target, callee save regs may be live *)
(*    - at the return target, caller save regs must be dead *)

(* 
  This translates into the following update function:
  - if it's a return instr, set callee saves to live and caller saves to dead
  - if it's a return target, flow all callee saves live to it's call
  - if it's a call, flow backwards normally

  With the following post-processing checks:
  - top of function: all callee saves must be live, all caller saves must be dead
  - each call site: all caller saves must be dead
  - each return target: we get results for free from callsite check above
  - each return site: we get for free since update just set to right answer
*)

(* 

  is there a good way to do this without flowing information over
  calls? this seems hard to deal with in the proof and stuff.
  How do we do this?

*)

(* given a current liveness map, take one step and produce a new liveness map *)
(* This is the heart of the liveness analysis. Pay attention to this function *)
Definition update_liveness (c : code) (z : Z) (lm : liveness_map_t) : liveness_map_t :=
  match find_instr z c with
    | Some i =>
      if (is_call_return_dec i) then
        if (is_call_dec i) then
          ZMap.set z (regs_live_across_call ++ parameter_regs) lm
        else 
          ZMap.set z (regs_live_across_call ++ return_regs_sig (call_type i)) lm
      else
        (* get succs *)
        match (succ z c) with
          | Some ss => 
            (* get liveout to work with *)
            let liveout := union_l preg_eq (map (fun z => ZMap.get z lm) ss) in
            (* get old livein value that we will replace *)
            let livein_old := ZMap.get z lm in
            (* calculate new livein value from liveout *)
            let livein_new := transfer i liveout  in
            ZMap.set z livein_new lm
          | None => lm
        end
    | None => lm
  end.

(* update the working notion of liveness, and treat the worklist accordingly *)
Definition update_iter_state (c : code) (it : iter_state) : liveness_map_t + iter_state :=
  match it with
    | mkstate lm wl =>
      match wl with
        | nil => inl lm
        | z :: zs => let lm' := update_liveness c z lm in
                     if set_equiv_dec (eq := preg_eq) (ZMap.get z lm) (ZMap.get z lm')
                     then inr (mkstate lm' zs)
                     else inr (mkstate lm' (wl_add (pred z c) zs))
      end
  end.

Fixpoint iter (A B : Type) (update : A -> B + A) (n : nat) (init : A) : option B :=
  match n with
    | O => None
    | S n' => 
      match update init with
        | inr next => iter A B update n' next
        | inl res => Some res
      end
  end.


Lemma iter_prop :
  forall (m n : nat),
    (n < m)%nat ->
  forall (A B : Type) (step : A -> B + A) (P : A -> Prop)
         (Q : B -> Prop),
    (forall a : A,
       P a -> match step a with
                | inl b => Q b
                | inr a' => P a'
              end) ->
    forall (a : A) (b : B),
      iter A B step n a = Some b -> P a -> Q b.
Proof.
  induction m; intros.
  * omega.
  * destruct n. simpl in H1. inv H1.
    unfold iter in H1. fold iter in H1.
    destruct (step a) eqn:?.
    - name (H0 a H2) Hm. rewrite Heqs in Hm. inv H1. assumption.
    - name (H0 a H2) Hm. rewrite Heqs in Hm.
      eapply IHm; eauto. omega.
Qed.

(* not sure size of code by num regs is strict theoretical upper bound on number of iterations needed but is probably pretty good *)
Definition find_liveness(c : code) := iter iter_state liveness_map_t (update_iter_state c) (S (S ((length c) * (length all_pregs)))) (init_state c).

Definition in_wl_or_updated(c : code) (it : iter_state):Prop :=
  match it with
    | mkstate lm wl => (forall z, (z >= 0) /\ (z < zlen c) -> ((In z wl) \/ (forall p, (In p (ZMap.get z lm) <-> In p (ZMap.get z (update_liveness c z lm))))))
  end.

Definition reached_fixed_point(c : code)(lm : liveness_map_t):Prop :=
  forall p z, 
    In p (ZMap.get z lm) <-> In p (ZMap.get z (update_liveness c z lm)).

(* TODO: replace subset_dec with better code *)
Definition entry_ok(lm : liveness_map_t)(c : code) :=
  if @subset_dec preg preg_eq (ZMap.get 0 lm) (regs_live_across_call ++ parameter_regs) then
    true
  else
    false.

Definition ret_ok (lm : liveness_map_t)(c : code)(k : Z) : Prop :=
  forall z i,
    find_instr z c = Some i ->
    is_call i ->
    forall p, 
      In p (ZMap.get (z + k) lm) -> 
      In p (regs_live_across_call ++ (return_regs_sig (call_type i))).

Definition ret_ok_ind_case :
  forall lm a c k,
    ret_ok lm (a :: c) k ->
    ret_ok lm c (k + 1).
Proof.
  intros. unfold ret_ok in *. intros.
  assert (exists i, find_instr z c = Some i).
    exists i. auto.
  apply in_range_find_instr in H3.
  apply (H (z + 1) i). simpl. destruct (zeq (z + 1) 0). omega.
  replace (z + 1 - 1) with z by omega. auto. auto.
  replace (z + 1 + k) with (z + (k + 1)) by omega.
  auto.
Defined.

Definition ret_ok_dec :
  forall lm c k,
    { ret_ok lm c k } + { ~ ret_ok lm c k }.
Proof.
  induction c; intros.
  * left. unfold ret_ok. intros. simpl in H. inv H.
  * specialize (IHc (k + 1)). destruct IHc.
    - destruct (is_call_dec a).
      destruct (@subset_dec preg preg_eq (ZMap.get k lm) (regs_live_across_call ++ (return_regs_sig (call_type a)))) eqn:?.
      left. unfold ret_ok. intros.
      destruct (zeq z 0). subst z.
      simpl in H. inv H.
      apply i0. apply H1.
      replace z with (1 + (z-1)) in H by omega.
      rewrite find_instr_head in H.
      unfold ret_ok in r. eapply r; eauto.
      replace (z - 1 + (k + 1)) with (z + k) by omega.
      assumption.
      assert (exists x, find_instr z (a :: c) = Some x).
        exists i1. rewrite <- H. replace (1 + (z - 1)) with z by omega.
        reflexivity.
      rewrite <- in_range_find_instr in H2.
      omega.
      right. unfold not. intros.
      unfold not in n.
      unfold ret_ok in H.
      specialize (H 0 a eq_refl i).
      apply n in H. assumption.
      left. unfold ret_ok.
      intros.
      destruct (zeq z 0).
        subst z. simpl in H. inv H. congruence.
      assert (exists i, find_instr z (a :: c) = Some i).
        exists i. auto.
      apply in_range_find_instr in H2.
      replace z with (1 + (z - 1)) in H by omega.
      rewrite find_instr_head in H by omega.
      unfold ret_ok in r. eapply r; eauto.
      replace (z - 1 + (k + 1)) with (z + k) by omega.
      assumption.
    - right. unfold not. intros.
      apply ret_ok_ind_case in H. congruence.
Defined.

Definition ensure_liveness(lm : liveness_map_t)(c : code) : res unit :=
  if ret_ok_dec lm c 1 then
    if entry_ok lm c then
      OK tt
    else
      Error (MSG "entry_ok failed" :: nil)
  else
    Error (MSG "ret_ok failed" :: nil).

Definition ent_ok (lm : liveness_map_t)(c : code) : Prop :=
  forall p,
    In p (ZMap.get 0 lm) ->
    In p (regs_live_across_call ++ parameter_regs).

Lemma entry_ent_ok :
  forall lm c,
    entry_ok lm c = true ->
    ent_ok lm c.
Proof.
  intros. unfold entry_ok in H.
  break_match_hyp; inv H.
  unfold ent_ok. intros. apply (i p).
  assumption.
Qed.

Lemma ensure_liveness_sound :
  forall lm c,
    ensure_liveness lm c = OK tt ->
    (ent_ok lm c /\ ret_ok lm c 1).
Proof.
  intros. unfold ensure_liveness in H.
  repeat break_match_hyp; inv H.
  apply entry_ent_ok in Heqb.
  auto.
Qed.



Fixpoint ensure_liveness_prog (l : list (ident * globdef fundef unit)) : res unit :=
  match l with
    | nil => OK tt
    | (_,Gfun (Internal (mkfunction _ c))) :: l' => 
      match find_liveness c with
        | Some lm =>
          match ensure_liveness lm c with
            | OK _ => ensure_liveness_prog l'
            | Error x => Error x
          end
        | None => Error (MSG "find_liveness didn't reach fixed point" :: nil)
      end
    | (_,Gfun (External ef)) :: l' => ensure_liveness_prog l'
    | (_,Gvar _) :: l' => ensure_liveness_prog l'
  end.


Lemma ensure_liveness_prog_sound :
  forall (p : Asm.program),
    ensure_liveness_prog (prog_defs p) = OK tt ->
    forall c,
      code_of_prog c p ->
      exists lm,
        find_liveness c = Some lm /\ ensure_liveness lm c = OK tt.
Proof.
  intro p. destruct p. induction prog_defs; intros.
  * unfold code_of_prog in H0. simpl in H0. repeat break_exists. inv H0.
  * unfold code_of_prog in H0.
    simpl in H0. repeat break_exists. destruct H0.
    subst a. simpl in H. repeat break_match_hyp; inv H. destruct u.
    eexists; split; eauto. congruence.
    unfold code_of_prog in IHprog_defs. simpl in IHprog_defs.
    assert (exists b s, In (b, Gfun (Internal (mkfunction s c))) prog_defs) by eauto.
    app IHprog_defs H1.
    simpl in H. 
    repeat break_match_hyp; inv H; reflexivity.
Qed.
    
