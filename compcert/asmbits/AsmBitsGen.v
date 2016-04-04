Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Memdata.
Require Import Op.
Require Import Locations.
Require Import Asm.
Require Import Zlen.
Require Import Globalenvs.

Require Import AsmBits.
Require Import Asm2Bits.


Open Local Scope string_scope.
Open Local Scope error_monad_scope.

Definition ident_eqdec:
  forall (i1 i2: ident), {i1 = i2} + {i1 <> i2}.
Proof.
  decide equality.
Defined.

Definition is_nonempty_fun_dec:
  forall id p, {is_nonempty_fun id p} + {~ is_nonempty_fun id p}.
Proof.
  intros. unfold is_nonempty_fun. destruct p; simpl.
  induction prog_defs; simpl; auto.
  left. intros. inversion H.
  destruct IHprog_defs.
  - destruct a. destruct (ident_eqdec i id); subst.
    + destruct g eqn:?.
      * destruct f eqn:?. destruct (fn_code f0) eqn:?.
        right. subst. intro. specialize (H (Gfun (Internal f0))).
        exploit H. left. reflexivity. intros.
        destruct H0. destruct H0. inversion H0.
        subst. congruence.
        left. intros.
        simpl in H. destruct H. inv H.
        exists (Internal f0). split; eauto.
        rewrite Heqc. congruence.
        eapply e in H. destruct H. destruct H.
        subst. exists x0. split; eauto.
        left. intros.
        simpl in H. destruct H. inversion H. subst.
        exists (External e0). split; auto.
        eapply e in H. destruct H.
        destruct H. subst.
        exists x0. split; auto.
      * right; intro. specialize (H (Gvar v)).
        edestruct H; eauto.        
        destruct H0. congruence.
    + left; intros. destruct H; [congruence|].
      eapply e; eauto.
  - right; intro.
    apply n; intros.
    apply H; auto.
Qed.

Require Import PeekTactics.

Fixpoint pfundefs_aux (l: list (ident * globdef fundef unit)) : list fundef :=
  match l with
    | nil => nil
    | (_, Gfun f) :: l' => f :: pfundefs_aux l'
    | _ :: l' => pfundefs_aux l'
  end.

Definition pfundefs (p: program) : list fundef :=
  pfundefs_aux (prog_defs p).

Definition forall_fundef (P: fundef -> Prop) (p: program) :=
  Forall P (pfundefs p).

Fixpoint pcodes_aux (l: list (ident * globdef fundef unit)) : list code :=
    match l with
    | nil => nil
    | (_, Gfun (Internal f)) :: l' => fn_code f :: pcodes_aux l'
    | _ :: l' => pcodes_aux l'
  end.

Definition pcodes (p: program) : list code :=
  pcodes_aux (prog_defs p).

Definition forall_code (P: code -> Prop) (p: program) :=
  Forall P (pcodes p).

Definition forall_instr (P: instruction -> Prop) (p: program) :=
  Forall (Forall P) (pcodes p).

Definition Forall_dec:
  forall (T: Type)
         (P: T -> Prop)
         (P_dec: forall t, {P t} + {~ P t})
         (l: list T),
    {Forall P l} + {~ Forall P l}.
Proof.
  intros T P P_dec l.
  induction l; simpl; auto.
  destruct IHl.
  - destruct (P_dec a).
    + left; auto.
    + right; intro.
      inversion H; contradiction.
  - right; intro.
    inversion H; contradiction.
Qed.

Definition forall_instr_dec:
  forall (P: instruction -> Prop)
         (P_dec: forall i, {P i} + {~ P i})
         (p: program),
    {forall_instr P p} + {~ forall_instr P p}.
Proof.
  unfold forall_instr; intros.
  apply Forall_dec.
  apply Forall_dec.
  exact P_dec.
Qed.

(* Definition wf_addrmode (p: program) (a: addrmode) : Prop := *)
(*   well_formed_addrmode a p. *)

(* Definition wf_addrmode_dec: *)
(*   forall p a, *)
(*     {wf_addrmode p a} + {~ wf_addrmode p a}. *)
(* Proof. *)
(*   unfold wf_addrmode, well_formed_addrmode. intros p a. *)
(*   destruct a as [base ofs const]. destruct const; auto. *)
(*   destruct p0; simpl. *)
(*   destruct (in_dec ident_eqdec i (prog_defs_names p)). *)
(*   - destruct (Z_le_dec 0 (Int.unsigned i0)). *)
(*     + destruct (Z_lt_dec (Int.unsigned i0) (global_size i p)). *)
(*       * left; auto.  *)
(*       * right; intro. apply n; apply H; auto. *)
(*     + right; intro. apply n. *)
(*       specialize (H i1). destruct H. *)
(*       exact H. *)
(*   - left; intros; contradiction. *)
(* Qed. *)

(* Definition wf_lea (p: program) (i: instruction) : Prop := *)
(*   match i with *)
(*     | Plea r a => wf_addrmode p a *)
(*     | _ => True *)
(*   end. *)

(* Definition wf_lea_dec: *)
(*   forall p i, *)
(*     {wf_lea p i} + {~ wf_lea p i}. *)
(* Proof. *)
(*   intros p i. *)
(*   destruct i; simpl; auto. *)
(*   apply wf_addrmode_dec. *)
(* Qed. *)

(* Definition all_lea_wf (p: program) := *)
(*   forall_instr (wf_lea p) p. *)

(* Definition all_lea_wf_dec: *)
(*   forall p, *)
(*     {all_lea_wf p} + {~ all_lea_wf p}. *)
(* Proof. *)
(*   unfold all_lea_wf; intros. *)
(*   apply forall_instr_dec. *)
(*   apply wf_lea_dec. *)
(* Qed. *)

Require Import ProgPropDec.

Lemma code_of_prog_in_pcodes:
  forall c p,
    code_of_prog c p ->
    In c (pcodes p).
Proof.
  unfold code_of_prog, pcodes; intros.
  repeat break_exists. destruct p; simpl in *.
  induction prog_defs; simpl in *; auto.
  destruct H; subst; simpl in *; auto.
  apply IHprog_defs in H.
  destruct a.
  destruct g; simpl in *; auto.
  destruct f; simpl in *; auto.
Qed.

Lemma in_pcodes_code_of_prog:
  forall c p,
    In c (pcodes p) ->
    code_of_prog c p.
Proof.
  unfold code_of_prog, pcodes; intros.
  destruct p; simpl in *.
  induction prog_defs; simpl in *; auto.
  - contradiction.
  - destruct a. destruct g.
    + destruct f. simpl in H.
      * destruct H; subst.
        destruct f; simpl in *.
        exists i; exists fn_sig; auto.
        apply IHprog_defs in H.
        repeat break_exists.
        exists x; exists x0; auto.
      * apply IHprog_defs in H.
        repeat break_exists.
        exists x; exists x0; auto.
    + apply IHprog_defs in H.
      repeat break_exists.
      exists x; exists x0; auto.
Qed.

Lemma find_instr_in_code:
  forall c z i,
    find_instr z c = Some i ->
    In i c.
Proof.
  induction c; simpl; intros; auto.
  - congruence.
  - destruct (zeq z 0); subst.
    + inv H; auto.
    + apply IHc in H; auto.
Qed.


Lemma find_instr_ge_0:
  forall c z i,
    find_instr z c = Some i ->
    z >= 0.
Proof.
  induction c; simpl; intros; auto.
  - congruence.
  - destruct (zeq z 0); subst.
    + omega.
    + apply IHc in H. omega.
Qed.

Lemma in_code_find_instr:
  forall c i,
    In i c ->
    exists z, find_instr z c = Some i.
Proof.
  induction c; simpl; intros; auto.
  - contradiction.
  - inv H.
    + exists 0. rewrite zeq_true; auto.
    + apply IHc in H0. break_exists.
      remember (find_instr_ge_0 _ _ _ H) as Foo; clear HeqFoo.
      exists (x + 1). destruct (zeq (x + 1) 0); subst.
      * exfalso; omega.
      * replace (x + 1 - 1) with x by omega; auto.
Qed.
  
Lemma forall_instr_instr_of_prog:
  forall (P: instruction -> Prop)
         (p: program),
    forall_instr P p ->
    forall i, instr_of_prog i p -> P i.
Proof.
  intros. inversion H0.
  break_exists; break_and.
  unfold forall_instr in H.
  rewrite Forall_forall in H.
  remember (H x0) as Foo; clear HeqFoo.
  assert (In x0 (pcodes p)). apply code_of_prog_in_pcodes; auto.
  apply Foo in H3. rewrite Forall_forall in H3.
  assert (In i x0). apply find_instr_in_code in H2; auto.
  apply H3 in H4; auto.
Qed.


Lemma instr_of_prog_forall_instr:
  forall (P: instruction -> Prop)
         (p: program),
    (forall i, instr_of_prog i p -> P i) ->
    forall_instr P p.
Proof.
  intros. unfold forall_instr.
  rewrite Forall_forall. intros.
  rewrite Forall_forall. intros.
  apply H. unfold instr_of_prog.
  apply in_pcodes_code_of_prog in H0.
  apply in_code_find_instr in H1.
  repeat break_exists.
  exists x1; exists x; auto.
Qed.

(* Definition all_addrmode_wf_dec: *)
(*   forall p, *)
(*     {all_lea_well_formed p} + {~ all_lea_well_formed p}. *)
(* Proof. *)
(*   intros. destruct (all_lea_wf_dec p). *)
(*   - left. unfold all_lea_wf, all_lea_well_formed in *. *)
(*     intros; eapply forall_instr_instr_of_prog in a; eauto. *)
(*     auto. *)
(*   - right; intro; apply n. *)
(*     unfold all_lea_wf, all_lea_well_formed in *. *)
(*     apply instr_of_prog_forall_instr; intros. *)
(*     destruct i; simpl; auto. *)
(*     unfold wf_addrmode. apply H with (r := rd); auto. *)
(* Qed. *)


Definition wf_annot_arg (p: program) (aa: annot_arg preg) :=
  well_formed_annot_arg aa p.

Definition wf_annot_arg_dec:
  forall p aa, {wf_annot_arg p aa} + {~ wf_annot_arg p aa}.
Proof.
  intros. unfold wf_annot_arg, well_formed_annot_arg.
  induction aa; simpl; auto.
  - destruct (in_dec ident_eqdec id (prog_defs_names p)).
    + destruct (Z_le_dec 0 (Int.unsigned ofs)).
      * { destruct (Z_lt_dec (Int.unsigned ofs) (Asm2Bits.global_size id p)).
          - left; intros; auto. 
          - right; intro; apply n.
            apply H in i.
            omega.
        }
      * right; intro; apply n.
        apply H in i. omega.
    + left; intros; congruence.
  - intuition.
Qed.

Definition wf_pannot (p: program) (i: instruction) : Prop :=
  match i with
    | Pannot e l => Forall (wf_annot_arg p) l
    | _ => True
  end.

Definition wf_pannot_dec:
  forall p i,
    {wf_pannot p i} + {~ wf_pannot p i}.
Proof.
  intros p i.
  destruct i; simpl; auto.
  induction args; simpl; auto.
  destruct IHargs.
  - destruct (wf_annot_arg_dec p a).
    + left; auto.
    + right; intro; apply n.
      inv H; auto.
  - right; intro; apply n.
    inv H; auto.
Qed.

Definition all_pannot_wf (p: program) :=
  forall_instr (wf_pannot p) p.

Definition all_pannot_wf_dec:
  forall p,
    {all_pannot_wf p} + {~ all_pannot_wf p}.
Proof.
  unfold all_pannot_wf; intros.
  apply forall_instr_dec.
  apply wf_pannot_dec.
Qed.

Definition all_annot_wf_dec:
  forall p, {all_annot_well_formed p} + {~ all_annot_well_formed p}.
Proof.
  intros. destruct (all_pannot_wf_dec p).
  - left. unfold all_annot_well_formed, all_pannot_wf in *.
    intros; eapply forall_instr_instr_of_prog in a; eauto.
    unfold wf_pannot in a. rewrite Forall_forall in a.
    unfold wf_annot_arg in a. apply a; auto.
  - right; intro; apply n.
    unfold all_annot_well_formed, all_pannot_wf in *.
    apply instr_of_prog_forall_instr; intros.
    destruct i; simpl; auto.
    rewrite Forall_forall; intros.
    unfold wf_annot_arg. eapply H; eauto.
Qed.

Definition init_data_eqdec:
  forall (id1 id2: init_data),
    {id1 = id2} + {id1 <> id2}.
Proof.
  decide equality.
  apply Int.eq_dec.
  apply Int.eq_dec.
  apply Int.eq_dec.
  apply Int64.eq_dec.
  apply Float32.eq_dec.
  apply Float.eq_dec.
  apply Z_eq_dec.
  apply Int.eq_dec.
  apply ident_eqdec.
Qed.

(* Definition wf_init_data_dec: *)
(*   forall p a, {wf_init_data p a} + {~ wf_init_data p a}. *)
(* Proof. *)
(*   unfold wf_init_data; intros. *)
(*   destruct a; auto. *)
(*   destruct (Z_le_dec 0 (Int.unsigned i0)). *)
(*   - destruct (Z_le_dec (Int.unsigned i0) (global_size i p)). *)
(*     + auto. *)
(*     + right; intro; apply n. omega. *)
(*   - right; intro; apply n. omega. *)
(* Qed. *)

(* Definition wf_idg_dec: *)
(*   forall p idg, {wf_idg p idg} + {~ wf_idg p idg}. *)
(* Proof. *)
(*   unfold wf_idg, wf_globdef, wf_gvar. *)
(*   intros. destruct idg; destruct g; simpl; auto. *)
(*   destruct v; simpl. induction gvar_init; simpl. *)
(*   - left; intros. inv H. *)
(*   - destruct IHgvar_init. *)
(*     + destruct (wf_init_data_dec p a). *)
(*       * left; intros. destruct H; subst; auto. *)
(*       * right; intro; apply n; auto. *)
(*     + right; intro; apply n; intros. *)
(*       apply H; auto. *)
(* Qed. *)

(* Definition defs_wf_dec: *)
(*   forall p ds, {wf_defs p ds} + {~ wf_defs p ds}. *)
(* Proof. *)
(*   unfold wf_defs; intros. *)
(*   induction ds; simpl. *)
(*   - left; intros; contradiction. *)
(*   - destruct IHds. *)
(*     + destruct (wf_idg_dec p a). *)
(*       * left; intros. destruct H; subst; auto. *)
(*       * right; intro; apply n; auto. *)
(*     + right; intro; apply n; intros. *)
(*       apply H; auto. *)
(* Qed. *)

Definition global_nonempty_l_dec :
  forall l,
    { forall (y : ident) x, In (y,x) l -> global_nonempty x } + { ~ (forall (y : ident) x, In (y,x) l -> global_nonempty x ) }.
Proof.
  induction l; intros.
  left. intros. simpl in *. inv_false.
  destruct IHl.
  destruct a. subst.
  destruct g0 eqn:?.
  destruct f. destruct (zle (Zlen.zlen (fn_code f)) 0).
  right. intro. specialize (H i g0). subst g0.
  simpl in H. exploit H. left. reflexivity.
  intro. omega.
  left. intros. simpl in H. break_or.
  inv H0. 
  simpl. assumption.
  eapply g; eauto.
  left. intros. simpl in H.
  subst. break_or. inv H0.
  simpl. exact I.
  eapply g; eauto.
  destruct (zle (Globalenvs.Genv.init_data_list_size (gvar_init v)) 0).
  right.
  intro.  exploit H. simpl. left. reflexivity.
  intros. simpl in H0. omega.
  left. intros. simpl in H. repeat break_or.
  inv H0.
  simpl. assumption.
  eapply g; eauto.
  right. intro. apply n. intros. eapply H.
  simpl. right. eassumption.
Defined.
  
Definition globals_nonempty_dec :
  forall p,
    { globals_nonempty p } + { ~ globals_nonempty p}.
Proof.
  intros.
  unfold globals_nonempty.
  eapply global_nonempty_l_dec.
Qed.

Definition transf_program (p: program) : res program :=
  if all_allocframes_positive_prog_dec p then
    if list_norepet_dec ident_eqdec (prog_defs_names p) then
      if is_nonempty_fun_dec (prog_main p) p then
        if all_annot_wf_dec p then
          if no_PC_overflow_prog_dec p then
            OK p
          else
            Error (msg "PC overflow")
        else
          Error (msg "not all annots well formed")
      else
        Error (msg "main not a nonempty fn")
    else
      Error (msg "name repeated")
  else
    Error (msg "non-positive allocframe").

Require Import PeekTactics.

Lemma transf_inv:
  forall p p',
    transf_program p = OK p' ->
    all_allocframes_positive p /\
    list_norepet (prog_defs_names p) /\
    is_nonempty_fun (prog_main p) p /\
    all_annot_well_formed p /\
    no_PC_overflow_prog p /\
    p = p'.
Proof.
  unfold transf_program; intros.
  repeat break_if_hyp; try discriminate.
  intuition. 
  inv H; auto.
Qed.

