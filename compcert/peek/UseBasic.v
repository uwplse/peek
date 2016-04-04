Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Axioms.
Require Import Floats.
Require Import Asm.
Require Import Values.
Require Import Memory.

Require Import PeekLib.
Require Import AsmCallingConv.
Require Import AsmBits.
Require Import PeekTactics.
Require Import MemoryAxioms.
Require Import PregTactics.
Require Import ValEq.
Require Import MemEq.
Require Import MemBits.

Definition use_addr(a : addrmode):list preg :=
  match a with
    | Addrmode (Some ir1) (Some (ir2,_)) _ => IR ir1 :: IR ir2 :: nil
    | Addrmode _ (Some (ir2,_)) _ => IR ir2 :: nil
    | Addrmode (Some ir1) _ _ => IR ir1 :: nil
    | Addrmode _ _ _ => nil
  end.


Definition efres (ef : external_function)(res : list preg) : list preg :=
  match sig_res (ef_sig ef) with
    | Some Tlong => tail (tail res)
    | _ => tail res
  end.

Fixpoint get_annot_preg (a : annot_arg preg):list preg :=
  match a with
    | AA_base x => x :: nil
    | AA_longofwords a1 a2 => get_annot_preg a1 ++ get_annot_preg a2
    | _ => nil
  end.

Definition get_annot_pregs  :=
  flat_map get_annot_preg.

(* given an instruction, return a pair of lists *)
(* first is regs used, second is regs defined *)

Definition use_def'(i : instruction):(list preg) * (list preg) :=
  match i with
  | Pmov_rr rd r1 => (IR r1 :: nil, IR rd :: nil)
  | Pmov_ri rd n => (nil, IR rd :: nil)
  | Pmov_ra rd id => (nil, IR rd :: flags)
  | Pmov_rm rd a => (use_addr a, IR rd :: flags)
  | Pmov_mr a r1 => (IR r1 :: (use_addr a), flags)
  | Pmov_mi a n => (use_addr a, flags)
  | Pmovsd_ff rd r1 => (FR r1 :: nil, FR rd :: nil)
  | Pmovsd_fi rd n => (nil, FR rd :: nil)
  | Pmovsd_fm rd a => (use_addr a, FR rd :: flags)
  | Pmovsd_mf a r1 => (FR r1 :: (use_addr a), flags)
  | Pmovss_fi rd n => (nil, FR rd :: nil)
  | Pmovss_fm rd a => (use_addr a, FR rd :: flags)
  | Pmovss_mf a r1 => (FR r1 :: (use_addr a), flags)
  | Pfldl_m a => (use_addr a, ST0 :: flags)
  | Pflds_m a => (use_addr a, ST0 :: flags)
  | Pfstpl_m a => (ST0 :: (use_addr a), ST0 :: flags)
  | Pfstps_m a => (ST0 :: (use_addr a), ST0 :: flags)
  | Pxchg_rr r1 r2 => (IR r1 :: IR r2 :: nil, IR r1 :: IR r2 :: nil)
  | Pmovups_rm brd a =>
    let (lrd,hrd) := split_big_freg brd in
    (use_addr a, FR lrd :: FRH hrd :: flags)
   | Pmovups_mr a brs =>
    let (lrs,hrs) := split_big_freg brs in
    (FR lrs :: FRH hrs :: use_addr a, flags)
  (** Moves with conversion *)
  | Pmovb_mr a r1 => (IR r1 :: (use_addr a), flags)
  | Pmovw_mr a r1 => (IR r1 :: (use_addr a), flags)
  | Pmovzb_rr rd r1 => (IR r1 :: nil, IR rd :: nil)
  | Pmovzb_rm rd a => (use_addr a, IR rd :: flags)
  | Pmovsb_rr rd r1 => (IR r1 :: nil, IR rd :: nil)
  | Pmovsb_rm rd a => (use_addr a, IR rd :: flags)
  | Pmovzw_rr rd r1 => (IR r1 :: nil, IR rd :: nil)
  | Pmovzw_rm rd a => (use_addr a, IR rd :: flags)
  | Pmovsw_rr rd r1 => (IR r1 :: nil, IR rd :: nil)
  | Pmovsw_rm rd a => (use_addr a, IR rd :: flags)
  | Pcvtsd2ss_ff rd r1 => (FR r1 :: nil, FR rd :: nil)
  | Pcvtss2sd_ff rd r1 => (FR r1 :: nil, FR rd :: nil)
  | Pcvttsd2si_rf rd r1 => (FR r1 :: nil, IR rd :: nil)
  | Pcvtsi2sd_fr rd r1 => (IR r1 :: nil, FR rd :: nil)
  | Pcvttss2si_rf rd r1 => (FR r1 :: nil, IR rd :: nil)
  | Pcvtsi2ss_fr rd r1 => (IR r1 :: nil, FR rd :: nil)
  (** Integer arithmetic *)
  | Plea rd a => (use_addr a, IR rd :: nil)
  | Pneg rd => (IR rd :: nil, IR rd :: flags)
  | Pnot rd => (IR rd :: nil, IR rd :: flags)
  | Padd_rr rd r1 => (IR r1 :: IR rd :: nil, IR rd :: flags)
  | Padd_ri rd _ => (IR rd :: nil, IR rd :: flags)
  | Pdec rd => (IR rd :: nil, IR rd :: flags)
  | Pinc rd => (IR rd :: nil, IR rd :: flags)
  | Pimul_r r1 => (IR EAX :: IR EDX :: IR r1 :: nil, IR EAX :: IR EDX :: flags)
  | Pmul_r r1 =>  (IR EAX :: IR EDX :: IR r1 :: nil, IR EAX :: IR EDX :: flags)
  | Psub_rr rd r1 => (IR r1 :: IR rd :: nil, IR rd :: flags)
  | Psub_ri rd _ => (IR rd :: nil, IR rd :: flags)
  | Pimul_rr rd r1 => (IR r1 :: IR rd :: nil, IR rd :: flags)
  | Pimul_ri rd n => (IR rd :: nil, IR rd :: flags)
  | Pdiv r1 => (IR EAX :: IR r1 :: nil, IR EAX :: IR EDX :: flags)
  | Pidiv r1 => (IR EAX :: IR r1 :: nil, IR EAX :: IR EDX :: flags)
  | Pand_rr rd r1 => (IR rd :: IR r1 :: nil, IR rd :: flags)
  | Pand_ri rd n => (IR rd :: nil, IR rd :: flags)
  | Por_rr rd r1 => (IR rd :: IR r1 :: nil, IR rd :: flags)
  | Por_ri rd n => (IR rd :: nil, IR rd :: flags)
  | Pxor_r rd => (nil, IR rd :: flags)
  | Pxor_rr rd r1 => (IR rd :: IR r1 :: nil, IR rd :: flags)
  | Pxor_ri rd n => (IR rd :: nil, IR rd :: flags)
  | Psal_rcl rd => (IR rd :: IR ECX :: nil, IR rd :: flags)
  | Psal_ri rd n => (IR rd :: nil, IR rd :: flags)
  | Pshr_rcl rd => (IR rd :: IR ECX :: nil, IR rd :: flags)
  | Pshr_ri rd n => (IR rd :: nil, IR rd :: flags)
  | Psar_rcl rd => (IR rd :: IR ECX :: nil, IR rd :: flags)
  | Psar_ri rd n => (IR rd :: nil, IR rd :: flags)
  | Pshld_ri rd r1 n => (IR rd :: IR r1 :: nil, IR rd :: flags)
  | Pror_ri rd n => (IR rd :: nil, IR rd :: flags)
  | Pcmp_rr r1 r2 => (IR r1 :: IR r2 :: nil, flags)
  | Pcmp_ri r1 n => (IR r1 :: nil, flags)
  | Ptest_rr r1 r2 => (IR r1 :: IR r2 :: nil, flags)
  | Ptest_ri r1 n => (IR r1 :: nil, flags)
  | Pcmov c rd r1 => (IR rd :: IR r1 :: flags, IR rd :: nil)
  | Psetcc c rd => (flags, IR rd :: nil)
  (** Arithmetic operations over double-precision floats *)
  | Paddd_ff rd r1 => (FR r1 :: FR rd :: nil, FR rd :: nil)
  | Paddpd_ff rd r1 =>
    let (ad,bd) := split_big_freg rd in
    let (a1,b1) := split_big_freg r1 in
    (FR ad :: FRH bd :: FR a1 :: FRH b1 :: nil, FR ad :: FRH bd :: nil)
  | Pmulpd_ff rd r1 =>
    let (ad,bd) := split_big_freg rd in
    let (a1,b1) := split_big_freg r1 in
    (FR ad :: FRH bd :: FR a1 :: FRH b1 :: nil, FR ad :: FRH bd :: nil)
  | Psubd_ff rd r1 => (FR r1 :: FR rd :: nil, FR rd :: nil)
  | Pmuld_ff rd r1 => (FR r1 :: FR rd :: nil, FR rd :: nil)
  | Pdivd_ff rd r1 => (FR r1 :: FR rd :: nil, FR rd :: nil)
  | Pnegd rd => (FR rd :: nil, FR rd :: nil)
  | Pabsd rd => (FR rd :: nil, FR rd :: nil)
  | Pcomisd_ff r1 r2 => (FR r1 :: FR r2 :: nil, flags)
  | Pxorpd_f rd => (nil, FR rd :: flags)
  (** Arithmetic operations over single-precision floats *)
  | Padds_ff rd r1 => (FR r1 :: FR rd :: nil, FR rd :: nil)
  | Psubs_ff rd r1 => (FR r1 :: FR rd :: nil, FR rd :: nil)
  | Pmuls_ff rd r1 => (FR r1 :: FR rd :: nil, FR rd :: nil)
  | Pdivs_ff rd r1 => (FR r1 :: FR rd :: nil, FR rd :: nil)
  | Pnegs rd => (FR rd :: nil, FR rd :: nil)
  | Pabss rd => (FR rd :: nil, FR rd :: nil)
  | Pcomiss_ff r1 r2 => (FR r1 :: FR r2 :: nil, flags)
  | Pxorps_f rd => (nil, FR rd :: flags)
  (** Branches and calls *)
  | Pjmp_l lbl => (nil, nil)
  | Pjcc cond lbl => (flags, nil)
  | Pjcc2 cond1 cond2 lbl => (flags, nil)
  | Pjmptbl r tbl => (IR r :: nil, nil)
  (* In order to model calls correctly *)
  (* return has no successors *)
  (* return uses all callee save registers *)
  (* return defines nothing, as it has no succs, doesn't matter *)
  (* ensuring that they are all live at exit *)
  (* | Pret => (regs_live_across_call ++ return_regs, RA :: nil) *)
  (* call defines all caller save registers *)
  (* call uses any args *)
  (* | Pcall_s id => (regs_live_across_call, RA :: regs_dead_across_call ++ return_regs) *)
  (* | Pcall_r r => (IR r :: regs_live_across_call, RA :: regs_dead_across_call ++ return_regs) *)
  (* reg jump is tail call *)
  (* thus no successors *)
  (* and uses all callee save regs *)
  (* since is effectively return *)
  (* | Pjmp_s id => (regs_live_across_call, regs_dead_across_call ++ return_regs) *)
  (* | Pjmp_r r => (IR r :: regs_live_across_call, regs_dead_across_call ++ return_regs) *)
  (* call and return liveness is not handled here *)
  | Pret _ => (nil,nil)
  | Pcall_s id _ => (nil,nil)
  | Pcall_r r _ => (nil,nil)
  | Pjmp_s id _ => (nil,nil)
  | Pjmp_r r _ => (nil,nil)
  (** Saving and restoring registers *)
  | Pmov_rm_a rd a => (use_addr a, IR rd :: flags)
  | Pmov_mr_a a r1 => (IR r1 :: (use_addr a), flags)
  | Pmovsd_fm_a rd a => (use_addr a, FR rd :: flags)
  | Pmovsd_mf_a a r1 => (FR r1 :: (use_addr a), flags)
  (** Pseudo-instructions *)
  | Plabel lbl => (nil, nil)
  | Pallocframe sz ofs_ra ofs_link => (IR ESP :: RA :: nil, IR EDX :: IR ESP :: nil)
  | Pfreeframe sz ofs_ra ofs_link => (IR ESP :: nil, IR ESP :: RA :: nil)
  | Pbuiltin ef args res => (args ++ (efres ef res), flags ++ res ++ (map preg_of (Machregs.destroyed_by_builtin ef)))
  | Pannot ef args => (IR ESP :: get_annot_pregs args, nil)
  | Pnop => (nil, nil)
  end.

(* every instruction uses and defines the PC *)
Definition use_def (i : instruction) : (list preg) * (list preg) :=
  match use_def' i with
    | (u,d) => (PC :: u, PC :: d)
  end.

Definition use (i : instruction) : list preg :=
  fst (use_def i).

Definition def (i : instruction) : list preg :=
  snd (use_def i).


Lemma use_addr_correct_no_ptr:
  forall s1 s2 t ge a,
    (forall p, In p (use_addr a) ->
               val_eq (s1 p) (s2 p)) ->
    val_eq (eval_addrmode_no_ptr ge t a s1) (eval_addrmode_no_ptr ge t a s2).
Proof.
  intros.
  unfold val_eq.
  unfold eval_addrmode_no_ptr.
  
  destruct a. simpl.
  unfold Val.add.
    
  unfold use_addr in H.
  destruct base; destruct ofs;
  try destruct p;
  try name (H i) Hi;
  try name (H i0) Hi0;
  clear H;
  repeat match goal with
           | [ H : ?A -> ?B |- _ ] => assert (B ) by (apply H; simpl; intuition); clear H
         end;
  
  unfold val_eq in *;
    repeat break_match_hyp;
    try inv_false;
    intros;
    try congruence;
    simpl;
    try solve [repeat (break_match; intros; try congruence);
                unfold Val.mul in *; break_match_hyp; congruence].
Qed.
  
(* Lemma use_addr_correct: *)
(*   forall s1 s2 ge a, *)
(*     (forall p, In p (use_addr a) -> *)
(*                val_eq (s1 p) (s2 p)) -> *)
(*     val_eq (eval_addrmode ge a s1) (eval_addrmode ge a s2). *)
(* Proof. *)
(*   intros. *)
(*   unfold val_eq. *)
(*   unfold eval_addrmode. *)
  
(*   destruct a. simpl. *)
(*   unfold Val.add. *)
    
(*   unfold use_addr in H. *)
(*   destruct base; destruct ofs; *)
(*   try destruct p; *)
(*   try name (H i) Hi; *)
(*   try name (H i0) Hi0; *)
(*   clear H; *)
(*   repeat match goal with *)
(*            | [ H : ?A -> ?B |- _ ] => assert (B ) by (apply H; simpl; intuition); clear H *)
(*          end; *)
  
(*   unfold val_eq in *; *)
(*     repeat break_match_hyp; *)
(*     try inv_false; *)
(*     intros; *)
(*     try congruence; *)
(*     simpl; *)
(*     try solve [repeat (break_match; intros; try congruence); *)
(*                 unfold Val.mul in *; break_match_hyp; congruence]. *)

(*   repeat (break_match; intros; try congruence); *)
(*     unfold Val.mul in *; repeat break_match_hyp; try congruence. *)
  
(*   intros. *)
(*   eapply val_eq_or. *)
(*   unfold eval_addrmode_no_ptr. *)

(*   destruct a. simpl. *)
(*   unfold use_addr in H. *)
(*   destruct base; destruct ofs; *)
(*   try destruct p; *)
(*   try name (H i) Hi; *)
(*   try name (H i0) Hi0; *)
(*   clear H; *)
(*   repeat match goal with *)
(*            | [ H : ?A -> ?B |- _ ] => assert (B ) by (apply H; simpl; intuition); clear H *)
(*          end; *)
(*   repeat match goal with *)
(*            | [ H : val_eq _ _ |- _ ] => rewrite val_eq_or in H *)
(*          end; *)
(*   repeat break_or; *)

(*   repeat match goal with *)
(*            | [ H : _ = _ |- _ ] => progress rewrite H *)
(*          end; *)
(*   try solve [simpl; left; *)
(*              try destruct (Int.eq i1 Int.one); *)
(*              simpl; *)
(*              unfold Val.add; *)
(*              simpl; *)
(*              repeat break_match; *)
(*              simpl; *)
(*              congruence]; *)

(*   right; try reflexivity. *)
(* Qed. *)

Lemma use_addr_correct_bits:
  forall s1 s2 ge a t,
    (forall p, In p (use_addr a) ->
               val_eq (s1 p) (s2 p)) ->
    eval_addrmode_bits ge t a s1 = Vundef \/ eval_addrmode_bits ge t a s1 = eval_addrmode_bits ge t a s2.
Proof.
  intros.
  unfold eval_addrmode_bits.
  
  destruct a. simpl.
  unfold Val.add.
    
  unfold use_addr in H.
  destruct base; destruct ofs;
  try destruct p;
  try name (H i) Hi;
  try name (H i0) Hi0;
  clear H;
  repeat match goal with
           | [ H : ?A -> ?B |- _ ] => assert (B ) by (apply H; simpl; intuition); clear H
         end.
  
  unfold val_eq in *;
    repeat break_match_hyp;
    try inv_false;
    intros;
    try congruence;
    simpl;
    try solve [left; reflexivity];
  repeat (break_match; intros; try congruence);
    unfold Val.mul in *; repeat break_match_hyp;
    try solve [left; reflexivity];
    try solve [right; congruence].

    unfold val_eq in *;
    repeat break_match_hyp;
    try inv_false;
    intros;
    try congruence;
    simpl;
    try solve [left; reflexivity];
  repeat (break_match; intros; try congruence);
    unfold Val.mul in *; repeat break_match_hyp;
    try solve [left; reflexivity];
    try solve [right; congruence].

  unfold val_eq in *;
    repeat break_match_hyp;
    try inv_false;
    intros;
    try congruence;
    simpl;
    try solve [left; reflexivity];
  repeat (break_match; intros; try congruence);
    unfold Val.mul in *; repeat break_match_hyp;
    try solve [left; reflexivity];
    try solve [right; congruence].

  unfold Vzero.
  repeat (break_match; intros; try solve [left; congruence]);
    right; reflexivity.
  
  
Qed.

Lemma use_addr_eval_addrmode_bits :
  forall s1 s2 ge a t v,
    (forall p, In p (use_addr a) ->
               val_eq (s1 p) (s2 p)) ->
    v <> Vundef ->
    eval_addrmode_bits ge t a s1 = v ->
    eval_addrmode_bits ge t a s2 = v.
Proof.
  intros.
  
  app use_addr_correct_bits H.
  
  instantiate (2 := ge) in H.
  instantiate (1 := t) in H.
  rewrite H1 in H.
  break_or; congruence.
Qed.

Lemma eval_testcond_match:
  forall (s1 s2 : regset) c0,
    val_eq (s1 ZF) (s2 ZF) ->
    val_eq (s1 CF) (s2 CF) ->
    val_eq (s1 PF) (s2 PF) ->
    val_eq (s1 SF) (s2 SF) ->
    val_eq (s1 OF) (s2 OF) ->
    eval_testcond c0 s1 = None \/
    eval_testcond c0 s1 = eval_testcond c0 s2.
Proof.
  intros. unfold eval_testcond.
  eapply val_eq_or in H.
  eapply val_eq_or in H0.
  eapply val_eq_or in H1.
  eapply val_eq_or in H2.
  eapply val_eq_or in H3.
  repeat break_or;
    rewrite H0, H1, H2, H3, H4;
    repeat break_match;
    try (right; reflexivity);
    try (left; reflexivity).
Qed.

Lemma rs_replace :
  forall (rs rs' : preg -> Values.val) p,
    rs p = rs' p ->
    forall r v,
      (rs # r <- v) p = (rs' # r <- v) p.
Proof.
  intros. destruct (preg_eq p r).
  subst. repeat rewrite Pregmap.gss.
  reflexivity. repeat rewrite Pregmap.gso by congruence.
  assumption.
Qed.

Lemma use_addr_add :
  forall a p,
    In p (use_addr a) <-> (exists x, In p (use_addr (addr_add a x))).
Proof.
  split; intros.
  destruct a; unfold addr_add; unfold use_addr;
  destruct base; destruct const; destruct ofs;
  simpl in *; simpl; eauto;
  eexists;
  repeat break_let; try congruence;
  try find_inversion; eauto;
  exact 0.
  
  destruct a; unfold addr_add; unfold use_addr;
  destruct base; destruct const; destruct ofs;
  simpl in *; simpl; eauto;
  break_exists;
  repeat break_let; try congruence;
  try find_inversion; eauto.

  Grab Existential Variables.
  exact 0. exact 0.
  exact 0. exact 0.
Qed.

Lemma use_spec :
  forall ge s1 s1' s2 bits b z f s c i m1 m1' m2 md md',
    s1 PC = Values.Vint bits ->
    s2 PC = Values.Vint bits ->
    MemoryAxioms.psur md bits = Some (b,z) ->
    no_ptr_regs s1 ->
    no_ptr_regs s2 ->
    f = mkfunction s c ->
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    find_instr (Int.unsigned z) c = Some i ->
    (forall p,
       In p (use i) ->
       val_eq (s1 p) (s2 p)) ->
    exec_instr_bits ge md f i b s1 m1 = Nxt s1' m1' md' ->
    ~ is_call_return i ->
    mem_eq md m1 m2 ->
    (exists s2' m2', exec_instr_bits ge md f i b s2 m2 = Nxt s2' m2' md').
Proof.
  intros.

  rename H7 into Hreg_equiv.  
  
  (* this only gets proved by destructing the instruction *)
  (* hopefully this is the highest level thing that needs to *)
  
  destruct i; simpl in *;
  unfold exec_load_bits in *; unfold exec_store_bits in *;
  unfold exec_big_load_bits in *;
  unfold exec_big_store_bits in *;
  unfold goto_label_bits in *; unfold Mem.loadv in *; unfold storev_bits in *;
  repeat break_match_hyp;
  try state_inv;
  eauto;
  try congruence;
  try solve [
  match goal with
    | [ H : eval_addrmode_bits _ _ _ _ = Vptr _ _ |- _ ] =>
      app use_addr_eval_addrmode_bits H;
        try congruence;
        try rewrite H
    | [ |- _ ] => idtac
  end;
  match goal with
    | [ H : Mem.load _ _ _ _ = Some _ |- _ ] =>
      app eq_mem_load H
    | [ H : store_bits _ _ _ _ _ = Some _ |- _ ] =>
      app eq_mem_store H
    | [ |- _ ] => idtac
  end;
  repeat break_and;
  try collapse_match;
  eauto;
  try solve [
        edestruct (eval_testcond_match); try eapply Hreg_equiv;
        try prove_or_eq reflexivity;
        try match goal with
              | [ H : eval_testcond _ _ = Some _, H2 : eval_testcond _ _ = None |- _ ] =>
                erewrite H2 in H; congruence
              | [ |- _ ] => idtac
            end;
        match goal with
          | [ H : eval_testcond _ _ = eval_testcond _ _ , H2 : eval_testcond _ _ = _ |- _ ] =>
            rewrite <- H; rewrite H2
          | [ |- _ ] => idtac
        end;
        repeat break_match;
        eauto;
        match goal with
          | [ H : Vint _ = Vint _ |- _ ] => inv H
          | [ |- _ ] => idtac
        end;
        try unify_psur; try congruence;
        try (destruct (eval_testcond_match s1 s2 c1); try eapply Hreg_equiv; try prove_or_eq reflexivity; congruence)
        
        
      ];
  try solve [find_inversion; unify_psur; find_rewrite; find_rewrite; eauto]].
  * (* Pmov_mi *)
    
    erewrite use_addr_eval_addrmode_bits; eauto; try congruence.
    simpl.
    app_new eq_mem_store Heqo; try instantiate (1 := (Vint n)) in H4.
    break_and.
    rewrite H4.
    eauto.
    simpl.
    reflexivity.
  * (* Pmovups_rm *)
    app use_addr_eval_addrmode_bits Heqv0; try congruence.
    rewrite Heqv0.
    app use_addr_eval_addrmode_bits Heqv1; try congruence.
    rewrite Heqv1.
    app eq_mem_load Heqo. break_and. collapse_match.
    app eq_mem_load Heqo0. break_and. collapse_match.
    eexists. eexists.
    reflexivity.
    intros. apply Hreg_equiv.
    unfold use. unfold use_def.
    break_let. simpl.
    unfold use_def' in *. simpl in *.
    break_let. find_inversion. right.
    apex use_addr_add H8.

    intros. apply Hreg_equiv.
    unfold use. unfold use_def.
    break_let. simpl.
    unfold use_def' in *. simpl in *.
    break_let. find_inversion. right.
    assumption.
    
  * (* Pmovups_rm *)
    unfold Mem.storev in *.
    repeat break_match_hyp; try congruence.
    app use_addr_eval_addrmode_bits Heqv0; try congruence.
    rewrite Heqv0.
    app use_addr_eval_addrmode_bits Heqv; try congruence.
    rewrite Heqv.
    simpl.
    app eq_mem_store Heqo. break_and. 
    app eq_mem_store Heqo0. break_and.
    repeat eexists. rewrite H11.
    rewrite H14.
    reflexivity.
    eapply Hreg_equiv. unfold use. unfold use_def.
    break_let. simpl.
    simpl in Heqp0. break_let. inv Heqp0.
    inv Heqp.
    simpl. prove_or_eq reflexivity.
    eapply Hreg_equiv. unfold use. unfold use_def.
    break_let. simpl.
    simpl in Heqp0. break_let. inv Heqp0.
    inv Heqp.
    simpl. prove_or_eq reflexivity.
    intros.
    eapply Hreg_equiv. unfold use.
    unfold use_def. unfold use_def'.
    repeat break_let. inv Heqp0.
    simpl.
    right. right. right.
    apex use_addr_add H8.
    intros. eapply Hreg_equiv.
    unfold use. unfold use_def. unfold use_def'.
    repeat break_let; simpl. inv Heqp0.
    simpl. repeat right. eauto.
    
  * (* Pdiv *)
    assert (val_eq (s1 EAX) (s2 EAX)).
    eapply Hreg_equiv. prove_or_eq reflexivity.
    unfold Val.divu in *;
      unfold Val.modu in *;
      repeat break_match_hyp;
      try congruence;
      preg_case;
      try rewrite <- e in *;
      preg_simpl_hyp Heqv0;
      try congruence.
      repeat opt_inv.
      subst.

      rewrite <- Heqv1 in H4.
      repeat rewrite (val_eq_def _ _ Heqv1 _ H4) by congruence.
    assert (val_eq (s1 r1) (s2 r1)).
    eapply Hreg_equiv. prove_or_eq reflexivity.
    repeat rewrite (val_eq_def _ _ Heqv0 _ H7) by congruence.
    repeat rewrite Heqb0. eauto.
  * (* Pidiv *)
    assert (val_eq (s1 EAX) (s2 EAX)).
    eapply Hreg_equiv. prove_or_eq reflexivity.
    unfold Val.divs in *;
      unfold Val.mods in *;
      repeat break_match_hyp;
      try congruence;
      preg_case;
      try rewrite <- e in *;
      preg_simpl_hyp Heqv0;
      try congruence.
      repeat opt_inv.
      subst.

      rewrite <- Heqv1 in H4.
      repeat rewrite (val_eq_def _ _ Heqv1 _ H4) by congruence.
    assert (val_eq (s1 r1) (s2 r1)).
    eapply Hreg_equiv. prove_or_eq reflexivity.
    repeat rewrite (val_eq_def _ _ Heqv0 _ H7) by congruence.
    repeat rewrite Heqb0. eauto.

  * (* Pjmptbl *)

    rewrite (val_eq_def _ _ Heqv _); try congruence;
    try eapply Hreg_equiv; try prove_or_eq reflexivity.
    repeat collapse_match.
    eauto.
  * (* Pallocframe *)
    
    break_let.
    app eq_mem_alloc Heqp. break_and.
    rewrite H7 in Heqp0.
    inv Heqp0.
    find_rewrite.
    app eq_mem_store Heqo.
    break_and.
    collapse_match.
    app eq_mem_store Heqo0.
    break_and.
    collapse_match.
    eauto.

  * (* Pfreeframe *)
    rewrite (val_eq_def _ _ Heqv _); try congruence;
    try eapply Hreg_equiv; try prove_or_eq reflexivity.
    collapse_match.
    
    app eq_mem_load Heqo0. break_and. repeat collapse_match.
    app eq_mem_load Heqo2. break_and. repeat collapse_match.
    app eq_mem_free Heqo3. break_and. repeat collapse_match.
    eauto.
Qed.

Lemma or_nest_rewrite :
  forall A B C,
    B \/ C ->
    (A \/ B) \/ C.
Proof.
  intuition.
Qed.

Ltac destruct_or_left_preg :=
  match goal with
    | [ |- (?X = ?Y \/ _) \/ _ ] => destruct (preg_eq X Y); (try (left; left; assumption)); apply or_nest_rewrite
    | [ |- False \/ _ ] => right
  end.


Lemma def_spec :
  forall ge c i s1 m s1' m' md md' b,
    exec_instr_bits ge md c i b s1 m = Nxt s1' m' md' ->
    ~ is_call_return i ->
    (forall p, (In p (def i) \/ s1 p = s1' p)).
Proof.
  intros.  

  unfold def. unfold use_def. unfold snd.
  
  destruct i; simpl in *; 
  unfold not in *;
  try (specialize (H0 I); inv H0);
  unfold exec_load_bits in *; unfold exec_store_bits in *;
  unfold exec_big_load_bits in *; unfold exec_big_store_bits in *;
  unfold goto_label_bits in *;
  inversion H; unfold nextinstr_nf; unfold nextinstr;
  unfold undef_regs; unfold compare_ints; unfold compare_floats; unfold compare_floats32;
  repeat break_match_hyp;
  repeat state_inv;
  simpl;
  repeat destruct_or_left_preg;
  preg_simpl;
  try congruence;
  repeat break_match;
  preg_simpl;
  try congruence.
  
Qed.

Ltac destruct_or_hyp :=
  match goal with
    | [ H : _ \/ _  |- _ ] => destruct H
    | [ H : False |- _ ] => inversion H
  end.

Ltac or_refl :=
  match goal with
    | [ |- _ \/ _ ] => try (left; reflexivity); right
  end.

Ltac or_refl_assump :=
  match goal with
    | [ |- _ \/ _ ] => try (left; reflexivity); try (right; assumption); right
  end.



Ltac invert_outcomes :=
  repeat match goal with
           | [ H : Next _ _ = Next _ _ |- _ ] => inv H
         end.

Ltac unfold_semantics := unfold nextinstr_nf; unfold nextinstr; unfold undef_regs; unfold compare_ints; unfold compare_floats; unfold compare_floats32; unfold undef_regs.

Ltac easy_contra :=
  match goal with
    | [ H : Stuck = Next _ _ |- _ ] => inversion H
    | [ H : Next _ _ = Stuck |- _ ] => inversion H
    | [ |- _ ] => idtac
  end.

Ltac preg_map_equiv H1 P H2 :=
  repeat rewrite H1 by (simpl; subst; repeat or_refl);
  repeat rewrite P;
  repeat rewrite H1 by (simpl; subst; repeat or_refl);
  repeat break_match; try reflexivity;
  simpl in H2; repeat destruct_or_hyp; try congruence.

Ltac div_mod_simpl H1 P :=
  repeat match goal with
           | [ H : Pregmap.elt_eq _ _ = _ _ |- _ ] => rewrite H in *
           | [ H : Some _ = Some _ |- _ ] => inversion H; reflexivity
           | [ H : right _ = left _ |- _ ] => inversion H
           | [ H : left _ = right _ |- _ ] => inversion H
           | [ H : Values.Val.modu _ _ = Some _ |- _ ] => try rewrite H1 in H by (simpl; repeat or_refl); rewrite P in H; break_match_hyp
           | [ H : Values.Val.modu _ _ = Some _ |- _ ] => rewrite H in * 
           | [ H : Values.Val.modu _ _ = Some _ |- _ ] => rewrite H1 in H by (simpl; repeat or_refl)
           | [ H : Values.Val.mods _ _ = Some _ |- _ ] => try rewrite H1 in H by (simpl; repeat or_refl); rewrite P in H; break_match_hyp
           | [ H : Values.Val.mods _ _ = Some _ |- _ ] => rewrite H in * 
           | [ H : Values.Val.mods _ _ = Some _ |- _ ] => rewrite H1 in H by (simpl; repeat or_refl)
           | [ H : Values.Val.divu _ _ = Some _ |- _ ] => try rewrite H1 in H by (simpl; repeat or_refl); rewrite P in H; break_match_hyp
           | [ H : Values.Val.divu _ _ = Some _ |- _ ] => rewrite H in * 
           | [ H : Values.Val.divu _ _ = Some _ |- _ ] => rewrite H1 in H by (simpl; repeat or_refl)
           | [ H : Values.Val.divs _ _ = Some _ |- _ ] => try rewrite H1 in H by (simpl; repeat or_refl); rewrite P in H; break_match_hyp
           | [ H : Values.Val.divs _ _ = Some _ |- _ ] => rewrite H in * 
           | [ H : Values.Val.divs _ _ = Some _ |- _ ] => rewrite H1 in H by (simpl; repeat or_refl)
         end.


Lemma eq_update :
  forall (s1 s2 : regset) r,
    s1 r = s2 r ->
    forall rr v,
      (s1 # rr <- v) r = (s2 # rr <- v) r.
Proof.
  intros. preg_case; preg_simpl; auto.
Qed.


Lemma eq_mem_load' :
  forall md m m',
    mem_eq md m m' ->
    forall c b ofs v v',
      Mem.load c m b ofs = Some v ->
      Mem.load c m' b ofs = Some v' ->
      val_eq v v'.
Proof.
  intros. app eq_mem_load H0. break_and.
  rewrite H0 in H1. inv H1. eauto.
Qed.


Lemma eq_mem_storev_bits :
  forall md m m',
    mem_eq md m m' ->
    forall c a1 a2 v v' m0 m0',
      (a1 = Vundef \/ a1 = a2) ->
      val_eq v v' ->
      storev_bits c m a1 v = Some m0 ->
      storev_bits c m' a2 v' = Some m0' ->
      mem_eq md m0 m0'.
Proof.
  intros. unfold storev_bits in *.
  repeat break_match_hyp; try congruence.
  break_or; try congruence.
  inv H4.
  app eq_mem_store H2.
  break_and. rewrite H2 in H3. inv H3.
  eauto.
Qed.


Lemma val_eq_undef_right :
  forall v v',
    val_eq v v' ->
    val_eq Vundef v'.
Proof.
  intros.
  unfold val_eq in H.
  break_match_hyp; try subst; try inv_false;
  simpl; intros; try congruence.
Qed.


Lemma use_def_exec :
  forall ge c i s1 s2 s1' s2' m m' m0 m0' md md' b,
    exec_instr_bits ge md c i b s1 m = Nxt s1' m0 md' ->
    exec_instr_bits ge md c i b s2 m' = Nxt s2' m0' md' ->
    mem_eq md m m' ->
    (forall p, In p (use i) -> val_eq (s1 p) (s2 p)) ->
    ~ is_call_return i ->
    (forall p, In p (def i) -> val_eq (s1' p) (s2' p)) /\ mem_eq md' m0 m0'.
Proof.
  intros.

  rename H1 into Heq.

  rename H3 into Hcall_ret.
  rename H2 into H3.
  
  name (use_addr_correct_bits s1 s2 ge) Huac.
  name (use_addr_correct_no_ptr s1 s2 md ge) Huacnp.

  unfold use in *. unfold def in *. unfold use_def in *.
  simpl in *.

  remember i as instr.

  
  destruct instr;
    simpl in *;
    unfold exec_big_load_bits in *;
    unfold exec_big_store_bits in *;
    unfold exec_load_bits in *;
    unfold exec_store_bits in *;
  repeat break_let;
  repeat (break_match_hyp; try congruence);
  repeat st_inv;
  simpl in *;
  match goal with
    | [ H : (_,_) = (_,_) |- _ ] => inv H
    | [ |- _ ] => idtac
  end;
  simpl in *;
  split;
  intros;
  repeat break_or; try inv_false;
  repeat st_inv;
  subst;
  repeat (break_match_hyp; try congruence);
  repeat st_inv;


  try eapply val_eq_nextinstr_nf; intros;
  try eapply val_eq_nextinstr;
  try solve [eapply H3; prove_or_eq reflexivity];
  try (break_match; repeat break_match; preg_simpl);
  repeat eapply val_eq_update; intros;
  try solve [eapply H3; prove_or_eq reflexivity];
  try congruence;
  try not_in_hyp;
  try solve [unfold val_eq; eauto];
  
  try eapply val_eq_add;
  try eapply val_eq_zero_ext;
  try eapply val_eq_sub;
  try eapply val_eq_mul;
  try eapply val_eq_mulhs;
  try eapply val_eq_and;
  try eapply val_eq_vor;
  try eapply val_eq_xor;
  try eapply val_eq_shl;
  try eapply val_eq_shru;
  try eapply val_eq_shr;
  try eapply val_eq_sign_ext;
  try eapply val_eq_singleoffloat;
  try eapply val_eq_floatofsingle;
  try eapply val_eq_neg;
  try eapply val_eq_mulhu;
  try eapply val_eq_notint;
  try eapply val_eq_ror;
  try eapply val_eq_cmpu;
  try eapply val_eq_negative;
  try eapply val_eq_sub_overflow;
  try eapply val_eq_addf;
  try eapply val_eq_subf;
  try eapply val_eq_mulf;
  try eapply val_eq_divf;
  try eapply val_eq_addfs;
  try eapply val_eq_mulfs;
  try eapply val_eq_subfs;
  try eapply val_eq_divfs;
  try eapply val_eq_negf;
  try eapply val_eq_absf;
  try eapply val_eq_negfs;
  try eapply val_eq_absfs;
  try eapply val_eq_intofsingle;
  try eapply val_eq_singleofint;
  try eapply val_eq_floatofint;
  try eapply val_eq_intoffloat;
  try eapply val_eq_compare_floats;
  try eapply val_eq_compare_floats32;
  try eapply Huacnp; intros;

  match goal with
    | [ H : Val.modu _ _ = Some ?X,
            H2 : Val.modu _ _ = Some ?Y |- val_eq ?X ?Y ] =>
      preg_simpl;
      eapply val_eq_modu; try eapply H; try eapply H2
    | [ H : Val.mods _ _ = Some ?X,
            H2 : Val.mods _ _ = Some ?Y |- val_eq ?X ?Y ] =>
      preg_simpl;
      eapply val_eq_mods; try eapply H; try eapply H2
    | [ H : Val.divu _ _ = Some ?X,
            H2 : Val.divu _ _ = Some ?Y |- val_eq ?X ?Y ] =>
      preg_simpl;
      eapply val_eq_divu; try eapply H; try eapply H2
    | [ H : Val.divs _ _ = Some ?X,
            H2 : Val.divs _ _ = Some ?Y |- val_eq ?X ?Y ] =>
      preg_simpl;
      eapply val_eq_divs; try eapply H; try eapply H2
    | [ |- _ ] => idtac
  end;
  try eapply val_eq_sub;
  try eapply val_eq_and;
  try eapply val_eq_update; intros;
  try solve [
        edestruct eval_testcond_match;
        try eapply H3; try prove_or_eq reflexivity;
        match goal with
          | [ H : eval_testcond _ ?X = _, H2 : eval_testcond _ ?Y = _ |- _ ] =>
            rewrite H2 in H; congruence
        end];
  try solve [unfold val_eq; simpl; eauto];
  try solve [eapply val_eq_loadv; try eapply Huac; eauto];
  match goal with
    | [ |- context[s1 ?X] ] =>
      let H := fresh "H" in
      destruct (s1 X) eqn:H;
        try rewrite (val_eq_def _ _ H) in *;
        eapply H3; prove_or_eq reflexivity
    | [ |- _ ] => idtac
  end;
  try solve [unfold val_eq; simpl; eauto];
  try solve [eapply H3; try prove_or_eq reflexivity; try intuition idtac];
  match goal with
    | [ H : Mem.loadv _ _ _ = _ |- _ ] =>
      unfold Mem.loadv in *;
        repeat break_match_hyp; try congruence;
        edestruct Huac as [Hev | Hev]; try congruence;
        try solve [intros; apply H3; prove_or_eq eassumption; eassumption];
        instantiate; try congruence;
        eapply eq_mem_load'; eauto;
        eauto; instantiate;
        try instantiate (1 := md') in Hev;
        instantiate;
        congruence
    | [ |- _ ] => idtac
  end;
  try solve [
        eapply eq_mem_storev_bits;
        repeat match goal with
                 | [ H : storev_bits _ _ _ _ = _ |- _ ] => try eapply H
               end;
        eauto];
  try solve [simpl; intros; congruence];
  try solve [simpl; prove_or_eq reflexivity];
  try solve [unfold goto_label_bits in *;
              repeat break_match_hyp; congruence].

  
  - 
    eapply eq_mem_storev_bits; try eassumption; eauto.
    simpl. reflexivity.

  - unfold exec_big_load_bits in *;
    repeat break_match_hyp;
    try congruence;
    repeat st_inv.
    preg_simpl.
    edestruct Huac as [Hev | Hev].
    intros. eapply H3. right.
    eapply use_addr_add; eauto.
    rewrite Hev in Heqo2. simpl in *. congruence.
    rewrite Hev in Heqo2.
    unfold Mem.loadv in Heqo2.
    repeat break_match_hyp; try congruence.
    app eq_mem_load Heqo2.
    break_and. unfold Mem.loadv in Heqo0.
    congruence.
    
  - 
    repeat break_or; try inv_false;
    preg_simpl;
    try solve [simpl; intros; congruence].
    unfold Mem.loadv in *.
    repeat (break_match_hyp; try congruence).
    app use_addr_eval_addrmode_bits Heqv0; try congruence.
    rewrite Heqv0 in Heqv2. inv Heqv2.
    app use_addr_eval_addrmode_bits Heqv3; try congruence.
    rewrite Heqv3 in Heqv1. inv Heqv1.
    app eq_mem_load Heqo2. break_and.
    congruence.
    intros. eapply H3.
    right. eapply use_addr_add; eauto.

  - unfold storev_bits in *.
    repeat (break_match_hyp; try congruence).
    app use_addr_eval_addrmode_bits Heqv; try congruence.
    rewrite Heqv in Heqv0. inv Heqv0.
    app use_addr_eval_addrmode_bits Heqv2; try congruence.
    rewrite Heqv2 in Heqv1. inv Heqv1.
    app eq_mem_store Heqo1. break_and.
    find_rewrite. find_inversion.
    app eq_mem_store Heqo2. break_and.
    find_rewrite. find_inversion.
    eauto.
    intros. eapply H3.
    prove_or_eq fail.
    eapply use_addr_add; eauto.

  - unfold val_eq.
    exploit (H3 r1); try prove_or_eq reflexivity.
    intros. unfold val_eq in H.
    break_match_hyp; try congruence.

  - preg_simpl.
    unfold val_eq.
    exploit (H3 rd); try prove_or_eq reflexivity.
    intros. unfold val_eq in H.
    break_match_hyp; try congruence.

  - edestruct eval_testcond_match;
    try eapply H3; try prove_or_eq reflexivity;
    rewrite H; unfold Val.of_optbool; repeat break_match;
    unfold Vtrue; unfold Vfalse; simpl; intros; try congruence.
  - eapply val_eq_addf;
    repeat break_or; try subst; try inv_false;
    eapply H3; simpl; prove_or_eq reflexivity.
  - eapply val_eq_mulf. 
    eapply H3; simpl; prove_or_eq reflexivity.
    eapply H3; simpl; prove_or_eq reflexivity.
  - unfold goto_label_bits in *.
    repeat break_match_hyp; try congruence.
    repeat state_inv. preg_simpl.
    name (H3 PC) HPC. exploit HPC. left. reflexivity.
    intros. reflexivity.
  - unfold goto_label_bits in *.
    repeat break_match_hyp; try congruence.
    repeat state_inv. preg_simpl.
    name (H3 PC) HPC. exploit HPC. left. reflexivity.
    intros. reflexivity.
  - unfold goto_label_bits in *.
    repeat break_match_hyp; try congruence.
    repeat state_inv. preg_simpl.
    name (H3 PC) HPC. exploit HPC. left. reflexivity.
    intros. reflexivity.
  - edestruct eval_testcond_match;
    try eapply H3; try prove_or_eq reflexivity.
    rewrite H in Heqo1. congruence.
    rewrite H in Heqo1. rewrite Heqo1 in Heqo.
    congruence.
  - edestruct eval_testcond_match;
    try eapply H3; try prove_or_eq reflexivity.
    rewrite H0 in Heqo1. congruence.
    rewrite H0 in Heqo1. rewrite Heqo1 in Heqo.
    congruence.
  - name (H3 r) Hr.
    exploit Hr. prove_or_eq reflexivity.
    intros. app val_eq_or H1.
    destruct H1.
    unfold goto_label_bits in *.
    repeat break_match_hyp; try congruence.
    rewrite H1 in Heqv0.
    rewrite Heqv0 in Heqv.
    inv Heqv.
    rewrite Heqo in Heqo0.
    inv Heqo0.
    unfold goto_label_bits in *.
    repeat break_match_hyp; try congruence.
    state_inv. state_inv.
    preg_simpl.
    name (H3 PC) HPC. exploit HPC. left. reflexivity.
    intros.
    congruence.
  - app eq_mem_alloc Heqp0.
    break_and. rewrite H0 in Heqp.
    inv Heqp.
    unify_pinj. simpl. reflexivity.
  - app eq_mem_alloc Heqp0.
    break_and. rewrite H0 in Heqp.
    inv Heqp.
    unify_pinj. simpl.
    app eq_mem_store Heqo2.
    break_and.
    rewrite H5 in Heqo. inv Heqo.
    app eq_mem_store Heqo3.
    break_and.
    rewrite H8 in Heqo0. inv Heqo0.
    eauto.
  - app eq_mem_load Heqo7.
    break_and.
    name (H3 ESP) HESP.
    exploit HESP. prove_or_eq reflexivity.
    intros. 
    rewrite Heqv1 in H5. rewrite Heqv in H5.
    simpl in H5. inv H5.
    unify_psur. rewrite H1 in Heqo2. inv Heqo2. eauto.
  - app eq_mem_load Heqo5.
    break_and.
    name (H3 ESP) HESP.
    exploit HESP. prove_or_eq reflexivity.
    intros.
    rewrite Heqv1 in H2. rewrite Heqv in H2.
    simpl in H2. inv H2.
    repeat unify_psur.  
    rewrite H0 in Heqo0. inv Heqo0.
    eauto.
  - app eq_mem_load Heqo5.
    break_and.
    name (H3 ESP) HESP.
    exploit HESP. prove_or_eq reflexivity.
    intros. 
    rewrite Heqv1 in H2. rewrite Heqv in H2.
    simpl in H2. inv H2.
    repeat unify_psur.
    rewrite H0 in Heqo0. inv Heqo0.
    eauto.
  - app eq_mem_free Heqo8.
    break_and.
    name (H3 ESP) HESP.
    exploit HESP. prove_or_eq reflexivity.
    intros. 
    rewrite Heqv1 in H2. rewrite Heqv in H2.
    simpl in H2. inv H2.
    repeat unify_psur.
    rewrite H0 in Heqo3. inv Heqo3.
    eauto.
Qed.


