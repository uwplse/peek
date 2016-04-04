Require Import Coqlib.
Require Import Asm.
Require Import Globalenvs.
Require Import compcert.lib.Integers.
Require Import Ring_theory.

Require Import AsmBits.


(* hypothesis management *)
Ltac name A B :=
  let Heq := fresh "H" in
  remember A as B eqn:Heq; clear Heq.

Ltac sploit HH :=
  let rec gg H :=
      match type of H with
        | ?T -> ?U =>
          let x := fresh "H" in
          assert (x : T);
            [ | specialize (H x); gg HH]
        | _ => idtac
      end
  in gg HH.

Ltac uespecialize H :=
  let rec ues X :=
      match type of X with
        | _ -> ?T => idtac
        | forall (_ : ?A), _ =>
          let x := fresh "H" in
          evar (x : A);
            specialize (X x);
            unfold x in X;
            clear x;
            ues X
        | _ => idtac
      end
  in
    ues H.

Ltac use H :=
  let x := fresh "H" in
  pose proof H as x;
    uespecialize x;
    sploit x.

Ltac copy H :=
  let x := fresh "H" in
  name H x.

Ltac clean :=
  match goal with
    | [ H : ?X = ?X |- _ ] => clear H
    | [ H : ?X, H' : ?X |- _ ] => clear H'
  end.

Ltac subst_max :=
  repeat match goal with
           | [ H : ?X = _ |- _ ]  => subst X
           | [H : _ = ?X |- _] => subst X
         end.

(* break/destruct helpers *)
Ltac break_if_hyp :=
  match goal with
    | [ H : context [ if ?X then _ else _ ] |- _] => destruct X eqn:?
  end.
Ltac break_if_goal :=
  match goal with
    | [ |- context [ if ?X then _ else _ ] ] => destruct X eqn:?
  end.
Ltac break_if := break_if_hyp || break_if_goal.

Ltac break_match_hyp :=
  match goal with
    | [ H : context [ match ?X with _ => _ end ] |- _] => destruct X eqn:?
  end.
Ltac break_match_goal :=
  match goal with
    | [ |- context [ match ?X with _ => _ end ] ] => destruct X eqn:?
  end.
Ltac break_match := break_match_goal || break_match_hyp.

Ltac break_exists :=
  match goal with
    | [H : exists _, _ |- _ ] => destruct H
  end.

Ltac break_and :=
  match goal with
   | [H : _ /\ _ |- _ ] => destruct H
  end.

Ltac break_let_hyp :=
  match goal with
    | [ H : context [ (let (_,_) := ?X in _) ] |- _ ] => destruct X eqn:?
  end.
Ltac break_let_goal :=
  match goal with
    | [ |- context [ (let (_,_) := ?X in _) ] ] => destruct X eqn:?
  end.
Ltac break_let := break_let_hyp || break_let_goal.

Ltac break_or :=
  match goal with
    | [ H : _ \/ _ |- _ ] => inv H
  end.

Ltac break_any := 
  break_if || break_match || break_let || break_and || break_or || break_exists.

Ltac break_match_sm' t :=
  match t with
    | context[match ?X with _ => _ end] =>
      break_match_sm' X || destruct X eqn:?
    | _ => destruct t eqn:?
  end.

Ltac break_match_sm :=
  match goal with
    (* | [ H : context[match ?X with _ => _ end] |- _ ] => *)
    (*   break_match_sm' X *)
    | [ |- context[match ?X with _ => _ end] ] =>
      break_match_sm' X
  end.

(* apply/rewrite helpers *)
Ltac find_apply_lem lem :=
  match goal with
    | [ H : _ |- _ ] => apply lem in H
    | [ |- _ ] => apply lem
  end.
Ltac find_eapply_lem lem :=
  match goal with
    | [ H : _ |- _ ] => eapply lem in H
    | [ |- _ ] => eapply lem
  end.
Ltac find_rewrite_lem lem :=
  match goal with
    | [ H : _ |- _ ] => rewrite lem in H
    | [ |- _ ] => rewrite lem
  end.
Ltac find_reverse_rewrite_lem lem :=
  match goal with
    | [ H : _ |- _ ] => rewrite <- lem in H
    | [ |- _ ] => rewrite <- lem
  end.
Ltac find_use lem :=
  find_apply_lem lem || find_rewrite_lem lem || find_reverse_rewrite_lem lem.
Ltac find_euse lem := find_use lem || find_eapply_lem lem.

(* find any apply/rewrite *)

Ltac find_rewrite :=
  match goal with
    | [ H : ?X = _, H' : ?X = _ |- _ ] => rewrite H in H'
    | [ H : ?X = _, H' : context [ ?X ] |- _ ] => rewrite H in H'
    | [ H : ?X = _ |- context [ ?X ] ] => rewrite H
    | [ H : _ = ?X, H' : context [ ?X ] |- _ ] => rewrite <- H in H'
    | [ H : _ = ?X |- context [ ?X ] ] => rewrite <- H
  end.

Ltac find_apply_goal :=
  match goal with
    | [ H : _ |- _ ] => apply H
  end.

Ltac find_apply_hyp :=
  match goal with
    | [ H : forall _, _ -> _,
        H' : _ |- _ ] =>
      apply H in H'; [idtac]
    | [ H : _ -> _ , H' : _ |- _ ] =>
      apply H in H'; auto; [idtac]
  end.

Ltac find_apply := find_apply_goal || find_apply_hyp.

Ltac find_higher_order_rewrite :=
  match goal with
    | [ H : _ = _ |- _ ] => rewrite H in *
    | [ H : forall _, _ = _ |- _ ] => rewrite H in *
    | [ H : forall _ _, _ = _ |- _ ] => rewrite H in *
  end.

Ltac find_reverse_higher_order_rewrite :=
  match goal with
    | [ H : _ = _ |- _ ] => rewrite <- H in *
    | [ H : forall _, _ = _ |- _ ] => rewrite <- H in *
    | [ H : forall _ _, _ = _ |- _ ] => rewrite <- H in *
  end.

Ltac find_inversion :=
  match goal with
    | [ H : ?X _ _ _ _ _ _ = ?X _ _ _ _ _ _ |- _ ] => inv H
    | [ H : ?X _ _ _ _ _ = ?X _ _ _ _ _ |- _ ] => inv H
    | [ H : ?X _ _ _ _ = ?X _ _ _ _ |- _ ] => inv H
    | [ H : ?X _ _ _ = ?X _ _ _ |- _ ] => inv H
    | [ H : ?X _ _ = ?X _ _ |- _ ] => inv H
    | [ H : ?X _ = ?X _ |- _ ] => inv H
  end.

Ltac find_inversion_tuple :=
  match goal with
    | [ H : (_, _, _, _) = (_, _, _, _) |- _ ] => inv H
    | [ H : (_, _, _) = (_, _, _) |- _ ] => inv H
    | [ H : (_, _) = (_, _) |- _ ] => inv H
  end.

(* Solvers *)
Ltac solve_by_inversion_and tac :=
  match goal with
    | [H : _ |- _] => solve [inv H; tac]
  end.
Ltac solve_by_inversion := solve_by_inversion_and auto.

Ltac solve_by_contradiction :=
  match goal with
    | [ H : ?X = _, H' : ?X = _ |- _ ] => rewrite H in H'; solve_by_inversion
  end.

Ltac prove_eq :=
  match goal with
    | [ H : ?X ?x1 ?x2 ?x3 = ?X ?y1 ?y2 ?y3 |- _ ] =>
      assert (x1 = y1) by congruence;
        assert (x2 = y2) by congruence;
        assert (x3 = y3) by congruence;
        clear H
    | [ H : ?X ?x1 ?x2 = ?X ?y1 ?y2 |- _ ] =>
      assert (x1 = y1) by congruence;
        assert (x2 = y2) by congruence;
        clear H
    | [ H : ?X ?x1 = ?X ?y1 |- _ ] =>
      assert (x1 = y1) by congruence;
        clear H
  end.

(* implication helpers *)

Ltac conclude H tac :=
  (let H' := fresh in
   match type of H with
     | ?P -> _ => assert P as H' by (tac)
   end; specialize (H H'); clear H').

Ltac concludes :=
  match goal with
    | [ H : ?P -> _ |- _ ] => conclude H auto
  end.

Ltac econcludes :=
  match goal with
    | [ H : ?P -> _ |- _ ] => conclude H eauto
  end.

Ltac forward H :=
  let H' := fresh in
   match type of H with
     | ?P -> _ => assert P as H'
   end.

Ltac forwards :=
  match goal with
    | [ H : ?P -> _ |- _ ] => forward H
  end.

(* misc/unsorted *)

Ltac opt_inv :=
  match goal with
    | [ H : Some _ = None |- _ ] => inversion H
    | [ H : None = Some _ |- _ ] => inversion H
    | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
    | [ H : None = None |- _ ] => clear H
  end.

Ltac apex Hyp Hx :=
  let H := fresh "H" in
  let H2 := fresh "H" in 
  exploit Hyp;
  match goal with 
    | [ |- (?A <-> ?B) -> ?G ] => assert (H : B); [ eexists; solve [eapply Hx] | intro H2; eapply H2 in H; eauto; clear H2 ]
  end.

Ltac neg_inv  :=
  unfold not in *;
  match goal with
    | [ H : ?P -> False |- _ ] => assert P by (simpl; auto); congruence
  end.

Ltac destex :=
  repeat match goal with
           | [ H : ex _ |- _ ] => destruct H
         end.

Ltac app Hlem H := copy H; eapply Hlem in H; eauto; destex.

Lemma impl_conj :
  forall (A B : Prop),
    A /\ (A -> B) ->
    A /\ B.
Proof.
  intros. break_and.
  app H0 H.
Qed.

Ltac isplit :=
  match goal with
    | [ |- _ /\ _ ] => apply impl_conj; split; intros
  end.

Ltac collapse_match :=
  match goal with
    | [ H : ?X = _ |- context[match ?X with _ => _ end] ] => rewrite H
    | [ H : _ = ?X |- context[match ?X with _ => _ end] ] => rewrite <- H
  end.


(* Peek specific *)

Ltac state_inv :=
  match goal with
    | [ H : Stuck = Next _ _ |- _ ] => inversion H
    | [ H : Next _ _ = Stuck |- _ ] => inversion H
    | [ H : Next _ _ = Next _ _ |- _ ] => inv H
    | [ H : Stck = Nxt _ _ _ |- _ ] => inversion H
    | [ H : Nxt _ _ _ = Stck |- _ ] => inversion H
    | [ H : Nxt _ _ _ = Nxt _ _ _ |- _ ] => inv H
  end.

Ltac st_inv :=
  match goal with
    | [ H : Nxt _ _ _ = Nxt _ _ _ |- _ ] => inv H
    | [ H : Nxt _ _ _ = Stck |- _ ] => congruence
    | [ H : Stck = Nxt _ _ _ |- _ ] => congruence
  end.


Ltac inv_step H :=
  inversion H;
  repeat match goal with
    | [ H1 : ?X PC = _, H2 : ?X PC = _ |- _ ] => rewrite H1 in H2; inv H2
    | [ H1 : Genv.find_funct_ptr ?X ?Y = _, H2 : Genv.find_funct_ptr ?X ?Y = _ |- _ ] => rewrite H1 in H2; inv H2
    | [ H : find_instr _ (fn_code {| fn_sig := _; fn_code := _ |}) = _ |- _ ] => simpl in H
    | [ H1 : find_instr ?X ?Y = _, H2 : find_instr ?X ?Y = _ |- _ ] => rewrite H1 in H2; inv H2
         end.

Lemma PC_neq:
  forall (rd : ireg),
    PC <> IR rd.
Proof.
  destruct rd; congruence.
Qed.

Lemma PC_neq_crbit:
  forall (cr : crbit),
    PC <> CR cr.
Proof.
  destruct cr; congruence.
Qed.

Ltac simpl_exec :=
  repeat match goal with
           | [ H : exec_instr _ _ _ _ _ = Nxt _ _ _ |- _ ] => simpl in H
           | [ H : exec_instr_bits _ _ _ _ _ = Nxt _ _ _ |- _ ] => simpl in H
           | [ H : exec_load _ _ _ _ _ _ = Nxt _ _ _ |- _ ] => unfold exec_load in H
           | [ H : exec_load_bits _ _ _ _ _ _ = Nxt _ _ _ |- _ ] => unfold exec_load_bits in H
           | [ H : exec_store _ _ _ _ _ _ _ = Nxt _ _ _ |- _ ] => unfold exec_store in H
           | [ H : exec_store_bits _ _ _ _ _ _ _ = Nxt _ _ _ |- _ ] => unfold exec_store_bits in H
           | [ H : goto_label _ _ _ _ = Nxt _ _ _ |- _ ] => unfold goto_label in H
           | [ H : goto_label_bits _ _ _ _ = Nxt _ _ _ |- _ ] => unfold goto_label_bits in H
         end.

Ltac inv_false :=
  match goal with
    | [ H : False |- _ ] => solve [inversion H]
    | [ H : ~ True |- _ ] => solve [exfalso; apply H; exact I]
  end.

Ltac unify_loadv :=
  match goal with
    | [ H : Memory.Mem.loadv _ _ _ = _, H2 : Memory.Mem.loadv _ _ _ = _ |- _ ] =>
      rewrite H in H2; inv H2
  end.

Ltac unify_storev :=
  match goal with
    | [ H : Memory.Mem.storev _ _ _ = _, H2 : Memory.Mem.storev _ _ _ = _ |- _ ] =>
      rewrite H in H2; inv H2
  end.

Ltac unify_modu :=
  match goal with
    | [ H : Values.Val.modu _ _ = _, H2 : Values.Val.modu _ _ = _ |- _ ] =>
      rewrite H in H2; inv H2
  end.

Ltac unify_divu :=
  match goal with
    | [ H : Values.Val.divu _ _ = _, H2 : Values.Val.divu _ _ = _ |- _ ] =>
      rewrite H in H2; inv H2
  end.

Ltac unify_mods :=
  match goal with
    | [ H : Values.Val.mods _ _ = _, H2 : Values.Val.mods _ _ = _ |- _ ] =>
      rewrite H in H2; inv H2
  end.

Ltac unify_divs :=
  match goal with
    | [ H : Values.Val.divs _ _ = _, H2 : Values.Val.divs _ _ = _ |- _ ] =>
      rewrite H in H2; inv H2
  end.

Ltac unify_eval_testcond :=
  match goal with
    | [ H : eval_testcond _ _ = _, H2 : eval_testcond _ _ = _ |- _ ] =>
      rewrite H in H2; inv H2
  end.

Ltac unify_PC :=
  match goal with
    | [ H : ?RS PC = _, H2 : ?RS PC = _ |- _ ] => rewrite H in H2; inv H2
  end.

Ltac invs :=
  match goal with
    | [ H : step_bits _ _ _ _ |- _ ] => inv_step H
  end.

Ltac unify_find_funct_ptr :=
  match goal with
    | [ H : Genv.find_funct_ptr _ _ = _ , H2 : Genv.find_funct_ptr _ _ = _ |- _ ] =>
      unfold fundef in *; rewrite H in H2; inv H2
  end.

Ltac unify_find_instr :=
  match goal with
    | [ H : find_instr _ _ = _, H2 : find_instr _ _ = _ |- _ ] => rewrite H in H2; inv H2
  end.

Ltac app_new Hlem H :=
  let HNEW := fresh "H" in
  name H HNEW; eapply Hlem in HNEW; eauto; destex.

(* DEPRECATED use P, PP, NP, PN etc with aliases instead *)
Ltac app_np nm pat :=
  match goal with
    | [ H1 : context [ pat ], H2 : context [ pat ] |- _ ] => fail 1
    | [ H : context [ pat ] |- _ ] => app nm H
  end.
Ltac app_np1 nm pat :=
  match goal with
    | [ H : context [ pat ] |- _ ] => app nm H
  end.
Ltac app_pn pat nm :=
  match goal with
    | [ H1 : context [ pat ], H2 : context [ pat ] |- _ ] => fail 1
    | [ H : context [ pat ] |- _ ] => app H nm
  end.
Ltac app_pn1 pat nm :=
  match goal with
    | [ H : context [ pat ] |- _ ] => app H nm
  end.
Ltac app_p pat :=
  match goal with
    | [ H1 : context [ pat ], H2 : context [ pat ] |- _ ] => fail 1
    | [ H : context [ pat ] |- _ ] => app H
  end.
Ltac app_p1 pat :=
  match goal with
    | [ H : context [ pat ] |- _ ] => app H
  end.

Ltac rwrt H1 H2 := rewrite H1 in H2.
Ltac rwrtb H1 H2 := rewrite <- H1 in H2.
Ltac rwrt_n H := rewrite H.
Ltac rwrtb_n H := rewrite <- H.
Ltac erwrt H1 H2 := erewrite H1 in H2.
Ltac erwrtb H1 H2 := erewrite <- H1 in H2.
Ltac erwrt_n H1 := erewrite H1.
Ltac erwrtb_n H1 := erewrite <- H1.

(*END DEPRICATED*)

Ltac P tac pat :=
  match goal with
    | [ H1 : context [ pat ], H2 : context [ pat ] |- _ ] => fail 1
    | [ H : context [ pat ] |- _ ] => tac H
  end.
Ltac P1 tac pat :=
  match goal with
    | [ H : context [ pat ] |- _ ] => tac H
  end.
Ltac P2 tac pat :=
  match goal with
    | [ H1 : context [ pat ], H2 : context [ pat ] |- _ ] => tac H1
  end.
Ltac PP tac pat1 pat2 :=
  match goal with
    | [ H1 : context [ pat1 ], H2 : context [ pat1 ] |- _ ] => fail 1
    | [ H1 : context [ pat2 ], H2 : context [ pat2 ] |- _ ] => fail 1
    | [ H1 : context [ pat1 ], H2 : context [ pat2 ] |- _ ] => tac H1 H2
  end.
Ltac PP1 tac pat1 pat2 :=
  match goal with
    | [ H1 : context [ pat1 ], H2 : context [ pat2 ] |- _ ] => tac H1 H2
  end.
Ltac NP tac Hnm pat :=
  match goal with
    | [ H1 : context [ pat ], H2 : context [ pat ] |- _ ] => fail 1
    | [ H : context [ pat ] |- _ ] => tac Hnm H
  end.
Ltac NP1 tac Hnm pat :=
  match goal with
    | [ H : context [ pat ] |- _ ] => tac Hnm H
  end.
Ltac PN tac pat Hnm :=
  match goal with
    | [ H1 : context [ pat ], H2 : context [ pat ] |- _ ] => fail 1
    | [ H : context [ pat ] |- _ ] => tac H Hnm
  end.
Ltac PN1 tac pat Hnm :=
  match goal with
    | [ H : context [ pat ] |- _ ] => tac H Hnm
  end.

(* aliases that make P, NP, etc. tacticals work with builtin tactics. It's annoying that we need these. *)
Ltac _simpl H := simpl in H.
Ltac _destruct H := destruct H.
Ltac _clear H := clear H.
Ltac _inversion H := inversion H.
Ltac _apply H := apply H.
Ltac _eapply H := eapply H.
Ltac _applyin H1 H2 := apply H1 in H2.
Ltac _eapplyin H1 H2 := eapply H1 in H2.
Ltac _rewritein H1 H2 := rewrite H1 in H2.
Ltac _rewritebin H1 H2 := rewrite <- H1 in H2.
Ltac _rewrite H := rewrite H.
Ltac _rewriteb H := rewrite <- H.
Ltac _erewritein H1 H2 := erewrite H1 in H2.
Ltac _erewritebin H1 H2 := erewrite <- H1 in H2.
Ltac _erewrite H1 := erewrite H1.
Ltac _erewriteb H1 := erewrite <- H1.
(* For whatever reason, _app works with PP and co and app doesn't... *)
Ltac _app Hlem H := copy H; eapply Hlem in H; eauto; destex.

Ltac T tac typ :=
  match goal with
    | [ H1 : typ, H2 : typ |- _ ] => fail 1
    | [ H : typ |- _ ] => tac H
  end.
Ltac T1 tac typ :=
  match goal with
    | [ H : typ |- _ ] => tac H
  end.
Ltac T2 tac typ :=
  match goal with
    | [ H1 : typ, H2 : typ |- _ ] => tac H1
  end.
Ltac TT tac typ1 typ2 :=
  match goal with
    | [ H1 : typ1, H2 : typ1 |- _ ] => fail 1
    | [ H1 : typ2, H2 : typ2 |- _ ] => fail 1
    | [ H1 : typ1, H2 : typ2 |- _ ] => tac H1 H2
  end.
Ltac TT1 tac typ1 typ2 :=
  match goal with
    | [ H1 : typ1, H2 : typ2 |- _ ] => tac H1 H2
  end.
Ltac NT tac Hnm typ :=
  match goal with
    | [ H1 : typ, H2 : typ |- _ ] => fail 1
    | [ H : typ |- _ ] => tac Hnm H
  end.
Ltac NT1 tac Hnm typ :=
  match goal with
    | [ H : typ |- _ ] => tac Hnm H
  end.
Ltac TN tac typ Hnm :=
  match goal with
    | [ H1 : typ, H2 : typ |- _ ] => fail 1
    | [ H : typ |- _ ] => tac H Hnm
  end.
Ltac TN1 tac typ Hnm :=
  match goal with
    | [ H : typ |- _ ] => tac H Hnm
  end.

Ltac mark_hyp H :=
  let TMP := fresh "TMP" in
  match type of H with
    | True /\ True -> _ => fail 1
    | ?A => rename H into TMP; assert (True /\ True -> A) as H by auto; clear TMP
  end.  
Ltac unmark_hyp H :=
  let TMP := fresh "TMP" in
  match type of H with
    | True /\ True -> ?P => rename H into TMP; assert (P) as H by auto; clear TMP
    | _ => fail 1
  end.
Ltac is_marked_hyp H :=
  match type of H with
    | True /\ True -> ?P => idtac
    | _ => fail 1
  end.
Ltac none_marked_hyp :=
  match goal with
    | [H: True /\ True -> _ |- _] => fail 1
    | _ => idtac
  end.

Ltac mark_var H1 :=
  match goal with
    | [H2: context[(id (id H1))] |- _ ] => fail 1
    | _ => replace H1 with (id (id H1)) in * by auto
  end.
Ltac unmark_var H1 := replace (id (id H1)) with H1 in * by auto.
Ltac is_marked_var H1 :=
  match goal with
    | [H2: context[(id (id H1))] |- _ ] => idtac
    | _ => fail 1
  end.
Ltac none_marked_var :=
  match goal with
    | [H: context[(id (id _))] |- _ ] => fail 1
    | _ => idtac
  end.

Ltac mark H := (mark_hyp H; is_marked_hyp H) || (mark_var H; is_marked_var H).
Ltac unmark H := (is_marked_hyp H; unmark_hyp H) || (is_marked_var H; unmark_var H).
Ltac is_marked H := is_marked_hyp H || is_marked_var H.
Ltac none_marked := none_marked_hyp; none_marked_var.

Ltac P0 tac pat :=
  repeat P1 mark_hyp pat;
  repeat match goal with
           | [H: _ |- _] => is_marked_hyp H; unmark_hyp H; tac H
         end;
  none_marked_hyp.
Ltac PN0 tac pat Hnm :=
  repeat P1 mark_hyp pat;
  repeat match goal with
           | [H: _ |- _] => is_marked_hyp H; unmark_hyp H; tac H Hnm
         end;
  none_marked_hyp.
Ltac NP0 tac Hnm pat :=
  repeat P1 mark_hyp pat;
  repeat match goal with
           | [H: _ |- _] => is_marked_hyp H; unmark_hyp H; tac Hnm H
         end;
  none_marked_hyp.

Ltac T0 tac typ :=
  repeat T1 mark_var typ;
  repeat match goal with
           | [H: _ |- _] => is_marked_var H; unmark_var H; tac H
         end;
  none_marked_var.
Ltac TN0 tac typ Hnm :=
  repeat T1 mark_var typ;
  repeat match goal with
           | [H: _ |- _] => is_marked_var H; unmark_var H; tac H Hnm
         end;
  none_marked_var.
Ltac NT0 tac Hnm typ :=
  repeat T1 mark_var typ;
  repeat match goal with
           | [H: _ |- _] => is_marked_var H; unmark_var H; tac Hnm H
         end;
  none_marked_var.

Ltac _rename H1 H2 := rename H1 into H2.

Ltac mk_exists' a H :=
  pattern a in H; apply ex_intro in H.

Tactic Notation "mk_exists" ident(a) "in" ident(H) := mk_exists' a H.

Ltac clear_taut :=
  repeat match goal with
    | [H: ?X = ?X |- _] => clear H
  end.

Ltac rename_fresh H Nm := _rename H fresh Nm.

Ltac rename_all_var typ nm := TN0 rename_fresh typ nm.  
Ltac rename_all_hyp pat nm := PN0 rename_fresh pat nm.    
Ltac rename_all pat nm := (progress rename_all_var pat nm) || (progress rename_all_hyp pat nm).

Ltac empty H := clear H; assert True as H by auto.
Ltac rename_careful H Nm := name H Nm; empty H.

Ltac compute_expr E :=
  remember E as TEMP_EXPR eqn:HeqTEMP_EXPR;
  vm_compute in HeqTEMP_EXPR; subst TEMP_EXPR.

Ltac simpl_expr E :=
  remember E as TEMP_EXPR eqn:HeqTEMP_EXPR;
  simpl in HeqTEMP_EXPR; subst TEMP_EXPR.

Ltac prove_or_eq H :=
  match goal with
    | [ |- _ \/ _ ] => try solve [left; H]; right; prove_or_eq H
    | [ |- _ ] => idtac
  end.


Ltac not_in_hyp :=
  match goal with
    | [ H : ~ In _ _ |- _ ] =>
      solve [exfalso; apply H;
             simpl; prove_or_eq reflexivity]
  end.

