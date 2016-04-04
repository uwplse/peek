Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Asm.
Require Import Axioms.
Require Import Floats.

Require Import PeekTactics.

Definition int_eq: forall a b : int,
 {a = b} + {a <> b}.
Proof.
  destruct a. destruct b.
  destruct (zeq intval intval0).
  * subst. left. replace intrange with intrange0. auto. apply proof_irr.
  * right. intro HC. inv HC. congruence.
Defined.

Definition int_id_eq: forall a b : int + ident * int,
 {a = b} + {a <> b}.
Proof.
  decide equality. apply int_eq. decide equality. apply int_eq. decide equality.
Defined.

Definition opt_ireg_int_eq : forall a b : option (ireg * int),
 {a = b} + {a <> b}.
Proof.
  decide equality. decide equality.
  apply int_eq. decide equality.
Defined.

Definition float_eq : forall a b : Floats.float,
 {a = b} + {a <> b}.
Proof.
  apply Float.eq_dec.
Defined.

Definition float32_eq : forall a b : Floats.float32,
 {a = b} + {a <> b}.
Proof.
  apply Float32.eq_dec.
Defined.

Definition instr_eq: forall a b : instruction, 
 {a = b} + {a <> b}.
Proof.
  repeat decide equality;
  try apply int_eq;
  try apply int_id_eq;
  try apply float_eq;
  try apply float32_eq;
  try apply opt_ireg_eq;
  apply Int64.eq_dec.
Defined.

Fixpoint prefix_match (a b : code) : option code :=
  match a,b with
    | fa::ra,fb::rb =>
      if instr_eq fa fb then prefix_match ra rb else None
    | nil,_ => Some b
    | _,nil => None
  end.

Fixpoint split_pat (a b : code) : option (code * code) :=
  match a,b with
    | fa::ra,fb::rb => 
      match prefix_match a b with
        | Some t => Some (nil,t)
        | None => 
          match split_pat (fa::ra) rb with
            | Some (h,t) => Some (fb::h,t)
            | None => None
          end
      end
    | nil,b => Some (nil,b)
    | _,nil => None
  end.


Theorem prefix_match_spec:
  forall c p c1,
    prefix_match p c = Some(c1) -> c = p ++ c1.
Proof.
  induction c.
  * simpl. intros.
    unfold prefix_match in H. destruct p.
    - inv H. auto.
    - inversion H.
  * intros. destruct p.
    - unfold prefix_match in H. inv H. auto.
    - destruct (instr_eq i a) eqn:Heq.
      + subst. simpl in H. destruct (instr_eq a a).
        apply (IHc p c1) in H. subst. auto.
        inv H.
      + unfold prefix_match in H. rewrite Heq in H.
        inversion H.
Qed.

Theorem prefix_match_neq:
  forall i j a b,
    i<>j -> prefix_match (i::a) (j::b) = None.
Proof.
  intros. unfold prefix_match. destruct instr_eq. 
  * apply H in e. contradiction.
  * auto.
Qed.

Theorem split_pat_spec:
  forall c p c1 c2,
    split_pat p c = Some(c1,c2) -> c = c1 ++ p ++ c2.
Proof.
  induction c.
  * intros. simpl in *. destruct p; inv H; auto.
  * intros. destruct p.
    - unfold split_pat in H. inv H. auto.
    - unfold split_pat in H. fold split_pat in H. destruct (instr_eq i a ).
      (* instructions are equal *)
      + subst. simpl in H. destruct (instr_eq a a).
          (* a=a *)
          destruct (prefix_match p c) eqn:Hpre.
            (* Some *)
            inv H. simpl. apply prefix_match_spec in Hpre.
            f_equal. assumption.
            (* None *)
            destruct (split_pat (a::p) c) eqn:Hsplit_pat.
              (* Some *)
              destruct p0. inv H. apply (IHc (a::p) c0 c2) in Hsplit_pat.
              simpl. f_equal. assumption.
              (* None *)
              inv H.
          (* a<>a *)
          unfold not in n. destruct n. auto.
      (* instructions are different *)
      + apply (prefix_match_neq i a p c) in n.
        rewrite n in H. destruct c1.
          (* nil *)
          simpl. destruct (split_pat (i :: p) c). destruct p0. inv H. inv H.
          (* cons *)
          specialize IHc with (i::p) c1 c2.
          destruct (split_pat (i::p) c) eqn:Hsplit_pat.
            (* Some *)
            destruct p0. inversion H. subst. simpl in IHc.
            inv H. assert (H0: Some (c1,c2) = Some (c1,c2)).
              auto.
            apply IHc in H0. simpl. f_equal. assumption.
            (* None *)
            inversion H.
Qed.

Lemma split_pat_none:
  forall i c p,
    split_pat p (i::c) = None -> split_pat p c = None.
Proof.
  intros. unfold split_pat in H. fold split_pat in H.
  destruct p. inversion H.
  destruct (prefix_match (i0::p) (i::c)). inversion H.
  destruct (split_pat (i0::p) c). destruct p0. inversion H.
  auto.
Qed.
