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
Require Import StepEquiv.

(* We want to have a representation of a rewrite that is parameterized over registers*)

Definition same_opcode (x y : instruction) : bool.
Proof.
  destruct x eqn:?; destruct y eqn:?;
  first [  assert (x <> y) by congruence; exact false | exact true ].
Defined.

(* TODO: get not just first match, but all matches *)

Fixpoint match_opcodes_head (pat : code) (c : code) (acc : code) : option code :=
  match pat,c with
    | p :: pr, i :: ir => if same_opcode p i then
                            match_opcodes_head pr ir (acc ++ (i :: nil))
                          else
                            None
    | nil, _ => Some acc
    | _, nil => None
  end.

Fixpoint match_pat_r (pat : code) (c : code) (acc : list code) : list code :=
  match c with
    | nil => acc
    | f :: r =>
      match match_opcodes_head pat c nil with
        | Some res1 =>
          match_pat_r pat r (res1 :: acc)
        | None =>
          match_pat_r pat r acc
      end
  end.

Definition matched_pat (pat : code) (c : code) : list code :=
  match_pat_r pat c nil.


(* Definition pat := Pmov_rr EAX EAX :: Pnop :: nil. *)
(* Definition c := Pnop :: Pmov_rr EBX ECX :: Pnop :: nil. *)

(* Eval compute in matched_pat pat c. *)
