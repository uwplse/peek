Require Import Coqlib.
Require Import Asm.
Require Import Globalenvs.
Require Import PeekTactics. 

Ltac preg_unfold :=
  try unfold nextinstr_nf;
  try unfold nextinstr;
  try unfold exec_load;
  try unfold exec_store;
  try unfold compare_ints;
  try unfold compare_floats;
  try unfold compare_floats32;
  try unfold goto_label;
  try unfold undef_regs.


Ltac preg_unfold_hyp H :=
  try unfold nextinstr_nf in H;
  try unfold nextinstr in H;
  try unfold exec_load in H;
  try unfold exec_store in H;
  try unfold compare_ints in H;
  try unfold compare_floats in H;
  try unfold compare_floats32 in H;
  try unfold goto_label in H;
  try unfold undef_regs in H.
  
Ltac preg_simpl_one_step_hyp H :=
  preg_unfold_hyp H;
  try rewrite Pregmap.gss in H;
  try rewrite Pregmap.gso in H by (try apply PC_neq; try apply PC_neq_crbit; try congruence; auto).

Ltac preg_simpl_hyp H :=
  repeat preg_simpl_one_step_hyp H.

Ltac preg_simpl_one_step :=
  preg_unfold;
  try rewrite Pregmap.gss;
  try rewrite Pregmap.gso by (try apply PC_neq; try apply PC_neq_crbit; try congruence; auto).

Ltac preg_simpl :=
  repeat preg_simpl_one_step; try symmetry; repeat preg_simpl_one_step; try symmetry.

Ltac preg_case :=
  match goal with
    | [ |- context[ (_ # ?X <- _) ?Y ]] => destruct (preg_eq X Y); try subst; preg_simpl
  end.

Ltac preg_omega H :=
  preg_simpl;
  repeat (preg_case; try (simpl; rewrite H; simpl; reflexivity)).
