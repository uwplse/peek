Require Import Coqlib.
Require Import Asm.
Require Import Integers.


Lemma addrmode_eq :
  forall (a b : addrmode),
    { a = b } + { a <> b }.
Proof.
  intros.
  destruct a; destruct b.
  destruct base; destruct base0;
  try (right; congruence);
  destruct ofs; destruct ofs0;
  try (right; congruence);
  [  destruct const; destruct const0;
     try (right; congruence) |
     idtac | idtac | idtac].
  Focus 1.
  destruct p. destruct p0.
  destruct (Int.eq_dec i1 i2);
    destruct (Int.eq_dec i4 i6);
    destruct (ireg_eq i i0);
    destruct (ireg_eq i3 i5);
    subst;
    try (left; reflexivity);
    right.
  congruence.
  (* If I chain these I get a stack overflow. fml. *)
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.

    Focus 1.
    destruct p. destruct p0.
    destruct p1. destruct p2.
    destruct (Int.eq_dec i2 i4);
    destruct (Int.eq_dec i6 i8);
    destruct (ireg_eq i i0);
    destruct (peq i5 i7);
    destruct (ireg_eq i1 i3);
    subst;
    try (left; reflexivity);
    right.
  (* If I chain these I get a stack overflow. fml. *)
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.

  destruct const; destruct const0.
  Focus 1.
  destruct (Int.eq_dec i1 i2);
    destruct (ireg_eq i i0);
    subst;
    try (left; reflexivity);
    right.
  (* If I chain these I get a stack overflow. fml. *)
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.

  right. intro. inv H.
  right. intro. inv H.

  Focus 1.
  destruct p. destruct p0.
    destruct (Int.eq_dec i2 i4);
    destruct (ireg_eq i i0);
    destruct (peq i1 i3);
    subst;
    try (left; reflexivity);
    right.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.

  destruct p. destruct p0.
  destruct const; destruct const0;
  try solve [right; intro; inv H; congruence];
  try destruct p; try destruct p0.
  destruct (Int.eq_dec i0 i2);
    destruct (ireg_eq i i1);
    destruct (Int.eq_dec i3 i4);
    subst;
    try (left; reflexivity);
    right.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  
  destruct (Int.eq_dec i0 i2);
    destruct (ireg_eq i i1);
    destruct (Int.eq_dec i4 i6);
    destruct (peq i3 i5);
    subst;
    try (left; reflexivity);
    right.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
  
  destruct const; destruct const0;
  try solve [right; intro; inv H; congruence];
  try destruct p; try destruct p0.
  destruct (Int.eq_dec i i0);
    subst;
    try (left; reflexivity);
    right.
  intro. inv H. congruence.

  destruct (Int.eq_dec i0 i2);
    destruct (peq i i1);
    subst;
    try (left; reflexivity);
    right.
  intro. inv H. congruence.
  intro. inv H. congruence.
  intro. inv H. congruence.
Defined.  

