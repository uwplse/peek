Require Import Coqlib.
(* Zlen *)

Definition zlen {A:Type} (l:list A) : Z := 
  Z_of_nat' (length l).
