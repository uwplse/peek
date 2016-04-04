Require Import Coqlib.
Require Import Memory.
Require Import Values.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Maps.


(* This should be checked for matching hardware *)
Definition encode_val_bits (chunk : memory_chunk) (v : val) : list memval :=
  match v with
    | Vundef =>
      match chunk with
        | Mint8signed => list_repeat (size_chunk_nat chunk) Undef
        | Mint8unsigned => list_repeat (size_chunk_nat chunk) Undef
        | Mint16signed => list_repeat (size_chunk_nat chunk) Undef
        | Mint16unsigned => list_repeat (size_chunk_nat chunk) Undef
        | Mint32 => list_repeat (size_chunk_nat chunk) Undef
        | Mint64 => list_repeat (size_chunk_nat chunk) Undef
        | Mfloat32 => list_repeat (size_chunk_nat chunk) Undef
        | Mfloat64 => list_repeat (size_chunk_nat chunk) Undef
        | Many32 => list_repeat (size_chunk_nat chunk) Undef
        | Many64 => list_repeat (size_chunk_nat chunk) Undef
      end
    | Vint n =>
      match chunk with
        | Mint8signed => inj_bytes (encode_int 1 (Int.unsigned n))
        | Mint8unsigned => inj_bytes (encode_int 1 (Int.unsigned n))
        | Mint16signed => inj_bytes (encode_int 2 (Int.unsigned n))
        | Mint16unsigned => inj_bytes (encode_int 2 (Int.unsigned n))
        | Mint32 => inj_bytes (encode_int 4 (Int.unsigned n))
        | Mint64 => list_repeat (size_chunk_nat chunk) Undef
        | Mfloat32 => list_repeat (size_chunk_nat chunk) Undef
        | Mfloat64 => list_repeat (size_chunk_nat chunk) Undef
        | Many32 => inj_bytes (encode_int 4 (Int.unsigned n))
        | Many64 => inj_value Q64 v
      end
    | Vlong n =>
      match chunk with
        | Mint8signed => list_repeat (size_chunk_nat chunk) Undef
        | Mint8unsigned => list_repeat (size_chunk_nat chunk) Undef
        | Mint16signed => list_repeat (size_chunk_nat chunk) Undef
        | Mint16unsigned => list_repeat (size_chunk_nat chunk) Undef
        | Mint32 => list_repeat (size_chunk_nat chunk) Undef
        | Mint64 => inj_bytes (encode_int 8 (Int64.unsigned n))
        | Mfloat32 => list_repeat (size_chunk_nat chunk) Undef
        | Mfloat64 => list_repeat (size_chunk_nat chunk) Undef
        | Many32 => list_repeat (size_chunk_nat chunk) Undef
        | Many64 => inj_value Q64 v
      end
    | Vfloat n =>
      match chunk with
        | Mint8signed => list_repeat (size_chunk_nat chunk) Undef
        | Mint8unsigned => list_repeat (size_chunk_nat chunk) Undef
        | Mint16signed => list_repeat (size_chunk_nat chunk) Undef
        | Mint16unsigned => list_repeat (size_chunk_nat chunk) Undef
        | Mint32 => list_repeat (size_chunk_nat chunk) Undef
        | Mint64 => list_repeat (size_chunk_nat chunk) Undef
        | Mfloat32 => list_repeat (size_chunk_nat chunk) Undef
        | Mfloat64 => inj_bytes (encode_int 8 (Int64.unsigned (Float.to_bits n)))
        | Many32 => list_repeat (size_chunk_nat chunk) Undef
        | Many64 => inj_value Q64 v
      end
    | Vsingle n =>
      match chunk with
        | Mint8signed => list_repeat (size_chunk_nat chunk) Undef
        | Mint8unsigned => list_repeat (size_chunk_nat chunk) Undef
        | Mint16signed => list_repeat (size_chunk_nat chunk) Undef
        | Mint16unsigned => list_repeat (size_chunk_nat chunk) Undef
        | Mint32 => list_repeat (size_chunk_nat chunk) Undef
        | Mint64 => list_repeat (size_chunk_nat chunk) Undef
        | Mfloat32 => inj_bytes (encode_int 4 (Int.unsigned (Float32.to_bits n)))
        | Mfloat64 => list_repeat (size_chunk_nat chunk) Undef
        | Many32 => inj_value Q32 v
        | Many64 => inj_value Q64 v
      end
    | Vptr _ _ =>
      match chunk with
        | Mint8signed => list_repeat (size_chunk_nat chunk) Undef
        | Mint8unsigned => list_repeat (size_chunk_nat chunk) Undef
        | Mint16signed => list_repeat (size_chunk_nat chunk) Undef
        | Mint16unsigned => list_repeat (size_chunk_nat chunk) Undef
        | Mint32 => list_repeat (size_chunk_nat chunk) Undef
        | Mint64 => list_repeat (size_chunk_nat chunk) Undef
        | Mfloat32 => list_repeat (size_chunk_nat chunk) Undef
        | Mfloat64 => list_repeat (size_chunk_nat chunk) Undef
        | Many32 => list_repeat (size_chunk_nat chunk) Undef
        | Many64 => list_repeat (size_chunk_nat chunk) Undef
      end
  end.

Lemma store_obligation_3_bits
     : forall (chunk : memory_chunk) (m : mem) (b : block) 
         (ofs : Z) (v : val),
       Mem.valid_access m chunk b ofs Writable ->
       forall b0 : positive,
       fst
         (PMap.set b
            (Mem.setN (encode_val_bits chunk v) ofs (Mem.mem_contents m) !! b)
            (Mem.mem_contents m)) !! b0 = Undef.
Proof.
  intros.
  remember H as Hva. clear HeqHva.
  eapply Mem.store_obligation_3 in H.
  instantiate (1 := v) in H. instantiate (1 := b0) in H.
  rewrite PMap.gsspec in *. destruct (peq b0 b).
  subst. rewrite Mem.setN_default in *. assumption.
  assumption.
Qed.

Definition store_bits (chunk : memory_chunk) (m : mem) (b : block) (ofs : Z) (v : val) :=
  match Mem.valid_access_dec m chunk b ofs Writable with
    | left x =>
      Some
        {|
          Mem.mem_contents := PMap.set b
                                       (Mem.setN (encode_val_bits chunk v) ofs
                                                 (Mem.mem_contents m) !! b)
                                       (Mem.mem_contents m);
          Mem.mem_access := Mem.mem_access m;
          Mem.nextblock := Mem.nextblock m;
          Mem.access_max := Mem.store_obligation_1 chunk m b ofs v x;
          Mem.nextblock_noaccess := Mem.store_obligation_2 chunk m b ofs v x;
          Mem.contents_default := store_obligation_3_bits chunk m b ofs v x |}
    | right _ => None
  end.

Definition set_perm (m : mem) (b : block) (lo hi : Z) (p : permission) : option mem.
  destruct (plt b (Mem.nextblock m)); [ | exact None].
  refine (Some (
  {|
    Mem.mem_contents := Mem.mem_contents m;
    Mem.mem_access := PMap.set b (fun ofs k =>
                                    if zle lo ofs && zlt ofs hi
                                    then Some p
                                    else (Mem.mem_access m) !! b ofs k)
                               (Mem.mem_access m);
    Mem.nextblock := Mem.nextblock m;
    Mem.access_max := _;
    Mem.nextblock_noaccess := _;
    Mem.contents_default := _ |})).
  * intros.
    destruct (peq b b0). subst. rewrite PMap.gss.
    destruct (zle lo ofs && zlt ofs hi) eqn:?.
    simpl. econstructor.
    apply (Mem.access_max m b0 ofs).
    rewrite PMap.gso by congruence.
    apply (Mem.access_max m b0 ofs).
  * intros.
    unfold Plt in *.
    destruct (peq b b0). subst. congruence.
    rewrite PMap.gso by congruence.
    eapply Mem.nextblock_noaccess; eauto.
  * eapply Mem.contents_default.
Defined.  
