Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Import Stacklayout.
Require Import Conventions.
Require Import Zwf.
Require Import Asm. (* Lots of shared code *)
Require Import ProofIrrelevance.


Require Import MemoryAxioms.
Require Import MemBits.
Require Import Zlen.

Section RELSEM_BITS.

Variable ge: genv.

(** Evaluating an addressing mode *)

Definition eval_addrmode_no_ptr (t : allocator_metadata) (a : addrmode) (rs : regset) :=
  match a with
    | Addrmode base ofs const =>
      Val.add match base with
                | Some r => rs r
                | None => Vzero
              end
              (Val.add
                 match ofs with
                   | Some (r, sc) =>
                     if Int.eq sc Int.one then rs r else Val.mul (rs r) (Vint sc)
                   | None => Vzero
                 end
                 match const with
                   | inl ofs0 => Vint ofs0
                   | inr (id, ofs0) =>
                     match Genv.symbol_address ge id ofs0 with
                       | Vptr b i => match pinj t b i with
                                       | Some bits => Vint bits
                                       | None => Vundef
                                     end
                       | _ => Vundef (* unreachable *)
                     end
                 end)
  end.

Definition eval_addrmode_bits (t : allocator_metadata) (a: addrmode) (rs: regset) : val :=
  match eval_addrmode ge a rs with
    | Vint i =>
      match psur t i with
        | Some (b,ofs) => Vptr b ofs
        | None => Vundef
      end
    | _ => eval_addrmode ge a rs
  end.

Inductive alloc_outcome : Type :=
| Nxt : regset -> mem -> allocator_metadata -> alloc_outcome
| Stck : alloc_outcome.

Definition goto_label_bits (t : allocator_metadata) (f: function) (lbl: label) (b : block) (rs: regset) (m: mem) : alloc_outcome :=
  match label_pos lbl 0 (fn_code f) with
    | None => Stck
    | Some pos =>
      match pinj t b (Int.repr pos) with
        | Some i' => Nxt (rs#PC <- (Vint i')) m t
        | None => Stck
      end
  end.

(** Auxiliaries for memory accesses. *)

Definition unpointer (t : allocator_metadata) (v : val) : option val :=
  match v with
    | Vptr b ofs =>
      match pinj t b ofs with
        | Some i => Some (Vint i)
        | None => None
      end
    | _ => Some v
  end.

Definition exec_load_bits (t : allocator_metadata) (chunk: memory_chunk) (m: mem)
                     (a: addrmode) (rs: regset) (rd: preg) : alloc_outcome :=
  match Mem.loadv chunk m (eval_addrmode_bits t a rs) with
    | Some v => Nxt (nextinstr_nf (rs#rd <- v)) m t
    | None => Stck
  end.

Definition exec_big_load_bits (t : allocator_metadata) (chunk: memory_chunk) (m: mem)
                         (a: addrmode) (rs: regset) (rd: bfreg) : alloc_outcome :=
  let (lrd,hrd) := split_big_freg rd in
  match Mem.loadv chunk m (eval_addrmode_bits t a rs) with
    | Some v =>
      match Mem.loadv chunk m (eval_addrmode_bits t (addr_add a (size_chunk chunk)) rs) with
        | Some v' => Nxt (nextinstr_nf ((rs#lrd <- v)#hrd <- v')) m t
        | None => Stck
      end
    | None => Stck
  end.


Definition storev_bits (chunk : memory_chunk) (m : mem) (addr v : val) :=
  match addr with
    | Vptr b ofs => store_bits chunk m b (Int.unsigned ofs) v
    | _ => None
  end.

Definition exec_store_bits (t : allocator_metadata) (chunk: memory_chunk) (m: mem)
                      (a: addrmode) (rs: regset) (r1: preg)
                      (destroyed: list preg) :=
  match storev_bits chunk m (eval_addrmode_bits t a rs) (rs r1) with
  | Some m' => Nxt (nextinstr_nf (undef_regs destroyed rs)) m' t
  | None => Stck
  end.

Definition exec_big_store_bits (t: allocator_metadata) (chunk: memory_chunk) (m: mem)
                          (a: addrmode) (rs: regset) (r1: bfreg)
                          (destroyed: list preg) :=
  let (lr1,hr1) := split_big_freg r1 in
  match storev_bits chunk m (eval_addrmode_bits t a rs) (rs#lr1) with
    | Some m' =>
      match storev_bits chunk m' (eval_addrmode_bits t (addr_add a (size_chunk chunk)) rs) (rs#hr1) with
        | Some m'' => Nxt (nextinstr_nf rs) m'' t
        | None => Stck
      end
    | None => Stck
  end.


Definition exec_instr_bits (t : allocator_metadata) (f: function) (i: instruction) (b : block) (rs: regset) (m: mem) : alloc_outcome :=
  match i with
  | Pnop =>
      Nxt (nextinstr rs) m t
  (** Moves *)
  | Pmov_rr rd r1 =>
      Nxt (nextinstr (rs#rd <- (rs r1))) m t
  | Pmov_ri rd n =>
      Nxt (nextinstr (rs#rd <- (Vint n))) m t
  | Pmov_ra rd id =>
    match Genv.symbol_address ge id Int.zero with
      | Vptr b i =>
        match pinj t b i with
          | Some bits => Nxt (nextinstr_nf (rs#rd <- (Vint bits))) m t
          | None => Stck
        end
      | _ => Nxt (nextinstr_nf (rs#rd <- (Genv.symbol_address ge id Int.zero))) m t
    end
  | Pmov_rm rd a =>
      exec_load_bits t Mint32 m a rs rd
  | Pmov_mr a r1 =>
      exec_store_bits t Mint32 m a rs r1 nil
  | Pmov_mi a n =>
    match storev_bits Mint32 m (eval_addrmode_bits t a rs) (Vint n) with
      | Some m' => Nxt (nextinstr_nf rs) m' t
      | None => Stck
    end
  | Pmovsd_ff rd r1 =>
      Nxt (nextinstr (rs#rd <- (rs r1))) m t
  | Pmovsd_fi rd n =>
      Nxt (nextinstr (rs#rd <- (Vfloat n))) m t
  | Pmovsd_fm rd a =>
      exec_load_bits t Mfloat64 m a rs rd
  | Pmovsd_mf a r1 =>
      exec_store_bits t Mfloat64 m a rs r1 nil
  | Pmovss_fi rd n =>
      Nxt (nextinstr (rs#rd <- (Vsingle n))) m t
  | Pmovss_fm rd a =>
      exec_load_bits t Mfloat32 m a rs rd
  | Pmovss_mf a r1 =>
      exec_store_bits t Mfloat32 m a rs r1 nil
  | Pfldl_m a =>
      exec_load_bits t Mfloat64 m a rs ST0
  | Pfstpl_m a =>
      exec_store_bits t Mfloat64 m a rs ST0 (ST0 :: nil)
  | Pflds_m a =>
      exec_load_bits t Mfloat32 m a rs ST0
  | Pfstps_m a =>
      exec_store_bits t Mfloat32 m a rs ST0 (ST0 :: nil)
  | Pxchg_rr r1 r2 =>
      Nxt (nextinstr (rs#r1 <- (rs r2) #r2 <- (rs r1))) m t
  | Pmovups_rm brd a =>
      exec_big_load_bits t Mfloat64 m a rs brd
  | Pmovups_mr a br1 =>
      exec_big_store_bits t Mfloat64 m a rs br1 nil
  (** Moves with conversion *)
  | Pmovb_mr a r1 =>
      exec_store_bits t Mint8unsigned m a rs r1 nil
  | Pmovw_mr a r1 =>
      exec_store_bits t Mint16unsigned m a rs r1 nil
  | Pmovzb_rr rd r1 =>
      Nxt (nextinstr (rs#rd <- (Val.zero_ext 8 rs#r1))) m t
  | Pmovzb_rm rd a =>
      exec_load_bits t Mint8unsigned m a rs rd
  | Pmovsb_rr rd r1 =>
      Nxt (nextinstr (rs#rd <- (Val.sign_ext 8 rs#r1))) m t
  | Pmovsb_rm rd a =>
      exec_load_bits t Mint8signed m a rs rd
  | Pmovzw_rr rd r1 =>
      Nxt (nextinstr (rs#rd <- (Val.zero_ext 16 rs#r1))) m t
  | Pmovzw_rm rd a =>
      exec_load_bits t Mint16unsigned m a rs rd
  | Pmovsw_rr rd r1 =>
      Nxt (nextinstr (rs#rd <- (Val.sign_ext 16 rs#r1))) m t
  | Pmovsw_rm rd a =>
      exec_load_bits t Mint16signed m a rs rd
  | Pcvtsd2ss_ff rd r1 =>
      Nxt (nextinstr (rs#rd <- (Val.singleoffloat rs#r1))) m t
  | Pcvtss2sd_ff rd r1 =>
      Nxt (nextinstr (rs#rd <- (Val.floatofsingle rs#r1))) m t
  | Pcvttsd2si_rf rd r1 =>
      Nxt (nextinstr (rs#rd <- (Val.maketotal (Val.intoffloat rs#r1)))) m t
  | Pcvtsi2sd_fr rd r1 =>
      Nxt (nextinstr (rs#rd <- (Val.maketotal (Val.floatofint rs#r1)))) m t
  | Pcvttss2si_rf rd r1 =>
      Nxt (nextinstr (rs#rd <- (Val.maketotal (Val.intofsingle rs#r1)))) m t
  | Pcvtsi2ss_fr rd r1 =>
      Nxt (nextinstr (rs#rd <- (Val.maketotal (Val.singleofint rs#r1)))) m t
  (** Integer arithmetic *)
  | Plea rd a =>
      Nxt (nextinstr (rs#rd <- (eval_addrmode_no_ptr t a rs))) m t
  | Pneg rd =>
      Nxt (nextinstr_nf (rs#rd <- (Val.neg rs#rd))) m t
  | Pinc rd =>
      Nxt (nextinstr_nf (rs#rd <- (Val.add rs#rd Vone))) m t
  | Pdec rd =>
      Nxt (nextinstr_nf (rs#rd <- (Val.sub rs#rd Vone))) m t
  | Padd_rr rd r1 =>
      Nxt (nextinstr_nf (rs#rd <- (Val.add rs#rd rs#r1))) m t
  | Psub_rr rd r1 =>
      Nxt (nextinstr_nf (rs#rd <- (Val.sub rs#rd rs#r1))) m t
  | Padd_ri rd n =>
      Nxt (nextinstr_nf (rs#rd <- (Val.add rs#rd (Vint n)))) m t
  | Psub_ri rd n =>
      Nxt (nextinstr_nf (rs#rd <- (Val.sub rs#rd (Vint n)))) m t
  | Pimul_rr rd r1 =>
      Nxt (nextinstr_nf (rs#rd <- (Val.mul rs#rd rs#r1))) m t
  | Pimul_ri rd n =>
      Nxt (nextinstr_nf (rs#rd <- (Val.mul rs#rd (Vint n)))) m t
  | Pimul_r r1 =>
      Nxt (nextinstr_nf (rs#EAX <- (Val.mul rs#EAX rs#r1)
                            #EDX <- (Val.mulhs rs#EAX rs#r1))) m t
  | Pmul_r r1 =>
      Nxt (nextinstr_nf (rs#EAX <- (Val.mul rs#EAX rs#r1)
                            #EDX <- (Val.mulhu rs#EAX rs#r1))) m t
  | Pdiv r1 =>
      let vn := rs#EAX in let vd := (rs#EDX <- Vundef)#r1 in
      match Val.divu vn vd, Val.modu vn vd with
      | Some vq, Some vr => Nxt (nextinstr_nf (rs#EAX <- vq #EDX <- vr)) m t
      | _, _ => Stck
      end
  | Pidiv r1 =>
      let vn := rs#EAX in let vd := (rs#EDX <- Vundef)#r1 in
      match Val.divs vn vd, Val.mods vn vd with
      | Some vq, Some vr => Nxt (nextinstr_nf (rs#EAX <- vq #EDX <- vr)) m t
      | _, _ => Stck
      end
  | Pand_rr rd r1 =>
      Nxt (nextinstr_nf (rs#rd <- (Val.and rs#rd rs#r1))) m t
  | Pand_ri rd n =>
      Nxt (nextinstr_nf (rs#rd <- (Val.and rs#rd (Vint n)))) m t
  | Por_rr rd r1 =>
      Nxt (nextinstr_nf (rs#rd <- (Val.or rs#rd rs#r1))) m t
  | Por_ri rd n =>
      Nxt (nextinstr_nf (rs#rd <- (Val.or rs#rd (Vint n)))) m t
  | Pxor_r rd =>
      Nxt (nextinstr_nf (rs#rd <- Vzero)) m t
  | Pxor_rr rd r1 =>
      Nxt (nextinstr_nf (rs#rd <- (Val.xor rs#rd rs#r1))) m t
  | Pxor_ri rd n =>
      Nxt (nextinstr_nf (rs#rd <- (Val.xor rs#rd (Vint n)))) m t
  | Pnot rd =>
      Nxt (nextinstr_nf (rs#rd <- (Val.notint rs#rd))) m t
  | Psal_rcl rd =>
      Nxt (nextinstr_nf (rs#rd <- (Val.shl rs#rd rs#ECX))) m t
  | Psal_ri rd n =>
      Nxt (nextinstr_nf (rs#rd <- (Val.shl rs#rd (Vint n)))) m t
  | Pshr_rcl rd =>
      Nxt (nextinstr_nf (rs#rd <- (Val.shru rs#rd rs#ECX))) m t
  | Pshr_ri rd n =>
      Nxt (nextinstr_nf (rs#rd <- (Val.shru rs#rd (Vint n)))) m t
  | Psar_rcl rd =>
      Nxt (nextinstr_nf (rs#rd <- (Val.shr rs#rd rs#ECX))) m t
  | Psar_ri rd n =>
      Nxt (nextinstr_nf (rs#rd <- (Val.shr rs#rd (Vint n)))) m t
  | Pshld_ri rd r1 n =>
      Nxt (nextinstr_nf
              (rs#rd <- (Val.or (Val.shl rs#rd (Vint n))
                                (Val.shru rs#r1 (Vint (Int.sub Int.iwordsize n)))))) m t
  | Pror_ri rd n =>
      Nxt (nextinstr_nf (rs#rd <- (Val.ror rs#rd (Vint n)))) m t
  | Pcmp_rr r1 r2 =>
      Nxt (nextinstr (compare_ints (rs r1) (rs r2) rs m)) m t
  | Pcmp_ri r1 n =>
      Nxt (nextinstr (compare_ints (rs r1) (Vint n) rs m)) m t
  | Ptest_rr r1 r2 =>
      Nxt (nextinstr (compare_ints (Val.and (rs r1) (rs r2)) Vzero rs m)) m t
  | Ptest_ri r1 n =>
      Nxt (nextinstr (compare_ints (Val.and (rs r1) (Vint n)) Vzero rs m)) m t
  | Pcmov c rd r1 =>
      match eval_testcond c rs with
      | Some true => Nxt (nextinstr (rs#rd <- (rs#r1))) m t
      | Some false => Nxt (nextinstr rs) m t
      | None => Nxt (nextinstr (rs#rd <- Vundef)) m t
      end
  | Psetcc c rd =>
      Nxt (nextinstr (rs#rd <- (Val.of_optbool (eval_testcond c rs)))) m t
  (** Arithmetic operations over double-precision floats *)
  | Paddd_ff rd r1 =>
      Nxt (nextinstr (rs#rd <- (Val.addf rs#rd rs#r1))) m t
  | Paddpd_ff brd br1 =>
    let (rd,rd') := split_big_freg brd in
    let (r1,r1') := split_big_freg br1 in
    let nrd := Val.addf rs#rd rs#r1 in
    let nrd' := Val.addf rs#rd' rs#r1' in
    Nxt (nextinstr ((rs#rd <- nrd)#rd' <- nrd')) m t
  | Pmulpd_ff brd br1 =>
    let (rd,rd') := split_big_freg brd in
    let (r1,r1') := split_big_freg br1 in
    let nrd := Val.mulf rs#rd rs#r1 in
    let nrd' := Val.mulf rs#rd' rs#r1' in
    Nxt (nextinstr ((rs#rd <- nrd)#rd' <- nrd')) m t
  | Psubd_ff rd r1 =>
      Nxt (nextinstr (rs#rd <- (Val.subf rs#rd rs#r1))) m t
  | Pmuld_ff rd r1 =>
      Nxt (nextinstr (rs#rd <- (Val.mulf rs#rd rs#r1))) m t
  | Pdivd_ff rd r1 =>
      Nxt (nextinstr (rs#rd <- (Val.divf rs#rd rs#r1))) m t
  | Pnegd rd =>
      Nxt (nextinstr (rs#rd <- (Val.negf rs#rd))) m t
  | Pabsd rd =>
      Nxt (nextinstr (rs#rd <- (Val.absf rs#rd))) m t
  | Pcomisd_ff r1 r2 =>
      Nxt (nextinstr (compare_floats (rs r1) (rs r2) rs)) m t
  | Pxorpd_f rd =>
      Nxt (nextinstr_nf (rs#rd <- (Vfloat Float.zero))) m t
  (** Arithmetic operations over single-precision floats *)
  | Padds_ff rd r1 =>
      Nxt (nextinstr (rs#rd <- (Val.addfs rs#rd rs#r1))) m t
  | Psubs_ff rd r1 =>
      Nxt (nextinstr (rs#rd <- (Val.subfs rs#rd rs#r1))) m t
  | Pmuls_ff rd r1 =>
      Nxt (nextinstr (rs#rd <- (Val.mulfs rs#rd rs#r1))) m t
  | Pdivs_ff rd r1 =>
      Nxt (nextinstr (rs#rd <- (Val.divfs rs#rd rs#r1))) m t
  | Pnegs rd =>
      Nxt (nextinstr (rs#rd <- (Val.negfs rs#rd))) m t
  | Pabss rd =>
      Nxt (nextinstr (rs#rd <- (Val.absfs rs#rd))) m t
  | Pcomiss_ff r1 r2 =>
      Nxt (nextinstr (compare_floats32 (rs r1) (rs r2) rs)) m t
  | Pxorps_f rd =>
      Nxt (nextinstr_nf (rs#rd <- (Vsingle Float32.zero))) m t
  (** Branches and calls *)
  | Pjmp_l lbl =>
      goto_label_bits t f lbl b rs m
  | Pjmp_s id sg =>
      match Genv.symbol_address ge id Int.zero with
        | Vptr b i =>
          match pinj t b i with
            | Some bits => Nxt (rs#PC <- (Vint bits)) m t
            | None => Stck
          end
        | _ => Nxt (rs#PC <- (Genv.symbol_address ge id Int.zero)) m t
      end
  | Pjmp_r r sg =>
      Nxt (rs#PC <- (rs r)) m t
  | Pjcc cond lbl =>
      match eval_testcond cond rs with
      | Some true => goto_label_bits t f lbl b rs m
      | Some false => Nxt (nextinstr rs) m t
      | None => Stck
      end
  | Pjcc2 cond1 cond2 lbl =>
      match eval_testcond cond1 rs, eval_testcond cond2 rs with
      | Some true, Some true => goto_label_bits t f lbl b rs m
      | Some _, Some _ => Nxt (nextinstr rs) m t
      | _, _ => Stck
      end
  | Pjmptbl r tbl =>
      match rs#r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stck
          | Some lbl => goto_label_bits t f lbl b rs m
          end
      | _ => Stck
      end
  | Pcall_s id sg =>
    match Genv.symbol_address ge id Int.zero with
      | Vptr b i =>
        match pinj t b i with
          | Some bits => Nxt (rs # RA <- (Val.add (rs PC) Vone)) # PC <- (Vint bits) m t
          | None => Stck
        end
      | _ => Nxt (rs # RA <- (Val.add (rs PC) Vone)) # PC <- (Genv.symbol_address ge id Int.zero) m t
    end
  | Pcall_r r sg =>
      Nxt (rs#RA <- (Val.add rs#PC Vone) #PC <- (rs r)) m t
  | Pret _ =>
      Nxt (rs#PC <- (rs#RA)) m t
  (** Saving and restoring registers *)
  | Pmov_rm_a rd a =>
      exec_load_bits t Many32 m a rs rd
  | Pmov_mr_a a r1 =>
      exec_store_bits t Many32 m a rs r1 nil
  | Pmovsd_fm_a rd a =>
      exec_load_bits t Many64 m a rs rd
  | Pmovsd_mf_a a r1 =>
      exec_store_bits t Many64 m a rs r1 nil
  (** Pseudo-instructions *)
  | Plabel lbl =>
      Nxt (nextinstr rs) m t
  | Pallocframe sz ofs_ra ofs_link =>
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := Vptr stk Int.zero in
      let t' := md_alloc t 0 sz stk in
      match storev_bits Mint32 m1 (Val.add sp (Vint ofs_link)) rs#ESP with
      | None => Stck
      | Some m2 =>
          match storev_bits Mint32 m2 (Val.add sp (Vint ofs_ra)) rs#RA with
          | None => Stck
          | Some m3 =>
            match pinj t' stk Int.zero with
              | Some bits => Nxt (nextinstr (rs #EDX <- (rs#ESP) #ESP <- (Vint bits))) m3 t'
              | None => Stck
            end
          end
      end
  | Pfreeframe sz ofs_ra ofs_link =>
    match rs#ESP with
      | Vint bits =>
        match (psur t (Int.add bits ofs_ra)) with
          | Some (b,ofs) =>
            match Mem.loadv Mint32 m (Vptr b ofs) with
              | None => Stck
              | Some ra =>
                match (psur t (Int.add bits ofs_link)) with
                  | Some (b',ofs') =>
                    match Mem.loadv Mint32 m (Vptr b' ofs') with
                      | None => Stck
                      | Some sp =>
                        match Mem.free m b 0 sz with
                          | None => Stck
                          | Some m' => Nxt (nextinstr (rs#ESP <- sp #RA <- ra)) m' (md_free t 0 sz b)
                        end
                    end
                  | None => Stck
                end
            end
          | None => Stck
        end
      | _ => Stck
    end
  | Pbuiltin ef args res =>
      Stck                             (**r treated specially below *)
  | Pannot ef args =>
      Stck                             (**r treated specially below *)
  end.


End RELSEM_BITS.

Definition no_ptr_regs (rs : regset) : Prop :=
  forall x b i, rs x <> Vptr b i.

Definition no_ptr_mem (m : Memory.Mem.mem) : Prop :=
  forall z ofs,
    match ZMap.get z ((Memory.Mem.mem_contents m) !! ofs) with
      | Undef => True
      | Byte _ => True
      | Fragment v q n => forall x y, v <> Vptr x y
    end.


Inductive extcall_arg_bits (t: allocator_metadata) (rs: regset) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg_bits: forall r,
      extcall_arg_bits t rs m (R r) (rs (preg_of r))
  | extcall_arg_stack_bits:
      forall ofs ty stack_ofs v bits b o,
        stack_ofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
        (Val.add (rs (IR ESP)) (Vint (Int.repr stack_ofs))) = Vint bits ->
        psur t bits = Some (b,o) ->
        Mem.loadv (chunk_of_type ty) m (Vptr b o) = Some v ->
        extcall_arg_bits t rs m (S Outgoing ofs ty) v.

Definition extcall_arguments_bits (t : allocator_metadata)
    (rs: regset) (m: mem) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg_bits t rs m) (loc_arguments sg) args.

Section EVAL_ANNOT_ARG_BITS.

Variable t: allocator_metadata.
Variable ge: Senv.t.
Variable e: preg -> val.
Variable sp: val.
Variable m: mem.

Hypothesis mm : match_metadata t m.

Inductive eval_annot_arg_bits : annot_arg preg -> val -> Prop :=
  | eval_AA_base_bits : forall x : preg, eval_annot_arg_bits (AA_base x) (e x)
  | eval_AA_int_bits : forall n : int,
                  eval_annot_arg_bits (AA_int n) (Vint n)
  | eval_AA_long_bits : forall n : int64,
                   eval_annot_arg_bits (AA_long n) (Vlong n)
  | eval_AA_float_bits : forall n : float,
                    eval_annot_arg_bits (AA_float n) (Vfloat n)
  | eval_AA_single_bits : forall n : float32,
                     eval_annot_arg_bits (AA_single n) (Vsingle n)
  | eval_AA_loadstack_bits : forall chunk ofs v bits b o,
                               sp = Vint bits ->
                               psur t (Int.add bits ofs) = Some (b,(Int.add o ofs)) ->
                               Mem.loadv chunk m (Val.add (Vptr b o) (Vint ofs)) = Some v ->
                               eval_annot_arg_bits (AA_loadstack chunk ofs) v
  | eval_AA_addrstack_bits : forall ofs : int,
                        eval_annot_arg_bits (AA_addrstack ofs)
                          (Val.add sp (Vint ofs))
  | eval_AA_loadglobal_bits : forall (chunk : memory_chunk) 
                           (id : ident) (ofs : int) 
                           (v : val),
                         Mem.loadv chunk m (Senv.symbol_address ge id ofs) =
                         Some v ->
                         eval_annot_arg_bits (AA_loadglobal chunk id ofs) v
  | eval_AA_addrglobal_bits : forall (id : ident) (ofs : int) b o bits,
                                Senv.symbol_address ge id ofs = Vptr b o ->
                                pinj t b o = Some bits ->
                         eval_annot_arg_bits (AA_addrglobal id ofs)
                                             (Vint bits)
  | eval_AA_addrglobal_undef : forall id ofs,
                                 Senv.symbol_address ge id ofs = Vundef ->
                                 eval_annot_arg_bits (AA_addrglobal id ofs) (Vundef)
  | eval_AA_longofwords_bits : forall (hi lo : annot_arg preg) (vhi vlo : val),
                          eval_annot_arg_bits hi vhi ->
                          eval_annot_arg_bits lo vlo ->
                          eval_annot_arg_bits 
                            (AA_longofwords hi lo) 
                            (Val.longofwords vhi vlo).

Definition eval_annot_args_bits 
           (al: list (annot_arg preg)) (vl: list val) : Prop :=
  list_forall2 eval_annot_arg_bits al vl.

Lemma eval_annot_arg_bits_determ:
  forall a v, eval_annot_arg_bits a v -> forall v', eval_annot_arg_bits a v' -> v' = v.
Proof.
  induction 1; intros v' EV; inv EV; try congruence.
  inv H4. rewrite H5 in H0. inv H0.
  unfold Val.add in *.
  destruct (Int.add o0 ofs) eqn:?.
  destruct (Int.add o ofs) eqn:?.
  subst intval.
  assert (intrange = intrange0).
  eapply proof_irrelevance; eauto.
  subst intrange.
  congruence.

  f_equal; eauto.
Qed.

Lemma eval_annot_arg_bitss_determ:
  forall al vl, eval_annot_args_bits al vl -> forall vl', eval_annot_args_bits al vl' -> vl' = vl.
Proof.
  induction 1; intros v' EV; inv EV; f_equal; eauto using eval_annot_arg_bits_determ.
Qed.

End EVAL_ANNOT_ARG_BITS.

Hint Constructors eval_annot_arg_bits: aarg.

Section EVAL_ANNOT_ARG_BITS_PRESERVED.

Variables F1 V1 F2 V2: Type.
Variable t : allocator_metadata.
Variable ge1: Genv.t F1 V1.
Variable ge2: Genv.t F2 V2.
Variable e: preg -> val.
Variable sp: val.
Variable m: mem.

Hypothesis symbols_preserved:
  forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id.

Lemma eval_annot_arg_bits_preserved:
  forall a v, eval_annot_arg_bits t ge1 e sp m a v -> eval_annot_arg_bits t ge2 e sp m a v.
Proof.
  assert (EQ: forall id ofs, Senv.symbol_address ge2 id ofs = Senv.symbol_address ge1 id ofs).
  { unfold Senv.symbol_address; simpl; intros. rewrite symbols_preserved; auto. }
  induction 1; eauto with aarg. rewrite <- EQ in H; eauto with aarg.
  econstructor; eauto. congruence.
  econstructor; eauto. congruence.
Qed. 

Lemma eval_annot_arg_bitss_preserved:
  forall al vl, eval_annot_args_bits t ge1 e sp m al vl -> eval_annot_args_bits t ge2 e sp m al vl.
Proof.
  induction 1; constructor; auto; eapply eval_annot_arg_bits_preserved; eauto. 
Qed.

End EVAL_ANNOT_ARG_BITS_PRESERVED.

Definition in_var_range (ge : Genv.t fundef unit) (b : block) (ofs : int) : Prop :=
  match Genv.find_var_info ge b with
    | Some v =>
      let sz := Genv.init_data_list_size (gvar_init v) in
      0 <= Int.unsigned ofs < sz
    | None => False
  end.



Definition in_code_range (ge : Genv.t fundef unit) (b : block) (ofs : int) : Prop :=
  match Genv.find_funct_ptr ge b with
    | Some (Internal f) =>
      let sz := zlen (fn_code f) in
      0 <= Int.unsigned ofs < sz
    | Some (External e) =>
      0 <= Int.unsigned ofs < 1
    | None => False
  end.


Definition is_global (ge : Genv.t fundef unit) (b : block) (ofs : int) : Prop :=
  in_code_range ge b ofs \/ in_var_range ge b ofs.


Definition valid_globals (ge : Genv.t fundef unit) (m : mem) :=
  forall b ofs,
    is_global ge b ofs ->
    Mem.valid_pointer m b (Int.unsigned ofs) = true.


Definition global_perms (ge : Genv.t fundef unit) (m : mem) :=
  forall b ofs,
    is_global ge b ofs ->
    exists p,
      (Mem.mem_access m) !! b (Int.unsigned ofs) Cur = Some p /\
      p <> Freeable.


Lemma global_perms_valid_globals :
  forall ge m,
    global_perms ge m ->
    valid_globals ge m.
Proof.
  intros.
  unfold valid_globals.
  intros.
  unfold global_perms in *.
  eapply H in H0.
  destruct H0.
  destruct H0.
  unfold Mem.valid_pointer.
  unfold proj_sumbool.
  destruct (Mem.perm_dec m b (Int.unsigned ofs) Cur Nonempty) eqn:?;
           try reflexivity.
  exfalso. apply n.
  unfold Mem.perm.
  unfold Mem.perm_order'.
  rewrite H0.
  econstructor.
Qed.

Section STEP_SEM.

  Variable ge : genv.

  Inductive state_bits : Type :=
    | State_bits : regset -> mem -> allocator_metadata -> state_bits.

Inductive step_bits: state_bits -> trace -> state_bits -> Prop :=
  | exec_step_internal_bits:
      forall b ofs f i rs m rs' m' bits md md',
        rs PC = Vint bits ->
        psur md bits = Some (b,ofs) ->
        no_ptr_regs rs ->
        no_ptr_mem m ->
        Genv.find_funct_ptr ge b = Some (Internal f) ->
        find_instr (Int.unsigned ofs) f.(fn_code) = Some i ->
        exec_instr_bits ge md f i b rs m = Nxt rs' m' md' ->
        match_metadata md m ->
        global_perms ge m ->
        step_bits (State_bits rs m md) E0 (State_bits rs' m' md')
  | exec_step_builtin_bits:
      forall b ofs f ef args res rs m t vl rs' m' bits md,
        rs PC = Vint bits ->
        psur md bits = Some (b,ofs) ->
        Genv.find_funct_ptr ge b = Some (Internal f) ->
        find_instr (Int.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
        external_call' ef ge (map rs args) m t vl m' ->
        rs' = nextinstr_nf
                (set_regs res vl
                          (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
        no_ptr_regs rs' ->
        no_ptr_mem m' ->
        match_metadata md m ->
        global_perms ge m ->
      step_bits (State_bits rs m md) t (State_bits rs' m' (md_ec' md ef ge (map rs args) m t vl m'))
  | exec_step_annot_bits:
      forall b ofs bits f ef args rs m vargs t v m' md,
        rs PC = Vint bits ->
        psur md bits = Some (b,ofs) ->
        no_ptr_regs rs ->
        no_ptr_mem m ->
        Genv.find_funct_ptr ge b = Some (Internal f) ->
        find_instr (Int.unsigned ofs) f.(fn_code) = Some (Pannot ef args) ->
        eval_annot_args_bits md ge rs (rs ESP) m args vargs ->
        external_call ef ge vargs m t v m' ->
        no_ptr_mem m' ->
        match_metadata md m ->
        global_perms ge m ->
        step_bits (State_bits rs m md) t
             (State_bits (nextinstr rs) m' (md_ec md ef ge vargs m t v m'))
  | exec_step_external_bits:
      forall b ef args res rs m t rs' m' bits md,
        rs PC = Vint bits ->
        psur md bits = Some (b,Int.zero) ->
        Genv.find_funct_ptr ge b = Some (External ef) ->
        extcall_arguments_bits md rs m (ef_sig ef) args ->
        external_call' ef ge args m t res m' ->
        rs' = (set_regs (loc_external_result (ef_sig ef)) res rs) #PC <- (rs RA) ->
        no_ptr_regs rs' ->
        no_ptr_mem m' ->
        match_metadata md m ->
        global_perms ge m ->
        step_bits (State_bits rs m md) t (State_bits rs' m' (md_ec' md ef ge args m t res m')).


End STEP_SEM.

Definition store_init_data_bits (md : allocator_metadata) (ge : Genv.t fundef unit) (m : mem) (b : block) (p : Z) (id : init_data) :=
  match id with
    | Init_int8 n => store_bits Mint8unsigned m b p (Vint n)
    | Init_int16 n => store_bits Mint16unsigned m b p (Vint n)
    | Init_int32 n => store_bits Mint32 m b p (Vint n)
    | Init_int64 n => store_bits Mint64 m b p (Vlong n)
    | Init_float32 n => store_bits Mfloat32 m b p (Vsingle n)
    | Init_float64 n => store_bits Mfloat64 m b p (Vfloat n)
    | Init_space _ => Some m
    | Init_addrof symb ofs =>
      match Genv.find_symbol ge symb with
        | Some b' =>
          match (pinj md b' ofs) with
            | Some bits => store_bits Mint32 m b p (Vint bits)
            | None => None
          end
        | None => None
      end
  end.


Fixpoint store_init_data_list_bits (md : allocator_metadata) (ge : Genv.t fundef unit) (m : mem) (b : block) (p : Z) (idl : list init_data) : option mem :=
  match idl with
    | nil => Some m
    | id :: idl' =>
      match store_init_data_bits md ge m b p id with
        | Some m' =>
          store_init_data_list_bits md ge m' b (p + Genv.init_data_size id) idl'
        | None => None
      end
  end.


Function store_zeros_bits (m: mem) (b: block) (p: Z) (n: Z) {wf (Zwf 0) n}: option mem :=
  if zle n 0 then Some m else
    match store_bits Mint8unsigned m b p Vzero with
    | Some m' => store_zeros_bits m' b (p + 1) (n - 1)
    | None => None
    end.
Proof.
  intros. red. omega.
  apply Zwf_well_founded.
Qed.


Definition alloc_only_global_bits (md : allocator_metadata) (ge : Genv.t fundef unit)
           (m : mem) (idg : ident * globdef fundef unit) : option (mem * allocator_metadata * ident * block * globdef fundef unit) :=
  let (id,g) := idg in
  match g with
    | Gfun (Internal f) =>
      let (m1, b) := Mem.alloc m 0 (zlen (fn_code f)) in
      match Mem.drop_perm m1 b 0 (zlen (fn_code f)) Writable with
        | Some m' => Some (m', md_alloc md 0 (zlen (fn_code f)) b,id, b, g)
        | None => None
      end
    | Gfun (External ef) =>
      let (m1, b) := Mem.alloc m 0 1 in
      match Mem.drop_perm m1 b 0 1 Writable with
        | Some m' => Some (m', md_alloc md 0 1 b,id, b, g)
        | None => None
      end
    | Gvar v =>
      let init := gvar_init v in
      let sz := Genv.init_data_list_size init in
      let (m1, b) := Mem.alloc m 0 sz in
      let md' := md_alloc md 0 sz b in
      match Mem.drop_perm m1 b 0 sz Writable with
        | Some m2 =>
          Some (m2,md',id,b, g)
        | None => None
      end
  end.


                                 

Definition store_global_bits (md : allocator_metadata) (ge : Genv.t fundef unit)
           (m : mem) (b : block) (g : globdef fundef unit) : option (mem * allocator_metadata) :=
  match g with
    | Gvar v =>
      let init := gvar_init v in
      let sz := Genv.init_data_list_size init in
      match store_zeros_bits m b 0 sz with
        | Some m2 =>
          match store_init_data_list_bits md ge m2 b 0 init with
            | Some m3 =>
              match set_perm m3 b 0 sz (Genv.perm_globvar v) with
                | Some m4 => Some (m4, md)
                | None => None
              end
            | None => None
          end
        | None => None
      end
    | Gfun f =>
      let sz := match f with
                  | Internal fd => Z.max (zlen (fn_code fd)) 1
                  | External e => 1
                end in
      match set_perm m b 0 sz Nonempty with
        | Some m' => Some (m',md)
        | None => None
      end
  end.

Fixpoint alloc_only_globals_bits (md : allocator_metadata) (ge : Genv.t fundef unit)
         (m : mem) (gl : list (ident * globdef fundef unit)) : option (mem * allocator_metadata * list (ident * block * globdef fundef unit)) :=
  match gl with
    | nil => Some (m,md,nil)
    | g :: gl' =>
      match alloc_only_global_bits md ge m g with
        | Some (m',md',id,b,gv) =>
          match alloc_only_globals_bits md' ge m' gl' with
            | Some (m'',md'',l) => Some (m'',md'',(id,b,gv)::l)
            | None => None
          end
        | None => None
      end
  end.


Fixpoint store_globals_bits (md : allocator_metadata) (ge : Genv.t fundef unit)
         (m : mem) (gl : list (ident * block * globdef fundef unit)) : option (mem * allocator_metadata) :=
  match gl with
    | nil => Some (m,md)
    | (id,b,g) :: gl' =>
      match store_global_bits md ge m b g with
        | Some (m',md') => store_globals_bits md' ge m' gl'
        | None => None
      end
  end.

Definition alloc_globals_bits (md : allocator_metadata) (ge : Genv.t fundef unit)
           (m : mem) (gl : list (ident * globdef fundef unit)) : option (mem * allocator_metadata) :=
  match alloc_only_globals_bits md ge m gl with
    | Some (m',md',l) =>
      store_globals_bits md' ge m' l
    | None => None
  end.

Definition init_mem_bits (p : program) : option (mem * allocator_metadata) :=
  alloc_globals_bits md_init (Genv.globalenv p) Mem.empty (prog_defs p).

(** Execution of whole programs. *)

Inductive initial_state_bits (p: program): state_bits -> Prop :=
| initial_state_intro_bits:
    forall m0 md bits,
      init_mem_bits p = Some (m0,md) ->
      match Genv.symbol_address (Genv.globalenv p) p.(prog_main) Int.zero with
        | Vptr b i => psur md bits = Some (b,i)
        | _ => Int.zero = bits
      end ->
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (Vint bits)
        # RA <- Vzero
        # ESP <- Vzero in
      initial_state_bits p (State_bits rs0 m0 md).

Inductive final_state_bits: state_bits -> int -> Prop :=
  | final_state_intro: forall rs m r md,
      rs#PC = Vzero ->
      rs#EAX = Vint r ->
      final_state_bits (State_bits rs m md) r.

Definition semantics_bits (p: program) :=
  Semantics step_bits (initial_state_bits p) final_state_bits (Genv.globalenv p).

