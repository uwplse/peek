Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Axioms.
Require Import Floats.
Require Import Asm.
Require Import AsmBits.
Require Import MemoryAxioms.
Require Import ValEq.
Require Import MemEq.

(* callee save registers *)
Definition regs_live_across_call : list preg := PC :: RA :: ST0 :: IR EBX :: IR ESI :: IR EDI :: IR EBP :: IR ESP :: nil.

(* caller save registers *)
(* should this be all the rest? *)
(* not sure this is correct *)
(* not sure this is necessary either *)
Definition regs_dead_across_call : list preg :=
  IR EAX :: IR ECX :: IR EDX ::
     FR XMM0 :: FR XMM1 :: FR XMM2 :: FR XMM3 :: FR XMM4 :: FR XMM5 :: FR XMM6 :: FR XMM7 ::
     FRH XMM0H :: FRH XMM1H :: FRH XMM2H :: FRH XMM3H :: FRH XMM4H :: FRH XMM5H :: FRH XMM6H :: FRH XMM7H ::
  CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil.

Lemma call_conv_coverage :
  forall p,
    (In p regs_live_across_call \/ In p regs_dead_across_call).
Proof.
  intros.
  destruct p; 
  try destruct i;
  try destruct f;
  try destruct c;
  try destruct h;
  try solve [(left; simpl; repeat ((try left; reflexivity) || right))];
  try solve [(right; simpl; repeat ((try left; reflexivity) || right))].
Qed.

(* all registers that it's possible to pass arguments in *)
Definition parameter_regs : list preg := nil.

(* all registers that it's possible to return results in *)
Definition return_regs (t : option typ) : list preg := 
  match t with
  | None => nil
  | Some Tint => IR EAX :: nil
  | Some (Tfloat | Tsingle) => ST0 :: nil
  | Some Tlong => IR EDX :: IR EAX :: nil
  | Some Tany32 => IR EAX :: ST0 :: nil
  | Some Tany64 => IR EDX :: IR EAX :: ST0 :: nil
  end.

Definition return_regs_sig (t : option signature) : list preg :=
  match t with
  | None => nil
  | Some t' => return_regs (sig_res t')
  end.

Definition all_return_regs : list preg :=
  IR EAX :: IR EDX :: ST0 :: nil.

Lemma all_return_regs_spec :
  forall p t,
    In p (return_regs t) ->
    In p all_return_regs.
Proof.
  intros. 
  destruct t; try destruct t;
  simpl in H; simpl; destruct H;
  auto; destruct H; auto.
Qed.

Definition is_call_return (i : instruction) : Prop :=
  match i with
    | Pcall_r _ _ => True
    | Pcall_s _ _ => True
    | Pjmp_r _ _ => True
    | Pjmp_s _ _ => True
    | Pret _ => True
    | _ => False
  end.

Definition is_call (i : instruction) : Prop :=
  match i with
    | Pcall_r _ _ => True
    | Pcall_s _ _ => True
    | Pjmp_r _ _ => True
    | Pjmp_s _ _ => True
    | _ => False
  end.

Definition is_return (i : instruction) : Prop :=
  match i with
    | Pret _ => True
    | _ => False
  end.

Definition call_type (i : instruction) : option signature :=
  match i with
    | Pjmp_s _ t => Some t
    | Pjmp_r _ t => Some t
    | Pcall_r _ t => Some t
    | Pcall_s _ t => Some t
    | Pret t => Some t
    | _ => None
  end.

Lemma is_call_return_dec :
  forall i,
    { is_call_return i } + { ~ is_call_return i}.
Proof.
  intros.
  destruct i; auto;
  left; simpl; auto.
Defined.

Lemma is_call_dec :
  forall i,
    { is_call i } + { ~ is_call i}.
Proof.
  intros.
  destruct i; auto;
  left; simpl; auto.
Defined.

Lemma is_call_or_return_dec :
  forall i,
    is_call_return i ->
    (is_call i \/ exists p, i = Pret p).
Proof.
  intros. 
  destruct i; inv H;
  try (left; simpl; solve [auto]).
  right. eauto.
Defined.

(* THE FOLLOWING IS OUT OF DATE, DOESN'T USE VAL_EQ AND MEM_EQ CORRECTLY
(* if return steps to a state, it steps to the instruction after a call *)
Definition return_steps_back_to_call (p : Asm.program) : Prop :=
  forall rs m rs' m' t b i s c typ,
    step (Genv.globalenv p) (State rs m) t (State rs' m') ->
    rs PC = Values.Vptr b i ->
    Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal (mkfunction s c)) ->
    find_instr (Int.unsigned i) c = Some (Pret typ) ->
    exists b',
      exists i',
        rs' PC = Values.Vptr b' i' /\ 
        (exists s' c' instr,
           (Genv.find_funct_ptr (Genv.globalenv p) b' = Some (Internal (mkfunction s' c')) /\
            find_instr ((Int.unsigned i') - 1) c' = Some instr /\
            is_call instr)).


(* calls step to the beginning of the block *)
Definition call_steps_to_beginning (p : Asm.program) : Prop :=
  forall rs m rs' m' t b i s c instr,
    step (Genv.globalenv p) (State rs m) t (State rs' m') ->
    rs PC = Values.Vptr b i ->
    Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal (mkfunction s c)) ->
    find_instr (Int.unsigned i) c = Some instr ->
    is_call instr ->
    exists b' f, 
      rs' PC = Values.Vptr b' (Int.zero) /\
      Genv.find_funct_ptr (Genv.globalenv p) b' = Some f.

(* the callee_save_regs liveness fun is correct for call steps *)
(* if we have two states that are at the same point, and agree on
callee_save regs and one can take a step across a call or return, then
the other can too, and the resulting states agree on callee_save regs
*)
Definition call_liveness_correct (p : Asm.program) : Prop :=
  forall sl sr ml sl' ml' mr t b i s c instr,
    step (Genv.globalenv p) (State sl ml) t (State sl' ml') ->
    mem_eq ml mr ->
    sl PC = Values.Vptr b i ->
    Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal (mkfunction s c)) ->
    find_instr (Int.unsigned i) c = Some instr ->
    is_call instr ->
    (forall r, In r (regs_live_across_call ++ parameter_regs) -> val_eq (sl r) (sr r)) ->
    (exists sr' mr', (step (Genv.globalenv p) (State sr mr) t (State sr' mr') /\
                      (forall r, In r regs_live_across_call -> val_eq (sl' r) (sr' r))) /\
                     (mem_eq ml' mr')).

Definition return_liveness_correct (p : Asm.program) : Prop :=
  forall sl sr ml sl' ml' mr t b i s c args res cc,
    step (Genv.globalenv p) (State sl ml) t (State sl' ml') ->
    sl PC = Values.Vptr b i ->
    Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal (mkfunction s c)) ->
    find_instr (Int.unsigned i) c = Some (Pret (mksignature args res cc)) ->
    (forall r, In r (regs_live_across_call ++ (return_regs res)) -> sl r = sr r) ->
    (exists sr' mr', (step (Genv.globalenv p) (State sr m) t (State sr' m') /\
                  (forall r, In r (regs_live_across_call ++ (return_regs res)) -> sl' r = sr' r))).

Definition external_fun_steps_back_to_call (p : Asm.program) : Prop :=
  forall rs m rs' m' t b i ef instr,
    step (Genv.globalenv p) (State rs m) t (State rs' m') ->
    rs PC = Values.Vptr b i ->
    Genv.find_funct_ptr (Genv.globalenv p) b = Some (External ef) ->
    exists b',
      exists i',
        rs' PC = Values.Vptr b' i' /\
        (exists s' c',
           (Genv.find_funct_ptr (Genv.globalenv p) b' = Some (Internal (mkfunction s' c')) /\
            find_instr ((Int.unsigned i') - 1) c' = Some instr /\
            is_call instr)).
  
Definition external_fun_liveness_correct (p : Asm.program) : Prop :=
  forall sl sr m sl' m' t b i ef,
    step (Genv.globalenv p) (State sl m) t (State sl' m') ->
    sl PC = Values.Vptr b i ->
    Genv.find_funct_ptr (Genv.globalenv p) b = Some (External ef) ->
    (forall r, In r regs_live_across_call -> sl r = sr r) ->
    (exists sr', (step (Genv.globalenv p) (State sr m) t (State sr' m') /\
                 (forall r, In r (regs_live_across_call ++ (return_regs (sig_res (ef_sig ef)))) -> sl' r = sr' r))).

Definition internal_calls_well_typed (p : Asm.program) : Prop :=
  forall rs m t rs' m' b i b' i' s c s' c' sig instr,
    step (Genv.globalenv p) (State rs m) t (State rs' m') ->
    rs PC = Values.Vptr b i ->
    rs' PC = Values.Vptr b' i' ->
    Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal (mkfunction s c)) ->
    Genv.find_funct_ptr (Genv.globalenv p) b' = Some (Internal (mkfunction s' c')) ->
    find_instr (Int.unsigned i) c = Some (Pret sig) ->
    find_instr (Int.unsigned i' - 1) c' = Some instr ->
    is_call instr ->
    call_type instr = Some sig.

Definition external_calls_well_typed (p : Asm.program) : Prop :=
  forall rs m t rs' m' b i b' i' s c ef instr,
    step (Genv.globalenv p) (State rs m) t (State rs' m') ->
    rs PC = Values.Vptr b i ->
    rs' PC = Values.Vptr b' i' ->
    Genv.find_funct_ptr (Genv.globalenv p) b = Some (External ef) ->
    Genv.find_funct_ptr (Genv.globalenv p) b' = Some (Internal (mkfunction s c)) ->
    find_instr (Int.unsigned i' - 1) c = Some instr ->
    is_call instr ->
    call_type instr = Some (ef_sig ef).

Definition calls_well_typed (p : Asm.program) : Prop :=
  internal_calls_well_typed p /\ external_calls_well_typed p.

Definition calling_conv_correct (p : Asm.program) : Prop :=
  return_steps_back_to_call p /\ call_steps_to_beginning p /\
  call_liveness_correct p /\ return_liveness_correct p /\ 
  external_fun_liveness_correct p /\ external_fun_steps_back_to_call p /\ calls_well_typed p.

 *)


(* if return steps to a state, it steps to the instruction after a call *)
Definition return_steps_back_to_call_bits (p : Asm.program) : Prop :=
  forall rs ml rs' ml'  t b i s c typ bits md md',
    step_bits (Genv.globalenv p) (State_bits rs ml md) t (State_bits rs' ml' md') ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,i) ->
    Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal (mkfunction s c)) ->
    find_instr (Int.unsigned i) c = Some (Pret typ) ->
    exists b',
      exists i',
        exists bits',
          psur md' bits' = Some (b',i') /\
        rs' PC = Values.Vint bits' /\ 
        (exists s' c' instr,
           (Genv.find_funct_ptr (Genv.globalenv p) b' = Some (Internal (mkfunction s' c')) /\
            find_instr ((Int.unsigned i') - 1) c' = Some instr /\
            is_call instr)).


(* calls step to the beginning of the block *)
Definition call_steps_to_beginning_bits (p : Asm.program) : Prop :=
  forall rs m rs' m' t b i s c instr bits md md',
    step_bits (Genv.globalenv p) (State_bits rs m md) t (State_bits rs' m' md') ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,i) ->
    Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal (mkfunction s c)) ->
    find_instr (Int.unsigned i) c = Some instr ->
    is_call instr ->
    exists bits' b' f, 
      rs' PC = Values.Vint bits' /\
      psur md' bits' = Some (b',Int.zero) /\
      Genv.find_funct_ptr (Genv.globalenv p) b' = Some f.

(* the callee_save_regs liveness fun is correct for call steps *)
(* if we have two states that are at the same point, and agree on
callee_save regs and one can take a step across a call or return, then
the other can too, and the resulting states agree on callee_save regs
*)
Definition call_liveness_correct_bits (p : Asm.program) : Prop :=
  forall sl sr ml sl' ml' mr t b i s c instr bits md md',
    step_bits (Genv.globalenv p) (State_bits sl ml md) t (State_bits sl' ml' md') ->
    sl PC = Values.Vint bits ->
    psur md bits = Some (b,i) ->
    Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal (mkfunction s c)) ->
    find_instr (Int.unsigned i) c = Some instr ->
    is_call instr ->
    (forall r, In r (regs_live_across_call ++ parameter_regs) -> val_eq (sl r) (sr r)) ->
    mem_eq md ml mr ->
    (exists sr' mr', (step_bits (Genv.globalenv p) (State_bits sr mr md) t (State_bits sr' mr' md') /\
                      (forall r, In r regs_live_across_call -> val_eq (sl' r) (sr' r))) /\
                     (mem_eq md' ml' mr')).

Definition return_liveness_correct_bits (p : Asm.program) : Prop :=
  forall sl sr ml sl' ml' mr t b i s c args res cc bits md md',
    step_bits (Genv.globalenv p) (State_bits sl ml md) t (State_bits sl' ml' md') ->
    sl PC = Values.Vint bits ->
    psur md bits = Some (b,i) ->
    Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal (mkfunction s c)) ->
    find_instr (Int.unsigned i) c = Some (Pret (mksignature args res cc)) ->
    (forall r, In r (regs_live_across_call ++ (return_regs res)) -> val_eq (sl r) (sr r)) ->
    mem_eq md ml mr ->
    (exists sr' mr', (step_bits (Genv.globalenv p) (State_bits sr mr md) t (State_bits sr' mr' md') /\
                      (forall r, In r (regs_live_across_call ++ (return_regs res)) -> val_eq (sl' r) (sr' r))) /\
                     mem_eq md' ml' mr').

Definition external_fun_steps_back_to_call_bits (p : Asm.program) : Prop :=
  forall rs m rs' m' t b i ef instr bits md md',
    step_bits (Genv.globalenv p) (State_bits rs m md) t (State_bits rs' m' md') ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,i) ->
    Genv.find_funct_ptr (Genv.globalenv p) b = Some (External ef) ->
    exists b',
      exists i',
        exists bits',
          rs' PC = Values.Vint bits' /\
          psur md' bits' = Some (b',i') /\
        (exists s' c',
           (Genv.find_funct_ptr (Genv.globalenv p) b' = Some (Internal (mkfunction s' c')) /\
            find_instr ((Int.unsigned i') - 1) c' = Some instr /\
            is_call instr)).
  
Definition external_fun_liveness_correct_bits (p : Asm.program) : Prop :=
  forall sl sr ml sl' ml' mr t b i ef bits md md',
    step_bits (Genv.globalenv p) (State_bits sl ml md) t (State_bits sl' ml' md') ->
    sl PC = Values.Vint bits ->
    psur md bits = Some (b,i) ->
    Genv.find_funct_ptr (Genv.globalenv p) b = Some (External ef) ->
    (forall r, In r regs_live_across_call -> val_eq (sl r) (sr r)) ->
    mem_eq md ml mr ->
    (exists sr' mr', (step_bits (Genv.globalenv p) (State_bits sr mr md) t (State_bits sr' mr' md') /\
                      (forall r, In r (regs_live_across_call ++ (return_regs (sig_res (ef_sig ef)))) -> val_eq (sl' r) (sr' r))) /\
                     mem_eq md' ml' mr').

Definition internal_calls_well_typed_bits (p : Asm.program) : Prop :=
  forall rs m t rs' m' b i b' i' s c s' c' sig instr bits bits' md md',
    step_bits (Genv.globalenv p) (State_bits rs m md) t (State_bits rs' m' md') ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,i) ->
    rs' PC = Values.Vint bits' ->
    psur md' bits' = Some (b',i') ->
    Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal (mkfunction s c)) ->
    Genv.find_funct_ptr (Genv.globalenv p) b' = Some (Internal (mkfunction s' c')) ->
    find_instr (Int.unsigned i) c = Some (Pret sig) ->
    find_instr (Int.unsigned i' - 1) c' = Some instr ->
    is_call instr ->
    call_type instr = Some sig.

Definition external_calls_well_typed_bits (p : Asm.program) : Prop :=
  forall rs m t rs' m' b i b' i' s c ef instr bits bits' md md',
    step_bits (Genv.globalenv p) (State_bits rs m md) t (State_bits rs' m' md') ->
    rs PC = Values.Vint bits ->
    psur md bits = Some (b,i) ->
    rs' PC = Values.Vint bits' ->
    psur md' bits' = Some (b',i') ->
    Genv.find_funct_ptr (Genv.globalenv p) b = Some (External ef) ->
    Genv.find_funct_ptr (Genv.globalenv p) b' = Some (Internal (mkfunction s c)) ->
    find_instr (Int.unsigned i' - 1) c = Some instr ->
    is_call instr ->
    call_type instr = Some (ef_sig ef).

Definition calls_well_typed_bits (p : Asm.program) : Prop :=
  internal_calls_well_typed_bits p /\ external_calls_well_typed_bits p.

Definition calling_conv_correct_bits (p : Asm.program) : Prop :=
  return_steps_back_to_call_bits p /\ call_steps_to_beginning_bits p /\
  call_liveness_correct_bits p /\ return_liveness_correct_bits p /\ 
  external_fun_liveness_correct_bits p /\ external_fun_steps_back_to_call_bits p /\ calls_well_typed_bits p.

