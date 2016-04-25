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
Require Import Asm.
Require Import AsmBits.
Require Import MemoryAxioms.
Require Import Errors.
Require Import PeekLib.
Require Import PeekTactics.
Require Import FindInstrLib.
Require Import PregTactics.
Require Import ForwardJumps.
Require Import Peephole.
Require Import PeepholeProof.
Require Import StepIn.
Require Import StepEquiv.
Require Import ProgPropDec.
Require Import PeepsLib.
Require Import Union.
Require Import ParamSplit.
Require Import AddrmodeEq.
Require Import UseBasic.

(*IMPORT PEEPHOLES*)
(* Require Import Peep_LoadStore. *)
(* Require Import Peep_ExtendedShift. *)
(* Require Import Peep_ExtendedShift2.  *)
(* Require Import Peep_HmacLoadElim.  *)
(* Require Import Peep_LeaAdd. *)
(* Require Import Peep_LeaAdd2. *)
(* Require Import Peep_XorToMov0. *)
Require Import Peep_ZeroSub.

(* Require Import Peep_VecMul. 
Require Import Peep_TestThenLea. *)


(*Require Import Peep_Add1ToInc.
Require Import Peep_AddNeg1ToDec.*)
(*Require Import Peep_Div2ToShift.*)
(*Require Import Peep_IncDecNop.*)
(*Require Import Peep_IncIncDecToInc.*)
(*Require Import Peep_JumpNop.*)
(*Require Import Peep_Mov0ToXor.*)
(*Require Import Peep_TestVecAdd.*)
(*Require Import Peep_MovNop.*)
(*Require Import Peep_Mul2ToShift.*)
(*Require Import Peep_Mul4ToShift.
Require Import Peep_Mul8ToShift.*)
(*Require Import Peep_NotAddToSubNot.*)
(*Require Import Peep_OverwriteMovNop.*)
(*Require Import Peep_Sub1ToDec.
Require Import Peep_SubNeg1ToDec.*)
(*Require Import Peep_XorVec.*)
(*Require Import Aiken2.
Require Import Aiken3.
Require Import Aiken4.
Require Import Aiken5.
Require Import Aiken6.
Require Import Aiken7.*)

(* external interface for a peephole is a function like mov_nop *)
(* it's a function which takes the code for an entire Asm function *)
(* and produces a rewrite *)
(* We hook all of them into CompCert here *)
Definition gen_rewrites : list (code -> list StepEquiv.rewrite) :=
  (* START *)
         (* Peep.store_load :: *)
         (* extended_shift ::  *)
         (* extended_shift_2 ::  *)
         (* lea_add :: *)
         (* lea_add2 :: *)
         (* hmac_load_elim :: *)
         (* xor_to_mov_0 :: *)
         zero_sub ::
         (*xor_vec ::*) (*TODO possibly useful*)
         (* test_then_lea :: *)
         (*div_2_to_shr ::*)
         (*inc_dec_nop ::*)
         (*inc_inc_dec_to_inc ::*)
         (*jump_nop ::*)
         (*mov_nop ::*)
         (*not_add_to_sub_not ::*)
         (*aiken_2 ::
         aiken_3 ::
         aiken_4 ::
         aiken_5 ::
         aiken_6 ::
         aiken_7 ::*)
          nil.

Fixpoint param_collect (l : list code) (f : code -> list StepEquiv.rewrite) : list StepEquiv.rewrite :=
  match l with
    | nil => nil
    | c :: r => (f c) ++ param_collect r f
  end.

Definition prog_code (p : program) : list code :=
  collect (map (fun x => match x with | Gfun (Internal f) => Some (fn_code f) | _ => None end) (map snd (prog_defs p))).


Fixpoint collect_candidates (p : program) (rwrs : list (code -> list StepEquiv.rewrite)): list StepEquiv.rewrite :=
  match rwrs with
    | nil => nil
    | f :: r => (param_collect (prog_code p) f) ++ (collect_candidates p r)
  end.

Fixpoint t_prog (p : program) (l : list StepEquiv.rewrite) : res program :=
  match l with
    | nil => OK p
    | f :: r =>
      match Peephole.transf_program f p with
        | OK p' => t_prog p' r
        | Error x => Error x
      end
  end.

Definition transf_program (p : program) : res program := t_prog p (collect_candidates p gen_rewrites).

Lemma fsim_refl:
  forall p,
    forward_simulation (AsmBits.semantics_bits p) (AsmBits.semantics_bits p).
Proof.
  intros.
  apply forward_simulation_step with (match_states := eq);
    intros; subst; auto.
  - eexists; intuition; auto.
  - eexists; intuition; auto.
Qed.
  
Lemma t_prog_correct :
  forall l prog tprog,
    t_prog prog l = OK tprog ->
    forward_simulation (AsmBits.semantics_bits prog) (AsmBits.semantics_bits (tprog)).
Proof.
  induction l; intros.
  * simpl in H. inv H.
    apply fsim_refl.
  * simpl in H. break_match_hyp; inv H.
    specialize (IHl _ _ H1).
    apply compose_forward_simulation with (semantics_bits p).
    eapply PeepholeProof.transf_program_correct; eauto.
    admit. (* have to admit calling convention *)
    apply IHl.
Qed.

Section PRESERVATION.

  Variable prog: program.
  Variable tprog: program.
  Hypothesis TRANSF: transf_program prog = OK tprog.

  Lemma transf_program_correct :
    forward_simulation (semantics_bits prog) (semantics_bits tprog).
  Proof.
    eapply t_prog_correct; eauto.
  Qed.
  
End PRESERVATION.
