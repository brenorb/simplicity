(** Actual C check-lock jets against literal assertion programs. *)
From Coq Require Import ZArith List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_partial C.jet_elements_current_spec C.jet_elements_prim_sem.
Require Import C.jet_order_spec C.jet_elements_lock_literal C.jet_elements_check_lock.
Require Import C.jet_application_partial_transport.
Local Open Scope ty_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition elements_check_lock_literal_program (height : bool) {alg : Primitive.Algebra} :
    alg Word32 Ty.Unit :=
  elements_assert_spec
    ((iden &&& (unit >>> elements_lock_literal_program height))
      >>> @le_word_spec (Primitive.CanonicalStructures.toCore alg) 5).

Lemma elements_check_lock_literal_program_matches height {alg : Primitive.Algebra} :
  @elements_check_lock_literal_program height alg = @elements_check_lock_program height alg.
Proof.
  unfold elements_check_lock_literal_program.
  rewrite elements_lock_literal_program_matches.
  unfold elements_check_lock_program, elements_comp, elements_pair, elements_core.
  reflexivity.
Qed.

Theorem elements_check_lock_height_literal_local_spec :
  application_jet_partial_spec f_simplicity_check_lock_height elements_ge Elements.env
    Word32 Ty.Unit elements_check_lock_env_rep
    (fun a environment => @elements_check_lock_literal_program Datatypes.true
      (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply application_jet_partial_spec_pointwise;
    [|exact elements_check_lock_height_local_spec].
  intros a environment. rewrite elements_check_lock_literal_program_matches. reflexivity.
Qed.

Theorem elements_check_lock_time_literal_local_spec :
  application_jet_partial_spec f_simplicity_check_lock_time elements_ge Elements.env
    Word32 Ty.Unit elements_check_lock_env_rep
    (fun a environment => @elements_check_lock_literal_program Datatypes.false
      (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply application_jet_partial_spec_pointwise;
    [|exact elements_check_lock_time_local_spec].
  intros a environment. rewrite elements_check_lock_literal_program_matches. reflexivity.
Qed.

Print Assumptions elements_check_lock_literal_program_matches.
Print Assumptions elements_check_lock_height_literal_local_spec.
Print Assumptions elements_check_lock_time_literal_local_spec.
