(** Actual Elements lock jets against their literal source programs, including
    Ty.Word.toWord32's state traversal for the parseLock threshold. *)
From Coq Require Import ZArith List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_sequence_literal.
Require Import C.jet_haskell_word_conversion C.jet_order_spec C.jet_timelock_spec.
Require Import C.jet_elements_is_final_spec C.jet_elements_lock_spec C.jet_elements_lock_local.
Local Open Scope ty_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition elements_parse_lock_literal {alg : Core.Algebra} :
    alg Word32 (Word32 + Word32) :=
  ((iden &&& Alg.scribe (haskell_to_word 5 500000000) >>> @lt_word_spec alg 5) &&& iden)
    >>> Bit.cond (injl iden) (injr iden).

Definition elements_lock_literal_tail (height : bool) {alg : Core.Algebra} :
    alg (Bit * Word32) Word32 :=
  Bit.cond (unit >>> zero (n := 5))
    (elements_parse_lock_literal >>>
      (if height then copair iden (unit >>> zero (n := 5))
       else copair (unit >>> zero (n := 5)) iden)).

Definition elements_lock_literal_program (height : bool) {alg : Primitive.Algebra} :
    alg Ty.Unit Word32 :=
  (elements_tx_is_final_spec &&& Primitive.Combinators.prim Elements.LockTime)
    >>> elements_lock_literal_tail height.

Lemma elements_parse_lock_literal_matches {alg : Core.Algebra} :
  @elements_parse_lock_literal alg = @parse_lock_spec alg.
Proof.
  unfold elements_parse_lock_literal, parse_lock_spec, parse_lock_threshold.
  rewrite haskell_to_word_matches. reflexivity.
Qed.

Lemma elements_lock_literal_program_matches height {alg : Primitive.Algebra} :
  @elements_lock_literal_program height alg =
    @lock_program height (Primitive.CanonicalStructures.toCore alg)
      elements_tx_is_final_spec elements_lock_time_prim.
Proof.
  unfold elements_lock_literal_program, lock_program, elements_lock_literal_tail,
    lock_tail, lock_zero, elements_lock_time_prim.
  rewrite elements_parse_lock_literal_matches. reflexivity.
Qed.

Theorem elements_tx_lock_height_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_tx_lock_height elements_ge Elements.env
    Ty.Unit Word32 elements_lock_env_rep
    (fun a environment => @elements_lock_literal_program Datatypes.true
      (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [|exact elements_tx_lock_height_local_spec].
  intros a environment. rewrite elements_lock_literal_program_matches. reflexivity.
Qed.

Theorem elements_tx_lock_time_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_tx_lock_time elements_ge Elements.env
    Ty.Unit Word32 elements_lock_env_rep
    (fun a environment => @elements_lock_literal_program Datatypes.false
      (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [|exact elements_tx_lock_time_local_spec].
  intros a environment. rewrite elements_lock_literal_program_matches. reflexivity.
Qed.

Print Assumptions elements_parse_lock_literal_matches.
Print Assumptions elements_lock_literal_program_matches.
Print Assumptions elements_tx_lock_height_literal_local_spec.
Print Assumptions elements_tx_lock_time_literal_local_spec.
