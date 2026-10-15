(** Actual C tapleaf_version against the literal Haskell toWord8 primitive.
    Reuse the all-width converter and separated-contract transport. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers Clight Ctypes Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_tapleaf_version_local.
Require Import C.jet_haskell_word_conversion C.jet_elements_sequence_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition elements_tapleaf_version_literal_spec
    (_ : tySem Ty.Unit) (environment : Elements.env) : option (tySem Word8) :=
  Some (haskell_to_word 3 (Byte.unsigned (tapleafVersion (Elements.envTap environment)))).

Lemma elements_tapleaf_version_literal_matches a environment :
  @elements_tapleaf_version_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_tapleaf_version_literal_spec a environment.
Proof.
  destruct a. rewrite elements_tapleaf_version_spec_sem.
  unfold elements_tapleaf_version_literal_spec.
  rewrite haskell_to_word_matches. reflexivity.
Qed.

Theorem elements_tapleaf_version_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_tapleaf_version elements_ge Elements.env Ty.Unit Word8
    elements_tapleaf_version_env_rep elements_tapleaf_version_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_tapleaf_version_literal_matches|exact elements_tapleaf_version_local_spec].
Qed.

Print Assumptions elements_tapleaf_version_literal_matches.
Print Assumptions elements_tapleaf_version_literal_local_spec.
