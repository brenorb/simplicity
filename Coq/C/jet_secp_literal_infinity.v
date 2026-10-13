(** Literal LibSecp256k1.gej_infinity program and the original writer's zero bridge.
    This is a specification bridge, not a standalone public C jet contract. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_write_fe_wide_exec.
Require Import C.jet_encoding.
Require Simplicity.Translate.
Import ListNotations.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_fe_zero256 {term : Alg.Core.Algebra} : term Ty.Unit (Word 8) :=
  @Word.zero 8 term.
Definition literal_gej_infinity {term : Alg.Core.Algebra} :
  term Ty.Unit (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) :=
  (@literal_fe_zero256 term &&& @literal_fe_zero256 term) &&& @literal_fe_zero256 term.

Lemma literal_fe_zero256_parametric : Alg.Core.Parametric (@literal_fe_zero256).
Proof. intros term1 term2 R. unfold literal_fe_zero256; apply Word.zero_Parametric. Qed.
Lemma literal_gej_infinity_parametric : Alg.Core.Parametric (@literal_gej_infinity).
Proof.
  intros term1 term2 R. unfold literal_gej_infinity.
  apply Alg.pair_Parametric;
    [apply Alg.pair_Parametric; apply literal_fe_zero256_parametric
    |apply literal_fe_zero256_parametric].
Qed.

Lemma zero_field_writer_literal_output :
  wide_fe_output Int64.zero Int64.zero Int64.zero Int64.zero Int64.zero =
    @literal_fe_zero256 Alg.CoreFunSem tt.
Proof.
  apply (toZ_injective (WordToZ 8)).
  unfold literal_fe_zero256. rewrite wide_fe_output_value, Word.zero_correct.
  reflexivity.
Qed.

Lemma literal_gej_infinity_encoding :
  Simplicity.Translate.encode (@literal_gej_infinity Alg.CoreFunSem tt) =
  (Simplicity.Translate.encode (@literal_fe_zero256 Alg.CoreFunSem tt) ++
   Simplicity.Translate.encode (@literal_fe_zero256 Alg.CoreFunSem tt)) ++
   Simplicity.Translate.encode (@literal_fe_zero256 Alg.CoreFunSem tt).
Proof. reflexivity. Qed.
Print Assumptions zero_field_writer_literal_output.
Print Assumptions literal_gej_infinity_parametric.
