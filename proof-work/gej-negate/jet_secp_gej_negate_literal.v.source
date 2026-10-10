(** Literal Haskell ge_negate (line 548) and gej_negate (line 508), using
    the existing literal field-negation program rather than a numeric target. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Word.
Require Import Simplicity.Ty Simplicity.Alg.
Require Simplicity.Translate.
Require Import C.jet_toZ C.jet_secp_canonical_normalize C.jet_secp_canonical_negate.
Require Import C.jet_secp_negate_input_bridge C.jet_secp_negate_literal_contract.
Require Import C.jet_secp_point_write_field C.jet_secp_point_field_bridge.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_normalize canonical_fe_negate literal_fe_negate Simplicity.Translate.encode.

Definition literal_ge_negate {term : Alg.Core.Algebra} :
  term (Ty.Prod (Word 8) (Word 8)) (Ty.Prod (Word 8) (Word 8)) :=
  O (@canonical_fe_normalize term) &&& I (@literal_fe_negate term).
Definition literal_gej_negate {term : Alg.Core.Algebra} :
  term (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))
    (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) :=
  O (@literal_ge_negate term) &&& I (@canonical_fe_normalize term).

Lemma literal_gej_negate_step (x y z : Ty.tySem (Word 8)) :
  @literal_gej_negate Alg.CoreFunSem ((x,y),z) =
    ((@canonical_fe_normalize Alg.CoreFunSem x,@literal_fe_negate Alg.CoreFunSem y),
      @canonical_fe_normalize Alg.CoreFunSem z).
Proof. unfold literal_gej_negate,literal_ge_negate; reflexivity. Qed.

Lemma point_normalized_field_output (x : Ty.tySem (Word 8)) :
  point_field_output (point_canonical_field
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem x))) =
    @canonical_fe_normalize Alg.CoreFunSem x.
Proof. rewrite point_canonical_field_output; apply canonical_fe_normalize_idempotent. Qed.

Lemma point_normalized_negative_field_output (x : Ty.tySem (Word 8)) :
  point_field_output (point_negative_field
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem x))) =
    @literal_fe_negate Alg.CoreFunSem x.
Proof.
  rewrite point_negative_field_output.
  - rewrite canonical_fe_negate_normalized_input, literal_fe_negate_matches; reflexivity.
  - rewrite <- canonical_field_order_matches_limb_model.
    exact (proj2 (canonical_normalized_field_range x)).
Qed.

Lemma point_encode_pair {A B : Ty.Ty} (a : Ty.tySem A) (b : Ty.tySem B) :
  @Simplicity.Translate.encode (Ty.Prod A B) (a,b) =
    @Simplicity.Translate.encode A a ++ @Simplicity.Translate.encode B b.
Proof. reflexivity. Qed.

Lemma literal_gej_negate_writer_encoding (x y z : Ty.tySem (Word 8)) :
  ((Simplicity.Translate.encode (point_field_output (point_canonical_field
      (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem x)))) ++
    Simplicity.Translate.encode (point_field_output (point_negative_field
      (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem y))))) ++
    Simplicity.Translate.encode (point_field_output (point_canonical_field
      (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem z))))) =
    Simplicity.Translate.encode (@literal_gej_negate Alg.CoreFunSem ((x,y),z)).
Proof.
  rewrite (point_normalized_field_output x).
  rewrite (point_normalized_negative_field_output y).
  rewrite (point_normalized_field_output z).
  rewrite literal_gej_negate_step.
  exact (eq_sym (eq_trans
    (@point_encode_pair (Ty.Prod (Word 8) (Word 8)) (Word 8)
      (@canonical_fe_normalize Alg.CoreFunSem x,@literal_fe_negate Alg.CoreFunSem y)
      (@canonical_fe_normalize Alg.CoreFunSem z))
    (f_equal (fun bits => bits ++ Simplicity.Translate.encode (@canonical_fe_normalize Alg.CoreFunSem z))
      (@point_encode_pair (Word 8) (Word 8) (@canonical_fe_normalize Alg.CoreFunSem x)
        (@literal_fe_negate Alg.CoreFunSem y))))).
Qed.
Print Assumptions literal_gej_negate_writer_encoding.
