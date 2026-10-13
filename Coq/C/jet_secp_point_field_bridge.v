(** Concrete reader/negative limbs and their canonical field-program outputs.
    Internal writer bridge, not yet the complete public point jet theorem. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Word.
Require Simplicity.Ty Simplicity.Alg.
Require Import C.jet_toZ C.jet_word_repr C.jet_secp_fe_math C.jet_secp_b32_exec.
Require Import C.jet_secp_write_fe_numeric C.jet_secp_write_fe_wide_exec.
Require Import C.jet_secp_field_negate_values C.jet_secp_field_negate_storage.
Require Import C.jet_secp_negate_writer_bridge C.jet_secp_canonical_normalize C.jet_secp_canonical_negate.
Require Import C.jet_secp_point_write_field.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_normalize canonical_fe_negate.

Definition point_canonical_field value := mkpointfield
  (limb_rho value 0) (limb_rho value 1) (limb_rho value 2) (limb_rho value 3) (limb_rho value 4).
Definition point_negative_field value := mkpointfield
  (negate_value (write_fe_rho value 0) 0) (negate_value (write_fe_rho value 0) 1)
  (negate_value (write_fe_rho value 0) 2) (negate_value (write_fe_rho value 0) 3)
  (negate_value (write_fe_rho value 0) 4).

Lemma point_canonical_field_limbs value :
  point_field_limbs (point_canonical_field value) = map Int64.repr (fe_limbs_of value).
Proof. reflexivity. Qed.
Lemma point_negative_field_limbs value :
  point_field_limbs (point_negative_field value) = negate_values (write_fe_rho value 0).
Proof. reflexivity. Qed.

Lemma point_reader_limb_model value : 0 <= value < 2^256 ->
  fe_limbs_ok (Int64.unsigned (write_fe_rho value 0 1%nat))
    (Int64.unsigned (write_fe_rho value 0 2%nat)) (Int64.unsigned (write_fe_rho value 0 3%nat))
    (Int64.unsigned (write_fe_rho value 0 4%nat)) (Int64.unsigned (write_fe_rho value 0 5%nat)) /\
  fe_val (Int64.unsigned (write_fe_rho value 0 1%nat))
    (Int64.unsigned (write_fe_rho value 0 2%nat)) (Int64.unsigned (write_fe_rho value 0 3%nat))
    (Int64.unsigned (write_fe_rho value 0 4%nat)) (Int64.unsigned (write_fe_rho value 0 5%nat)) = value.
Proof.
  intro HV; cbn [write_fe_rho]; rewrite !limb_rho_unsigned by exact HV.
  exact (fe_limbs_of_ok value HV).
Qed.

Lemma point_canonical_field_bounded value :
  0 <= value < 2^256 -> point_field_bounds (point_canonical_field value).
Proof.
  intro HV.
  assert (HN : forall n, Int64.unsigned (limb_rho value n) <= 2^60).
  { intro n; rewrite limb_rho_unsigned by exact HV.
    pose proof (nth_limb_52_bound _ (limb_list_52_bound value HV) n);
    change (2^60) with 1152921504606846976;
    change (2^52) with 4503599627370496 in *; lia. }
  unfold point_field_bounds,point_canonical_field; cbn [pf0 pf1 pf2 pf3 pf4].
  repeat split; apply HN.
Qed.

Lemma point_negative_field_bounded value :
  0 <= value < 2^256 -> point_field_bounds (point_negative_field value).
Proof.
  intro HV; destruct (point_reader_limb_model value HV) as [HBounds HValue].
  unfold fe_limbs_ok in HBounds; destruct HBounds as (H0&H1&H2&H3&H4).
  assert (HN : forall n, (n < 5)%nat ->
    Int64.unsigned (negate_value (write_fe_rho value 0) n) <= 2^60).
  { intros n Hi.
    rewrite negate_value_unsigned by
      (try exact Hi; do 5 (destruct n as [|n]; [cbn [Nat.eqb];lia|]); lia).
    change (2^60) with 1152921504606846976.
    do 5 (destruct n as [|n]; [cbn [negate_mask];lia|]); lia. }
  unfold point_field_bounds,point_negative_field; cbn [pf0 pf1 pf2 pf3 pf4].
  repeat split; apply HN; lia.
Qed.

Lemma point_canonical_field_output (x : Ty.tySem (Word 8)) :
  point_field_output (point_canonical_field (@toZ (WordToZ 8) x)) =
    @canonical_fe_normalize Alg.CoreFunSem x.
Proof.
  apply (toZ_injective (WordToZ 8)).
  unfold point_field_output,point_canonical_field; cbn [pf0 pf1 pf2 pf3 pf4].
  rewrite wide_fe_output_value, canonical_fe_normalize_numeric,
    canonical_field_order_matches_limb_model.
  exact (f_equal (fun v => v mod feP)
    (proj2 (point_reader_limb_model _ (word_toZ_range 8 x)))).
Qed.

Lemma point_negative_field_output (x : Ty.tySem (Word 8)) :
  @toZ (WordToZ 8) x < feP ->
  point_field_output (point_negative_field (@toZ (WordToZ 8) x)) =
    @canonical_fe_negate Alg.CoreFunSem x.
Proof.
  intro Hlt; unfold point_field_output,point_negative_field; cbn [pf0 pf1 pf2 pf3 pf4].
  destruct (point_reader_limb_model _ (word_toZ_range 8 x)) as [HB HV].
  apply wide_negate_output; assumption.
Qed.
Print Assumptions point_negative_field_output.
