(** Range preservation for the exact scalar-order coefficient recurrence.
    These internal bounds are concluded of the real update's output words;
    the inverse loop still has to establish them at its initial state. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers.
Require Import C.jet_secp_scalar_de_numeric C.jet_secp_scalar_de_recurrence
 C.jet_secp_modinv_de_numeric C.jet_secp_modinv_de_correction_numeric
 C.jet_secp_modinv_normalize62_modulus C.jet_secp_modinv_normalize62_words
 C.jet_secp_scalar_normalize62 C.jet_secp_canonical_scalar.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_de62_state_bounds rho :=
 (forall high,modnorm62_limb_bounds(de62_array rho high)) /\
 (forall high,-2*canonical_group_order<de62_input_value rho high<canonical_group_order).
Definition scalar_de62_balanced_value (rho : nat -> int64) (high : bool) := de62_input_value rho high+
 if Int64.lt (rho(if high then 9%nat else 4%nat)) Int64.zero then canonical_group_order else 0.

Lemma scalar_de62_state_input_bound rho : scalar_de62_state_bounds rho -> de62_input_bound rho.
Proof.
 intros(Limbs & Values) i I.
 pose proof(Limbs false i I) as D;pose proof(Limbs true i I) as E.
 split;apply Z.abs_le;change(-(2^62-1)<=Int64.signed(rho i)<=2^62-1) in D;
 change(-(2^62-1)<=Int64.signed(rho(5+i)%nat)<=2^62-1) in E;lia.
Qed.

Lemma scalar_de62_balanced_range rho high : scalar_de62_state_bounds rho ->
 -canonical_group_order<scalar_de62_balanced_value rho high<canonical_group_order.
Proof.
 intros(Limbs & Values).
 pose proof(modnorm62_first_range modinfo_scalar_limb canonical_group_order scalar_norm62_modulus_bound
   scalar_norm62_modulus_value scalar_norm62_modulus_range
   (de62_array rho high) Int64.zero (Limbs high) (Values high)) as Range.
 rewrite (modnorm62_first_value modinfo_scalar_limb canonical_group_order scalar_norm62_modulus_bound
   scalar_norm62_modulus_value (de62_array rho high) Int64.zero (Limbs high)) in Range.
 change(-canonical_group_order<1*scalar_de62_balanced_value rho high<canonical_group_order) in Range.
 rewrite Z.mul_1_l in Range;exact Range.
Qed.

Theorem scalar_de62_output_range rho high : de62_row_bound rho high -> scalar_de62_state_bounds rho ->
 -2*canonical_group_order<scalar_de62_output_value rho high<canonical_group_order.
Proof.
 intros Row Bounds;pose proof(scalar_de62_state_input_bound rho Bounds) as Inputs.
 pose proof(de62_balanced_row_modulus canonical_group_order
   (Int64.signed(rho(if high then 12%nat else 10%nat)))
   (Int64.signed(rho(if high then 13%nat else 11%nat)))
   (scalar_de62_balanced_value rho false) (scalar_de62_balanced_value rho true)
   ltac:(unfold canonical_group_order;lia) Row
   (scalar_de62_balanced_range rho false Bounds) (scalar_de62_balanced_range rho true Bounds)) as Balanced.
 set(rem:=(3815112494326173377*de62_first_value rho high+de62_multiple_value rho high) mod 2^62).
 pose proof(Z.mod_pos_bound
   (3815112494326173377*de62_first_value rho high+de62_multiple_value rho high) (2^62) ltac:(lia)) as Rem.
 change(0<=rem<2^62) in Rem.
 assert(Total : 2^62*scalar_de62_output_value rho high=
   Int64.signed(rho(if high then 12%nat else 10%nat))*scalar_de62_balanced_value rho false+
   Int64.signed(rho(if high then 13%nat else 11%nat))*scalar_de62_balanced_value rho true-
   canonical_group_order*rem).
 { rewrite (scalar_de62_scaled_value rho high Row Inputs).
   unfold de62_matrix_value,scalar_de62_correction_value,scalar_de62_balanced_value,rem,de62_multiple_value.
   destruct(Int64.lt(rho 4%nat) Int64.zero),(Int64.lt(rho 9%nat) Int64.zero);ring. }
 unfold canonical_group_order in *;lia.
Qed.

Theorem scalar_de62_output_limb_bounds rho high : de62_row_bound rho high -> scalar_de62_state_bounds rho ->
 modnorm62_limb_bounds(scalar_de62_recurrence_word rho high).
Proof.
 intros Row Bounds;pose proof(scalar_de62_state_input_bound rho Bounds) as Inputs.
 assert(Low : forall i,(i<4)%nat -> 0<=Int64.signed(scalar_de62_recurrence_word rho high i)<2^62).
 { intros i I;rewrite scalar_de62_lower_signed by assumption;apply Z.mod_pos_bound;lia. }
 pose proof(scalar_de62_output_range rho high Row Bounds) as Range.
 pose proof(Low 0%nat ltac:(lia));pose proof(Low 1%nat ltac:(lia));
 pose proof(Low 2%nat ltac:(lia));pose proof(Low 3%nat ltac:(lia)).
 assert(Top : -(2^62-1)<=Int64.signed(scalar_de62_recurrence_word rho high 4)<=2^62-1).
 { unfold scalar_de62_output_value in Range;cbn [norm62_value_z] in Range;unfold canonical_group_order in *;lia. }
 intros i I;destruct(Nat.eq_dec i 4) as [->|Other];[exact Top|pose proof(Low i ltac:(lia));lia].
Qed.
