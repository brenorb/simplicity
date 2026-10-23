(** Exact machine words returned by the original signed lookup. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import C.jet_secp_fe_math C.jet_secp_generator_globals
 C.jet_secp_generator_table_samples C.jet_secp_generator_tables_check
 C.jet_secp_storage_unpack C.jet_secp_storage_numeric C.jet_secp_affine_storage
 C.jet_secp_table_decode C.jet_secp_field_negate_separate C.jet_secp_field_weak_loose
 C.jet_secp_field_mul_small C.jet_secp_b32_exec C.jet_secp_multiply_input_input
 C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge.
Require Import C.jet_secp_square_columns.
Require Import C.jet_secp_generator_table_bounds.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition generator_lookup_words high index (neg k : bool) :=
 if k then if neg then negate_sep_words (limb_rho (snd (generator_entry_numeric high index)))
 else affine_storage_coord (generator_entry_words high index) true
 else affine_storage_coord (generator_entry_words high index) false.

Lemma generator_lookup_words_list high index neg k :
 words5 (generator_lookup_words high index neg k)=
 table_signed_coordinate (generator_entry_words high index) neg k.
Proof.
 destruct k,neg;reflexivity.
Qed.

Lemma generator_limb_input_bounds value : 0<=value<2^256 -> mul_small_input_bounds (limb_rho value).
Proof.
 intros Value i Index;rewrite limb_rho_unsigned by exact Value.
 pose proof (proj1 (fe_limbs_of_ok value Value)) as Bounds;unfold fe_limbs_ok in Bounds.
 destruct i as [|[|[|[|[|i]]]]];try lia;cbn [nth fe_limbs_of Nat.eqb];lia.
Qed.

Theorem generator_lookup_words_square_bounds high index neg k :
 square_input_bounds (generator_lookup_words high index neg k).
Proof.
 destruct k,neg;cbn [generator_lookup_words].
 - apply (proj2 (negate_sep_numeric _ (generator_limb_input_bounds _ (field_storage_value_bounds _)))).
 - intros i Index;unfold affine_storage_coord;pose proof (storage_unpack_limb_bounds
     (fun j=>generator_entry_words high index (4+j)%nat)) as Bounds.
   unfold fe_limbs_ok in Bounds.
   destruct i as [|[|[|[|[|i]]]]];try lia;cbn [Nat.eqb];lia.
 - intros i Index;unfold affine_storage_coord;pose proof (storage_unpack_limb_bounds
     (fun j=>generator_entry_words high index (0+j)%nat)) as Bounds.
   unfold fe_limbs_ok in Bounds.
   destruct i as [|[|[|[|[|i]]]]];try lia;cbn [Nat.eqb];lia.
 - intros i Index;unfold affine_storage_coord;pose proof (storage_unpack_limb_bounds
     (fun j=>generator_entry_words high index (0+j)%nat)) as Bounds.
   unfold fe_limbs_ok in Bounds.
   destruct i as [|[|[|[|[|i]]]]];try lia;cbn [Nat.eqb];lia.
Qed.

Theorem generator_lookup_words_bounds high index neg k :
 forall i,(i<5)%nat -> Int64.unsigned (generator_lookup_words high index neg k i)<=2^60.
Proof.
 intros i Index;destruct k,neg;cbn [generator_lookup_words].
 - apply negate_reader_loose_bound;[apply field_storage_value_bounds|exact Index].
 - unfold affine_storage_coord;pose proof (storage_unpack_limb_bounds
     (fun j=>generator_entry_words high index (4+j)%nat)) as Bounds.
   unfold fe_limbs_ok in Bounds.
   destruct i as [|[|[|[|[|i]]]]];try lia;lia.
 - unfold affine_storage_coord;pose proof (storage_unpack_limb_bounds
     (fun j=>generator_entry_words high index (0+j)%nat)) as Bounds.
   unfold fe_limbs_ok in Bounds.
   destruct i as [|[|[|[|[|i]]]]];try lia;lia.
 - unfold affine_storage_coord;pose proof (storage_unpack_limb_bounds
     (fun j=>generator_entry_words high index (0+j)%nat)) as Bounds.
   unfold fe_limbs_ok in Bounds.
   destruct i as [|[|[|[|[|i]]]]];try lia;lia.
Qed.

Theorem generator_lookup_words_numeric high index neg k :
 generator_tables_check high false=Some nil -> Z.of_nat index<8192 ->
 radix_value (generator_lookup_words high index neg k) mod feP=
 if k then snd (generator_entry_signed_numeric high index neg)
 else fst (generator_entry_signed_numeric high index neg).
Proof.
 intros Check Index.
 pose proof (generator_actual_entry_bounds high index Check Index) as Bounds.
 unfold generator_affine_bounds,generator_entry_numeric in Bounds;cbn [fst snd] in Bounds.
 unfold generator_lookup_words,generator_entry_signed_numeric,generator_entry_numeric.
 destruct k,neg;cbn [fst snd].
 - rewrite (proj1 (negate_sep_numeric _ (generator_limb_input_bounds _ (field_storage_value_bounds _)))),
     radix_limb_rho by apply field_storage_value_bounds.
   replace (4*feP-field_storage_value (fun j=>generator_entry_words high index (4+j)%nat))
     with ((feP-field_storage_value (fun j=>generator_entry_words high index (4+j)%nat))+3*feP) by ring.
   apply Z.mod_add;unfold feP,feR;lia.
 - unfold affine_storage_coord;rewrite storage_unpack_preserves_value;apply Z.mod_small;tauto.
 - unfold affine_storage_coord;rewrite storage_unpack_preserves_value;apply Z.mod_small;tauto.
 - unfold affine_storage_coord;rewrite storage_unpack_preserves_value;apply Z.mod_small;tauto.
Qed.
