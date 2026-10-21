(** The original mixed-addition infinity branch against its literal Simplicity
    program on actual reader words. No public jet registration is claimed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_toZ C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp
  C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge
  C.jet_secp_square_spec_bridge C.jet_secp_square_columns C.jet_secp_multiply_finish_product
  C.jet_secp_rescale_literal C.jet_secp_double_literal_bridge C.jet_secp_canonical_normalize
  C.jet_secp_canonical_zero C.jet_secp_literal_gej_predicate C.jet_secp_literal_add_program
  C.jet_secp_literal_add_numeric C.jet_secp_point_set_bit C.jet_secp_mixed_head C.jet_secp_add_literal.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_gej_ge_add rescale_field_output canonical_fe_normalize literal_fe_one256.

Lemma mixed_reader_output x :
  rescale_field_output (square_reader_rho x)=@canonical_fe_normalize Alg.CoreFunSem x.
Proof.
  apply (toZ_injective (WordToZ 8)).
  rewrite rescale_field_output_value,canonical_fe_normalize_numeric,canonical_field_order_matches_limb_model.
  rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue.
Qed.
Lemma mixed_one_bounds : square_input_bounds (point_set_bit_words true).
Proof.
  intros i HI;unfold point_set_bit_words;
    destruct (Nat.eqb i 0), (Nat.eqb i 4);vm_compute;split;discriminate.
Qed.
Lemma mixed_one_output : rescale_field_output (point_set_bit_words true)=
  @canonical_fe_normalize Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt).
Proof.
  apply (toZ_injective (WordToZ 8)).
  rewrite rescale_field_output_value,canonical_fe_normalize_numeric,canonical_field_order_matches_limb_model,
    field_prime_matches_normalizer,literal_fe_one256_value.
  change (1 mod feP=1 mod feP);reflexivity.
Qed.

Theorem mixed_infinite_body_literal e le m ba bb (ax ay az bx byword : Ty.tySem (Word 8)) :
  le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr ba Ptrofs.zero) ->
  le!_b=Some (Vptr bb Ptrofs.zero) -> le!_rzr=Some (Vlong Int64.zero) ->
  e!_secp256k1_gej_set_ge=None -> ba<>bb -> Mem.range_perm m ba 0 128 Cur Freeable ->
  Mem.load Mint32 m ba 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)))) ->
  Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)=true ->
  fe_at m bb 0 (words5 (square_reader_rho bx)) -> fe_at m bb 40 (words5 (square_reader_rho byword)) ->
  Mem.load Mint32 m bb 80=Some (Vint Int.zero) ->
  exists mf x y z,
  Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_ge_var) E0
    (PTree.set _t'4 (Vint Int.one) le) mf (Out_return None) /\
  fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\ fe_at mf ba 80 (words5 z) /\
  square_input_bounds x /\ square_input_bounds y /\ square_input_bounds z /\
  ((rescale_field_output x,rescale_field_output y),rescale_field_output z)=
    @literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),(bx,byword)) /\
  Mem.load Mint32 mf ba 120=Some (Vint Int.zero) /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
  lframe (fun b _=>b<>ba) m mf.
Proof.
  intros HA HR HB HN HE HSep HF HFlag HInf HX HY HBF.
  rewrite HInf in HFlag;change (Mem.load Mint32 m ba 120=Some (Vint Int.one)) in HFlag.
  destruct (mixed_infinite_body_owned e le m ba bb (square_reader_rho bx) (square_reader_rho byword) Int.one
    HA HR HB HN HE HSep HF HFlag ltac:(discriminate) HX HY HBF)
    as (mf & HC & XO & YO & ZO & FO & FF & Frame).
  exists mf,(square_reader_rho bx),(square_reader_rho byword),(point_set_bit_words true).
  split;[exact HC|];split;[exact XO|];split;[exact YO|];split;[exact ZO|].
  split;[apply square_reader_bounds|];split;[apply square_reader_bounds|];split;[exact mixed_one_bounds|].
  split.
  - rewrite !mixed_reader_output,mixed_one_output,literal_gej_ge_add_infinite;[reflexivity|].
    change (@canonical_fe_is_zero Alg.CoreFunSem az=inr tt).
    destruct (@canonical_fe_is_zero Alg.CoreFunSem az) as [[] | []];[discriminate HInf|reflexivity].
  - split;[exact FO|];split;assumption.
Qed.
