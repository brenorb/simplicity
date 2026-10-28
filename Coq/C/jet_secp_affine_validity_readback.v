(** Literal affine validity with the flag readback required by its real
    linear-verifier caller. The existing curve guard is unchanged. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_sx_mem C.jet_readBit_layout C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp
 C.jet_secp_curve_function C.jet_secp_curve_literal_bridge C.jet_secp_curve_literal
 C.jet_secp_point_three_reads C.jet_secp_rescale_public_reads C.jet_secp_square_spec_bridge C.jet_secp_field_read_preservation
 C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_ge_is_on_curve.
Lemma affine_validity_helper_closed :
 closed_stmtb secp_closed_helpers (fn_body f_secp256k1_ge_is_valid_var)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma affine_validity_helper_preserved m args t mf result :
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_is_valid_var) args t mf result ->
 readonly_preserved m mf.
Proof.
 apply secp_closed_function_preserved;[exact affine_validity_helper_closed|reflexivity].
Qed.
Theorem eval_affine_validity_literal_readback x y m ba :
 fe_at m ba 0 (point_canonical_limbs x) -> fe_at m ba 40 (point_canonical_limbs y) ->
 Mem.range_perm m ba 0 88 Cur Freeable -> Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_is_valid_var)
   (Vptr ba Ptrofs.zero::nil) E0 mf
   (Vint (bit_int (Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (x,y))))) /\
 fe_at mf ba 0 (point_canonical_limbs x) /\ fe_at mf ba 40 (point_canonical_limbs y) /\
 Mem.load Mint32 mf ba 80=Some (Vint Int.zero) /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 lframe (fun b _=>b<>ba) m mf /\ readonly_preserved m mf.
Proof.
 rewrite !rescale_reader_limbs;intros X Y Owned Flag.
 destruct (eval_curve_finite_function_readback (square_reader_rho x) (square_reader_rho y) m ba
   (square_reader_bounds x) (square_reader_bounds y) X Y Owned Flag)
   as (mf & Call & XF & YF & Free & Frame & FlagReadback).
 rewrite curve_result_matches_literal in Call.
 exists mf;split;[exact Call|];split;[exact XF|];split;[exact YF|];split.
 - rewrite FlagReadback;exact Flag.
 - split;[exact Free|];split;[exact Frame|eapply affine_validity_helper_preserved;exact Call].
Qed.
