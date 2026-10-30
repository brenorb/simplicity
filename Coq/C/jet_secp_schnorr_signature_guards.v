(** Signature-range guards of the original Schnorr verifier and frozen predicate. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_toZ C.jet_read8s_layout C.jet_sx_state C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_secp_canonical_scalar C.jet_secp_canonical_normalize C.jet_secp_fe_math
 C.jet_secp_schnorr_verify_literal C.jet_secp_root_chain_owned C.jet_secp_statement_prefix
 C.jet_secp_xonly_parse_field C.jet_secp_scalar_set_flag C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Require Import C.jet_secp_schnorr_scalar_read C.jet_secp_schnorr_check_predicate C.jet_secp_xonly_parse_result.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_bip0340_check.
Lemma schnorr_spec_reject_scalar (pk msg r s:Ty.tySem (Word 8)):
 canonical_group_order<=@toZ (WordToZ 8) s ->
 Simplicity.Bit.toBool (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,msg),(r,s)))=false.
Proof.
 intro Bound;rewrite literal_bip0340_check_guarded_value.
 assert (Rejected:Z.ltb (@toZ (WordToZ 8) s) canonical_group_order=false) by (apply Z.ltb_ge;exact Bound).
 rewrite Rejected,Bool.andb_false_r;destruct (Z.ltb (@toZ (WordToZ 8) pk) canonical_field_order);reflexivity.
Qed.
Lemma schnorr_spec_reject_r (pk msg r s:Ty.tySem (Word 8)):
 feP<=@toZ (WordToZ 8) r ->
 Simplicity.Bit.toBool (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,msg),(r,s)))=false.
Proof.
 intro Bound;rewrite literal_bip0340_check_guarded_value,canonical_field_order_matches_limb_model.
 assert (Rejected:Z.ltb (@toZ (WordToZ 8) r) feP=false) by (apply Z.ltb_ge;exact Bound).
 rewrite Rejected;cbn [andb];destruct (Z.ltb (@toZ (WordToZ 8) pk) feP);reflexivity.
Qed.
Theorem exec_schnorr_scalar_reject (pk msg r s:Ty.tySem (Word 8)) e le m bs bsig bf:
 canonical_group_order<=@toZ (WordToZ 8) s ->
 e!_s=Some (bs,Tstruct __5826 noattr) ->e!_overflow=Some (bf,tint) ->
 e!_secp256k1_scalar_set_b32=None ->le!_sig64=Some (Vptr bsig Ptrofs.zero) ->
 bs<>bsig ->bf<>bs ->bf<>bsig ->
 Mem.range_perm m bs 0 32 Cur Freeable ->Mem.range_perm m bsig 0 64 Cur Freeable ->
 Mem.range_perm m bf 0 4 Cur Freeable ->
 uint8_array_at m bsig 32 (map Int.repr (xonly_input_bytes s)) ->exists mf lef,
 Clight2.exec_stmt secp_ge e le m
 (root_drop_statements 4 (fn_body f_secp256k1_schnorrsig_verify)) E0 lef mf
 (Out_return (Some (Vint Int.zero,tint))) /\
 Simplicity.Bit.toBool (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,msg),(r,s)))=false /\
 keeps_permissions m mf /\
 lframe (fun block pos=>~foot [(bs,0);(bsig,32);(bf,0)]
  (map rshape scalar_flag_regs) block pos /\block<>bf) m mf /\readonly_preserved m mf.
Proof.
 intros Bound S Flag Symbol Sig Separate FB FS Free SigFree FlagFree Input.
 destruct (exec_schnorr_scalar_read s [] e le m bs bsig bf S Flag Symbol Sig Separate FB FS
  Free SigFree FlagFree Input ltac:(cbn;lia) ltac:(intros i Index;cbn in Index;lia))
 as (mf & Prefix & Scalar & Overflow & Empty & Keep & Frame & Read).
 assert (Rejected:Z.leb canonical_group_order (@toZ (WordToZ 8) s)=true) by (apply Z.leb_le;exact Bound).
 rewrite Rejected in Prefix.
 exists mf,(schnorr_scalar_read_temps le true);split.
 - rewrite schnorr_scalar_read_source;eapply exec_statement_prefix_aborts;[discriminate|exact Prefix].
 - split;[apply schnorr_spec_reject_scalar;exact Bound|];split;[exact Keep|];split;assumption.
Qed.

Lemma schnorr_spec_reject_pubkey (pk msg r s:Ty.tySem (Word 8)):
 xonly_parse_result pk=Int.zero ->
 Simplicity.Bit.toBool (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,msg),(r,s)))=false.
Proof.
 intro Rejected;apply xonly_parse_failure_iff in Rejected;destruct Rejected as [Bound|Failed].
 - rewrite literal_bip0340_check_guarded_value,canonical_field_order_matches_limb_model.
   assert (PK:Z.ltb (@toZ (WordToZ 8) pk) feP=false) by (apply Z.ltb_ge;exact Bound).
   rewrite PK;reflexivity.
 - rewrite literal_bip0340_check_guarded_value.
   destruct (Z.ltb (@toZ (WordToZ 8) pk) canonical_field_order);[|reflexivity].
   destruct (andb (Z.ltb (@toZ (WordToZ 8) r) canonical_field_order)
    (Z.ltb (@toZ (WordToZ 8) s) canonical_group_order));[|reflexivity].
   apply secp_schnorr_point_failed;exact Failed.
Qed.
