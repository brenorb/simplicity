(** Canonical zero-test of an owned coordinate, without offset allocations. *)
From Coq Require Import ZArith List Lia FunctionalExtensionality.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_word_repr C.jet_toZ C.jet_exec C.jet_readBit_layout.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_linkage C.jets_secp.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_secp_local_regions C.jet_secp_write_fe_numeric C.jet_secp_write_fe_wide_values.
Require Import C.jet_secp_b32_exec C.jet_secp_field_zero C.jet_secp_zero_numeric.
Require Import C.jet_secp_canonical_zero C.jet_secp_canonical_normalize.
Require Import C.jet_secp_point_write_run C.jet_secp_point_write_initial C.jet_secp_point_write_preservation.
Require Import C.jet_secp_point_zero_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_normalize canonical_fe_is_zero.

Lemma point_canonical_write_rho value rc :
  wide_fe_rho (limb_rho value 0) (limb_rho value 1) (limb_rho value 2)
    (limb_rho value 3) (limb_rho value 4) rc = write_fe_rho value rc.
Proof.
  apply functional_extensionality; intro n.
  do 6 (destruct n as [|n]; [reflexivity|]).
  unfold wide_fe_rho, write_fe_rho, limb_rho, rho5, fe_limbs_of.
  destruct n; reflexivity.
Qed.

Lemma point_zero_initial_rep k value rc m b :
  fe_at m b (point_coordinate_offset k) (map Int64.repr (fe_limbs_of value)) ->
  Mem.range_perm m b 0 128 Cur Freeable ->
  rep (write_fe_rho value rc) [(b,0)] (point_write_initial_regs k) m.
Proof.
  intros HField HFree.
  rewrite <- point_canonical_write_rho.
  apply point_write_initial_rep; [|exact HFree].
  change (fe_at m b (point_coordinate_offset k) (map Int64.repr (fe_limbs_of value))).
  exact HField.
Qed.

Theorem eval_point_zero_canonical k m b (value : Ty.tySem (Word 8)) :
  fe_at m b (point_coordinate_offset k) (map Int64.repr (fe_limbs_of
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)))) ->
  Mem.range_perm m b 0 128 Cur Freeable ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_is_zero)
      [Vptr b (Ptrofs.repr (point_coordinate_offset k))] E0 mf
      (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem value)))) /\
    Mem.range_perm mf b 0 128 Cur Freeable /\
    lframe (fun bx _ => bx <> b) m mf.
Proof.
  intros HField HFree.
  set (v := @toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)).
  pose proof (point_zero_initial_rep k v 0 m b HField HFree) as HRep.
  destruct (eval_point_zero_from_owned_region k m [(b,0)] (write_fe_rho v 0) HRep)
    as [mf [HCall [HFinal HFrame]]].
  assert (HBounds : 0 <= v < 2 ^ 256).
  { unfold v; apply word_toZ_range. }
  rewrite (field_or_canonical_zero v 0 HBounds) in HCall.
  unfold v in HCall. rewrite canonical_fe_zero_after_normalize in HCall.
  change (Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_is_zero)
    [Vptr b (Ptrofs.repr (point_coordinate_offset k))] E0 mf
    (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem value))))) in HCall.
  pose proof (rep_free_region _ _ _ _ 0 128 HFinal ltac:(cbn;lia) eq_refl)
    as [_ HFinalFree].
  exists mf; split; [exact HCall|]; split; [exact HFinalFree|].
  eapply lframe_implies; [exact HFrame|]; intros bx pos HOther HValid.
  intro HFoot. destruct (point_write_foot_bounds k b bx pos HFoot) as [HB _].
  contradiction.
Qed.
Print Assumptions eval_point_zero_canonical.
