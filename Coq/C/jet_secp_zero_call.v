(** Canonical return of the actual C field-zero helper, from owned memory. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_word_repr C.jet_toZ C.jet_exec C.jet_readBit_layout C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_linkage C.jets_secp.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_secp_local_regions C.jet_secp_local_call C.jet_secp_write_fe_numeric.
Require Import C.jet_secp_field_zero C.jet_secp_zero_numeric C.jet_secp_canonical_zero C.jet_secp_canonical_normalize.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_normalize canonical_fe_is_zero.
Theorem eval_field_zero_canonical m ba (value : Ty.tySem (Word 8)) :
  fe_at m ba 0 (map Int64.repr (fe_limbs_of
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)))) ->
  Mem.range_perm m ba 0 40 Cur Freeable ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_is_zero)
      [Vptr ba Ptrofs.zero] E0 mf (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem value)))) /\
    Mem.range_perm mf ba 0 40 Cur Freeable /\
    lframe (fun b _ => b <> ba) m mf.
Proof.
  intros HField HFree.
  set (v := @toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)).
  pose proof (local_write_initial_rep_from_field v 0 m ba HField HFree) as HRep.
  destruct (eval_field_zero_from_owned_region m [(ba,0)] (write_fe_rho v 0) HRep)
    as [mf [HCall [HFinal HFrame]]].
  assert (HBounds : 0 <= v < 2 ^ 256).
  { unfold v; apply word_toZ_range. }
  rewrite (field_or_canonical_zero v 0 HBounds) in HCall.
  unfold v in HCall. rewrite canonical_fe_zero_after_normalize in HCall.
  change (Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_is_zero)
    [Vptr ba Ptrofs.zero] E0 mf
    (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem value))))) in HCall.
  pose proof (rep_free_region _ _ _ _ 0 40 HFinal ltac:(cbn; lia) eq_refl) as [_ HFinalFree].
  exists mf; split; [exact HCall|]; split; [exact HFinalFree|].
  eapply lframe_implies; [exact HFrame|]; intros b pos HOther HValid.
  apply no_local_write_foot; exact HOther.
Qed.
