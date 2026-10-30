(** Execute the final original Schnorr suffix from its actual owned fields. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_affine_y_parity C.jet_secp_canonical_odd C.jet_secp_rescale_literal C.jet_secp_equal_loose
 C.jet_secp_field_io_preserve C.jet_clight_internal_frame C.jet_clight_internal_permissions
 C.jet_clight_internal_preserve C.jet_secp_schnorr_return_control.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge field_io_helpers canonical_fe_is_odd rescale_field_output.
Lemma schnorr_equal_allowed:allowed_call field_io_helpers (Internal f_secp256k1_fe_equal_var).
Proof. exists _secp256k1_fe_equal_var,f_secp256k1_fe_equal_var;split;reflexivity. Qed.
Theorem exec_schnorr_return_owned e le m br bx x y r :
 e!_r=Some (br,curve_ge_type) ->e!_rx=Some (bx,curve_fe_type) ->
 e!_secp256k1_fe_normalize_var=None ->e!_secp256k1_fe_is_odd=None ->e!_secp256k1_fe_equal_var=None ->
 br<>bx ->square_input_bounds x ->square_input_bounds y ->
 (forall i,(i<5)%nat ->Int64.unsigned (r i)<if Nat.eqb i 4 then 562949953421312 else 4503599627370496) ->
 fe_at m br 0 (words5 x) ->fe_at m br 40 (words5 y) ->fe_at m bx 0 (words5 r) ->
 Mem.range_perm m br 0 88 Cur Freeable ->Mem.range_perm m bx 0 40 Cur Freeable ->
 let odd:=Simplicity.Bit.toBool (@canonical_fe_is_odd Simplicity.Alg.CoreFunSem (rescale_field_output y)) in
 let equal:=Z.eqb (radix_value r mod feP) (radix_value x mod feP) in
 exists mf,
 Clight2.exec_stmt secp_ge e le m schnorr_return_tail E0 (schnorr_return_temps le odd equal) mf
  (Out_return (Some (Vint (bit_int (andb (negb odd) equal)),tint))) /\
 Mem.range_perm mf br 0 88 Cur Freeable /\Mem.range_perm mf bx 0 40 Cur Freeable /\
 lframe (fun b _=>b<>br /\b<>bx) m mf /\readonly_preserved m mf.
Proof.
 intros LocalR LocalX NS OS ES Different BX BY BR X Y R FreeP FreeR;cbn zeta.
 set (odd:=Simplicity.Bit.toBool (@canonical_fe_is_odd Simplicity.Alg.CoreFunSem (rescale_field_output y))).
 set (equal:=Z.eqb (radix_value r mod feP) (radix_value x mod feP)).
 destruct (eval_affine_normalized_y_odd y m br BY Y FreeP)
  as (mn & mo & Normalize & Odd & FreePO & YFrame & YReadonly).
 fold odd in Odd.
 assert (XO:fe_at mo br 0 (words5 x)).
 { eapply curve_keep_field_range;[reflexivity|exact X|exact YFrame|].
   intros pos Bound;right;left;change (0<=pos<40) in Bound;lia. }
 assert (RO:fe_at mo bx 0 (words5 r)).
 { eapply curve_keep_field_range;[reflexivity|exact R|exact YFrame|].
   intros pos Bound;left;congruence. }
 assert (FreeRO:Mem.range_perm mo bx 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FreeR|exact YFrame|];intros;left;congruence. }
 destruct odd eqn:Parity.
 - exists mo;split.
   + eapply exec_schnorr_return_from_calls with (mn:=mn) (mo:=mo) (me:=mo);try eassumption.
     intro Impossible;discriminate Impossible.
   + split;[exact FreePO|];split;[exact FreeRO|];split;[|exact YReadonly].
     eapply lframe_implies;[exact YFrame|];intros b pos [Outside _] Valid;left;exact Outside.
 - destruct (eval_field_equal_loose_owned r x mo bx br (not_eq_sym Different) BR BX RO XO FreeRO
    ltac:(intros pos Bound;apply FreePO;lia)) as (mf & Equal & FreeRF & FreeXF & EqualFrame).
   change (Clight2.eval_funcall secp_ge mo (Internal f_secp256k1_fe_equal_var)
    [Vptr bx Ptrofs.zero;Vptr br Ptrofs.zero] E0 mf (Vint (bit_int equal))) in Equal.
   assert (Permissions:keeps_permissions mo mf).
   { exact (proj2 (internal_exec_keeps_permissions secp_ge field_io_helpers field_io_helpers_ok)
     mo _ _ _ mf _ Equal schnorr_equal_allowed). }
   assert (EqualReadonly:readonly_preserved mo mf).
   { exact (proj2 (internal_exec_preserved secp_ge field_io_helpers field_io_helpers_ok)
     mo _ _ _ mf _ Equal schnorr_equal_allowed). }
   exists mf;split.
   + eapply exec_schnorr_return_from_calls with (mn:=mn) (mo:=mo) (me:=mf);try eassumption.
     intros;exact Equal.
   + split;[intros pos Bound;apply Permissions;apply FreePO;exact Bound|].
     split;[exact FreeRF|];split.
     * eapply lframe_trans.
       { eapply lframe_implies;[exact YFrame|];intros b pos [Outside _] Valid;left;exact Outside. }
       eapply lframe_implies;[exact EqualFrame|];intros b pos [OutsideR OutsideX] Valid;split;assumption.
     * eapply preserved_trans;[exact YReadonly|exact EqualReadonly].
Qed.
