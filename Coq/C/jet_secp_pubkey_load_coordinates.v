(** Exact canonical field coordinates returned by the original opaque-key loader. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_memcpy_model C.jet_secp_linkage C.jets_secp
 C.jet_secp_fe_math C.jet_secp_fe_nv C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge
 C.jet_secp_affine_storage C.jet_secp_storage_numeric C.jet_secp_pubkey_load_function
 C.jet_secp_pubkey_load_body C.jet_secp_field_zero_readonly C.jet_secp_curve_literal C.jet_secp_curve_polynomial
 C.jet_clight_internal_preserve.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Lemma affine_storage_coord_canonical w k:
 words5 (affine_storage_coord w k)=map Int64.repr
  (fe_limbs_of (field_storage_value (fun i=>w ((if k then 4 else 0)+i)%nat))).
Proof.
 pose proof (affine_storage_exact_coordinate w k) as Values.
 apply (f_equal (map Int64.repr)) in Values;rewrite map_map in Values.
 assert (Exact:map (fun x=>Int64.repr (Int64.unsigned x)) (words5 (affine_storage_coord w k))=
  words5 (affine_storage_coord w k)).
 { transitivity (map (fun x:int64=>x) (words5 (affine_storage_coord w k)));
   [apply map_ext;intro x;apply Int64.repr_unsigned|apply map_id]. }
 rewrite Exact in Values;exact Values.
Qed.
Theorem pubkey_storage_accept_curve w (x y:Ty.tySem (Word 8)):
 field_storage_value w=@toZ (WordToZ 8) x ->
 Simplicity.Bit.toBool (@literal_ge_is_on_curve Simplicity.Alg.CoreFunSem (x,y))=true ->
 pubkey_storage_accept w=true.
Proof.
 intros X Curve;rewrite literal_ge_curve_numeric in Curve;apply Z.eqb_eq in Curve.
 pose proof (secp_curve_x_nonzero (@toZ (WordToZ 8) x) (@toZ (WordToZ 8) y) (eq_sym Curve)) as Nonzero.
 unfold pubkey_storage_accept;apply Bool.negb_true_iff;apply Bool.not_true_is_false;intro Zero.
 pose proof (field_words_or_zero (affine_storage_coord w false) Zero) as Value.
 unfold affine_storage_coord in Value;rewrite storage_unpack_preserves_value in Value.
 change (field_storage_value w=0) in Value;rewrite X in Value.
 apply Nonzero;rewrite Value;apply Z.mod_0_l;unfold feP,feR;lia.
Qed.
Theorem eval_xonly_pubkey_load_coordinates (Model:memcpy_model) w m bin base bout
 (x y:Ty.tySem (Word 8)):
 Mem.range_perm m bout 0 88 Cur Freeable ->affine_storage_readable m bin base w ->
 field_storage_value w=@toZ (WordToZ 8) x ->
 field_storage_value (fun i=>w (4+i)%nat)=@toZ (WordToZ 8) y ->
 Simplicity.Bit.toBool (@literal_ge_is_on_curve Simplicity.Alg.CoreFunSem (x,y))=true ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_xonly_pubkey_load)
  [Vptr bout Ptrofs.zero;Vptr bin (Ptrofs.repr base)] E0 mf (Vint Int.one) /\
 fe_at mf bout 0 (map Int64.repr (fe_limbs_of (@toZ (WordToZ 8) x))) /\
 fe_at mf bout 40 (map Int64.repr (fe_limbs_of (@toZ (WordToZ 8) y))) /\
 Mem.load Mint32 mf bout 80=Some (Vint Int.zero) /\Mem.range_perm mf bout 0 88 Cur Freeable /\
 lframe (fun b _=>b<>bout) m mf /\readonly_preserved m mf.
Proof.
 intros Free Input X Y Curve.
 destruct (eval_xonly_pubkey_load Model w m bin base bout Free Input)
 as (mf & Call & Fields & Flag & FreeOut & Frame & Read).
 rewrite (pubkey_storage_accept_curve w x y X Curve) in Call.
 exists mf;split;[exact Call|];split.
 - pose proof (Fields false) as FX;rewrite affine_storage_coord_canonical in FX.
   change (fe_at mf bout 0 (map Int64.repr (fe_limbs_of (field_storage_value w)))) in FX.
   rewrite X in FX;exact FX.
 - split.
   + pose proof (Fields true) as FY;rewrite affine_storage_coord_canonical in FY.
     change (fe_at mf bout 40 (map Int64.repr (fe_limbs_of (field_storage_value (fun i=>w (4+i)%nat))))) in FY.
     rewrite Y in FY;exact FY.
   + repeat first [assumption|split].
Qed.
