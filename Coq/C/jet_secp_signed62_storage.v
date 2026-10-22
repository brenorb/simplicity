(** Actual C conversion calls with their numeric value, range and ownership
    guarantees. These are inversion dependencies, not a public jet proof. *)
From Coq Require Import ZArith List.
From compcert Require Import AST Integers Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_signed62_repack C.jet_secp_signed62_numeric.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem eval_fe_to_signed62_value w m bout bin :
 fe_limbs_ok (Int64.unsigned (w 0%nat)) (Int64.unsigned (w 1%nat))
  (Int64.unsigned (w 2%nat)) (Int64.unsigned (w 3%nat)) (Int64.unsigned (w 4%nat)) ->
 bout<>bin -> Mem.range_perm m bout 0 40 Cur Freeable ->
 fe_at m bin 0 (words5 w) -> Mem.range_perm m bin 0 40 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_to_signed62)
  [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf Vundef /\
 fe_at mf bout 0 (words5 (fe_repack_words true w)) /\ fe_at mf bin 0 (words5 w) /\
 Mem.range_perm mf bout 0 40 Cur Freeable /\ Mem.range_perm mf bin 0 40 Cur Freeable /\
 signed62_normalized (fe_repack_words true w) /\
 signed62_unsigned_value (fe_repack_words true w)=radix_value w /\
 lframe (fun b _=>b<>bout /\ b<>bin) m mf.
Proof.
 intros Bound NE FO FI FS.
 destruct (eval_fe_repack_from_storage true w m bout bin NE FO FI FS)
  as (mf & Call & Out & Inp & OFree & IFree & Frame).
 exists mf;split;[exact Call|];split;[exact Out|];split;[exact Inp|];
 split;[exact OFree|];split;[exact IFree|];split.
 - apply fe_to62_normalized;exact Bound.
 - split;[apply fe_to62_preserves_value;exact Bound|exact Frame].
Qed.

Theorem eval_fe_from_signed62_value w m bout bin : signed62_normalized w ->
 bout<>bin -> Mem.range_perm m bout 0 40 Cur Freeable ->
 fe_at m bin 0 (words5 w) -> Mem.range_perm m bin 0 40 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_from_signed62)
  [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf Vundef /\
 fe_at mf bout 0 (words5 (fe_repack_words false w)) /\ fe_at mf bin 0 (words5 w) /\
 Mem.range_perm mf bout 0 40 Cur Freeable /\ Mem.range_perm mf bin 0 40 Cur Freeable /\
 fe_limbs_ok (Int64.unsigned (fe_repack_words false w 0%nat))
  (Int64.unsigned (fe_repack_words false w 1%nat))
  (Int64.unsigned (fe_repack_words false w 2%nat))
  (Int64.unsigned (fe_repack_words false w 3%nat))
  (Int64.unsigned (fe_repack_words false w 4%nat)) /\
 radix_value (fe_repack_words false w)=signed62_unsigned_value w /\
 lframe (fun b _=>b<>bout /\ b<>bin) m mf.
Proof.
 intros Bound NE FO FI FS.
 destruct (eval_fe_repack_from_storage false w m bout bin NE FO FI FS)
  as (mf & Call & Out & Inp & OFree & IFree & Frame).
 exists mf;split;[exact Call|];split;[exact Out|];split;[exact Inp|];
 split;[exact OFree|];split;[exact IFree|];split.
 - apply fe_from62_positioned;exact Bound.
 - split;[apply fe_from62_preserves_value;exact Bound|exact Frame].
Qed.
