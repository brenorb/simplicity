(** Retain the complete original decompression result in the actual linked
    Elements program, including both square-root outcomes and parity branches. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_multiply_normalize_bridge C.jet_secp_root_chain_numeric
 C.jet_secp_point_write_field C.jet_secp_decompress_literal C.jet_secp_decompress_function
 C.jet_secp_decompress_output C.jet_secp_decompress_helper_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_decompress decompress_machine_result.

Require Import C.jet_elements_taptweak_curve_transport C.jet_elements_taptweak_pure.
Theorem eval_elements_taptweak_decompress_literal w (x : Ty.tySem (Word 8)) (odd : Ty.tySem Bit) m bx br :
 bx<>br -> root_words_match w x -> fe_at m bx 0 (words5 w) ->
 Mem.range_perm m bx 0 40 Cur Freeable -> Mem.range_perm m br 0 88 Cur Freeable -> exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_ge_set_xo_var)
  (Vptr br Ptrofs.zero::Vptr bx Ptrofs.zero::Vint (if Bit.toBool odd then Int.one else Int.zero)::nil) E0 mf
  (Vint (match @literal_decompress Alg.CoreFunSem (odd,x) with inl _=>Int.zero | inr _=>Int.one end)) /\
 fe_at mf br 0 (point_field_limbs (decompress_input_field w)) /\
 fe_at mf br 40 (point_field_limbs (decompress_y_field w (Bit.toBool odd))) /\
 point_field_bounds (decompress_input_field w) /\ point_field_bounds (decompress_y_field w (Bit.toBool odd)) /\
 Mem.load Mint32 mf br 80=Some (Vint Int.zero) /\
 decompress_machine_result w (Bit.toBool odd)=@literal_decompress Alg.CoreFunSem (odd,x) /\
 Mem.range_perm mf bx 0 40 Cur Freeable /\ Mem.range_perm mf br 0 88 Cur Freeable /\
 lframe (fun b _=>b<>bx /\ b<>br) m mf.
Proof.
 intros Sep Match Field XF RF.
 destruct (eval_decompress_helper_literal w x odd m bx br Sep Match Field XF RF)
 as (mf & Call & Memory).
 exists mf;split;[|exact Memory].
 exact (elements_taptweak_curve_transport _ _ m _ _ mf _
 elements_taptweak_curve_has_decompress Call).
Qed.
