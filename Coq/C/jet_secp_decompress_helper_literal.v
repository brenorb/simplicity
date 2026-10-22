(** Full original decompression helper call against the literal expression,
    through bounded point fields consumed by the original writer. The public
    jet still needs its frame readers, writer/tag/padding and outer lifecycle. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_multiply_normalize_bridge C.jet_secp_root_chain_numeric
 C.jet_secp_point_write_field C.jet_secp_decompress_literal C.jet_secp_decompress_function
 C.jet_secp_decompress_output.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_decompress decompress_machine_result.

Theorem eval_decompress_helper_literal w (x : Ty.tySem (Word 8)) (odd : Ty.tySem Bit) m bx br :
 bx<>br -> root_words_match w x -> fe_at m bx 0 (words5 w) ->
 Mem.range_perm m bx 0 40 Cur Freeable -> Mem.range_perm m br 0 88 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_xo_var)
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
 destruct (eval_decompress_function w x (Bit.toBool odd) m bx br Sep Match Field XF RF)
  as (mf & Call & X & Y & Finite & RootLiteral & XFF & RFF & Frame).
 rewrite (decompress_return_matches_literal w x odd Match) in Call.
 rewrite <-decompress_input_limbs in X;rewrite <-decompress_y_field_limbs in Y.
 exists mf;split;[exact Call|];split;[exact X|];split;[exact Y|];split.
 - apply decompress_input_field_bounded;exact (proj1 Match).
 - split;[apply (decompress_y_field_bounded w x (Bit.toBool odd));exact Match|].
   split;[exact Finite|];split;[apply decompress_machine_matches_literal;exact Match|].
   split;[exact XFF|];split;[exact RFF|exact Frame].
Qed.
