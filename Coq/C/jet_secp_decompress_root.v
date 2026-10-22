(** Original sqrt_var writes directly into r->y, with the exact canonical
    y_from_x branch and candidate obtained from the caller's cubic-plus-seven. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns C.jet_secp_root_chain_numeric
 C.jet_secp_root_check C.jet_secp_root_function_literal C.jet_secp_root_affine_y_state
 C.jet_secp_root_affine_y_function C.jet_secp_decompress_numeric C.jet_secp_decompress_literal
 C.jet_secp_rescale_literal C.jet_secp_root_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge root_chain_candidate rescale_field_output literal_root_candidate
 literal_y_from_x literal_fe_square_root decompress_root_words root_check_flag.

Theorem eval_decompress_root w (x : Ty.tySem (Word 8)) m br ba :
 ba<>br -> root_words_match w x -> fe_at m ba 0 (words5 (decompress_root_words w)) ->
 Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m br 0 88 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqrt_var)
  (Vptr br (Ptrofs.repr 40)::Vptr ba Ptrofs.zero::nil) E0 mf
  (Vint (if root_check_flag (decompress_root_words w) then Int.one else Int.zero)) /\
 fe_at mf br 40 (words5 (root_chain_candidate (decompress_root_words w))) /\
 square_input_bounds (root_chain_candidate (decompress_root_words w)) /\
 @literal_y_from_x Alg.CoreFunSem x=
  (if root_check_flag (decompress_root_words w)
   then inr (rescale_field_output (root_chain_candidate (decompress_root_words w))) else inl tt) /\
 Mem.range_perm mf ba 0 40 Cur Freeable /\ Mem.range_perm mf br 0 88 Cur Freeable /\
 lframe (root_y_outside br ba) m mf.
Proof.
 intros AR Match A FA FR;pose proof (decompress_root_matches w x Match) as RootMatch.
 destruct (eval_root_affine_y_function (decompress_root_words w) (decompress_root_input x) m br ba AR RootMatch A FA FR)
  as (mf & Call & R & FAF & FRF & Frame).
 exists mf;split;[exact Call|];split;[exact R|];split.
 - exact (proj1 (root_chain_candidate_matches _ _ RootMatch)).
 - split.
   + pose proof (root_result_matches _ _ RootMatch) as Result.
     rewrite <-(root_candidate_output _ _ RootMatch) in Result.
     transitivity (@literal_fe_square_root Alg.CoreFunSem (decompress_root_input x)).
     * exact (literal_y_from_x_step x).
     * exact Result.
   + split;[exact FAF|];split;assumption.
Qed.
