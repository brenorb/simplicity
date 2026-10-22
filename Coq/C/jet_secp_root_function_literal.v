(** Specialize the complete original helper call to every Word256 reader
    result and connect its branch and serialized field value to Simplicity. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_toZ C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_square_execution C.jet_secp_square_spec_bridge C.jet_secp_multiply_literal_spec
 C.jet_secp_rescale_literal C.jet_secp_root_literal C.jet_secp_root_chain_numeric
 C.jet_secp_root_check C.jet_secp_root_function.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_fe_square literal_root_candidate root_chain_candidate rescale_field_output.

Lemma root_reader_matches (x : Ty.tySem (Word 8)) : root_words_match (square_reader_rho x) x.
Proof.
 split;[apply square_reader_bounds|].
 pose proof (rescale_reader_residue x) as HR;rewrite field_prime_matches_normalizer in HR;exact HR.
Qed.
Lemma root_literal_candidate_canonical (x : Ty.tySem (Word 8)) :
 @toZ (WordToZ 8) (literal_root_candidate x) mod feP=@toZ (WordToZ 8) (literal_root_candidate x).
Proof.
 Local Transparent literal_root_candidate.
 unfold literal_root_candidate;rewrite literal_square_numeric;apply Z.mod_mod;unfold feP,feR;lia.
Qed.
Local Opaque literal_root_candidate.
Lemma root_candidate_output w x : root_words_match w x ->
 rescale_field_output (root_chain_candidate w)=literal_root_candidate x.
Proof.
 intro HM;pose proof (root_chain_candidate_matches w x HM) as [_ HC].
 apply (toZ_injective (WordToZ 8));rewrite rescale_field_output_value,field_prime_matches_normalizer,HC.
 apply root_literal_candidate_canonical.
Qed.

Definition root_reader_candidate (x : Ty.tySem (Word 8)) := root_chain_candidate (square_reader_rho x).
Definition root_reader_flag (x : Ty.tySem (Word 8)) := root_check_flag (square_reader_rho x).
Theorem eval_root_function_literal (x : Ty.tySem (Word 8)) m br ba :
 ba<>br -> fe_at m ba 0 (words5 (square_reader_rho x)) ->
 Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m br 0 40 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqrt_var)
   (Vptr br Ptrofs.zero::Vptr ba Ptrofs.zero::nil) E0 mf
   (Vint (if root_reader_flag x then Int.one else Int.zero)) /\
 fe_at mf br 0 (words5 (root_reader_candidate x)) /\ square_input_bounds (root_reader_candidate x) /\
 rescale_field_output (root_reader_candidate x)=literal_root_candidate x /\
 @literal_fe_square_root Alg.CoreFunSem x=
   (if root_reader_flag x then inr (rescale_field_output (root_reader_candidate x)) else inl tt) /\
 Mem.range_perm mf ba 0 40 Cur Freeable /\ Mem.range_perm mf br 0 40 Cur Freeable /\
 lframe (fun b _=>b<>ba /\ b<>br) m mf.
Proof.
 intros AR A FA FR.
 destruct (eval_root_function (square_reader_rho x) x m br ba AR (root_reader_matches x) A FA FR)
   as (mf & Call & R & FAF & FRF & Frame).
 exists mf;split;[exact Call|];split;[exact R|];split.
 - exact (proj1 (root_chain_candidate_matches _ _ (root_reader_matches x))).
 - split;[apply root_candidate_output;apply root_reader_matches|];split.
   + unfold root_reader_candidate,root_reader_flag.
     rewrite (root_candidate_output _ _ (root_reader_matches x));apply root_result_matches;apply root_reader_matches.
   + split;[exact FAF|];split;assumption.
Qed.
