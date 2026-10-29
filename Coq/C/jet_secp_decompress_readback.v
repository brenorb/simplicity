(** Machine limbs and curve evidence retained by the original decompressor,
    for the following verifier arithmetic. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns
 C.jet_secp_b32_exec C.jet_secp_square_spec_bridge C.jet_secp_rescale_literal C.jet_secp_point_field_bridge
 C.jet_secp_point_write_field C.jet_secp_field_mul_small C.jet_secp_field_negate_separate
 C.jet_secp_field_weak_loose C.jet_secp_mixed_finite_prefix C.jet_secp_write_fe_numeric
 C.jet_secp_root_chain_numeric C.jet_secp_root_check C.jet_secp_decompress_numeric
 C.jet_secp_decompress_body C.jet_secp_decompress_parity C.jet_secp_decompress_literal
 C.jet_secp_decompress_output C.jet_secp_decompress_function C.jet_secp_decompress_curve
 C.jet_secp_curve_literal C.jet_secp_canonical_normalize C.jet_secp_canonical_odd C.jet_secp_negate_literal_contract
 C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque root_chain_candidate decompress_root_words rescale_field_output literal_decompress
 literal_ge_is_on_curve canonical_fe_normalize literal_fe_negate.

Definition decompress_parity_words value (odd:bool) := if xorb (Z.testbit value 0) odd
 then negate_sep_words (limb_rho value) else limb_rho value.
Definition decompress_y_words w odd := if root_check_flag (decompress_root_words w)
 then decompress_parity_words (decompress_body_value w) odd else root_chain_candidate (decompress_root_words w).

Lemma decompress_y_words_limbs w odd : words5 (decompress_y_words w odd)=decompress_body_y w odd.
Proof.
 unfold decompress_y_words,decompress_body_y;destruct (root_check_flag (decompress_root_words w));[|reflexivity].
 unfold decompress_parity_words,decompress_parity_limbs;destruct (xorb (Z.testbit (decompress_body_value w) 0) odd);reflexivity.
Qed.
Lemma decompress_y_words_output w odd :
 rescale_field_output (decompress_y_words w odd)=point_field_output (decompress_y_field w odd).
Proof.
 unfold decompress_y_words,decompress_y_field;destruct (root_check_flag (decompress_root_words w));[|reflexivity].
 unfold decompress_parity_words,decompress_parity_field;destruct (xorb (Z.testbit (decompress_body_value w) 0) odd);reflexivity.
Qed.
Lemma decompress_y_words_bounds w (x:Ty.tySem (Word 8)) odd : root_words_match w x ->
 square_input_bounds (decompress_y_words w odd).
Proof.
 intro Match;unfold decompress_y_words;destruct (root_check_flag (decompress_root_words w)).
 - pose proof (field_mod_256_range (radix_value (root_chain_candidate (decompress_root_words w)))) as Value.
   change (0<=decompress_body_value w<2^256) in Value.
   unfold decompress_parity_words;destruct (xorb (Z.testbit (decompress_body_value w) 0) odd).
   + apply (proj2 (negate_sep_numeric _ ltac:(apply mixed_positioned_tight;
       exact (proj1 (point_reader_limb_model _ Value))))).
   + intros i Hi;pose proof (limb_rho_bound _ Value i) as B.
     change (0<=Int64.unsigned (limb_rho (decompress_body_value w) i)<=4503599627370495) in B.
     destruct (Nat.eqb i 4);lia.
 - exact (proj1 (root_chain_candidate_matches _ _ (decompress_root_matches w x Match))).
Qed.

Lemma decompress_literal_point_curve w (x:Ty.tySem (Word 8)) (odd:Ty.tySem Bit) ap :
 root_words_match w x -> @literal_decompress Alg.CoreFunSem (odd,x)=inr ap ->
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem ap)=Datatypes.true.
Proof.
 intros Match Output;rewrite literal_decompress_step,(decompress_y_from_x_result w x Match) in Output.
 destruct (root_check_flag (decompress_root_words w)) eqn:Flag;[|discriminate].
 injection Output as <-.
 destruct (xorb (Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem
   (rescale_field_output (root_chain_candidate (decompress_root_words w))))) (Bit.toBool odd)).
 - rewrite decompress_negated_y_curve.
   exact (decompress_root_success_curve w _ (decompress_normalized_input_match w x Match) Flag).
 - exact (decompress_root_success_curve w _ (decompress_normalized_input_match w x Match) Flag).
Qed.
Lemma decompress_retained_literal w (x:Ty.tySem (Word 8)) (odd:Ty.tySem Bit) : root_words_match w x ->
 @literal_decompress Alg.CoreFunSem (odd,x)=
 if root_check_flag (decompress_root_words w)
 then inr (rescale_field_output w,rescale_field_output (decompress_y_words w (Bit.toBool odd))) else inl tt.
Proof.
 intro Match;rewrite <-(decompress_machine_matches_literal w x odd Match).
 unfold decompress_machine_result;destruct (root_check_flag (decompress_root_words w));[|reflexivity].
 rewrite decompress_input_field_output,decompress_y_words_output;reflexivity.
Qed.

Theorem eval_decompress_retained w (x:Ty.tySem (Word 8)) (odd:Ty.tySem Bit) m bx br :
 bx<>br -> root_words_match w x -> fe_at m bx 0 (words5 w) ->
 Mem.range_perm m bx 0 40 Cur Freeable -> Mem.range_perm m br 0 88 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_xo_var)
  [Vptr br Ptrofs.zero;Vptr bx Ptrofs.zero;Vint (if Bit.toBool odd then Int.one else Int.zero)] E0 mf
  (Vint (decompress_body_return w)) /\
 fe_at mf br 0 (words5 w) /\ fe_at mf br 40 (words5 (decompress_y_words w (Bit.toBool odd))) /\
 Mem.load Mint32 mf br 80=Some (Vint Int.zero) /\
 square_input_bounds (decompress_y_words w (Bit.toBool odd)) /\
 @literal_decompress Alg.CoreFunSem (odd,x)=
  (if root_check_flag (decompress_root_words w)
   then inr (rescale_field_output w,rescale_field_output (decompress_y_words w (Bit.toBool odd))) else inl tt) /\
 (root_check_flag (decompress_root_words w)=Datatypes.true ->
  Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem
   (rescale_field_output w,rescale_field_output (decompress_y_words w (Bit.toBool odd))))=Datatypes.true) /\
 Mem.range_perm mf bx 0 40 Cur Freeable /\ Mem.range_perm mf br 0 88 Cur Freeable /\
 lframe (fun b _=>b<>bx /\ b<>br) m mf.
Proof.
 intros Separate Match Input FreeX FreeR.
 destruct (eval_decompress_function w x (Bit.toBool odd) m bx br Separate Match Input FreeX FreeR)
  as (mf & Call & X & Y & Flag & Root & FX & FR & Frame).
 pose proof (decompress_retained_literal w x odd Match) as Literal.
 rewrite <-decompress_y_words_limbs in Y.
 exists mf;split;[exact Call|];split;[exact X|];split;[exact Y|];split;[exact Flag|];split.
 - exact (decompress_y_words_bounds w x (Bit.toBool odd) Match).
 - split;[exact Literal|];split.
   + intro Success;eapply decompress_literal_point_curve;[exact Match|].
     rewrite Success in Literal;exact Literal.
   + split;[exact FX|];split;[exact FR|exact Frame].
Qed.

Lemma decompress_readback_closed :
 closed_stmtb secp_closed_helpers (fn_body f_secp256k1_ge_set_xo_var)=Datatypes.true.
Proof. vm_compute;reflexivity. Qed.
Lemma decompress_call_readonly m mf args v :
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_xo_var) args E0 mf v ->
 readonly_preserved m mf.
Proof.
 intro Call;eapply secp_closed_function_preserved;[exact decompress_readback_closed|reflexivity|exact Call].
Qed.
