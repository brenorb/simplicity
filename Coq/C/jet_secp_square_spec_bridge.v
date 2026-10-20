(** Arithmetic boundary for unrestricted Word256 inputs after the real reader's
    established normalization. Public reader/writer execution is still separate. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers Values Memory AST Clight ClightBigstep Events.
Require Import Simplicity.Ty Simplicity.Word C.jet_toZ.
Require Simplicity.Alg.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_mem C.jet_sx_rep C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_local_regions C.jet_secp_fe_math C.jet_secp_write_fe_wide_values.
Require Import C.jet_secp_b32_exec.
Require Import C.jet_secp_write_fe_wide_exec.
Require Import C.jet_secp_multiply_input_input C.jet_secp_multiply_writer_bridge
  C.jet_secp_multiply_literal_spec C.jet_secp_multiply_finish_product C.jet_secp_multiply_finish_execute.
Require Import C.jet_secp_square_execution C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_square_numeric_call.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition square_reader_rho (x : tySem (Word 8)) := limb_rho (normalized_value x).
Lemma square_reader_bounds x : square_input_bounds (square_reader_rho x).
Proof.
  intros i HI; pose proof (limb_rho_bound (normalized_value x) (normalized_value_range x) i) as H.
  unfold square_reader_rho.
  change (0 <= Int64.unsigned (limb_rho (normalized_value x) i) <= 4503599627370495) in H.
  destruct (Nat.eqb i 4); lia.
Qed.
Lemma square_product_matches_literal x :
  product_word (diagonal (square_reader_rho x)) = @literal_fe_square Alg.CoreFunSem x.
Proof.
  transitivity (product_word (pair_rho x x)).
  - unfold product_word; rewrite diagonal_radix, diagonal_second_radix, pair_radix_left, pair_radix_right.
    unfold square_reader_rho; rewrite radix_limb_rho by apply normalized_value_range; reflexivity.
  - rewrite pair_product_word, input_product_matches_literal; symmetry; apply literal_square_step.
Qed.
Theorem square_writer_output_matches_literal x :
  wide_fe_output (square_words (square_reader_rho x) 0%nat)
    (square_words (square_reader_rho x) 1%nat) (square_words (square_reader_rho x) 2%nat)
    (square_words (square_reader_rho x) 3%nat) (square_words (square_reader_rho x) 4%nat) =
  @literal_fe_square Alg.CoreFunSem x.
Proof.
  unfold square_words; rewrite product_writer_output by
    (apply diagonal_input_bounds; apply square_reader_bounds).
  apply square_product_matches_literal.
Qed.

Theorem eval_original_square_literal_from_reader x layout m :
  rep (square_reader_rho x) layout square_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Ctypes.Internal f_secp256k1_fe_sqr)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
       Vptr (blk layout 0) (Ptrofs.repr (bas layout 0))] E0 mf Vundef /\
    rep (square_reader_rho x) layout [mkreg (u64_cells 0 square_limbs) true (Some 40)] mf /\
    output_words layout (square_words (square_reader_rho x)) mf /\
    wide_fe_output (square_words (square_reader_rho x) 0%nat)
      (square_words (square_reader_rho x) 1%nat) (square_words (square_reader_rho x) 2%nat)
      (square_words (square_reader_rho x) 3%nat) (square_words (square_reader_rho x) 4%nat) =
      @literal_fe_square Alg.CoreFunSem x /\
    (forall i, (i < 5)%nat -> 0 <= Int64.unsigned (square_words (square_reader_rho x) i) <
      if Nat.eqb i 4 then 562949953421312 else 4503599627370496) /\
    lframe (fun b ofs => ~ foot layout (map rshape square_regs) b ofs) m mf.
Proof.
  intro HR.
  destruct (eval_original_square_owned_numeric (square_reader_rho x) layout m (square_reader_bounds x) HR)
    as (mf & HC & HP & HL & HV & HB & HF).
  exists mf; split; [exact HC|]; split; [exact HP|]; split; [exact HL|];
    split; [apply square_writer_output_matches_literal|]; split; assumption.
Qed.
