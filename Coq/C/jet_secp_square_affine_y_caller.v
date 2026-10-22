(** Square into the Y field of a real 88-byte allocation, preserving all
    bytes outside the two actual field footprints. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_b32 C.jet_secp_local_regions.
Require Import C.jet_secp_b32_exec C.jet_secp_multiply_normalize_bridge C.jet_secp_point_mul_storage.
Require Import C.jet_secp_square_execution C.jet_secp_square_columns C.jet_secp_square_numeric
 C.jet_secp_square_separate_caller C.jet_secp_square_separate_numeric
 C.jet_secp_multiply_finish_product C.jet_secp_multiply_checkpoint_columns
 C.jet_secp_square_source_list C.jet_secp_square_affine_y C.jet_secp_square_separate_layout.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_limbs square_words.

Lemma affine_y_square_initial rho m bout bin :
 Mem.range_perm m bout 0 88 Cur Freeable ->
 fe_at m bin 0 (words5 rho) -> Mem.range_perm m bin 0 40 Cur Freeable -> bout<>bin ->
 rep rho [(bout,0);(bin,0)] affine_y_square_regs m.
Proof.
 intros FO FI FIn Ne;apply two_region_rep_separate;[reflexivity|exact Ne| |].
 - unfold region_ok;cbn [bas blk lay nth fst snd rcells rw rfree affine_y_square_regs].
   split;[change (0<=0);lia|].
   split;[eapply Mem.perm_valid_block;apply (FO 0);lia|].
   split;[reflexivity|]. split.
   + apply Forall_forall;intros c HC;cbn [rcells map In] in HC.
     repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end;
      try contradiction;subst c;apply writable_undefined_cell;
      cbn [bas blk lay nth fst snd size_chunk align_chunk].
     all: try (change Ptrofs.max_unsigned with 18446744073709551615;lia).
     all: try (match goal with |- (8 | ?offset) => exists (offset/8);reflexivity end).
     all: intros pos Range;apply Mem.perm_implies with (p1:=Freeable);[apply FO;lia|constructor].
   + split;[reflexivity|];split;[reflexivity|];split;[exact FO|].
     repeat constructor;cbn;lia.
 - change (region_ok rho [(bout,0);(bin,0)] m 1 (separate_input true (Some 40))).
   apply field_words_region;[reflexivity|exact FI|exact FIn].
Qed.

Lemma affine_y_square_fields rho m mf bout bin :
 square_input_bounds rho -> fe_at m bin 0 (words5 rho) ->
 rep rho [(bout,0);(bin,0)]
  [mkreg (u64_cells 40 square_limbs) true (Some 88);affine_y_square_input] mf ->
 fe_at mf bout 40 (words5 (square_words rho)) /\ Mem.range_perm mf bout 0 88 Cur Freeable /\
 fe_at mf bin 0 (words5 rho) /\ Mem.range_perm mf bin 0 40 Cur Freeable.
Proof.
 intros B In Rep.
 pose proof (rep_region _ _ _ mf 0 _ Rep eq_refl) as R0.
 pose proof (rep_region _ _ _ mf 1 _ Rep eq_refl) as R1.
 pose proof R0 as (_ & _ & _ & _ & _ & _ & F0 & _).
 pose proof R1 as (_ & _ & _ & _ & _ & _ & F1 & _).
 change (Mem.range_perm mf bout 0 88 Cur Freeable) in F0.
 change (Mem.range_perm mf bin 0 40 Cur Freeable) in F1.
 split.
 - split;[lia|];split;[exists 5;reflexivity|].
   split;[change (80<=18446744073709551615);lia|].
   split;[intros pos Range;apply Mem.perm_implies with (p1:=Freeable);[apply F0;lia|constructor]|].
   intros i x Nth.
   assert (I : (i<5)%nat).
   { change (i<length (words5 (square_words rho)))%nat;apply nth_error_Some;rewrite Nth;discriminate. }
   assert (NS : nth_error square_limbs i=Some (nth i square_limbs (XLv 0))).
   { apply nth_error_nth';rewrite original_square_symbolic_output;cbn;exact I. }
   pose proof (region_load rho [(bout,0);(bin,0)] mf 0 _ _ Mint64 _ R0
    (u64_cells_nth square_limbs 40 i _ NS)) as Load.
   rewrite square_output_den in Load by assumption.
   assert (X : x=square_words rho i).
   { unfold words5 in Nth;destruct i as [|[|[|[|[|i]]]]];try lia;inversion Nth;reflexivity. }
   subst x;exact Load.
 - split;[exact F0|];split;[|exact F1].
   exact (separate_input_field rho [(bout,0);(bin,0)] mf 1 (Some 40) R1).
Qed.

Theorem eval_square_affine_y_from_storage rho m bout bin :
 square_input_bounds rho -> Mem.range_perm m bout 0 88 Cur Freeable ->
 fe_at m bin 0 (words5 rho) -> Mem.range_perm m bin 0 40 Cur Freeable -> bout<>bin ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
  [Vptr bout (Ptrofs.repr 40);Vptr bin Ptrofs.zero] E0 mf Vundef /\
 fe_at mf bout 40 (words5 (square_words rho)) /\ Mem.range_perm mf bout 0 88 Cur Freeable /\
 fe_at mf bin 0 (words5 rho) /\ Mem.range_perm mf bin 0 40 Cur Freeable /\
 radix_value (square_words rho) mod field_prime=(radix_value rho*radix_value rho) mod field_prime /\
 square_input_bounds (square_words rho) /\
 lframe (fun b pos=>~foot [(bout,0);(bin,0)] (map rshape affine_y_square_regs) b pos) m mf.
Proof.
 intros B Out In Fin Ne.
 destruct (eval_square_affine_y_symbolic rho [(bout,0);(bin,0)] m
  (affine_y_square_initial rho m bout bin Out In Fin Ne)) as (mf & Call & Rep & Frame).
 destruct (affine_y_square_fields rho m mf bout bin B In Rep) as (O & FO & I & FI).
 exists mf;split;[exact Call|];split;[exact O|];split;[exact FO|];split;[exact I|];split;[exact FI|].
 split;[apply square_output_numeric;exact B|].
 split;[apply square_result_reusable;exact B|exact Frame].
Qed.
