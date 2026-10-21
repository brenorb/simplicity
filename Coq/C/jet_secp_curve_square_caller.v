(** Actual affine-source square calls, initialized from caller storage.
    Reuses the selected optimized-square arithmetic and exact source limbs. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_b32 C.jet_secp_local_regions.
Require Import C.jet_secp_b32_exec C.jet_secp_multiply_normalize_bridge C.jet_secp_point_mul_storage.
Require Import C.jet_secp_square_execution C.jet_secp_square_columns C.jet_secp_square_numeric
  C.jet_secp_square_separate_caller C.jet_secp_multiply_finish_product C.jet_secp_multiply_checkpoint_columns.
Require Import C.jet_secp_curve_square.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_limbs square_words.

Lemma curve_square_initial k rho m bout bin :
  Mem.range_perm m bout 0 40 Cur Freeable ->
  fe_at m bin (curve_square_offset k) (words5 rho) ->
  Mem.range_perm m bin 0 88 Cur Freeable -> bout <> bin ->
  rep rho [(bout,0);(bin,0)] (curve_square_regs k) m.
Proof.
  intros HO HI HF HNe. apply two_region_rep_separate; [reflexivity|exact HNe| |].
  - change (region_ok rho [(bout,0);(bin,0)] m 0 (free_region fe_undef 40)).
    apply region_with_freeable.
    + apply region_fe_undefined_from_storage; cbn [bas blk lay nth fst snd].
      * lia.
      * exists 0; reflexivity.
      * change (40 <= 18446744073709551615); lia.
      * apply freeable_range_writable; exact HO.
    + reflexivity.
    + reflexivity.
    + exact HO.
    + apply fe_undef_storage_size.
  - apply owned_field_slice_region; [reflexivity|lia|destruct k; cbn [curve_square_offset]; lia|exact HI|exact HF].
Qed.

Lemma curve_square_fields k rho m mf bout bin :
  square_input_bounds rho -> fe_at m bin (curve_square_offset k) (words5 rho) ->
  rep rho [(bout,0);(bin,0)]
    [mkreg (u64_cells 0 square_limbs) true (Some 40); curve_square_input k] mf ->
  fe_at mf bout 0 (words5 (square_words rho)) /\ Mem.range_perm mf bout 0 40 Cur Freeable /\
  fe_at mf bin (curve_square_offset k) (words5 rho) /\ Mem.range_perm mf bin 0 88 Cur Freeable.
Proof.
  intros HB HI HR.
  pose proof (rep_region _ _ _ mf 0 _ HR eq_refl) as H0.
  pose proof (rep_region _ _ _ mf 1 _ HR eq_refl) as H1.
  destruct (square_output_region_field rho [(bout,0);(bin,0)] mf 0 HB H0) as [HO HFO].
  pose proof H1 as (_ & _ & _ & _ & _ & _ & HFI & _).
  change (Mem.range_perm mf bin 0 88 Cur Freeable) in HFI.
  split; [exact HO|]. split; [exact HFO|]. split; [|exact HFI].
  destruct HI as (HOfs & HA & HM & _).
  split; [exact HOfs|]. split; [exact HA|]. split; [exact HM|]. split.
  - apply freeable_range_writable. intros o HO'. apply HFI.
    destruct k; cbn [curve_square_offset] in *; lia.
  - intros i x HN.
    assert (HI : (i < 5)%nat).
    { change (i < length (words5 rho))%nat. apply nth_error_Some; rewrite HN; discriminate. }
    assert (HNVars : nth_error (vars5 0) i = Some (XLv i)).
    { destruct i as [|[|[|[|[|i]]]]]; try lia; reflexivity. }
    assert (HX : x = rho i).
    { unfold words5 in HN. destruct i as [|[|[|[|[|i]]]]]; try lia; inversion HN; reflexivity. }
    subst x.
    pose proof (region_load rho [(bout,0);(bin,0)] mf 1 _ _ Mint64 (XLv i) H1
      (u64_cells_nth (vars5 0) (curve_square_offset k) i (XLv i) HNVars)) as HL.
    change (Mem.load Mint64 mf bin (0 + (curve_square_offset k + 8*Z.of_nat i)) = Some (Vlong (rho i))) in HL.
    rewrite Z.add_0_l in HL. exact HL.
Qed.

Theorem eval_curve_square_from_storage k rho m bout bin :
  square_input_bounds rho -> Mem.range_perm m bout 0 40 Cur Freeable ->
  fe_at m bin (curve_square_offset k) (words5 rho) ->
  Mem.range_perm m bin 0 88 Cur Freeable -> bout <> bin ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
    [Vptr bout Ptrofs.zero; Vptr bin (Ptrofs.repr (curve_square_offset k))] E0 mf Vundef /\
  fe_at mf bout 0 (words5 (square_words rho)) /\ Mem.range_perm mf bout 0 40 Cur Freeable /\
  fe_at mf bin (curve_square_offset k) (words5 rho) /\ Mem.range_perm mf bin 0 88 Cur Freeable /\
  radix_value (square_words rho) mod field_prime = (radix_value rho * radix_value rho) mod field_prime /\
  (forall i, (i < 5)%nat -> 0 <= Int64.unsigned (square_words rho i) <
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) /\
  lframe (fun bx pos => ~ foot [(bout,0);(bin,0)] (map rshape (curve_square_regs k)) bx pos) m mf.
Proof.
  intros HB HO HI HF HNe.
  destruct (eval_curve_square_symbolic k rho [(bout,0);(bin,0)] m
    (curve_square_initial k rho m bout bin HO HI HF HNe)) as (mf & HC & HP & HL).
  destruct (curve_square_fields k rho m mf bout bin HB HI HP) as (HO' & HFO & HI' & HFI).
  exists mf. split; [exact HC|]. split; [exact HO'|]. split; [exact HFO|].
  split; [exact HI'|]. split; [exact HFI|]. split; [apply square_output_numeric; exact HB|].
  split; [apply square_output_bounds; exact HB|exact HL].
Qed.
