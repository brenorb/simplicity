(** Construct both square-call regions from actual caller storage.
    The output may be uninitialized; no output/execution premise is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_rep C.jet_sx_revalue_cells.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_math C.jet_secp_fe_nv C.jet_secp_fe_b32 C.jet_secp_b32_exec
  C.jet_secp_local_regions C.jet_secp_wrapper_run C.jet_secp_multiply_run_run.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_multiply_checkpoint_columns C.jet_secp_multiply_finish_execute.
Require Import C.jet_secp_square_execution C.jet_secp_square_columns C.jet_secp_square_numeric
  C.jet_secp_square_source_list C.jet_secp_square_schedule C.jet_secp_square_denote.
Require Import C.jet_secp_square_separate_layout C.jet_secp_square_separate_exec C.jet_secp_square_separate_numeric.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque square_limbs sq_r0 sq_r1 sq_r2 sq_r3 sq_r4 square_words secp_ge.

Lemma field_words_region rho layout m r : bas layout r = 0 ->
  fe_at m (blk layout r) 0 (words5 rho) -> Mem.range_perm m (blk layout r) 0 40 Cur Freeable ->
  region_ok rho layout m r (separate_input true (Some 40)).
Proof.
  intros HBase (H0 & HA & HM & HP & HL) HF.
  apply (region_with_freeable rho layout m r (mkreg (u64_cells 0 (vars5 0)) true None) 40).
  - apply region_u64.
    + rewrite HBase; exact H0.
    + rewrite HBase; exact HA.
    + rewrite HBase; exact HM.
    + eapply Mem.perm_valid_block; apply (HP 0); lia.
    + rewrite HBase; exact HP.
    + intros i x HN; destruct (vars5_zero_nth i x HN) as [HI ->].
      rewrite HBase.
      split; [|reflexivity].
      change (Mem.load Mint64 m (blk layout r) (0 + 8 * Z.of_nat i) = Some (Vlong (rho i))).
      apply HL; unfold words5; destruct i as [|[|[|[|[|i]]]]]; try lia; reflexivity.
  - exact HBase.
  - reflexivity.
  - exact HF.
  - repeat constructor; cbn; lia.
Qed.

Theorem separate_square_initial_rep rho m bout bin :
  Mem.range_perm m bout 0 40 Cur Freeable ->
  fe_at m bin 0 (words5 rho) -> Mem.range_perm m bin 0 40 Cur Freeable -> bout <> bin ->
  rep rho [(bout,0);(bin,0)] (separate_regs true (Some 40)) m.
Proof.
  intros HO HI HF HNe; apply two_region_rep_separate; [reflexivity|exact HNe| |].
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
  - apply field_words_region; [reflexivity|exact HI|exact HF].
Qed.

Lemma separate_input_field rho layout m r freed :
  region_ok rho layout m r (separate_input true freed) ->
  fe_at m (blk layout r) (bas layout r) (words5 rho).
Proof.
  intro HR.
  pose proof (region_ok_revalue_u64 rho layout m r [XLv 0;XLv 1;XLv 2;XLv 3;XLv 4]
    true freed HR eq_refl) as HV.
  assert (HD : map (den rho (lay layout)) [XLv 0;XLv 1;XLv 2;XLv 3;XLv 4] = map Vlong (words5 rho)) by reflexivity.
  rewrite (revalue_u64_machine_map rho layout _ _ HD) in HV.
  eapply u64_region_fe_at; exact HV.
Qed.

Lemma square_output_region_field rho layout m r : square_input_bounds rho ->
  region_ok rho layout m r (mkreg (u64_cells 0 square_limbs) true (Some 40)) ->
  fe_at m (blk layout r) (bas layout r) (words5 (square_words rho)) /\
  Mem.range_perm m (blk layout r) 0 40 Cur Freeable.
Proof.
  intros HB H0.
  pose proof H0 as (_ & _ & _ & _ & HBase & HW & HF & _).
  assert (HK : forallb (isk KL) square_limbs = true).
  { rewrite original_square_symbolic_output; reflexivity. }
  pose proof (region_ok_revalue_u64 rho layout m r square_limbs true (Some 40) H0 HK) as HV.
  assert (HD : map (den rho (lay layout)) square_limbs = map Vlong (words5 (square_words rho))).
  { rewrite original_square_symbolic_output; cbn [map].
    rewrite (sq_r0_den rho (lay layout) HB), (sq_r1_den rho (lay layout) HB),
      (sq_r2_den rho (lay layout) HB), (sq_r3_den rho (lay layout) HB), (sq_r4_den rho (lay layout) HB).
    reflexivity. }
  rewrite (revalue_u64_machine_map rho layout _ _ HD) in HV.
  split; [eapply u64_region_fe_at; exact HV|exact HF].
Qed.

Lemma separate_output_field rho layout m writable freed : square_input_bounds rho ->
  rep rho layout [mkreg (u64_cells 0 square_limbs) true (Some 40); separate_input writable freed] m ->
  fe_at m (blk layout 0) (bas layout 0) (words5 (square_words rho)) /\
  Mem.range_perm m (blk layout 0) 0 40 Cur Freeable.
Proof.
  intros HB HR; apply square_output_region_field; [exact HB|].
  exact (rep_region _ _ _ m 0 _ HR eq_refl).
Qed.

Theorem eval_square_separate_from_storage rho m bout bin :
  square_input_bounds rho -> Mem.range_perm m bout 0 40 Cur Freeable ->
  fe_at m bin 0 (words5 rho) -> Mem.range_perm m bin 0 40 Cur Freeable -> bout <> bin ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
      [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf Vundef /\
    fe_at mf bout 0 (words5 (square_words rho)) /\ Mem.range_perm mf bout 0 40 Cur Freeable /\
    fe_at mf bin 0 (words5 rho) /\ Mem.range_perm mf bin 0 40 Cur Freeable /\
    radix_value (square_words rho) mod field_prime = (radix_value rho * radix_value rho) mod field_prime /\
    square_input_bounds (square_words rho) /\
    lframe (fun b _ => b <> bout /\ b <> bin) m mf.
Proof.
  intros HB HO HI HF HNe.
  destruct (eval_original_square_separate_numeric rho [(bout,0);(bin,0)] m true (Some 40) HB
    (separate_square_initial_rep rho m bout bin HO HI HF HNe)) as (mf & HC & HP & HL & HVal & HBounds & HFrame).
  destruct (separate_output_field rho [(bout,0);(bin,0)] mf true (Some 40) HB HP) as [HOut HOutFree].
  pose proof (rep_region _ _ _ mf 1 _ HP eq_refl) as HIn.
  pose proof (separate_input_field rho [(bout,0);(bin,0)] mf 1 (Some 40) HIn) as HInField.
  destruct HIn as (_ & _ & _ & _ & _ & _ & HInFree & _).
  exists mf; split; [exact HC|]; split; [exact HOut|]; split; [exact HOutFree|].
  split; [exact HInField|]; split; [exact HInFree|]; split; [exact HVal|].
  split; [apply square_result_reusable; exact HB|].
  eapply lframe_implies; [exact HFrame|].
  intros b ofs [HNoOut HNoIn] HV (r & sh & d & ch & HN & HCell & HE & HOfs).
  destruct r as [|[|r]]; [apply HNoOut; exact HE|apply HNoIn; exact HE|destruct r; discriminate HN].
Qed.
