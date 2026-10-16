(** Fresh-frame setup preserves the actual initialized readonly lambda global. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Integers Values Memory.
Require Import C.jet_secp_scalar_lambda_global
  C.jet_secp_scalar_lambda_initialized C.jet_clight_readonly_frame.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque scalar_lambda_block.

Lemma scalar_lambda_words_readable m b :
  (forall i w, nth_error scalar_lambda_words i = Some w ->
    Mem.load Mint64 m b (8 * Z.of_nat i) = Some (Vlong w)) ->
  Mem.range_perm m b 0 32 Cur Readable.
Proof.
  intros HL ofs Ho.
  assert (HP : forall i w, nth_error scalar_lambda_words i = Some w ->
    Mem.range_perm m b (8 * Z.of_nat i) (8 * Z.of_nat i + 8) Cur Readable).
  { intros i w HX; exact (proj1 (Mem.load_valid_access _ _ _ _ _ (HL i w HX))). }
  destruct (Z_lt_ge_dec ofs 8) as [H8|H8].
  - apply (HP 0%nat (Int64.repr (-2377172193522762382)) eq_refl); cbn; lia.
  - destruct (Z_lt_ge_dec ofs 16) as [H16|H16].
    + apply (HP 1%nat (Int64.repr 1310022930574435960) eq_refl); cbn; lia.
    + destruct (Z_lt_ge_dec ofs 24) as [H24|H24].
      * apply (HP 2%nat (Int64.repr (-6546514211138018214)) eq_refl); cbn; lia.
      * apply (HP 3%nat (Int64.repr 6008836872998760672) eq_refl); cbn; lia.
Qed.

Theorem scalar_lambda_initialized_old_blocks m m' :
  scalar_lambda_initialized m ->
  (forall b, Mem.valid_block m b ->
    Mem.valid_block m' b /\
    (forall chunk ofs, Mem.load chunk m' b ofs = Mem.load chunk m b ofs) /\
    (forall ofs k p, Mem.perm m' b ofs k p -> Mem.perm m b ofs k p)) ->
  scalar_lambda_initialized m'.
Proof.
  intros ((HV & HP & HL) & HB) HOld.
  destruct (HOld scalar_lambda_block HV) as (HV' & HLoads & HPerms).
  assert (HL' : forall i w, nth_error scalar_lambda_words i = Some w ->
    Mem.load Mint64 m' scalar_lambda_block (8 * Z.of_nat i) = Some (Vlong w)).
  { intros i w HX; rewrite HLoads; exact (HL i w HX). }
  pose proof (scalar_lambda_words_readable m' scalar_lambda_block HL') as HP'.
  split; [exact (conj HV' (conj HP' HL'))|].
  unfold readonly_region_bounds; intros ofs k p; split.
  - intro HFinal; apply (proj1 (HB ofs k p)); exact (HPerms ofs k p HFinal).
  - intros (HRange & HOrder); eapply Mem.perm_implies; [|exact HOrder].
    destruct k; [apply Mem.perm_cur_max; exact (HP' ofs HRange)|exact (HP' ofs HRange)].
Qed.
