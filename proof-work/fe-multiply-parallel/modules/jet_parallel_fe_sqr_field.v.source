(** Literal canonical [fe_square] ([iden &&& iden >>> fe_multiply], pinned
    Programs/LibSecp256k1.hs) and the original in-place squaring from the
    normalized store produced by the original reader. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Integers Values Memory Clight ClightBigstep Events.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_toZ C.jet_word_repr C.jet_multiply_spec.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_fe_math C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp C.jet_secp_local_regions.
Require Import C.jet_secp_b32_exec C.jet_secp_field_add_initial.
Require Import C.jet_secp_canonical_normalize C.jet_secp_canonical_negate C.jet_secp_negate_literal_contract.
Require Import C.jet_literal_division_parametric C.jet_secp_write_fe_wide_exec.
Require Import C.jet_parallel_fe_mul_oracle C.jet_parallel_fe_mul_model C.jet_parallel_fe_mul_run.
Require Import C.jet_parallel_fe_mul_field C.jet_parallel_fe_sqr_model C.jet_parallel_fe_sqr_run.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 20.

Definition literal_fe_square {term : Alg.Core.Algebra} : term (Word 8) (Word 8) :=
  iden &&& iden >>> @literal_fe_multiply term.

Lemma literal_fe_square_parametric : Alg.Core.Parametric (@literal_fe_square).
Proof.
  intros term1 term2 R. unfold literal_fe_square.
  apply Alg.comp_Parametric;
    [apply Alg.pair_Parametric; apply Alg.iden_Parametric|apply literal_fe_multiply_parametric].
Qed.

Local Opaque literal_fe_multiply.
Lemma literal_fe_square_numeric (a : Ty.tySem (Word 8)) :
  @toZ (WordToZ 8) (@literal_fe_square Alg.CoreFunSem a) =
  (@toZ (WordToZ 8) a * @toZ (WordToZ 8) a) mod canonical_field_order.
Proof.
  change (@toZ (WordToZ 8) (@literal_fe_multiply Alg.CoreFunSem (a,a)) =
    (@toZ (WordToZ 8) a * @toZ (WordToZ 8) a) mod canonical_field_order).
  apply literal_fe_multiply_numeric.
Qed.
Local Opaque literal_fe_square canonical_fe_normalize.

Section FIELD.
Variables A : Z.
Hypothesis HA : 0 <= A < 2 ^ 256.

Definition fsr : nat -> int64 :=
  fs_rho (limb_rho A 0) (limb_rho A 1) (limb_rho A 2) (limb_rho A 3) (limb_rho A 4).
Definition fs_out : list int64 :=
  [fs_t0 (limb_rho A 0) (limb_rho A 1) (limb_rho A 2) (limb_rho A 3) (limb_rho A 4);
   fs_t1 (limb_rho A 0) (limb_rho A 1) (limb_rho A 2) (limb_rho A 3) (limb_rho A 4);
   fs_t2 (limb_rho A 0) (limb_rho A 1) (limb_rho A 2) (limb_rho A 3) (limb_rho A 4);
   fs_t3 (limb_rho A 0) (limb_rho A 1) (limb_rho A 2) (limb_rho A 3) (limb_rho A 4);
   fs_t4 (limb_rho A 0) (limb_rho A 1) (limb_rho A 2) (limb_rho A 3) (limb_rho A 4)].

Lemma fsr_field : field_values fsr 0 = map Int64.repr (fe_limbs_of A).
Proof. reflexivity. Qed.

Lemma fe_sqr_initial_rep m ba :
  fe_at m ba 0 (map Int64.repr (fe_limbs_of A)) -> Mem.range_perm m ba 0 40 Cur Freeable ->
  rep fsr [(ba,0)] fe_sqr_regs m.
Proof.
  intros HFA HFreeA. rewrite <- fsr_field in HFA. unfold fe_sqr_regs.
  apply (rep_add fsr [] [] m ba 0); [apply rep_nil|cbn; tauto|].
  apply region_with_freeable.
  - apply field_region_from_values; exact HFA.
  - reflexivity.
  - reflexivity.
  - exact HFreeA.
  - apply field_region_storage_size.
Qed.

Lemma sqr_cell_in i : (i < 5)%nat ->
  In (mkcell (8 * Z.of_nat i) Mint64 (Some (nth i fe_sqr_out (XLc Int64.zero))))
    (rcells (mkreg (u64_cells 0 fe_sqr_out) true (Some 40))).
Proof. intros Hi. do 5 (destruct i as [|i]; [cbn; tauto|]). lia. Qed.

Lemma fe_sqr_out_field m ba :
  rep fsr [(ba,0)] fe_sqr_out_regs m ->
  fe_at m ba 0 fs_out /\ Mem.range_perm m ba 0 40 Cur Freeable.
Proof.
  intro HRep.
  pose proof (rep_region fsr [(ba,0)] _ m 0 _ HRep eq_refl) as HRegion.
  destruct HRegion as (HB0 & HV & HSort & HCells & HStorage).
  destruct HStorage as (_ & _ & HFree & _).
  change (Mem.range_perm m ba 0 40 Cur Freeable) in HFree.
  assert (HL : forall i x, nth_error fs_out i = Some x ->
    Mem.load Mint64 m ba (0 + 8 * Z.of_nat i) = Some (Vlong x)).
  { pose proof (rep_region fsr [(ba,0)] _ m 0 _ HRep eq_refl) as HR0.
    intros i x Hi.
    assert (Hi5 : (i < length fs_out)%nat).
    { apply nth_error_Some. rewrite Hi. discriminate. }
    change (length fs_out) with 5%nat in Hi5.
    pose proof (region_load fsr [(ba,0)] m 0 _ (8 * Z.of_nat i) Mint64 _ HR0
      (sqr_cell_in i Hi5)) as HLd.
    do 5 (destruct i as [|i]; [cbn in Hi; inversion Hi; subst x; exact HLd|]).
    lia. }
  split; [|exact HFree].
  unfold fe_at. split; [lia|]. split; [exists 0; lia|].
  split; [change Ptrofs.max_unsigned with 18446744073709551615; lia|].
  split; [apply freeable_range_writable; exact HFree|].
  exact HL.
Qed.

Lemma fs_solves_fsr : Forall (u128_evok fsr) fe_sqr_log.
Proof. apply fs_solves. Qed.

Lemma fe_sqr_out_bounds : forall n x, nth_error fs_out n = Some x -> Int64.unsigned x <= 2 ^ 60.
Proof.
  destruct (limbs_ok_of A HA) as [HLA _].
  destruct (fs_sqr_values _ _ _ _ _ HLA) as (B0 & B1 & B2 & B3 & B4 & _).
  intros n x Hn.
  do 5 (destruct n as [|n]; [cbn in Hn; inversion Hn; subst x; lia|]).
  destruct n; discriminate.
Qed.

Lemma fe_sqr_out_value :
  fe_val (Int64.unsigned (nth 0 fs_out Int64.zero)) (Int64.unsigned (nth 1 fs_out Int64.zero))
    (Int64.unsigned (nth 2 fs_out Int64.zero)) (Int64.unsigned (nth 3 fs_out Int64.zero))
    (Int64.unsigned (nth 4 fs_out Int64.zero)) mod feP = (A * A) mod feP.
Proof.
  destruct (limbs_ok_of A HA) as [HLA HVA].
  destruct (fs_sqr_values _ _ _ _ _ HLA) as (_ & _ & _ & _ & _ & HV).
  cbn [nth fs_out]. rewrite HV, HVA. reflexivity.
Qed.
End FIELD.

Theorem eval_fe_sqr_from_normalized_field m ba (a : Ty.tySem (Word 8)) :
  fe_at m ba 0 (map Int64.repr (fe_limbs_of
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem a)))) ->
  Mem.range_perm m ba 0 40 Cur Freeable ->
  exists mf t0 t1 t2 t3 t4,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
      [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero] E0 mf Vundef /\
    fe_at mf ba 0 [t0; t1; t2; t3; t4] /\
    Int64.unsigned t0 <= 2 ^ 60 /\ Int64.unsigned t1 <= 2 ^ 60 /\
    Int64.unsigned t2 <= 2 ^ 60 /\ Int64.unsigned t3 <= 2 ^ 60 /\
    Int64.unsigned t4 <= 2 ^ 60 /\
    wide_fe_output t0 t1 t2 t3 t4 = @literal_fe_square Alg.CoreFunSem a /\
    Mem.range_perm mf ba 0 40 Cur Freeable /\
    lframe (fun b' pos => ~ foot [(ba,0)] (map rshape fe_sqr_regs) b' pos) m mf.
Proof.
  intros HFA HFreeA.
  set (A := @toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem a)) in *.
  assert (RA : 0 <= A < 2 ^ 256) by apply word_toZ_range.
  assert (HRep : rep (fsr A) [(ba,0)] fe_sqr_regs m) by (eapply fe_sqr_initial_rep; eassumption).
  destruct (eval_fe_sqr_owned (fsr A) [(ba,0)] m HRep (fs_solves_fsr A))
    as (mf & HCall & HFinal & HFrame).
  destruct (fe_sqr_out_field A RA mf ba HFinal) as (HOut & HFA').
  pose proof (fe_sqr_out_bounds A RA) as HBnd.
  pose proof (fe_sqr_out_value A RA) as HVal.
  exists mf.
  do 5 eexists. split; [exact HCall|]. split; [exact HOut|].
  split; [apply (HBnd 0%nat); reflexivity|]. split; [apply (HBnd 1%nat); reflexivity|].
  split; [apply (HBnd 2%nat); reflexivity|]. split; [apply (HBnd 3%nat); reflexivity|].
  split; [apply (HBnd 4%nat); reflexivity|].
  split.
  - apply (toZ_injective (WordToZ 8)).
    rewrite wide_fe_output_value. cbn [nth fs_out] in HVal. rewrite HVal.
    rewrite literal_fe_square_numeric, <- canonical_field_order_matches_limb_model.
    unfold A. rewrite !canonical_fe_normalize_numeric.
    rewrite <- Z.mul_mod by (pose proof canonical_field_order_range; lia). reflexivity.
  - split; [exact HFA'|exact HFrame].
Qed.
Print Assumptions literal_fe_square_parametric.
Print Assumptions literal_fe_square_numeric.
Print Assumptions eval_fe_sqr_from_normalized_field.
