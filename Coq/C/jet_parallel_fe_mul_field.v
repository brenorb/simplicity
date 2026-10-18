(** Original in-place field multiplication from the two normalized stores
    produced by the original readers, with its five output words and their
    relation to the literal canonical [fe_multiply]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Integers Values Memory Clight ClightBigstep Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_toZ C.jet_word_repr C.jet_multiply_spec.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_fe_math C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp C.jet_secp_local_regions.
Require Import C.jet_secp_b32_exec C.jet_secp_field_add_initial.
Require Import C.jet_secp_canonical_normalize C.jet_secp_canonical_negate C.jet_secp_negate_literal_contract.
Require Import C.jet_secp_write_fe_wide_exec.
Require Import C.jet_parallel_fe_mul_oracle C.jet_parallel_fe_mul_model C.jet_parallel_fe_mul_run.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 20.
Local Opaque canonical_fe_normalize literal_fe_multiply.

(** Literal canonical program numeric meaning. *)
Lemma literal_fe_multiply_numeric (a b : Ty.tySem (Word 8)) :
  @toZ (WordToZ 8) (@literal_fe_multiply Alg.CoreFunSem (a,b)) =
  (@toZ (WordToZ 8) a * @toZ (WordToZ 8) b) mod canonical_field_order.
Proof.
  Local Transparent literal_fe_multiply.
  rewrite literal_fe_multiply_matches.
  change (@toZ (WordToZ 8) (@canonical_fe_normalize512 Alg.CoreFunSem
    (@multiply_word_spec 8 Alg.CoreFunSem (a,b))) =
    (@toZ (WordToZ 8) a * @toZ (WordToZ 8) b) mod canonical_field_order).
  rewrite canonical_fe_normalize512_numeric, multiply_word_spec_numeric. reflexivity.
Qed.
Local Opaque literal_fe_multiply.

Section FIELD.
Variables A B : Z.
Hypothesis HA : 0 <= A < 2 ^ 256.
Hypothesis HB : 0 <= B < 2 ^ 256.

Definition fmr : nat -> int64 :=
  fm_rho (limb_rho A 0) (limb_rho A 1) (limb_rho A 2) (limb_rho A 3) (limb_rho A 4)
    (limb_rho B 0) (limb_rho B 1) (limb_rho B 2) (limb_rho B 3) (limb_rho B 4).
Definition fm_out : list int64 :=
  [fm_t0 (limb_rho A 0) (limb_rho A 1) (limb_rho A 2) (limb_rho A 3) (limb_rho A 4)
     (limb_rho B 0) (limb_rho B 1) (limb_rho B 2) (limb_rho B 3) (limb_rho B 4);
   fm_t1 (limb_rho A 0) (limb_rho A 1) (limb_rho A 2) (limb_rho A 3) (limb_rho A 4)
     (limb_rho B 0) (limb_rho B 1) (limb_rho B 2) (limb_rho B 3) (limb_rho B 4);
   fm_t2 (limb_rho A 0) (limb_rho A 1) (limb_rho A 2) (limb_rho A 3) (limb_rho A 4)
     (limb_rho B 0) (limb_rho B 1) (limb_rho B 2) (limb_rho B 3) (limb_rho B 4);
   fm_t3 (limb_rho A 0) (limb_rho A 1) (limb_rho A 2) (limb_rho A 3) (limb_rho A 4)
     (limb_rho B 0) (limb_rho B 1) (limb_rho B 2) (limb_rho B 3) (limb_rho B 4);
   fm_t4 (limb_rho A 0) (limb_rho A 1) (limb_rho A 2) (limb_rho A 3) (limb_rho A 4)
     (limb_rho B 0) (limb_rho B 1) (limb_rho B 2) (limb_rho B 3) (limb_rho B 4)].

Lemma fmr_first : field_values fmr 0 = map Int64.repr (fe_limbs_of A).
Proof. reflexivity. Qed.
Lemma fmr_second : field_values fmr 5 = map Int64.repr (fe_limbs_of B).
Proof. reflexivity. Qed.

Lemma limbs_ok_of V : 0 <= V < 2 ^ 256 ->
  fe_limbs_ok (Int64.unsigned (limb_rho V 0)) (Int64.unsigned (limb_rho V 1))
    (Int64.unsigned (limb_rho V 2)) (Int64.unsigned (limb_rho V 3)) (Int64.unsigned (limb_rho V 4)) /\
  fe_val (Int64.unsigned (limb_rho V 0)) (Int64.unsigned (limb_rho V 1))
    (Int64.unsigned (limb_rho V 2)) (Int64.unsigned (limb_rho V 3)) (Int64.unsigned (limb_rho V 4)) = V.
Proof.
  intros HV. rewrite !limb_rho_unsigned by exact HV. exact (fe_limbs_of_ok V HV).
Qed.

Lemma fe_mul_initial_rep m ba bb :
  ba <> bb ->
  fe_at m ba 0 (map Int64.repr (fe_limbs_of A)) -> fe_at m bb 0 (map Int64.repr (fe_limbs_of B)) ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bb 0 40 Cur Freeable ->
  rep fmr [(ba,0);(bb,0)] fe_mul_regs m.
Proof.
  intros HSeparate HFA HFB HFreeA HFreeB.
  rewrite <- fmr_first in HFA. rewrite <- fmr_second in HFB.
  unfold fe_mul_regs.
  apply (rep_add fmr [(ba,0)] [free_region (fe_reg (vars5 0)) 40] m bb 0).
  - apply (rep_add fmr [] [] m ba 0); [apply rep_nil|cbn; tauto|].
    apply region_with_freeable.
    + apply field_region_from_values; exact HFA.
    + reflexivity.
    + reflexivity.
    + exact HFreeA.
    + apply field_region_storage_size.
  - cbn. intros [HEqual|HFalse]; [congruence|contradiction].
  - apply region_with_freeable.
    + apply field_region_from_values; exact HFB.
    + reflexivity.
    + reflexivity.
    + exact HFreeB.
    + apply field_region_storage_size.
Qed.

Lemma out_cell_in i : (i < 5)%nat ->
  In (mkcell (8 * Z.of_nat i) Mint64 (Some (nth i fe_mul_out (XLc Int64.zero))))
    (rcells (mkreg (u64_cells 0 fe_mul_out) true (Some 40))).
Proof. intros Hi. do 5 (destruct i as [|i]; [cbn; tauto|]). lia. Qed.

Lemma fe_mul_out_field m ba bb :
  rep fmr [(ba,0);(bb,0)] fe_mul_out_regs m ->
  fe_at m ba 0 fm_out /\ Mem.range_perm m ba 0 40 Cur Freeable /\
  Mem.range_perm m bb 0 40 Cur Freeable.
Proof.
  intro HRep.
  pose proof (rep_region fmr [(ba,0);(bb,0)] _ m 0 _ HRep eq_refl) as HRegion.
  pose proof (rep_free_region fmr [(ba,0);(bb,0)] fe_mul_out_regs m 1%nat 40 HRep
    ltac:(cbn; lia) eq_refl) as [_ HFreeB].
  destruct HRegion as (HB0 & HV & HSort & HCells & HStorage).
  destruct HStorage as (_ & _ & HFree & _).
  change (Mem.range_perm m ba 0 40 Cur Freeable) in HFree.
  change (Mem.range_perm m bb 0 40 Cur Freeable) in HFreeB.
  assert (HL : forall i x, nth_error fm_out i = Some x ->
    Mem.load Mint64 m ba (0 + 8 * Z.of_nat i) = Some (Vlong x)).
  { pose proof (rep_region fmr [(ba,0);(bb,0)] _ m 0 _ HRep eq_refl) as HR0.
    intros i x Hi.
    assert (Hi5 : (i < length fm_out)%nat).
    { apply nth_error_Some. rewrite Hi. discriminate. }
    change (length fm_out) with 5%nat in Hi5.
    pose proof (region_load fmr [(ba,0);(bb,0)] m 0 _ (8 * Z.of_nat i) Mint64 _ HR0
      (out_cell_in i Hi5)) as HLd.
    do 5 (destruct i as [|i]; [cbn in Hi; inversion Hi; subst x; exact HLd|]).
    lia. }
  split; [|split; assumption].
  unfold fe_at. split; [lia|]. split; [exists 0; lia|].
  split; [change Ptrofs.max_unsigned with 18446744073709551615; lia|].
  split; [apply freeable_range_writable; exact HFree|].
  exact HL.
Qed.

Lemma fm_solves_fmr : Forall (u128_evok fmr) fe_mul_log.
Proof. apply fm_solves. Qed.

Lemma fe_mul_out_bounds : forall n x, nth_error fm_out n = Some x -> Int64.unsigned x <= 2 ^ 60.
Proof.
  destruct (limbs_ok_of A HA) as [HLA _]. destruct (limbs_ok_of B HB) as [HLB _].
  destruct (fm_mul_values _ _ _ _ _ _ _ _ _ _ HLA HLB) as (B0 & B1 & B2 & B3 & B4 & _).
  intros n x Hn.
  do 5 (destruct n as [|n]; [cbn in Hn; inversion Hn; subst x; lia|]).
  destruct n; discriminate.
Qed.

Lemma fe_mul_out_value :
  fe_val (Int64.unsigned (nth 0 fm_out Int64.zero)) (Int64.unsigned (nth 1 fm_out Int64.zero))
    (Int64.unsigned (nth 2 fm_out Int64.zero)) (Int64.unsigned (nth 3 fm_out Int64.zero))
    (Int64.unsigned (nth 4 fm_out Int64.zero)) mod feP = (A * B) mod feP.
Proof.
  destruct (limbs_ok_of A HA) as [HLA HVA]. destruct (limbs_ok_of B HB) as [HLB HVB].
  destruct (fm_mul_values _ _ _ _ _ _ _ _ _ _ HLA HLB) as (_ & _ & _ & _ & _ & HV).
  cbn [nth fm_out]. rewrite HV, HVA, HVB. reflexivity.
Qed.
End FIELD.

Theorem eval_fe_mul_from_normalized_fields m ba bb (a b : Ty.tySem (Word 8)) :
  ba <> bb ->
  fe_at m ba 0 (map Int64.repr (fe_limbs_of
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem a)))) ->
  fe_at m bb 0 (map Int64.repr (fe_limbs_of
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem b)))) ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bb 0 40 Cur Freeable ->
  exists mf t0 t1 t2 t3 t4,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
      [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero; Vptr bb Ptrofs.zero] E0 mf Vundef /\
    fe_at mf ba 0 [t0; t1; t2; t3; t4] /\
    Int64.unsigned t0 <= 2 ^ 60 /\ Int64.unsigned t1 <= 2 ^ 60 /\
    Int64.unsigned t2 <= 2 ^ 60 /\ Int64.unsigned t3 <= 2 ^ 60 /\
    Int64.unsigned t4 <= 2 ^ 60 /\
    wide_fe_output t0 t1 t2 t3 t4 = @literal_fe_multiply Alg.CoreFunSem (a,b) /\
    Mem.range_perm mf ba 0 40 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
    lframe (fun b' pos => ~ foot [(ba,0);(bb,0)] (map rshape fe_mul_regs) b' pos) m mf.
Proof.
  intros HSeparate HFA HFB HFreeA HFreeB.
  set (A := @toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem a)) in *.
  set (B := @toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem b)) in *.
  assert (RA : 0 <= A < 2 ^ 256) by apply word_toZ_range.
  assert (RB : 0 <= B < 2 ^ 256) by apply word_toZ_range.
  assert (HRep : rep (fmr A B) [(ba,0);(bb,0)] fe_mul_regs m)
    by (eapply fe_mul_initial_rep; eassumption).
  assert (HSol : Forall (u128_evok (fmr A B)) fe_mul_log) by (eapply fm_solves_fmr; eassumption).
  destruct (eval_fe_mul_owned (fmr A B) [(ba,0);(bb,0)] m HRep HSol)
    as (mf & HCall & HFinal & HFrame).
  assert (HOF : fe_at mf ba 0 (fm_out A B) /\ Mem.range_perm mf ba 0 40 Cur Freeable /\
    Mem.range_perm mf bb 0 40 Cur Freeable) by (eapply fe_mul_out_field; eassumption).
  destruct HOF as (HOut & HFA' & HFB').
  pose proof (fe_mul_out_bounds A B RA RB) as HBnd.
  pose proof (fe_mul_out_value A B RA RB) as HVal.
  exists mf.
  do 5 eexists. split; [exact HCall|]. split; [exact HOut|].
  split; [apply (HBnd 0%nat); reflexivity|]. split; [apply (HBnd 1%nat); reflexivity|].
  split; [apply (HBnd 2%nat); reflexivity|]. split; [apply (HBnd 3%nat); reflexivity|].
  split; [apply (HBnd 4%nat); reflexivity|].
  split.
  - apply (toZ_injective (WordToZ 8)).
    rewrite wide_fe_output_value. cbn [nth fm_out] in HVal. rewrite HVal.
    rewrite literal_fe_multiply_numeric, <- canonical_field_order_matches_limb_model.
    unfold A, B. rewrite !canonical_fe_normalize_numeric.
    rewrite <- Z.mul_mod by (pose proof canonical_field_order_range; lia). reflexivity.
  - split; [exact HFA'|]. split; [exact HFB'|exact HFrame].
Qed.
Print Assumptions literal_fe_multiply_numeric.
Print Assumptions eval_fe_mul_from_normalized_fields.
