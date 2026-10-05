(** Literal port of the SigHash programs outputHash and inputUtxoHash, which
    share the shape
      (primitive VALUE &&& primitive SCRIPTHASH)
        >>> match (injl unit)
              (injr (((unit >>> ctx8Init) &&& oh >>> ctx8Add8)
                &&& (drop . assert $ iden) >>> ctx8Add32 >>> ctx8Finalize))
    with  assert t = t &&& unit >>> assertr cmrFail0 oh,
    and their value.  No C execution here. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Simplicity.Alg.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_assertion_spec C.jet_buffer_empty_spec C.jet_buffer_input C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha256_iv_init C.jet_read8s_layout.
Require Import C.jet_sha_ctx8_spec C.jet_sha_ctx8_model C.jet_sha_uchars_prep C.jet_sha_finalize_exec.
Require Import C.jet_sha_finalize_spec C.jet_sha_hash_closed.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim C.jet_sha_hash_loop C.jet_sha_hash_words.
Require Import C.jet_bitcoin_composite_hash C.jet_sha_ctxi.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 120.

(** assert t = t &&& unit >>> assertr cmrFail0 oh *)
Definition assert_spec {term : Alg.Assertion.Algebra} {A B : Ty}
    (t : @Alg.Assertion.domain term A (Ty.Sum Ty.Unit B)) : @Alg.Assertion.domain term A B :=
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core (@AC.pair _ _ _ core t (@AC.unit _ core))
    (@Alg.Assertion.Combinators.assertr Ty.Unit B Ty.Unit B term assertion_cmr_fail0
      (@AC.take _ _ _ core (@AC.iden _ core))).

Definition assert_iden_spec (B : Ty) {term : Alg.Assertion.Algebra} :
    @Alg.Assertion.domain term (Ty.Sum Ty.Unit B) B :=
  @assert_spec term _ B (@AC.iden _ (Alg.Assertion.toCore term)).

Lemma assert_iden_spec_parametric B : Alg.Assertion.Parametric (@assert_iden_spec B).
Proof.
  intros alg1 alg2 R. unfold assert_iden_spec, assert_spec. cbv zeta.
  pose proof (fun t1 t2 H => @Alg.assertr_Parametric alg1 alg2 R Ty.Unit B Ty.Unit B
    assertion_cmr_fail0 t1 t2 H) as HAR.
  destruct R as [R [HC HAm]]. set (RC := Alg.Core.Parametric.Pack HC).
  apply (Alg.comp_Parametric RC).
  - apply (Alg.pair_Parametric RC); [apply Alg.iden_Parametric|apply Alg.unit_Parametric].
  - apply HAR. apply (Alg.take_Parametric RC), Alg.iden_Parametric.
Qed.

Lemma assert_iden_option B (x : Ty.tySem (Ty.Sum Ty.Unit B)) :
  @assert_iden_spec B optalg x = match x with inl _ => None | inr b => Some b end.
Proof. destruct x as [[]|b]; reflexivity. Qed.

Definition vh_hash_spec (pv : BitcoinFull.t (Word 5) (Ty.Sum Ty.Unit (Word 6)))
    (ph : BitcoinFull.t (Word 5) (Ty.Sum Ty.Unit (Word 8))) {alg : PF.Algebra} :
    PF.domain alg (Word 5) (Ty.Sum Ty.Unit (Word 8)) :=
  let term := PF.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core (@PF.Combinators.prim _ _ alg pv) (@PF.Combinators.prim _ _ alg ph))
    (@AC.case _ _ _ _ core
      (@AC.injl _ _ _ core (@AC.unit _ core))
      (@AC.injr _ _ _ core
        (@AC.comp _ _ _ core
          (@AC.pair _ _ _ core
            (@AC.comp _ _ _ core
              (@AC.pair _ _ _ core
                (@AC.comp _ _ _ core (@AC.unit _ core) (@sha256_ctx8_init_spec core))
                (@AC.take _ _ _ core (@AC.iden _ core)))
              (@ctx8_addn_spec 3 term))
            (@AC.drop _ _ _ core (@assert_iden_spec (Word 8) term)))
          (@AC.comp _ _ _ core (@ctx8_addn_spec 5 term) (@ctx8_finalize_spec term))))).

Lemma vh_hash_spec_parametric pv ph : PF.Parametric (@vh_hash_spec pv ph).
Proof.
  intros alg1 alg2 R. destruct R as [R [HA [HP]]].
  set (RA := Alg.Assertion.Parametric.Pack HA).
  pose proof (ctx8_addn_spec_parametric 3 _ _ RA) as H3.
  pose proof (ctx8_addn_spec_parametric 5 _ _ RA) as H5.
  pose proof (ctx8_finalize_spec_parametric _ _ RA) as HF.
  pose proof (assert_iden_spec_parametric (Word 8) _ _ RA) as HAs.
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold vh_hash_spec. cbv zeta.
  apply (Alg.comp_Parametric RC); [apply (Alg.pair_Parametric RC); apply HP|].
  apply (Alg.case_Parametric RC); [apply (Alg.injl_Parametric RC), Alg.unit_Parametric|].
  apply (Alg.injr_Parametric RC).
  apply (Alg.comp_Parametric RC); [|apply (Alg.comp_Parametric RC); [exact H5|exact HF]].
  apply (Alg.pair_Parametric RC); [|apply (Alg.drop_Parametric RC); exact HAs].
  apply (Alg.comp_Parametric RC); [|exact H3].
  apply (Alg.pair_Parametric RC); [|apply (Alg.take_Parametric RC), Alg.iden_Parametric].
  apply (Alg.comp_Parametric RC); [apply Alg.unit_Parametric|apply (sha256_ctx8_init_spec_parametric _ _ RC)].
Qed.

Definition vh_bytes (v : Ty.tySem (Word 6)) (h : Ty.tySem (Word 8)) : list (Ty.tySem (Word 3)) :=
  vector_values (Word 3) 3 v ++ vector_values (Word 3) 5 h.

Lemma vh_hash_spec_none pv ph (i : Ty.tySem (Word 5)) e (oh : Ty.tySem (Ty.Sum Ty.Unit (Word 8))) :
  @BitcoinFull.sem (Word 5) (Ty.Sum Ty.Unit (Word 6)) pv i e = Some (inl tt) ->
  @BitcoinFull.sem (Word 5) (Ty.Sum Ty.Unit (Word 8)) ph i e = Some oh ->
  @vh_hash_spec pv ph fullalg i e = Some (inl tt).
Proof.
  intros Hv Hh. unfold vh_hash_spec. cbv zeta.
  rewrite fx_comp, fx_pair, !fx_prim, Hv, Hh. cbv beta iota.
  rewrite fx_case. cbn [fst snd]. rewrite fx_injl, fx_unit. reflexivity.
Qed.

Lemma vh_hash_spec_some pv ph (i : Ty.tySem (Word 5)) e v h :
  @BitcoinFull.sem (Word 5) (Ty.Sum Ty.Unit (Word 6)) pv i e = Some (inr v) ->
  @BitcoinFull.sem (Word 5) (Ty.Sum Ty.Unit (Word 8)) ph i e = Some (inr h) ->
  @vh_hash_spec pv ph fullalg i e = Some (inr (from_hash256 (sha256_bytes_of (vh_bytes v h)))).
Proof.
  intros Hv Hh. unfold vh_hash_spec. cbv zeta.
  rewrite fx_comp, fx_pair, !fx_prim, Hv, Hh. cbv beta iota.
  rewrite fx_case. cbn [fst snd]. rewrite fx_injr.
  rewrite fx_comp, fx_pair, fx_comp, fx_pair, fx_comp, fx_unit.
  rewrite (fx_core (fun alg => @sha256_ctx8_init_spec alg) sha256_ctx8_init_spec_parametric).
  rewrite fx_take, fx_iden. cbn [fst snd].
  rewrite (fx_assert (fun alg => @ctx8_addn_spec 3 alg) (ctx8_addn_spec_parametric 3)), (ctx8_addn_option 3).
  rewrite fx_drop. cbn [snd].
  rewrite (fx_assert (fun alg => @assert_iden_spec (Word 8) alg) (assert_iden_spec_parametric (Word 8))),
    assert_iden_option.
  destruct (init_hash_sem (vh_bytes v h)) as (cf & H1 & H2).
  { unfold vh_bytes. rewrite app_length, !vector_values_length. reflexivity. }
  unfold vh_bytes in H1.
  destruct (add_app_some _ _ _ _ H1) as (c1 & E1 & E2).
  use_add E1. cbv beta iota. rewrite fx_comp.
  rewrite (fx_assert (fun alg => @ctx8_addn_spec 5 alg) (ctx8_addn_spec_parametric 5)), (ctx8_addn_option 5).
  use_add E2.
  rewrite (fx_assert (fun alg => @ctx8_finalize_spec alg) ctx8_finalize_spec_parametric), H2.
  reflexivity.
Qed.

(** ** The registers of a short hash *)
Lemma absorb_small (bs : list (Ty.tySem (Word 3))) : forall l regs,
  (length l + length bs < 64)%nat -> absorb l regs bs = (l ++ bs, regs).
Proof.
  induction bs as [|x bs IH]; intros l regs HL.
  - unfold absorb. cbn. rewrite app_nil_r. reflexivity.
  - cbn [length] in HL. rewrite absorb_cons_small by lia.
    rewrite IH by (rewrite app_length; cbn [length]; lia).
    rewrite <- app_assoc. reflexivity.
Qed.

Lemma short_hash_regs (bs : list (Ty.tySem (Word 3))) : (length bs < 64)%nat ->
  hash256_reg (sha256_bytes_of bs) =
    snd (absorb_i (map word8_array_value bs) sha256_iv_words
      (sha_pad (Int64.repr (Z.of_nat (length bs))))).
Proof.
  intros HL. unfold sha256_bytes_of, sha_stream.
  rewrite (absorb_small bs [] sha256_iv_words) by (cbn [length]; lia).
  cbn [fst snd app length].
  assert (HD : (Z.of_nat 0 + Z.of_nat (length bs)) / 64 = 0) by (apply Z.div_small; lia).
  rewrite HD. change (64 * (0 + 0) + Z.of_nat (length bs)) with (Z.of_nat (length bs)).
  set (rs := snd (absorb_i (map word8_array_value bs) sha256_iv_words
    (sha_pad (Int64.repr (Z.of_nat (length bs)))))).
  assert (HR : length rs = 8%nat).
  { apply (absorb_i_len _ (map word8_array_value bs) sha256_iv_words);
      [rewrite map_length; exact HL|reflexivity]. }
  cbn [mk_hash256 hash256_reg].
  rewrite firstn_app, HR, Nat.sub_diag, firstn_O, app_nil_r. rewrite <- HR. apply firstn_all.
Qed.
