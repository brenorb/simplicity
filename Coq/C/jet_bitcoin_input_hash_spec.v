(** Literal port of the SigHash program inputHash
      inputHash = (primitive InputPrevOutpoint &&& (primitive InputSequence &&& primitive InputAnnexHash))
              >>> match (injl unit)
                    (injr ((((unit >>> ctx8Init) &&& oh >>> outpointHash)
                  &&& (drop . take . assert $ iden) >>> ctx8Add4)
                  &&& (drop . drop . assert $ iden) >>> annexHash >>> ctx8Finalize))
    and its value.  No C execution here. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Simplicity.Alg.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_assertion_spec C.jet_buffer_empty_spec C.jet_buffer_input C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha256_iv_init C.jet_read8s_layout C.jet_read32s_layout C.jet_word32_chunks.
Require Import C.jet_sha_ctx8_spec C.jet_sha_ctx8_model C.jet_sha_uchars_prep C.jet_sha_finalize_exec.
Require Import C.jet_sha_be32_write C.jet_sha_ctx8_bridge C.jet_sha_add_n_exec.
Require Import C.jet_sha_finalize_spec C.jet_sha_hash_closed C.jet_bitcoin_ctx_hash_spec.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim C.jet_sha_hash_loop C.jet_sha_hash_words.
Require Import C.jet_bitcoin_composite_hash C.jet_bitcoin_tx_hash C.jet_sha_ctx_abs C.jet_sha_ctxi.
Require Import C.jet_bitcoin_build_tapleaf_spec C.jet_bitcoin_vh_hash_spec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 120.

Definition input_hash_spec {alg : PF.Algebra} : PF.domain alg (Word 5) (Ty.Sum Ty.Unit (Word 8)) :=
  let term := PF.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@PF.Combinators.prim _ _ alg (BitcoinFull.Base Bitcoin.InputPrevOutpoint))
      (@AC.pair _ _ _ core
        (@PF.Combinators.prim _ _ alg (BitcoinFull.Base Bitcoin.InputSequence))
        (@PF.Combinators.prim _ _ alg (BitcoinFull.Ext BitcoinExt.InputAnnexHash))))
    (@AC.case _ _ _ _ core
      (@AC.injl _ _ _ core (@AC.unit _ core))
      (@AC.injr _ _ _ core
        (@AC.comp _ _ _ core
          (@AC.pair _ _ _ core
            (@AC.comp _ _ _ core
              (@AC.pair _ _ _ core
                (@AC.comp _ _ _ core
                  (@AC.pair _ _ _ core
                    (@AC.comp _ _ _ core (@AC.unit _ core) (@sha256_ctx8_init_spec core))
                    (@AC.take _ _ _ core (@AC.iden _ core)))
                  (@outpoint_hash_spec term))
                (@AC.drop _ _ _ core (@AC.take _ _ _ core (@assert_iden_spec (Word 5) term))))
              (@ctx8_addn_spec 2 term))
            (@AC.drop _ _ _ core (@AC.drop _ _ _ core
              (@assert_iden_spec (Ty.Sum Ty.Unit (Word 8)) term))))
          (@AC.comp _ _ _ core (@annex_hash_spec term) (@ctx8_finalize_spec term))))).

Lemma input_hash_spec_parametric : PF.Parametric (@input_hash_spec).
Proof.
  intros alg1 alg2 R. destruct R as [R [HA [HP]]].
  set (RA := Alg.Assertion.Parametric.Pack HA).
  pose proof (ctx8_addn_spec_parametric 2 _ _ RA) as H2.
  pose proof (ctx8_finalize_spec_parametric _ _ RA) as HF.
  pose proof (assert_iden_spec_parametric (Word 5) _ _ RA) as HA5.
  pose proof (assert_iden_spec_parametric (Ty.Sum Ty.Unit (Word 8)) _ _ RA) as HA8.
  pose proof (outpoint_hash_spec_parametric _ _ RA) as HO.
  pose proof (annex_hash_spec_parametric _ _ RA) as HX.
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold input_hash_spec. cbv zeta.
  apply (Alg.comp_Parametric RC).
  { apply (Alg.pair_Parametric RC); [apply HP|]. apply (Alg.pair_Parametric RC); apply HP. }
  apply (Alg.case_Parametric RC); [apply (Alg.injl_Parametric RC), Alg.unit_Parametric|].
  apply (Alg.injr_Parametric RC).
  apply (Alg.comp_Parametric RC); [|apply (Alg.comp_Parametric RC); [exact HX|exact HF]].
  apply (Alg.pair_Parametric RC);
    [|apply (Alg.drop_Parametric RC), (Alg.drop_Parametric RC); exact HA8].
  apply (Alg.comp_Parametric RC); [|exact H2].
  apply (Alg.pair_Parametric RC);
    [|apply (Alg.drop_Parametric RC), (Alg.take_Parametric RC); exact HA5].
  apply (Alg.comp_Parametric RC); [|exact HO].
  apply (Alg.pair_Parametric RC); [|apply (Alg.take_Parametric RC), Alg.iden_Parametric].
  apply (Alg.comp_Parametric RC); [apply Alg.unit_Parametric|apply (sha256_ctx8_init_spec_parametric _ _ RC)].
Qed.

Definition input_hash_bytes (op : Ty.tySem (Ty.Prod (Word 8) (Word 5))) (sq : Ty.tySem (Word 5))
    (ax : Ty.tySem (Ty.Sum Ty.Unit (Word 8))) : list (Ty.tySem (Word 3)) :=
  outpoint_bytes op ++ vector_values (Word 3) 2 sq ++ annex_elem_bytes ax.

Lemma input_hash_spec_none (i : Ty.tySem (Word 5)) e (os : Ty.tySem (Ty.Sum Ty.Unit (Word 5)))
    (oa : Ty.tySem (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (Word 8)))) :
  @BitcoinFull.sem (Word 5) (Ty.Sum Ty.Unit (Ty.Prod (Word 8) (Word 5)))
    (BitcoinFull.Base Bitcoin.InputPrevOutpoint) i e = Some (inl tt) ->
  @BitcoinFull.sem (Word 5) (Ty.Sum Ty.Unit (Word 5)) (BitcoinFull.Base Bitcoin.InputSequence) i e = Some os ->
  @BitcoinFull.sem (Word 5) (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (Word 8)))
    (BitcoinFull.Ext BitcoinExt.InputAnnexHash) i e = Some oa ->
  @input_hash_spec fullalg i e = Some (inl tt).
Proof.
  intros H1 H2 H3. unfold input_hash_spec. cbv zeta.
  rewrite fx_comp, fx_pair, fx_pair, !fx_prim, H1, H2, H3. cbv beta iota.
  rewrite fx_case. cbn [fst snd]. rewrite fx_injl, fx_unit. reflexivity.
Qed.

Lemma input_hash_spec_some (i : Ty.tySem (Word 5)) e op sq ax :
  @BitcoinFull.sem (Word 5) (Ty.Sum Ty.Unit (Ty.Prod (Word 8) (Word 5)))
    (BitcoinFull.Base Bitcoin.InputPrevOutpoint) i e = Some (inr op) ->
  @BitcoinFull.sem (Word 5) (Ty.Sum Ty.Unit (Word 5)) (BitcoinFull.Base Bitcoin.InputSequence) i e =
    Some (inr sq) ->
  @BitcoinFull.sem (Word 5) (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (Word 8)))
    (BitcoinFull.Ext BitcoinExt.InputAnnexHash) i e = Some (inr ax) ->
  @input_hash_spec fullalg i e =
    Some (inr (from_hash256 (sha256_bytes_of (input_hash_bytes op sq ax)))).
Proof.
  intros H1 H2 H3. unfold input_hash_spec. cbv zeta.
  rewrite fx_comp, fx_pair, fx_pair, !fx_prim, H1, H2, H3. cbv beta iota.
  rewrite fx_case. cbn [fst snd]. rewrite fx_injr.
  rewrite fx_comp, fx_pair, fx_comp, fx_pair, fx_comp, fx_pair, fx_comp, fx_unit.
  rewrite (fx_core (fun alg => @sha256_ctx8_init_spec alg) sha256_ctx8_init_spec_parametric).
  rewrite fx_take, fx_iden. cbn [fst snd].
  rewrite (fx_assert (fun alg => @outpoint_hash_spec alg) outpoint_hash_spec_parametric), outpoint_add_option.
  rewrite fx_drop, fx_take. cbn [fst snd].
  rewrite (fx_assert (fun alg => @assert_iden_spec (Word 5) alg) (assert_iden_spec_parametric (Word 5))),
    assert_iden_option.
  rewrite !fx_drop. cbn [snd].
  rewrite (fx_assert (fun alg => @assert_iden_spec (Ty.Sum Ty.Unit (Word 8)) alg)
    (assert_iden_spec_parametric (Ty.Sum Ty.Unit (Word 8)))), assert_iden_option.
  destruct (init_hash_sem (input_hash_bytes op sq ax)) as (cf & HI1 & HI2).
  { assert (HL : Z.of_nat (length (input_hash_bytes op sq ax)) <= 73).
    { unfold input_hash_bytes. rewrite !app_length, vector_values_length.
      pose proof (outpoint_bytes_bound op). pose proof (annex_bytes_bound ax).
      change (Nat.pow 2 2) with 4%nat. lia. }
    unfold ctx8_limit.
    assert (Z.of_nat (length (input_hash_bytes op sq ax)) / 64 < 2)
      by (apply Z.div_lt_upper_bound; lia). lia. }
  unfold input_hash_bytes in HI1.
  destruct (add_app_some _ _ _ _ HI1) as (c1 & E1 & E2).
  destruct (add_app_some _ _ _ _ E2) as (c2 & E3 & E4).
  use_add E1. cbv beta iota.
  rewrite (fx_assert (fun alg => @ctx8_addn_spec 2 alg) (ctx8_addn_spec_parametric 2)), (ctx8_addn_option 2).
  use_add E3. cbv beta iota. rewrite fx_comp.
  rewrite (fx_assert (fun alg => @annex_hash_spec alg) annex_hash_spec_parametric), annex_add_option.
  use_add E4.
  rewrite (fx_assert (fun alg => @ctx8_finalize_spec alg) ctx8_finalize_spec_parametric), HI2.
  reflexivity.
Qed.

(** ** The registers of a hash, as an absorbed byte stream *)
Lemma stream_hash_regs (bs : list (Ty.tySem (Word 3))) :
  hash256_reg (sha256_bytes_of bs) =
    snd (absorb_i (fst (absorb_i [] sha256_iv_words (map word8_array_value bs)))
      (snd (absorb_i [] sha256_iv_words (map word8_array_value bs)))
      (sha_pad (Int64.repr (Z.of_nat (length bs))))).
Proof.
  unfold sha256_bytes_of, sha_stream.
  change (@nil int) with (map word8_array_value []).
  rewrite absorb_i_fst, absorb_i_snd.
  destruct (absorb_length bs [] sha256_iv_words ltac:(cbn; lia)) as [HlenA HltA].
  match goal with |- context[sha_pad (Int64.repr ?z)] =>
    assert (HC : z = Z.of_nat (length bs)); [|rewrite HC] end.
  { cbn [length] in HlenA |- *. rewrite HlenA. change (Z.of_nat 0) with 0. rewrite !Z.add_0_l.
    pose proof (Z.div_mod (Z.of_nat (length bs)) 64 ltac:(lia)). lia. }
  set (rs := snd (absorb_i (map word8_array_value (fst (absorb [] sha256_iv_words bs)))
    (snd (absorb [] sha256_iv_words bs)) (sha_pad (Int64.repr (Z.of_nat (length bs)))))).
  assert (HR : length rs = 8%nat).
  { apply (absorb_i_len _ (map word8_array_value (fst (absorb [] sha256_iv_words bs)))
      (snd (absorb [] sha256_iv_words bs))).
    - rewrite map_length. exact HltA.
    - apply absorb_regs_length; [cbn; lia|reflexivity]. }
  cbn [mk_hash256 hash256_reg].
  rewrite firstn_app, HR, Nat.sub_diag, firstn_O, app_nil_r. rewrite <- HR. apply firstn_all.
Qed.

Lemma be32_bytes_word (w : int) :
  c_be32_bytes (Int64.repr (Int.unsigned w)) =
    map word8_array_value (vector_values (Word 3) 2 (@fromZ (WordToZ 5) (Int.unsigned w))).
Proof.
  etransitivity; [|exact (be_bytes_word (@fromZ (WordToZ 5) (Int.unsigned w)))].
  do 3 f_equal.
  unfold word32_array_value. rewrite to_fromZ.
  change (two_power_nat (ToZ.Theory.bitSize (WordToZ 5))) with Int.modulus.
  rewrite <- Int.unsigned_repr_eq, !Int.repr_unsigned. reflexivity.
Qed.

Lemma w8_zero : word8_array_value byte_zero = Int.repr 0.
Proof. vm_compute. reflexivity. Qed.
Lemma w8_one : word8_array_value byte_one = Int.repr 1.
Proof. vm_compute. reflexivity. Qed.
