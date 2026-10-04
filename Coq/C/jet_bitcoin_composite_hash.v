(** The SigHash programs that hash a fixed concatenation of other hashes:
      outputsHash    = ctx8Init &&& (outputValuesHash &&& outputScriptsHash) >>> ctx8Add64 >>> ctx8Finalize
      inputUtxosHash = ctx8Init &&& (inputValuesHash &&& inputScriptsHash) >>> ctx8Addn vector64 >>> ctx8Finalize
      tapEnvHash     = (ctx8Init &&& tapleafHash >>> ctx8Addn vector32)
                   &&& (tappathHash &&& primitive InternalKey) >>> ctx8Addn vector64 >>> ctx8Finalize
    with their values, and the C getters that return the cached hashes. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Maps Errors Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Simplicity.Alg.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jets_bitcoin C.jet_bitcoin_linkage.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_wrapper C.jet_bitcoin_hash_getters.
Require Import C.jet_bitcoin_script_cmr_local C.jet_bitcoin_hash_getter_local C.jet_bitcoin_hash_getter_writehash.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_forWhile_seq C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha256_iv_init C.jet_sha_ctx8_model.
Require Import C.jet_sha_ctx8_spec C.jet_sha_finalize_spec C.jet_sha_hash_closed.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim C.jet_sha_hash_loop C.jet_sha_hash_words.
Require Import C.jet_bitcoin_words_hash C.jet_bitcoin_tapleaf_hash_spec C.jet_bitcoin_tapleaf_hash_local.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 120.

Definition sha256_bytes_of (bs : list (Ty.tySem (Word 3))) : hash256 :=
  mk_hash256 (sha_stream [] sha256_iv_words 0 bs).

(** Hashing a byte list from the initial context. *)
Lemma init_hash_sem (bs : list (Ty.tySem (Word 3))) :
  Z.of_nat (length bs) / 64 < ctx8_limit ->
  exists cf, ctx8_add_list (@sha256_ctx8_init_spec Alg.CoreFunSem tt) bs = Some cf /\
    @ctx8_finalize_spec optalg cf = Some (from_hash256 (sha256_bytes_of bs)).
Proof.
  intros HB. rewrite sha256_ctx8_init_spec_value.
  assert (HT : @toZ (WordToZ 6) (@Word.zero 6 Alg.CoreFunSem tt) +
    (Z.of_nat (length (buffer_list (Word 3) 5 (buffer_empty_value (Word 3) 5))) +
     Z.of_nat (length bs)) / 64 < ctx8_limit).
  { rewrite buffer_list_empty. exact HB. }
  destruct (ctx8_hash_closed_gen bs (buffer_empty_value (Word 3) 5)
    (@Word.zero 6 Alg.CoreFunSem tt) (@sha256_iv_spec Alg.CoreFunSem tt) HT) as (cf & Hcf & HFin).
  rewrite buffer_list_empty, iv_spec_regs in HFin.
  exists cf. split; [exact Hcf|exact HFin].
Qed.

Lemma add_app_some c (bs1 bs2 : list (Ty.tySem (Word 3))) cf :
  ctx8_add_list c (bs1 ++ bs2) = Some cf ->
  exists c1, ctx8_add_list c bs1 = Some c1 /\ ctx8_add_list c1 bs2 = Some cf.
Proof.
  rewrite ctx8_add_list_app. intros H.
  destruct (ctx8_add_list c bs1) as [c1|]; [exists c1; split; [reflexivity|exact H]|discriminate].
Qed.

Ltac use_add H :=
  match goal with |- context[ctx8_add_list ?c ?l] =>
    match type of H with _ = ?r =>
      let HX := fresh in assert (HX : ctx8_add_list c l = r) by exact H; rewrite HX; clear HX
    end
  end.

(** ** A hash of two 32-byte values *)
Definition pair_hash_spec {alg : PF.Algebra} (s t : PF.domain alg Ty.Unit Word256) :
    PF.domain alg Ty.Unit Word256 :=
  let term := PF.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core (@sha256_ctx8_init_spec core) (@AC.pair _ _ _ core s t))
    (@AC.comp _ _ _ core (@ctx8_addn_spec 6 term) (@ctx8_finalize_spec term)).

Definition pair_hash_of (a b : hash256) : hash256 :=
  sha256_bytes_of (vector_values (Word 3) 6 (from_hash256 a, from_hash256 b)).

Lemma pair_hash_spec_sem (s t : PF.domain fullalg Ty.Unit Word256) (a b : hash256) e :
  s tt e = Some (from_hash256 a) -> t tt e = Some (from_hash256 b) ->
  @pair_hash_spec fullalg s t tt e = Some (from_hash256 (pair_hash_of a b)).
Proof.
  intros Hs Ht. unfold pair_hash_spec. cbv zeta.
  rewrite fx_comp, fx_pair, fx_pair, Hs, Ht.
  rewrite (fx_core (fun alg => @sha256_ctx8_init_spec alg) sha256_ctx8_init_spec_parametric).
  cbv beta iota. rewrite fx_comp.
  rewrite (fx_assert (fun alg => @ctx8_addn_spec 6 alg) (ctx8_addn_spec_parametric 6)), (ctx8_addn_option 6).
  destruct (init_hash_sem (vector_values (Word 3) 6 (from_hash256 a, from_hash256 b)))
    as (cf & H1 & H2).
  { rewrite vector_values_length. reflexivity. }
  use_add H1.
  rewrite (fx_assert (fun alg => @ctx8_finalize_spec alg) ctx8_finalize_spec_parametric).
  exact H2.
Qed.

Lemma pair_hash_spec_parametric (s t : forall alg : PF.Algebra, PF.domain alg Ty.Unit Word256) :
  PF.Parametric s -> PF.Parametric t -> PF.Parametric (fun alg => @pair_hash_spec alg (s alg) (t alg)).
Proof.
  intros Hs Ht alg1 alg2 R. specialize (Hs alg1 alg2 R). specialize (Ht alg1 alg2 R).
  destruct R as [R [HA [HP]]].
  set (RA := Alg.Assertion.Parametric.Pack HA).
  pose proof (ctx8_addn_spec_parametric 6 _ _ RA) as H6.
  pose proof (ctx8_finalize_spec_parametric _ _ RA) as HF.
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold pair_hash_spec. cbv zeta.
  apply (Alg.comp_Parametric RC); [|apply (Alg.comp_Parametric RC); [exact H6|exact HF]].
  apply (Alg.pair_Parametric RC); [apply (sha256_ctx8_init_spec_parametric _ _ RC)|].
  apply (Alg.pair_Parametric RC); [exact Hs|exact Ht].
Qed.

(** ** outputsHash *)
Definition outputs_hash_spec {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  @pair_hash_spec alg
    (@prim_words_hash_spec 3 5 (BitcoinFull.Base Bitcoin.OutputValue) alg)
    (@prim_words_hash_spec 5 5 (BitcoinFull.Base Bitcoin.OutputScriptHash) alg).

Lemma outputs_hash_spec_parametric : PF.Parametric (@outputs_hash_spec).
Proof. apply pair_hash_spec_parametric; apply prim_words_hash_spec_parametric. Qed.

Definition outputs_hash_of (e : ext_environment) : hash256 :=
  pair_hash_of (words_hash_of 3 5 (output_values_of e)) (words_hash_of 5 5 (output_scripts_of e)).

Lemma outputs_hash_spec_sem e :
  @outputs_hash_spec fullalg tt e = Some (from_hash256 (outputs_hash_of e)).
Proof.
  unfold outputs_hash_spec, outputs_hash_of.
  apply (pair_hash_spec_sem _ _ (words_hash_of 3 5 (output_values_of e))
    (words_hash_of 5 5 (output_scripts_of e)) e).
  - apply (prim_words_hash_spec_sem 3 5 _ output_values_of output_values_sem words_bound_8).
  - apply (prim_words_hash_spec_sem 5 5 _ output_scripts_of output_scripts_sem words_bound_32).
Qed.

Theorem bitcoin_outputs_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_outputs_hash bitcoin_ge ext_environment
    Ty.Unit Word256 (hash_getter_rep outputs_hash_of 0 80 432)
    (fun a environment => @outputs_hash_spec fullalg a environment).
Proof.
  eapply bitcoin_hash_getter_writeHash_local with (ptrfield := _tx) (sid := _bitcoinTransaction)
    (hashfield := _outputsHash).
  - exact outputs_hash_spec_sem.
  - getter_shape.
  - exact bitcoin_txEnv_tx.
  - vm_compute; reflexivity.
  - lia.
  - lia.
Qed.

(** ** inputUtxosHash *)
Definition input_utxos_hash_spec {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  @pair_hash_spec alg
    (@prim_words_hash_spec 3 5 (BitcoinFull.Base Bitcoin.InputValue) alg)
    (@prim_words_hash_spec 5 5 (BitcoinFull.Ext BitcoinExt.InputScriptHash) alg).

Lemma input_utxos_hash_spec_parametric : PF.Parametric (@input_utxos_hash_spec).
Proof. apply pair_hash_spec_parametric; apply prim_words_hash_spec_parametric. Qed.

Definition input_utxos_hash_of (e : ext_environment) : hash256 :=
  pair_hash_of (words_hash_of 3 5 (input_values_of e)) (words_hash_of 5 5 (input_scripts_of e)).

Lemma input_utxos_hash_spec_sem e :
  @input_utxos_hash_spec fullalg tt e = Some (from_hash256 (input_utxos_hash_of e)).
Proof.
  unfold input_utxos_hash_spec, input_utxos_hash_of.
  apply (pair_hash_spec_sem _ _ (words_hash_of 3 5 (input_values_of e))
    (words_hash_of 5 5 (input_scripts_of e)) e).
  - apply (prim_words_hash_spec_sem 3 5 _ input_values_of input_values_sem words_bound_8).
  - apply (prim_words_hash_spec_sem 5 5 _ input_scripts_of input_scripts_sem words_bound_32).
Qed.

Theorem bitcoin_input_utxos_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_utxos_hash bitcoin_ge ext_environment
    Ty.Unit Word256 (hash_getter_rep input_utxos_hash_of 0 208 432)
    (fun a environment => @input_utxos_hash_spec fullalg a environment).
Proof.
  eapply bitcoin_hash_getter_writeHash_local with (ptrfield := _tx) (sid := _bitcoinTransaction)
    (hashfield := _inputUTXOsHash).
  - exact input_utxos_hash_spec_sem.
  - getter_shape.
  - exact bitcoin_txEnv_tx.
  - vm_compute; reflexivity.
  - lia.
  - lia.
Qed.

(** ** tapEnvHash *)
Definition tap_env_hash_spec {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  let term := PF.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core (@sha256_ctx8_init_spec core) (@tapleaf_hash_spec alg))
        (@ctx8_addn_spec 5 term))
      (@AC.pair _ _ _ core
        (@prim_words_hash_spec 5 3 (BitcoinFull.Ext BitcoinExt.Tappath) alg)
        (@PF.Combinators.prim _ _ alg (BitcoinFull.Ext BitcoinExt.InternalKey))))
    (@AC.comp _ _ _ core (@ctx8_addn_spec 6 term) (@ctx8_finalize_spec term)).

Lemma tap_env_hash_spec_parametric : PF.Parametric (@tap_env_hash_spec).
Proof.
  intros alg1 alg2 R.
  pose proof (tapleaf_hash_spec_parametric alg1 alg2 R) as HL.
  pose proof (prim_words_hash_spec_parametric 5 3 (BitcoinFull.Ext BitcoinExt.Tappath) alg1 alg2 R) as HT.
  destruct R as [R [HA [HP]]].
  set (RA := Alg.Assertion.Parametric.Pack HA).
  pose proof (ctx8_addn_spec_parametric 5 _ _ RA) as H5.
  pose proof (ctx8_addn_spec_parametric 6 _ _ RA) as H6.
  pose proof (ctx8_finalize_spec_parametric _ _ RA) as HF.
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold tap_env_hash_spec. cbv zeta.
  apply (Alg.comp_Parametric RC); [|apply (Alg.comp_Parametric RC); [exact H6|exact HF]].
  apply (Alg.pair_Parametric RC).
  - apply (Alg.comp_Parametric RC); [|exact H5].
    apply (Alg.pair_Parametric RC); [apply (sha256_ctx8_init_spec_parametric _ _ RC)|exact HL].
  - apply (Alg.pair_Parametric RC); [exact HT|apply HP].
Qed.

Definition tap_env_hash_of (e : ext_environment) : hash256 :=
  sha256_bytes_of
    (vector_values (Word 3) 5 (from_hash256 (tapleaf_hash_of e)) ++
     vector_values (Word 3) 6
       (from_hash256 (words_hash_of 5 3 (tappath_of e)), from_hash256 (extInternalKey e))).

Lemma tap_env_hash_spec_sem e :
  @tap_env_hash_spec fullalg tt e = Some (from_hash256 (tap_env_hash_of e)).
Proof.
  unfold tap_env_hash_spec. cbv zeta.
  rewrite fx_comp, fx_pair, fx_comp, fx_pair.
  rewrite (fx_core (fun alg => @sha256_ctx8_init_spec alg) sha256_ctx8_init_spec_parametric).
  rewrite tapleaf_hash_spec_sem, fx_pair.
  rewrite (prim_words_hash_spec_sem 5 3 _ tappath_of tappath_sem words_bound_path), fx_prim.
  change (BitcoinFull.sem (BitcoinFull.Ext BitcoinExt.InternalKey) tt e) with
    (Some (from_hash256 (extInternalKey e))).
  cbv beta iota.
  rewrite (fx_assert (fun alg => @ctx8_addn_spec 5 alg) (ctx8_addn_spec_parametric 5)), (ctx8_addn_option 5).
  destruct (init_hash_sem
    (vector_values (Word 3) 5 (from_hash256 (tapleaf_hash_of e)) ++
     vector_values (Word 3) 6
       (from_hash256 (words_hash_of 5 3 (tappath_of e)), from_hash256 (extInternalKey e))))
    as (cf & H1 & H2).
  { rewrite app_length, !vector_values_length. reflexivity. }
  destruct (add_app_some _ _ _ _ H1) as (c1 & E1 & E2).
  use_add E1. cbv beta iota. rewrite fx_comp.
  rewrite (fx_assert (fun alg => @ctx8_addn_spec 6 alg) (ctx8_addn_spec_parametric 6)), (ctx8_addn_option 6).
  use_add E2.
  rewrite (fx_assert (fun alg => @ctx8_finalize_spec alg) ctx8_finalize_spec_parametric).
  exact H2.
Qed.

Theorem bitcoin_tap_env_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_tap_env_hash bitcoin_ge ext_environment
    Ty.Unit Word256 (hash_getter_rep tap_env_hash_of 8 72 176)
    (fun a environment => @tap_env_hash_spec fullalg a environment).
Proof.
  eapply bitcoin_hash_getter_writeHash_local with (ptrfield := _taproot) (sid := _bitcoinTapEnv)
    (hashfield := _tapEnvHash).
  - exact tap_env_hash_spec_sem.
  - getter_shape.
  - exact bitcoin_txEnv_taproot.
  - vm_compute; reflexivity.
  - lia.
  - lia.
Qed.
