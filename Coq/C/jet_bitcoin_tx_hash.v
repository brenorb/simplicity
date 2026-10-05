(** The remaining transaction-level SigHash programs:
      inputOutpointsHash, inputAnnexesHash  (loops over outpointHash / annexHash)
      inputsHash = (ctx8Init &&& (inputOutpointsHash &&& inputSequencesHash) >>> ctx8Addn vector64)
               &&& inputAnnexesHash >>> ctx8Addn vector32 >>> ctx8Finalize
      txHash = ((ctx8Init &&& (primitive Version &&& primitive LockTime) >>> ctx8Addn vector8)
           &&& (inputsHash &&& outputsHash) >>> ctx8Addn vector64)
           &&& inputUtxosHash >>> ctx8Addn vector32 >>> ctx8Finalize
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
Require Import C.jet_sha_ctx8_spec C.jet_sha_finalize_spec C.jet_sha_hash_closed C.jet_bitcoin_ctx_hash_spec.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim C.jet_sha_hash_loop C.jet_sha_hash_words.
Require Import C.jet_sha_hash_loop_gen.
Require Import C.jet_bitcoin_words_hash C.jet_bitcoin_composite_hash.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 120.

(** ** Hashing every element of a primitive array with an absorbing program *)
Section Elems.
Variable X : Ty.
Variable add : forall term : Alg.Assertion.Algebra,
  @Alg.Assertion.domain term (Ty.Prod sha256_ctx8_type X) sha256_ctx8_type.
Hypothesis add_parametric : Alg.Assertion.Parametric add.
Variable bytes_of : Ty.tySem X -> list (Ty.tySem (Word 3)).
Hypothesis add_option : forall c x, add optalg (c, x) = ctx8_add_list c (bytes_of x).
Variable w : nat.
Variable p : BitcoinFull.t (Word w) (Ty.Sum Ty.Unit X).

Definition elems_hash_spec {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  let term := PF.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core (@AC.unit _ core) (@sha256_ctx8_init_spec core))
    (@AC.comp _ _ _ core
      (@gen_loop_run X add w term Ty.Unit
        (@AC.drop Ty.Unit (Word w) _ core (@PF.Combinators.prim _ _ alg p)))
      (@AC.copair _ _ _ core (@ctx8_finalize_spec term) (@ctx8_finalize_spec term))).

Lemma elems_hash_spec_parametric : PF.Parametric (@elems_hash_spec).
Proof.
  intros alg1 alg2 R. destruct R as [R [HA [HP]]].
  set (RA := Alg.Assertion.Parametric.Pack HA).
  pose proof (ctx8_finalize_spec_parametric _ _ RA) as HF.
  pose proof (fun a1 a2 H => gen_loop_run_parametric X add add_parametric w (C := Ty.Unit) RA a1 a2 H) as HL.
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold elems_hash_spec. cbv zeta.
  apply (Alg.comp_Parametric RC).
  - apply (Alg.pair_Parametric RC); [apply Alg.unit_Parametric|apply (sha256_ctx8_init_spec_parametric _ _ RC)].
  - apply (Alg.comp_Parametric RC); [|apply (Alg.copair_Parametric RC); exact HF].
    apply HL. apply (Alg.drop_Parametric RC). apply HP.
Qed.

Variable N : Z.
Hypothesis bytes_bound : forall x, Z.of_nat (length (bytes_of x)) <= N.
Hypothesis HN : 0 <= N.
Hypothesis N_bound : N * wsize w / 64 < ctx8_limit.

Lemma gen_bytes_length_le (l : list (Ty.tySem X)) :
  Z.of_nat (length (gen_bytes X bytes_of l)) <= N * Z.of_nat (length l).
Proof.
  induction l as [|x l IH]; [cbn; lia|].
  change (gen_bytes X bytes_of (x :: l)) with (bytes_of x ++ gen_bytes X bytes_of l).
  rewrite app_length. cbn [length]. pose proof (bytes_bound x). lia.
Qed.

Definition elems_hash_of (xs : list (Ty.tySem X)) : hash256 :=
  sha256_bytes_of (gen_bytes X bytes_of (firstn (Z.to_nat (wsize w)) xs)).

Theorem elems_hash_spec_sem (xs_of : ext_environment -> list (Ty.tySem X)) :
  (forall i e, @BitcoinFull.sem (Word w) (Ty.Sum Ty.Unit X) p i e =
    Some (match nth_error (xs_of e) (Z.to_nat (wz w i)) with Some x => inr x | None => inl tt end)) ->
  forall e, @elems_hash_spec fullalg tt e = Some (from_hash256 (elems_hash_of (xs_of e))).
Proof.
  intros Hsem e. pose proof (wsize_pos w) as HW.
  set (items := firstn (Z.to_nat (wsize w)) (xs_of e)).
  destruct (init_hash_sem (gen_bytes X bytes_of items)) as (cf & H1 & H2).
  { eapply Z.le_lt_trans; [|exact N_bound]. apply Z.div_le_mono; [lia|].
    eapply Z.le_trans; [apply gen_bytes_length_le|].
    assert (HL : (length items <= Z.to_nat (wsize w))%nat) by (unfold items; apply firstn_le_length).
    apply Z.mul_le_mono_nonneg_l; lia. }
  destruct (gen_loop_run_sem X add add_parametric bytes_of add_option w Ty.Unit
    (@AC.drop Ty.Unit (Word w) _ fullcore (@PF.Combinators.prim _ _ fullalg p)) tt
    (@sha256_ctx8_init_spec Alg.CoreFunSem tt) e (xs_of e)
    ltac:(intros i; rewrite fx_drop; cbn [snd]; rewrite fx_prim; apply Hsem) cf H1) as (r & Hr1 & Hr2).
  unfold elems_hash_spec. cbv zeta.
  rewrite fx_comp, fx_pair, fx_unit.
  rewrite (fx_core (fun alg => @sha256_ctx8_init_spec alg) sha256_ctx8_init_spec_parametric).
  rewrite fx_comp.
  match goal with |- match ?Y with _ => _ end = _ =>
    assert (HX : Y = Some r) by exact Hr1; rewrite HX end.
  rewrite fx_copair.
  transitivity (@ctx8_finalize_spec fullassert cf e).
  { destruct r; cbn in Hr2; subst; reflexivity. }
  rewrite (fx_assert (fun alg => @ctx8_finalize_spec alg) ctx8_finalize_spec_parametric).
  exact H2.
Qed.

End Elems.

(** ** inputOutpointsHash *)
Definition outpoint_bytes (x : Ty.tySem (Ty.Prod (Word 8) (Word 5))) : list (Ty.tySem (Word 3)) :=
  vector_values (Word 3) 5 (fst x) ++ vector_values (Word 3) 2 (snd x).

Lemma outpoint_add_option c x : @outpoint_hash_spec optalg (c, x) = ctx8_add_list c (outpoint_bytes x).
Proof. destruct x as [h i]. apply outpoint_hash_option. Qed.

Lemma outpoint_bytes_bound x : Z.of_nat (length (outpoint_bytes x)) <= 36.
Proof. unfold outpoint_bytes. rewrite app_length, !vector_values_length. cbn. lia. Qed.

Lemma elems_bound_36 : 36 * wsize 5 / 64 < ctx8_limit.
Proof. vm_compute. reflexivity. Qed.

Definition input_outpoints_hash_spec {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  @elems_hash_spec (Ty.Prod (Word 8) (Word 5)) (fun term => @outpoint_hash_spec term) 5
    (BitcoinFull.Base Bitcoin.InputPrevOutpoint) alg.

Lemma input_outpoints_hash_spec_parametric : PF.Parametric (@input_outpoints_hash_spec).
Proof. apply elems_hash_spec_parametric. exact outpoint_hash_spec_parametric. Qed.

Definition outpoints_of (e : ext_environment) : list (Ty.tySem (Ty.Prod (Word 8) (Word 5))) :=
  map (fun x => (from_hash256 (opHash (sigTxiPreviousOutpoint x)),
                 @fromZ (WordToZ 5) (Int.unsigned (opIndex (sigTxiPreviousOutpoint x)))))
    (sigTxIn (Bitcoin.envTx (extBase e))).

Lemma outpoints_sem i e :
  @BitcoinFull.sem (Word 5) (Ty.Sum Ty.Unit (Ty.Prod (Word 8) (Word 5)))
    (BitcoinFull.Base Bitcoin.InputPrevOutpoint) i e =
    Some (match nth_error (outpoints_of e) (Z.to_nat (wz 5 i)) with
          | Some x => inr x | None => inl tt end).
Proof.
  unfold outpoints_of. rewrite nth_error_map. unfold wz.
  cbn [BitcoinFull.sem]. unfold Bitcoin.sem.
  destruct (nth_error (sigTxIn (Bitcoin.envTx (extBase e))) (Z.to_nat (@toZ (WordToZ 5) i))); reflexivity.
Qed.

Definition input_outpoints_hash_of (e : ext_environment) : hash256 :=
  elems_hash_of (Ty.Prod (Word 8) (Word 5)) outpoint_bytes 5 (outpoints_of e).

Lemma input_outpoints_hash_spec_sem e :
  @input_outpoints_hash_spec fullalg tt e = Some (from_hash256 (input_outpoints_hash_of e)).
Proof.
  apply (elems_hash_spec_sem (Ty.Prod (Word 8) (Word 5)) (fun term => @outpoint_hash_spec term)
    outpoint_hash_spec_parametric outpoint_bytes outpoint_add_option 5
    (BitcoinFull.Base Bitcoin.InputPrevOutpoint) 36 outpoint_bytes_bound ltac:(lia) elems_bound_36
    outpoints_of outpoints_sem e).
Qed.

Theorem bitcoin_input_outpoints_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_outpoints_hash bitcoin_ge ext_environment
    Ty.Unit Word256 (hash_getter_rep input_outpoints_hash_of 0 112 432)
    (fun a environment => @input_outpoints_hash_spec fullalg a environment).
Proof.
  eapply bitcoin_hash_getter_writeHash_local with (ptrfield := _tx) (sid := _bitcoinTransaction)
    (hashfield := _inputOutpointsHash).
  - exact input_outpoints_hash_spec_sem.
  - getter_shape.
  - exact bitcoin_txEnv_tx.
  - vm_compute; reflexivity.
  - lia.
  - lia.
Qed.

(** ** inputAnnexesHash *)
Definition annex_elem_bytes (a : Ty.tySem (Ty.Sum Ty.Unit (Word 8))) : list (Ty.tySem (Word 3)) :=
  match a with
  | inl _ => [byte_zero]
  | inr h => byte_one :: vector_values (Word 3) 5 h
  end.

Lemma annex_add_option c x : @annex_hash_spec optalg (c, x) = ctx8_add_list c (annex_elem_bytes x).
Proof. apply annex_hash_option. Qed.

Lemma annex_bytes_bound x : Z.of_nat (length (annex_elem_bytes x)) <= 33.
Proof.
  destruct x as [u|h]; [cbn; lia|]. unfold annex_elem_bytes. cbn [length].
  rewrite vector_values_length. cbn. lia.
Qed.

Lemma elems_bound_33 : 33 * wsize 5 / 64 < ctx8_limit.
Proof. vm_compute. reflexivity. Qed.

Definition input_annexes_hash_spec {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  @elems_hash_spec (Ty.Sum Ty.Unit (Word 8)) (fun term => @annex_hash_spec term) 5
    (BitcoinFull.Ext BitcoinExt.InputAnnexHash) alg.

Lemma input_annexes_hash_spec_parametric : PF.Parametric (@input_annexes_hash_spec).
Proof. apply elems_hash_spec_parametric. exact annex_hash_spec_parametric. Qed.

Definition annexes_of (e : ext_environment) : list (Ty.tySem (Ty.Sum Ty.Unit (Word 8))) :=
  map (fun o : option hash256 => match o with
                | None => inl tt
                | Some h => inr (from_hash256 h)
                end) (extInAnnexHash e).

Lemma annexes_sem i e :
  @BitcoinFull.sem (Word 5) (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (Word 8)))
    (BitcoinFull.Ext BitcoinExt.InputAnnexHash) i e =
    Some (match nth_error (annexes_of e) (Z.to_nat (wz 5 i)) with
          | Some x => inr x | None => inl tt end).
Proof.
  unfold annexes_of. rewrite nth_error_map. unfold wz.
  cbn [BitcoinFull.sem]. unfold BitcoinExt.sem.
  destruct (nth_error (extInAnnexHash e) (Z.to_nat (@toZ (WordToZ 5) i))) as [[h|]|]; reflexivity.
Qed.

Definition input_annexes_hash_of (e : ext_environment) : hash256 :=
  elems_hash_of (Ty.Sum Ty.Unit (Word 8)) annex_elem_bytes 5 (annexes_of e).

Lemma input_annexes_hash_spec_sem e :
  @input_annexes_hash_spec fullalg tt e = Some (from_hash256 (input_annexes_hash_of e)).
Proof.
  apply (elems_hash_spec_sem (Ty.Sum Ty.Unit (Word 8)) (fun term => @annex_hash_spec term)
    annex_hash_spec_parametric annex_elem_bytes annex_add_option 5
    (BitcoinFull.Ext BitcoinExt.InputAnnexHash) 33 annex_bytes_bound ltac:(lia) elems_bound_33
    annexes_of annexes_sem e).
Qed.

Theorem bitcoin_input_annexes_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_annexes_hash bitcoin_ge ext_environment
    Ty.Unit Word256 (hash_getter_rep input_annexes_hash_of 0 272 432)
    (fun a environment => @input_annexes_hash_spec fullalg a environment).
Proof.
  eapply bitcoin_hash_getter_writeHash_local with (ptrfield := _tx) (sid := _bitcoinTransaction)
    (hashfield := _inputAnnexesHash).
  - exact input_annexes_hash_spec_sem.
  - getter_shape.
  - exact bitcoin_txEnv_tx.
  - vm_compute; reflexivity.
  - lia.
  - lia.
Qed.

(** ** inputsHash *)
Definition inputs_hash_spec {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  let term := PF.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core (@sha256_ctx8_init_spec core)
          (@AC.pair _ _ _ core (@input_outpoints_hash_spec alg)
            (@prim_words_hash_spec 2 5 (BitcoinFull.Base Bitcoin.InputSequence) alg)))
        (@ctx8_addn_spec 6 term))
      (@input_annexes_hash_spec alg))
    (@AC.comp _ _ _ core (@ctx8_addn_spec 5 term) (@ctx8_finalize_spec term)).

Lemma inputs_hash_spec_parametric : PF.Parametric (@inputs_hash_spec).
Proof.
  intros alg1 alg2 R.
  pose proof (input_outpoints_hash_spec_parametric alg1 alg2 R) as HO.
  pose proof (input_annexes_hash_spec_parametric alg1 alg2 R) as HN.
  pose proof (prim_words_hash_spec_parametric 2 5 (BitcoinFull.Base Bitcoin.InputSequence) alg1 alg2 R) as HS.
  destruct R as [R [HA [HP]]].
  set (RA := Alg.Assertion.Parametric.Pack HA).
  pose proof (ctx8_addn_spec_parametric 5 _ _ RA) as H5.
  pose proof (ctx8_addn_spec_parametric 6 _ _ RA) as H6.
  pose proof (ctx8_finalize_spec_parametric _ _ RA) as HF.
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold inputs_hash_spec. cbv zeta.
  apply (Alg.comp_Parametric RC); [|apply (Alg.comp_Parametric RC); [exact H5|exact HF]].
  apply (Alg.pair_Parametric RC); [|exact HN].
  apply (Alg.comp_Parametric RC); [|exact H6].
  apply (Alg.pair_Parametric RC); [apply (sha256_ctx8_init_spec_parametric _ _ RC)|].
  apply (Alg.pair_Parametric RC); [exact HO|exact HS].
Qed.

Definition inputs_hash_of (e : ext_environment) : hash256 :=
  sha256_bytes_of
    (vector_values (Word 3) 6
       (from_hash256 (input_outpoints_hash_of e),
        from_hash256 (words_hash_of 2 5 (input_sequences_of e))) ++
     vector_values (Word 3) 5 (from_hash256 (input_annexes_hash_of e))).

Lemma inputs_hash_spec_sem e :
  @inputs_hash_spec fullalg tt e = Some (from_hash256 (inputs_hash_of e)).
Proof.
  unfold inputs_hash_spec. cbv zeta.
  rewrite fx_comp, fx_pair, fx_comp, fx_pair, fx_pair.
  rewrite (fx_core (fun alg => @sha256_ctx8_init_spec alg) sha256_ctx8_init_spec_parametric).
  rewrite input_outpoints_hash_spec_sem, input_annexes_hash_spec_sem.
  rewrite (prim_words_hash_spec_sem 2 5 _ input_sequences_of input_sequences_sem words_bound_4).
  cbv beta iota.
  rewrite (fx_assert (fun alg => @ctx8_addn_spec 6 alg) (ctx8_addn_spec_parametric 6)), (ctx8_addn_option 6).
  destruct (init_hash_sem
    (vector_values (Word 3) 6
       (from_hash256 (input_outpoints_hash_of e),
        from_hash256 (words_hash_of 2 5 (input_sequences_of e))) ++
     vector_values (Word 3) 5 (from_hash256 (input_annexes_hash_of e))))
    as (cf & H1 & H2).
  { rewrite app_length, !vector_values_length. reflexivity. }
  destruct (add_app_some _ _ _ _ H1) as (c1 & E1 & E2).
  use_add E1. cbv beta iota. rewrite fx_comp.
  rewrite (fx_assert (fun alg => @ctx8_addn_spec 5 alg) (ctx8_addn_spec_parametric 5)), (ctx8_addn_option 5).
  use_add E2.
  rewrite (fx_assert (fun alg => @ctx8_finalize_spec alg) ctx8_finalize_spec_parametric).
  exact H2.
Qed.

Theorem bitcoin_inputs_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_inputs_hash bitcoin_ge ext_environment
    Ty.Unit Word256 (hash_getter_rep inputs_hash_of 0 336 432)
    (fun a environment => @inputs_hash_spec fullalg a environment).
Proof.
  eapply bitcoin_hash_getter_writeHash_local with (ptrfield := _tx) (sid := _bitcoinTransaction)
    (hashfield := _inputsHash).
  - exact inputs_hash_spec_sem.
  - getter_shape.
  - exact bitcoin_txEnv_tx.
  - vm_compute; reflexivity.
  - lia.
  - lia.
Qed.

(** ** txHash *)
Definition tx_hash_spec {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  let term := PF.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core
          (@AC.comp _ _ _ core
            (@AC.pair _ _ _ core (@sha256_ctx8_init_spec core)
              (@AC.pair _ _ _ core
                (@PF.Combinators.prim _ _ alg (BitcoinFull.Base Bitcoin.Version))
                (@PF.Combinators.prim _ _ alg (BitcoinFull.Base Bitcoin.LockTime))))
            (@ctx8_addn_spec 3 term))
          (@AC.pair _ _ _ core (@inputs_hash_spec alg) (@outputs_hash_spec alg)))
        (@ctx8_addn_spec 6 term))
      (@input_utxos_hash_spec alg))
    (@AC.comp _ _ _ core (@ctx8_addn_spec 5 term) (@ctx8_finalize_spec term)).

Lemma tx_hash_spec_parametric : PF.Parametric (@tx_hash_spec).
Proof.
  intros alg1 alg2 R.
  pose proof (inputs_hash_spec_parametric alg1 alg2 R) as HI.
  pose proof (outputs_hash_spec_parametric alg1 alg2 R) as HO.
  pose proof (input_utxos_hash_spec_parametric alg1 alg2 R) as HU.
  destruct R as [R [HA [HP]]].
  set (RA := Alg.Assertion.Parametric.Pack HA).
  pose proof (ctx8_addn_spec_parametric 3 _ _ RA) as H3.
  pose proof (ctx8_addn_spec_parametric 5 _ _ RA) as H5.
  pose proof (ctx8_addn_spec_parametric 6 _ _ RA) as H6.
  pose proof (ctx8_finalize_spec_parametric _ _ RA) as HF.
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold tx_hash_spec. cbv zeta.
  apply (Alg.comp_Parametric RC); [|apply (Alg.comp_Parametric RC); [exact H5|exact HF]].
  apply (Alg.pair_Parametric RC); [|exact HU].
  apply (Alg.comp_Parametric RC); [|exact H6].
  apply (Alg.pair_Parametric RC); [|apply (Alg.pair_Parametric RC); [exact HI|exact HO]].
  apply (Alg.comp_Parametric RC); [|exact H3].
  apply (Alg.pair_Parametric RC); [apply (sha256_ctx8_init_spec_parametric _ _ RC)|].
  apply (Alg.pair_Parametric RC); apply HP.
Qed.

Definition tx_version_word (e : ext_environment) : Ty.tySem (Word 5) :=
  @fromZ (WordToZ 5) (Int.signed (sigTxVersion (Bitcoin.envTx (extBase e)))).
Definition tx_locktime_word (e : ext_environment) : Ty.tySem (Word 5) :=
  @fromZ (WordToZ 5) (Int.unsigned (sigTxLock (Bitcoin.envTx (extBase e)))).

Definition tx_hash_of (e : ext_environment) : hash256 :=
  sha256_bytes_of
    (vector_values (Word 3) 3 (tx_version_word e, tx_locktime_word e) ++
     vector_values (Word 3) 6 (from_hash256 (inputs_hash_of e), from_hash256 (outputs_hash_of e)) ++
     vector_values (Word 3) 5 (from_hash256 (input_utxos_hash_of e))).

Lemma tx_hash_spec_sem e :
  @tx_hash_spec fullalg tt e = Some (from_hash256 (tx_hash_of e)).
Proof.
  unfold tx_hash_spec. cbv zeta.
  rewrite fx_comp, fx_pair, fx_comp, fx_pair, fx_comp, fx_pair, fx_pair, fx_pair.
  rewrite (fx_core (fun alg => @sha256_ctx8_init_spec alg) sha256_ctx8_init_spec_parametric).
  rewrite !fx_prim.
  change (BitcoinFull.sem (BitcoinFull.Base Bitcoin.Version) tt e) with (Some (tx_version_word e)).
  change (BitcoinFull.sem (BitcoinFull.Base Bitcoin.LockTime) tt e) with (Some (tx_locktime_word e)).
  rewrite inputs_hash_spec_sem, outputs_hash_spec_sem, input_utxos_hash_spec_sem.
  cbv beta iota.
  rewrite (fx_assert (fun alg => @ctx8_addn_spec 3 alg) (ctx8_addn_spec_parametric 3)), (ctx8_addn_option 3).
  destruct (init_hash_sem
    (vector_values (Word 3) 3 (tx_version_word e, tx_locktime_word e) ++
     vector_values (Word 3) 6 (from_hash256 (inputs_hash_of e), from_hash256 (outputs_hash_of e)) ++
     vector_values (Word 3) 5 (from_hash256 (input_utxos_hash_of e))))
    as (cf & H1 & H2).
  { rewrite !app_length, !vector_values_length. reflexivity. }
  destruct (add_app_some _ _ _ _ H1) as (c1 & E1 & E2).
  destruct (add_app_some _ _ _ _ E2) as (c2 & E3 & E4).
  use_add E1. cbv beta iota.
  rewrite (fx_assert (fun alg => @ctx8_addn_spec 6 alg) (ctx8_addn_spec_parametric 6)), (ctx8_addn_option 6).
  use_add E3. cbv beta iota. rewrite fx_comp.
  rewrite (fx_assert (fun alg => @ctx8_addn_spec 5 alg) (ctx8_addn_spec_parametric 5)), (ctx8_addn_option 5).
  use_add E4.
  rewrite (fx_assert (fun alg => @ctx8_finalize_spec alg) ctx8_finalize_spec_parametric).
  exact H2.
Qed.

Theorem bitcoin_tx_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_tx_hash bitcoin_ge ext_environment
    Ty.Unit Word256 (hash_getter_rep tx_hash_of 0 368 432)
    (fun a environment => @tx_hash_spec fullalg a environment).
Proof.
  eapply bitcoin_hash_getter_writeHash_local with (ptrfield := _tx) (sid := _bitcoinTransaction)
    (hashfield := _txHash).
  - exact tx_hash_spec_sem.
  - getter_shape.
  - exact bitcoin_txEnv_tx.
  - vm_compute; reflexivity.
  - lia.
  - lia.
Qed.
