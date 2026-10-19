(** The SHA-256 states [simplicity_bitcoin_mallocTransaction] stores are the
    canonical hash values the accepted transaction hash-getter relations
    require, for any logical environment that describes the raw transaction
    the builder read.  Pure reasoning about the absorbed byte streams, then
    the combination with [eval_mallocTransaction]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Integers.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_read8s_layout C.jet_word32_chunks C.jet_buffer_input.
Require Import C.jet_sha_ctx8_model C.jet_sha_ctx8_bridge C.jet_sha_uchars_prep C.jet_sha_finalize_exec.
Require Import C.jet_sha_be32_write C.jet_sha_be64_exec C.jet_sha_finalize_bridge.
Require Import C.jet_sha_ctx_abs C.jet_sha_ctxi C.jet_sha_hash_closed.
Require Import C.jet_sha256_iv_init C.jet_forWhile_seq C.jet_sha_hash_loop C.jet_sha_hash_loop_gen C.jet_sha_hash_words.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim C.jet_bitcoin_words_hash C.jet_bitcoin_composite_hash.
Require Import C.jet_bitcoin_tx_hash C.jet_bitcoin_input_hash_spec C.jet_bitcoin_vh_hash_prep C.jet_bitcoin_version_spec.
Require Import C.jet_bitcoin_env_tomidstate C.jet_bitcoin_env_hashbuffer C.jet_bitcoin_env_tapenv_tail.
Require Import C.jet_uint32_array_init C.jet_sha_add_n_calls.
Require Import C.jet_bitcoin_env_stream C.jet_bitcoin_env_tapenv_link.
Require Import C.jet_bitcoin_env_tx_indefs C.jet_bitcoin_env_tx_inops C.jet_bitcoin_env_tx_inexec.
Require Import C.jet_bitcoin_env_tx_outloop C.jet_bitcoin_env_tx_outblock C.jet_bitcoin_env_tx_txhash.
Require Import C.jet_bitcoin_env_tx.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 120.

Lemma add_repr64 a b : Int64.add (Int64.repr a) (Int64.repr b) = Int64.repr (a + b).
Proof.
  unfold Int64.add. apply Int64.eqm_samerepr.
  apply Int64.eqm_add; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma in_cnt_repr s n : in_cnt s n = Int64.repr (s * Z.of_nat n).
Proof.
  induction n as [|n IH]; [rewrite Z.mul_0_r; reflexivity|].
  cbn [in_cnt]. rewrite IH, add_repr64. f_equal. lia.
Qed.

(* Never let [Z.to_nat (wsize 5)] be computed: it is a unary 2^32. *)
Lemma wsize5z : wsize 5 = 4294967296.
Proof. reflexivity. Qed.

Lemma firstn_wsize5 {A} (l : list A) :
  Z.of_nat (length l) <= 4294967296 -> firstn (Z.to_nat (wsize 5)) l = l.
Proof.
  intros H. apply firstn_all2. apply Nat2Z.inj_le.
  rewrite Z2Nat.id by (rewrite wsize5z; lia). rewrite wsize5z. exact H.
Qed.

Lemma concat_len_const {A B} (g : A -> list B) (n : nat) (l : list A) :
  (forall x, length (g x) = n) -> length (concat (map g l)) = (n * length l)%nat.
Proof.
  intros Hg. induction l as [|a l IH]; [cbn; lia|].
  cbn [map concat length]. rewrite app_length, IH, Hg. lia.
Qed.

(** A state built by absorbing one element's bytes per step is the canonical
    stream hash of the concatenation. *)
Section Fold.
Context {A : Type}.
Variables (bytes_of : A -> list (Ty.tySem (Word 3))) (xs : list A) (stf : nat -> list int * list int).
Hypothesis H0 : stf 0%nat = st0.
Hypothesis HS : forall j x, nth_error xs j = Some x ->
  stf (S j) = ab (stf j) (map word8_array_value (bytes_of x)).

Lemma fold_state : forall k, (k <= length xs)%nat ->
  stf k = absorb_i [] sha256_iv_words (map word8_array_value (concat (map bytes_of (firstn k xs)))).
Proof.
  induction k as [|k IH]; intros Hk.
  - rewrite H0. reflexivity.
  - destruct (nth_error xs k) as [x|] eqn:Hn; [|apply nth_error_None in Hn; lia].
    rewrite (HS k x Hn), IH by lia. unfold ab. rewrite <- absorb_i_app. f_equal.
    rewrite (firstn_snoc xs k x Hn), map_app, concat_app, map_app. cbn [map concat].
    rewrite app_nil_r. reflexivity.
Qed.

Theorem fold_link (c : int64) :
  c = Int64.repr (Z.of_nat (length (concat (map bytes_of xs)))) ->
  hash256_reg (sha256_bytes_of (concat (map bytes_of xs))) = fin_regs (stf (length xs)) c.
Proof.
  intros ->. rewrite stream_hash_regs. unfold fin_regs.
  rewrite (fold_state (length xs) (le_n _)), firstn_all. reflexivity.
Qed.

(** The same with the byte counter accumulated step by step. *)
Variable cf : nat -> int64.
Hypothesis C0 : cf 0%nat = Int64.zero.
Hypothesis CS : forall j x, nth_error xs j = Some x ->
  cf (S j) = Int64.add (cf j) (Int64.repr (Z.of_nat (length (bytes_of x)))).

Lemma fold_count : forall k, (k <= length xs)%nat ->
  cf k = Int64.repr (Z.of_nat (length (concat (map bytes_of (firstn k xs))))).
Proof.
  induction k as [|k IH]; intros Hk.
  - rewrite C0. reflexivity.
  - destruct (nth_error xs k) as [x|] eqn:Hn; [|apply nth_error_None in Hn; lia].
    rewrite (CS k x Hn), IH by lia. rewrite add_repr64. f_equal.
    rewrite (firstn_snoc xs k x Hn), map_app, concat_app, app_length. cbn [map concat].
    rewrite app_nil_r. lia.
Qed.

Theorem fold_link_count :
  hash256_reg (sha256_bytes_of (concat (map bytes_of xs))) = fin_regs (stf (length xs)) (cf (length xs)).
Proof. apply fold_link. rewrite (fold_count (length xs) (le_n _)), firstn_all. reflexivity. Qed.
End Fold.

(** The [hashWordNs] family over a mapped list. *)
Lemma words_link k {A} (f : A -> Ty.tySem (Vector (Word 3) k)) (l : list A)
    (stf : nat -> list int * list int) (c : int64) :
  Z.of_nat (length l) <= 4294967296 -> stf 0%nat = st0 ->
  (forall j x, nth_error l j = Some x ->
     stf (S j) = ab (stf j) (map word8_array_value (vector_values (Word 3) k (f x)))) ->
  c = Int64.repr (Z.of_nat (Nat.pow 2 k) * Z.of_nat (length l)) ->
  hash256_reg (words_hash_of k 5 (map f l)) = fin_regs (stf (length l)) c.
Proof.
  intros HL H0 HS ->. unfold words_hash_of.
  rewrite firstn_wsize5 by (rewrite map_length; exact HL).
  change (hash_words_of k (map f l))
    with (sha256_bytes_of (concat (map (vector_values (Word 3) k) (map f l)))).
  rewrite map_map.
  apply (fold_link (fun x => vector_values (Word 3) k (f x)) l stf H0 HS).
  f_equal. rewrite (concat_len_const _ (Nat.pow 2 k)) by (intros x; apply vector_values_length). lia.
Qed.

(** A logical environment describes the raw transaction the builder read. *)
Definition tx_describes (e : ext_environment) (niv nov ver lt : int) (txb : list int)
    (data : nat -> in_data) (val : nat -> int64) (spb : nat -> list int) : Prop :=
  let tx := Bitcoin.envTx (extBase e) in
  length (sigTxIn tx) = Z.to_nat (Int.unsigned niv) /\
  length (sigTxOut tx) = Z.to_nat (Int.unsigned nov) /\
  ver = sigTxVersion tx /\ lt = sigTxLock tx /\
  (forall j x, nth_error (sigTxIn tx) j = Some x ->
     d_val (data j) = sigTxiValue x /\ d_sq (data j) = sigTxiSequence x /\
     d_ix (data j) = opIndex (sigTxiPreviousOutpoint x) /\
     tm_words (d_txb (data j)) = hash256_reg (opHash (sigTxiPreviousOutpoint x))) /\
  (forall j h, nth_error (extInScriptHash e) j = Some h -> hash_buffer_regs (d_spb (data j)) = hash256_reg h) /\
  (forall j h, nth_error (extInScriptSigHash e) j = Some h -> hash_buffer_regs (d_ssb (data j)) = hash256_reg h) /\
  (forall j a, nth_error (extInAnnexHash e) j = Some a ->
     match a with
     | None => d_has (data j) = Int.zero
     | Some h => d_has (data j) = Int.one /\ d_areg (data j) = hash256_reg h
     end) /\
  (forall j o, nth_error (sigTxOut tx) j = Some o ->
     val j = txoValue o /\ hash_buffer_regs (spb j) = hash256_reg (byteStringHash (txoScript o))).

Lemma be64_value_bytes (v : int64) :
  c_be64_bytes v = map word8_array_value (vector_values (Word 3) 3 (@fromZ (WordToZ 6) (Int64.signed v))).
Proof. rewrite <- be64_bytes_word, repr_signed_word. reflexivity. Qed.

Lemma hash_reg_bytes (R : list int) (h : hash256) :
  R = hash256_reg h ->
  be_bytes (norm8 R) = map word8_array_value (vector_values (Word 3) 5 (from_hash256 h)).
Proof. intros ->. rewrite norm8_id by apply hash256_len. apply reg_bytes. Qed.

Lemma count_bound (n : int) : Z.of_nat (Z.to_nat (Int.unsigned n)) <= 4294967296.
Proof. pose proof (Int.unsigned_range n) as H. change Int.modulus with 4294967296 in H. lia. Qed.

Lemma ab_app (st : list int * list int) (b1 b2 : list int) : ab st (b1 ++ b2) = ab (ab st b1) b2.
Proof. unfold ab. rewrite absorb_i_app. reflexivity. Qed.

Lemma counter64 : c32 (c32 Int64.zero) = Int64.repr 64.
Proof. apply Int64.same_if_eq. vm_compute. reflexivity. Qed.
Lemma counter96' : c32 (c32 (c32 Int64.zero)) = Int64.repr 96.
Proof. apply Int64.same_if_eq. vm_compute. reflexivity. Qed.
Lemma counter104 :
  Int64.add (Int64.add (Int64.add (Int64.add (Int64.add Int64.zero (Int64.repr 4)) (Int64.repr 4))
    (Int64.repr 32)) (Int64.repr 32)) (Int64.repr 32) = Int64.repr 104.
Proof. apply Int64.same_if_eq. vm_compute. reflexivity. Qed.

Lemma hbytes (h : hash256) :
  be_bytes (norm8 (hash256_reg h)) = map word8_array_value (vector_values (Word 3) 5 (from_hash256 h)).
Proof. apply hash_reg_bytes. reflexivity. Qed.

(** Two and three hashes absorbed from the initial state. *)
Lemma pair_link (a b : hash256) :
  hash256_reg (pair_hash_of a b) =
    fin_regs (ab (ab st0 (be_bytes (norm8 (hash256_reg a)))) (be_bytes (norm8 (hash256_reg b))))
      (c32 (c32 Int64.zero)).
Proof.
  unfold pair_hash_of. rewrite stream_hash_regs.
  change (vector_values (Word 3) 6 (from_hash256 a, from_hash256 b))
    with (vector_values (Word 3) 5 (from_hash256 a) ++ vector_values (Word 3) 5 (from_hash256 b)).
  rewrite map_app, app_length, !vector_values_length, counter64, !hbytes, <- ab_app.
  reflexivity.
Qed.

Lemma triple_link (a b c : hash256) :
  hash256_reg (sha256_bytes_of
    (vector_values (Word 3) 6 (from_hash256 a, from_hash256 b) ++
     vector_values (Word 3) 5 (from_hash256 c))) =
    fin_regs (ab (ab (ab st0 (be_bytes (norm8 (hash256_reg a)))) (be_bytes (norm8 (hash256_reg b))))
                (be_bytes (norm8 (hash256_reg c))))
      (c32 (c32 (c32 Int64.zero))).
Proof.
  rewrite stream_hash_regs.
  change (vector_values (Word 3) 6 (from_hash256 a, from_hash256 b))
    with (vector_values (Word 3) 5 (from_hash256 a) ++ vector_values (Word 3) 5 (from_hash256 b)).
  rewrite !map_app, !app_length, !vector_values_length, counter96', !hbytes, <- !ab_app.
  reflexivity.
Qed.

Lemma tx_link_gen (vw lw : int) (a b c : hash256) :
  hash256_reg (sha256_bytes_of
    (vector_values (Word 3) 3 (@fromZ (WordToZ 5) (Int.unsigned vw), @fromZ (WordToZ 5) (Int.unsigned lw)) ++
     vector_values (Word 3) 6 (from_hash256 a, from_hash256 b) ++
     vector_values (Word 3) 5 (from_hash256 c))) =
    mt_txhash_regs (Int64.repr (Int.unsigned vw)) (Int64.repr (Int.unsigned lw))
      (hash256_reg a) (hash256_reg b) (hash256_reg c).
Proof.
  rewrite stream_hash_regs.
  change (vector_values (Word 3) 3 (@fromZ (WordToZ 5) (Int.unsigned vw), @fromZ (WordToZ 5) (Int.unsigned lw)))
    with (vector_values (Word 3) 2 (@fromZ (WordToZ 5) (Int.unsigned vw)) ++
          vector_values (Word 3) 2 (@fromZ (WordToZ 5) (Int.unsigned lw))).
  change (vector_values (Word 3) 6 (from_hash256 a, from_hash256 b))
    with (vector_values (Word 3) 5 (from_hash256 a) ++ vector_values (Word 3) 5 (from_hash256 b)).
  rewrite !map_app, !app_length, !vector_values_length.
  unfold mt_txhash_regs. cbv zeta. rewrite counter104, !hbytes, !be32_bytes_word.
  rewrite <- !absorb_i_app, <- !app_assoc. reflexivity.
Qed.

Section Links.
Variables (e : ext_environment) (niv nov ver lt : int) (txb : list int).
Variables (data : nat -> in_data) (val : nat -> int64) (spb : nat -> list int).
Hypothesis HD : tx_describes e niv nov ver lt txb data val spb.

Let tx := Bitcoin.envTx (extBase e).
Let Nn := Z.to_nat (Int.unsigned niv).
Let Mn := Z.to_nat (Int.unsigned nov).
Let no := Int.unsigned nov.

Lemma link_out_values : hash256_reg (words_hash_of 3 5 (output_values_of e)) = out_regsV no val.
Proof.
  destruct HD as (_ & HLo & _ & _ & _ & _ & _ & _ & HO). fold tx in HLo, HO.
  transitivity (fin_regs (out_stV val (length (sigTxOut tx))) (Int64.repr (8 * Z.of_nat Mn))).
  - apply (words_link 3 (fun o => @fromZ (WordToZ 6) (Int64.signed (txoValue o))) (sigTxOut tx) (out_stV val)).
    + rewrite HLo. apply count_bound.
    + reflexivity.
    + intros j o Hj. cbn [out_stV]. unfold ab. rewrite (proj1 (HO j o Hj)), be64_value_bytes. reflexivity.
    + rewrite HLo. reflexivity.
  - rewrite HLo. reflexivity.
Qed.

Lemma link_out_scripts : hash256_reg (words_hash_of 5 5 (output_scripts_of e)) = out_regsS no spb.
Proof.
  destruct HD as (_ & HLo & _ & _ & _ & _ & _ & _ & HO). fold tx in HLo, HO.
  transitivity (fin_regs (out_stS spb (length (sigTxOut tx))) (Int64.repr (32 * Z.of_nat Mn))).
  - apply (words_link 5 (fun x => from_hash256 (byteStringHash (txoScript x))) (sigTxOut tx) (out_stS spb)).
    + rewrite HLo. apply count_bound.
    + reflexivity.
    + intros j o Hj. cbn [out_stS]. unfold ab. rewrite (hash_reg_bytes _ _ (proj2 (HO j o Hj))). reflexivity.
    + rewrite HLo. reflexivity.
  - rewrite HLo. reflexivity.
Qed.

Lemma link_in_values : hash256_reg (words_hash_of 3 5 (input_values_of e)) = in_regsV data Nn.
Proof.
  destruct HD as (HLi & _ & _ & _ & HI & _). fold tx in HLi, HI.
  transitivity (fin_regs (in_stV data (length (sigTxIn tx))) (in_cnt 8 Nn)).
  - apply (words_link 3 (fun x => @fromZ (WordToZ 6) (Int64.signed (sigTxiValue x))) (sigTxIn tx) (in_stV data)).
    + rewrite HLi. apply count_bound.
    + reflexivity.
    + intros j x Hj. cbn [in_stV]. destruct (HI j x Hj) as (E1 & _). rewrite E1, be64_value_bytes. reflexivity.
    + rewrite in_cnt_repr, HLi. reflexivity.
  - rewrite HLi. reflexivity.
Qed.

Lemma link_in_sequences : hash256_reg (words_hash_of 2 5 (input_sequences_of e)) = in_regsQ data Nn.
Proof.
  destruct HD as (HLi & _ & _ & _ & HI & _). fold tx in HLi, HI.
  transitivity (fin_regs (in_stSeq data (length (sigTxIn tx))) (in_cnt 4 Nn)).
  - apply (words_link 2 (fun x => @fromZ (WordToZ 5) (Int.unsigned (sigTxiSequence x))) (sigTxIn tx) (in_stSeq data)).
    + rewrite HLi. apply count_bound.
    + reflexivity.
    + intros j x Hj. cbn [in_stSeq]. destruct (HI j x Hj) as (_ & E2 & _). rewrite E2, be32_bytes_word. reflexivity.
    + rewrite in_cnt_repr, HLi. reflexivity.
  - rewrite HLi. reflexivity.
Qed.

Lemma link_in_scripts : hash256_reg (words_hash_of 5 5 (input_scripts_of e)) = in_regsS data Nn.
Proof.
  destruct HD as (HLi & _ & _ & _ & _ & HSc & _). fold tx in HLi.
  pose proof (extInScriptHash_len e) as HL. fold tx in HL.
  transitivity (fin_regs (in_stSc data (length (extInScriptHash e))) (in_cnt 32 Nn)).
  - apply (words_link 5 (fun x => from_hash256 x) (extInScriptHash e) (in_stSc data)).
    + rewrite HL, HLi. apply count_bound.
    + reflexivity.
    + intros j h Hj. cbn [in_stSc]. rewrite (hash_reg_bytes _ _ (HSc j h Hj)). reflexivity.
    + rewrite in_cnt_repr, HL, HLi. reflexivity.
  - rewrite HL, HLi. reflexivity.
Qed.

Lemma link_in_script_sigs : hash256_reg (words_hash_of 5 5 (input_script_sigs_of e)) = in_regsG data Nn.
Proof.
  destruct HD as (HLi & _ & _ & _ & _ & _ & HSs & _). fold tx in HLi.
  pose proof (extInScriptSigHash_len e) as HL. fold tx in HL.
  transitivity (fin_regs (in_stSS data (length (extInScriptSigHash e))) (in_cnt 32 Nn)).
  - apply (words_link 5 (fun x => from_hash256 x) (extInScriptSigHash e) (in_stSS data)).
    + rewrite HL, HLi. apply count_bound.
    + reflexivity.
    + intros j h Hj. cbn [in_stSS]. rewrite (hash_reg_bytes _ _ (HSs j h Hj)). reflexivity.
    + rewrite in_cnt_repr, HL, HLi. reflexivity.
  - rewrite HL, HLi. reflexivity.
Qed.

Lemma link_in_outpoints : hash256_reg (input_outpoints_hash_of e) = in_regsP data Nn.
Proof.
  destruct HD as (HLi & _ & _ & _ & HI & _). fold tx in HLi, HI.
  unfold input_outpoints_hash_of, elems_hash_of, outpoints_of.
  rewrite firstn_wsize5 by (rewrite map_length; fold tx; rewrite HLi; apply count_bound).
  unfold gen_bytes. rewrite map_map.
  transitivity (fin_regs (in_stOP data (length (sigTxIn tx))) (in_cntOP (length (sigTxIn tx)))).
  - apply (fold_link_count
      (fun x => outpoint_bytes (from_hash256 (opHash (sigTxiPreviousOutpoint x)),
                                @fromZ (WordToZ 5) (Int.unsigned (opIndex (sigTxiPreviousOutpoint x)))))
      (sigTxIn tx) (in_stOP data) eq_refl).
    + intros j x Hj. cbn [in_stOP]. destruct (HI j x Hj) as (_ & _ & E3 & E4).
      unfold outpoint_bytes. cbn [fst snd]. rewrite map_app, (ab_app (in_stOP data j)).
      rewrite (hash_reg_bytes _ _ E4), E3, be32_bytes_word. reflexivity.
    + reflexivity.
    + intros j x Hj. cbn [in_cntOP]. unfold outpoint_bytes. cbn [fst snd].
      rewrite app_length, !vector_values_length, Int64.add_assoc. reflexivity.
  - rewrite HLi. reflexivity.
Qed.

Definition annex_value (o : option hash256) : Ty.tySem (Ty.Sum Ty.Unit (Word 8)) :=
  match o with None => inl tt | Some h => inr (from_hash256 h) end.

Lemma annex_state j a : nth_error (extInAnnexHash e) j = Some a ->
  in_stAn data (S j) = ab (in_stAn data j) (map word8_array_value (annex_elem_bytes (annex_value a))).
Proof.
  intros Hj. destruct HD as (_ & _ & _ & _ & _ & _ & _ & HAn & _).
  pose proof (HAn j a Hj) as Ha. cbn [in_stAn]. unfold an_step. destruct a as [h|].
  - destruct Ha as [E1 E2]. rewrite E1, (Int.eq_false Int.one Int.zero) by discriminate.
    unfold annex_value, annex_elem_bytes. cbn [map]. rewrite w8_one.
    change (Int.repr 1 :: map word8_array_value (vector_values (Word 3) 5 (from_hash256 h)))
      with ([Int.repr 1] ++ map word8_array_value (vector_values (Word 3) 5 (from_hash256 h))).
    rewrite (ab_app (in_stAn data j)), (hash_reg_bytes _ _ E2). reflexivity.
  - rewrite Ha, Int.eq_true. unfold annex_value, annex_elem_bytes. cbn [map]. rewrite w8_zero. reflexivity.
Qed.

Lemma c33 (c : int64) : Int64.add (Int64.add c (Int64.repr 1)) (Int64.repr 32) = Int64.add c (Int64.repr 33).
Proof. rewrite Int64.add_assoc. f_equal. Qed.

Lemma annex_count j a : nth_error (extInAnnexHash e) j = Some a ->
  in_nAn data (S j) =
    Int64.add (in_nAn data j) (Int64.repr (Z.of_nat (length (annex_elem_bytes (annex_value a))))).
Proof.
  intros Hj. destruct HD as (_ & _ & _ & _ & _ & _ & _ & HAn & _).
  pose proof (HAn j a Hj) as Ha. cbn [in_nAn]. destruct a as [h|].
  - destruct Ha as [E1 _]. rewrite E1, (Int.eq_false Int.one Int.zero) by discriminate.
    unfold annex_value, annex_elem_bytes. cbn [length]. rewrite vector_values_length, c33. reflexivity.
  - rewrite Ha, Int.eq_true. reflexivity.
Qed.

Lemma link_in_annexes : hash256_reg (input_annexes_hash_of e) = in_regsN data Nn.
Proof.
  destruct HD as (HLi & _). fold tx in HLi.
  pose proof (extInAnnexHash_len e) as HL. fold tx in HL.
  unfold input_annexes_hash_of, elems_hash_of, annexes_of.
  rewrite firstn_wsize5 by (rewrite map_length, HL, HLi; apply count_bound).
  unfold gen_bytes. rewrite map_map.
  transitivity (fin_regs (in_stAn data (length (extInAnnexHash e))) (in_nAn data (length (extInAnnexHash e)))).
  - exact (fold_link_count (fun o => annex_elem_bytes (annex_value o)) (extInAnnexHash e) (in_stAn data)
             eq_refl annex_state (in_nAn data) eq_refl annex_count).
  - rewrite HL, HLi. reflexivity.
Qed.

Lemma link_outputs : hash256_reg (outputs_hash_of e) = out_regsO no val spb.
Proof. unfold outputs_hash_of. rewrite pair_link, link_out_values, link_out_scripts. reflexivity. Qed.

Lemma link_in_utxos : hash256_reg (input_utxos_hash_of e) = in_regsU data Nn.
Proof. unfold input_utxos_hash_of. rewrite pair_link, link_in_values, link_in_scripts. reflexivity. Qed.

Lemma link_inputs : hash256_reg (inputs_hash_of e) = in_regsI data Nn.
Proof.
  unfold inputs_hash_of. rewrite triple_link, link_in_outpoints, link_in_sequences, link_in_annexes.
  reflexivity.
Qed.

Lemma link_tx :
  hash256_reg (tx_hash_of e) =
    mt_txhash_regs (Int64.repr (Int.unsigned ver)) (Int64.repr (Int.unsigned lt))
      (in_regsI data Nn) (out_regsO no val spb) (in_regsU data Nn).
Proof.
  destruct HD as (_ & _ & Ev & El & _). fold tx in Ev, El.
  unfold tx_hash_of, tx_version_word, tx_locktime_word. fold tx.
  rewrite <- bitcoin_version_word_signed_unsigned, <- Ev, <- El.
  rewrite tx_link_gen, link_inputs, link_outputs, link_in_utxos. reflexivity.
Qed.
End Links.

(** ** The cached hashes of the allocated transaction

    For a logical environment that describes the raw transaction, the twelve
    hash fields hold exactly the values the accepted hash-getter relations
    ([hash_getter_rep ... 0 16 432], [... 0 48 432], ..., [... 0 368 432])
    require of the transaction structure: the relation premises are
    established by the C code, not assumed. *)
Theorem tx_cached_hashes (e : ext_environment) m bA niv nov ver lt txb data val spb :
  tx_built m bA niv nov ver lt txb data val spb ->
  tx_describes e niv nov ver lt txb data val spb ->
  uint32_array_at m bA 16 (hash256_reg (words_hash_of 3 5 (output_values_of e))) /\
  uint32_array_at m bA 48 (hash256_reg (words_hash_of 5 5 (output_scripts_of e))) /\
  uint32_array_at m bA 80 (hash256_reg (outputs_hash_of e)) /\
  uint32_array_at m bA 112 (hash256_reg (input_outpoints_hash_of e)) /\
  uint32_array_at m bA 144 (hash256_reg (words_hash_of 3 5 (input_values_of e))) /\
  uint32_array_at m bA 176 (hash256_reg (words_hash_of 5 5 (input_scripts_of e))) /\
  uint32_array_at m bA 208 (hash256_reg (input_utxos_hash_of e)) /\
  uint32_array_at m bA 240 (hash256_reg (words_hash_of 2 5 (input_sequences_of e))) /\
  uint32_array_at m bA 272 (hash256_reg (input_annexes_hash_of e)) /\
  uint32_array_at m bA 304 (hash256_reg (words_hash_of 5 5 (input_script_sigs_of e))) /\
  uint32_array_at m bA 336 (hash256_reg (inputs_hash_of e)) /\
  uint32_array_at m bA 368 (hash256_reg (tx_hash_of e)).
Proof.
  intros HB HD. unfold tx_built in HB. cbv beta zeta in HB.
  destruct HB as (_ & _ & R16 & R48 & R80 & R112 & R144 & R176 & R208 & R240 & R272 & R304 & R336 & R368 & _).
  repeat split; apply u32_of_nth; intros i Hi; rewrite hash256_len in Hi.
  - rewrite (link_out_values e niv nov ver lt txb data val spb HD). apply R16, Hi.
  - rewrite (link_out_scripts e niv nov ver lt txb data val spb HD). apply R48, Hi.
  - rewrite (link_outputs e niv nov ver lt txb data val spb HD). apply R80, Hi.
  - rewrite (link_in_outpoints e niv nov ver lt txb data val spb HD). apply R112, Hi.
  - rewrite (link_in_values e niv nov ver lt txb data val spb HD). apply R144, Hi.
  - rewrite (link_in_scripts e niv nov ver lt txb data val spb HD). apply R176, Hi.
  - rewrite (link_in_utxos e niv nov ver lt txb data val spb HD). apply R208, Hi.
  - rewrite (link_in_sequences e niv nov ver lt txb data val spb HD). apply R240, Hi.
  - rewrite (link_in_annexes e niv nov ver lt txb data val spb HD). apply R272, Hi.
  - rewrite (link_in_script_sigs e niv nov ver lt txb data val spb HD). apply R304, Hi.
  - rewrite (link_inputs e niv nov ver lt txb data val spb HD). apply R336, Hi.
  - rewrite (link_tx e niv nov ver lt txb data val spb HD). apply R368, Hi.
Qed.

(** The headline statement: the actual builder establishes the cached-hash
    premises of the accepted transaction relations. *)
Theorem mallocTransaction_cached_hashes (Hmodel : jet_memcpy_model.memcpy_model) (e : ext_environment)
    m braw oraw btx otx bri ori bro oro (niv nov ver lt : int) (txb : list int) (data : nat -> in_data)
    (val : nat -> int64) (bsp : nat -> Values.block) (osp : nat -> ptrofs) (spb : nat -> list int) :
  0 <= oraw /\ oraw + 40 <= Ptrofs.max_unsigned ->
  Memory.Mem.load AST.Mptr m braw oraw = Some (Values.Vptr btx otx) ->
  (0 < Int.unsigned niv ->
   Memory.Mem.load AST.Mptr m braw (oraw + 8) = Some (Values.Vptr bri (Ptrofs.repr ori))) ->
  (0 < Int.unsigned nov ->
   Memory.Mem.load AST.Mptr m braw (oraw + 16) = Some (Values.Vptr bro (Ptrofs.repr oro))) ->
  Memory.Mem.load AST.Mint32 m braw (oraw + 24) = Some (Values.Vint niv) ->
  Memory.Mem.load AST.Mint32 m braw (oraw + 28) = Some (Values.Vint nov) ->
  Memory.Mem.load AST.Mint32 m braw (oraw + 32) = Some (Values.Vint ver) ->
  Memory.Mem.load AST.Mint32 m braw (oraw + 36) = Some (Values.Vint lt) ->
  Ptrofs.unsigned otx + 32 <= Ptrofs.max_unsigned ->
  (forall i, (i < 32)%nat ->
     Memory.Mem.load AST.Mint8unsigned m btx (Ptrofs.unsigned otx + Z.of_nat i) =
       Some (Values.Vint (nth i txb Int.zero))) ->
  0 <= ori /\ ori + 64 * Int.unsigned niv <= Ptrofs.max_unsigned ->
  (forall j, (j < Z.to_nat (Int.unsigned niv))%nat ->
     raw_in_at (Memory.Mem.valid_block m) m bri (ori + 64 * Z.of_nat j) (data j)) ->
  0 <= oro /\ oro + 24 * Int.unsigned nov <= Ptrofs.max_unsigned ->
  (forall j, (j < Z.to_nat (Int.unsigned nov))%nat ->
     Memory.Mem.load AST.Mint64 m bro (oro + 24 * Z.of_nat j) = Some (Values.Vlong (val j))) ->
  (forall j, (j < Z.to_nat (Int.unsigned nov))%nat ->
     jet_bitcoin_env_copyinput.raw_buffer_at m bro (oro + 24 * Z.of_nat j + 8) (bsp j) (osp j) (spb j)) ->
  jet_sha_block_local.sha_dispatch_ok m ->
  Memory.Mem.load AST.Mint64 m (jet_sha_linkage.sha_symbol_block jets_sha._sha256_max_counter) 0 =
    Some (Values.Vlong jet_sha_uchars_exec.sha_max_counter) ->
  tx_describes e niv nov ver lt txb data val spb ->
  exists m' bA,
    ClightBigstep.Clight2.eval_funcall jet_sha_linkage.sha_ge m
      (Ctypes.Internal jets_sha.f_simplicity_bitcoin_mallocTransaction)
      [Values.Vptr braw (Ptrofs.repr oraw)] Events.E0 m' (Values.Vptr bA Ptrofs.zero) /\
    ~ Memory.Mem.valid_block m bA /\
    uint32_array_at m' bA 16 (hash256_reg (words_hash_of 3 5 (output_values_of e))) /\
    uint32_array_at m' bA 48 (hash256_reg (words_hash_of 5 5 (output_scripts_of e))) /\
    uint32_array_at m' bA 80 (hash256_reg (outputs_hash_of e)) /\
    uint32_array_at m' bA 112 (hash256_reg (input_outpoints_hash_of e)) /\
    uint32_array_at m' bA 144 (hash256_reg (words_hash_of 3 5 (input_values_of e))) /\
    uint32_array_at m' bA 176 (hash256_reg (words_hash_of 5 5 (input_scripts_of e))) /\
    uint32_array_at m' bA 208 (hash256_reg (input_utxos_hash_of e)) /\
    uint32_array_at m' bA 240 (hash256_reg (words_hash_of 2 5 (input_sequences_of e))) /\
    uint32_array_at m' bA 272 (hash256_reg (input_annexes_hash_of e)) /\
    uint32_array_at m' bA 304 (hash256_reg (words_hash_of 5 5 (input_script_sigs_of e))) /\
    uint32_array_at m' bA 336 (hash256_reg (inputs_hash_of e)) /\
    uint32_array_at m' bA 368 (hash256_reg (tx_hash_of e)) /\
    (forall ch b ofs, Memory.Mem.valid_block m b -> Memory.Mem.load ch m' b ofs = Memory.Mem.load ch m b ofs).
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 HD.
  destruct (eval_mallocTransaction Hmodel m braw oraw btx otx bri ori bro oro niv nov ver lt txb data val bsp osp spb
    H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17) as (m' & bA & HCall & HFresh & HBuilt & HL & _).
  pose proof (tx_cached_hashes e m' bA niv nov ver lt txb data val spb HBuilt HD) as HH.
  exists m', bA. split; [exact HCall|]. split; [exact HFresh|].
  repeat (destruct HH as [HA HH]; split; [exact HA|clear HA]). split; [exact HH|exact HL].
Qed.
