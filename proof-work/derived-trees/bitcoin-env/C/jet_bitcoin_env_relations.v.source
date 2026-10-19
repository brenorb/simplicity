(** The environment relations of the accepted Bitcoin application jets are
    established by the real builders: for the [txEnv] that
    [build_environment] leaves ([env_ready]), each relation a jet theorem
    takes as a premise about the environment structure holds.  Pure
    consequences of [env_ready]; no program. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Values Memory.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Util.List.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_word_repr C.jet_read8s_layout C.jet_word32_chunks.
Require Import C.jet_uint32_array_init C.jet_sha_add_n_calls C.jet_sha_ctx8_model C.jet_sha_hash_closed.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_words_hash C.jet_bitcoin_composite_hash C.jet_bitcoin_tx_hash.
Require Import C.jet_bitcoin_tapleaf_hash_spec C.jet_bitcoin_sig_all_hash C.jet_bitcoin_hash_getter_local.
Require Import C.jet_bitcoin_version_local C.jet_bitcoin_locktime_local C.jet_bitcoin_count_local.
Require Import C.jet_bitcoin_totals_local C.jet_bitcoin_is_final_spec C.jet_bitcoin_is_final_local.
Require Import C.jet_bitcoin_lock_local C.jet_bitcoin_check_lock C.jet_bitcoin_fee_local.
Require Import C.jet_bitcoin_current_index_local C.jet_bitcoin_script_cmr_local.
Require Import C.jet_bitcoin_tapleaf_version_local C.jet_bitcoin_ext_ptr_jets C.jet_bitcoin_tappath_local.
Require Import C.jet_bitcoin_env_tomidstate C.jet_bitcoin_env_tapenv_key C.jet_bitcoin_env_tapenv.
Require Import C.jet_bitcoin_env_tapenv_link C.jet_bitcoin_env_tapenv_raw.
Require Import C.jet_bitcoin_env_tx_indefs C.jet_bitcoin_env_tx_outloop C.jet_bitcoin_env_tx.
Require Import C.jet_bitcoin_env_tx_link C.jet_bitcoin_env_build.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 120.

(** ** Arithmetic content of the scalar fields *)

Lemma Z_sum_app (a b : list Z) : Z_sum (a ++ b) = Z_sum a + Z_sum b.
Proof. unfold Z_sum. induction a as [|x a IH]; cbn [app fold_right]; [reflexivity|]. rewrite IH. lia. Qed.

Lemma add_repr_signed (a : Z) (b : int64) : Int64.add (Int64.repr a) b = Int64.repr (a + Int64.signed b).
Proof.
  unfold Int64.add. apply Int64.eqm_samerepr. apply Int64.eqm_add.
  - apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
  - apply Int64.eqm_sym, Int64.eqm_signed_unsigned.
Qed.

(** A running 64-bit total over a list is the sum of the signed values. *)
Lemma total_link {A} (f : nat -> int64) (g : A -> int64) (l : list A) (tot : nat -> int64) :
  tot 0%nat = Int64.zero -> (forall k, tot (S k) = Int64.add (tot k) (f k)) ->
  (forall j x, nth_error l j = Some x -> f j = g x) ->
  Int64.unsigned (tot (length l)) = Z_sum (map (fun x => Int64.signed (g x)) l) mod Int64.modulus.
Proof.
  intros H0 HS Hf.
  assert (HK : forall k, (k <= length l)%nat ->
    tot k = Int64.repr (Z_sum (map (fun x => Int64.signed (g x)) (firstn k l)))).
  { induction k as [|k IH]; intros Hk; [rewrite H0; reflexivity|].
    destruct (nth_error l k) as [x|] eqn:Hn; [|apply nth_error_None in Hn; lia].
    rewrite HS, IH by lia. rewrite (Hf k x Hn), add_repr_signed. f_equal.
    rewrite (firstn_snoc l k x Hn), map_app, Z_sum_app. cbn. lia. }
  rewrite (HK (length l) (le_n _)), firstn_all. apply Int64.unsigned_repr_eq.
Qed.

Lemma final_link (l : list sigTxInput) (data : nat -> in_data) :
  (forall j x, nth_error l j = Some x -> d_sq (data j) = sigTxiSequence x) ->
  in_final data (length l) = bool_int (forallb sequence_final l).
Proof.
  intros Hq.
  assert (HK : forall k, (k <= length l)%nat ->
    in_final data k = bool_int (forallb sequence_final (firstn k l))).
  { induction k as [|k IH]; intros Hk; [reflexivity|].
    destruct (nth_error l k) as [x|] eqn:Hn; [|apply nth_error_None in Hn; lia].
    cbn [in_final]. rewrite (Hq k x Hn), IH by lia.
    rewrite (firstn_snoc l k x Hn), forallb_app. cbn [forallb]. rewrite andb_true_r.
    pose proof (Int.unsigned_range_2 (sigTxiSequence x)) as HR. change Int.max_unsigned with 4294967295 in HR.
    unfold Int64.ltu, sequence_final.
    rewrite !Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
    destruct (zlt (Int.unsigned (sigTxiSequence x)) 4294967295) as [Hlt|Hge].
    - assert (E : (Int.unsigned (sigTxiSequence x) =? 4294967295) = false) by (apply Z.eqb_neq; lia).
      rewrite E, andb_false_r. reflexivity.
    - assert (E : (Int.unsigned (sigTxiSequence x) =? 4294967295) = true) by (apply Z.eqb_eq; lia).
      rewrite E, andb_true_r. reflexivity. }
  rewrite (HK (length l) (le_n _)), firstn_all. reflexivity.
Qed.

Lemma word8_value_small (z : Z) : 0 <= z < 256 -> word8_array_value (@fromZ (WordToZ 3) z) = Int.repr z.
Proof.
  intros HR. unfold word8_array_value. rewrite to_fromZ, two_power_nat_equiv, word_bitSize.
  change (2 ^ Z.of_nat (Nat.pow 2 3)) with 256. rewrite Z.mod_small by exact HR. reflexivity.
Qed.

Lemma repr32_unsigned (v : int) : Int64.unsigned (Int64.repr (Int.unsigned v)) = Int.unsigned v.
Proof.
  pose proof (Int.unsigned_range_2 v) as HV. change Int.max_unsigned with 4294967295 in HV.
  apply Int64.unsigned_repr. change Int64.max_unsigned with 18446744073709551615. lia.
Qed.

Section Ready.
Variables (m : mem) (bD : block) (oD : Z) (bT bE : block) (e : ext_environment).
Variables (niv nov ver lt : int) (txb : list int) (data : nat -> in_data) (val : nat -> int64).
Variables (spb : nat -> list int) (nb cb0 : int) (kb cmrb : list int) (pb : nat -> list int).
Hypothesis HR : env_ready m bD oD bT bE e niv nov ver lt txb data val spb nb cb0 kb cmrb pb.
Hypothesis HoD : 0 <= oD /\ oD + 56 <= Ptrofs.max_unsigned.

Let env := Vptr bD (Ptrofs.repr oD).
Let tx := Bitcoin.envTx (extBase e).

Ltac open_ready :=
  let R0 := fresh "R0" in let R8 := fresh "R8" in let RSig := fresh "RSig" in let RIx := fresh "RIx" in
  let HB := fresh "HB" in let HTb := fresh "HTb" in let HD := fresh "HD" in let HDt := fresh "HDt" in
  pose proof HR as (R0 & R8 & RSig & RIx & HB & HTb & HD & HDt);
  pose proof HB as HBu; unfold tx_built in HBu; cbv beta zeta in HBu;
  destruct HBu as (B0 & B8 & G16 & G48 & G80 & G112 & G144 & G176 & G208 & G240 & G272 & G304 & G336 & G368 &
                   G400 & B432 & B440 & B448 & B456 & B464 & B472 & B480 & BIn & BOut);
  pose proof HTb as HTu; unfold tapenv_built in HTu; cbv beta zeta in HTu;
  destruct HTu as (TP0 & TLeaf & TPath & TEnv & TKey & TCmr & TLen & TVer & TArr);
  pose proof HD as (HLi & HLo & Ev & El & HI & HSc & HSs & HAn & HO); fold tx in HLi, HLo, Ev, El, HI, HO;
  pose proof HDt as (Dv & Dc & DLn & DP & DK).

Lemma max488 : 0 + 488 <= Ptrofs.max_unsigned.
Proof. change Ptrofs.max_unsigned with 18446744073709551615. lia. Qed.

(** *** Scalar getters *)
Theorem ready_version : bitcoin_version_env_rep m env (extBase e).
Proof.
  open_ready. exists bD, oD, bT, 0, (Int64.repr (Int.unsigned ver)).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact max488|].
  split; [exact R0|]. split; [exact B464|].
  rewrite Ev. apply repr32_unsigned.
Qed.

Theorem ready_lock_time : bitcoin_locktime_env_rep m env (extBase e).
Proof.
  open_ready. exists bD, oD, bT, 0, (Int64.repr (Int.unsigned lt)).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact max488|].
  split; [exact R0|]. split; [exact B472|].
  rewrite El. apply repr32_unsigned.
Qed.

Lemma count_value (n : int) : Int64.unsigned (Int64.repr (Int.unsigned n)) = Z.of_nat (Z.to_nat (Int.unsigned n)).
Proof.
  pose proof (Int.unsigned_range_2 n) as HV. change Int.max_unsigned with 4294967295 in HV.
  rewrite Z2Nat.id by lia. apply Int64.unsigned_repr. change Int64.max_unsigned with 18446744073709551615. lia.
Qed.

Theorem ready_num_inputs : bitcoin_num_inputs_env_rep m env (extBase e).
Proof.
  open_ready. exists bD, oD, bT, 0, (Int64.repr (Int.unsigned niv)).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact max488|].
  split; [exact R0|]. split; [exact B448|]. fold tx. rewrite HLi. apply count_value.
Qed.

Theorem ready_num_outputs : bitcoin_num_outputs_env_rep m env (extBase e).
Proof.
  open_ready. exists bD, oD, bT, 0, (Int64.repr (Int.unsigned nov)).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact max488|].
  split; [exact R0|]. split; [exact B456|]. fold tx. rewrite HLo. apply count_value.
Qed.

Lemma ready_total_in :
  Int64.unsigned (in_tot data (Z.to_nat (Int.unsigned niv))) = sigTxTotalInValue tx mod Int64.modulus.
Proof.
  open_ready. rewrite <- HLi.
  apply (total_link (fun k => d_val (data k)) sigTxiValue (sigTxIn tx) (in_tot data)); [reflexivity|reflexivity|].
  intros j x Hj. exact (proj1 (HI j x Hj)).
Qed.

Lemma ready_total_out :
  Int64.unsigned (out_tot val (Z.to_nat (Int.unsigned nov))) = sigTxTotalOutValue tx mod Int64.modulus.
Proof.
  open_ready. rewrite <- HLo.
  apply (total_link val txoValue (sigTxOut tx) (out_tot val)); [reflexivity|reflexivity|].
  intros j x Hj. exact (proj1 (HO j x Hj)).
Qed.

Theorem ready_total_input_value :
  bitcoin_total_input_value_env_rep m env (extBase e) [(bD, oD, oD + 8); (bT, 0 + 432, 0 + 432 + 8)].
Proof.
  open_ready. exists bD, oD, bT, 0, (in_tot data (Z.to_nat (Int.unsigned niv))).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact max488|].
  split; [exact R0|]. split; [exact B432|]. split; [exact ready_total_in|reflexivity].
Qed.

Theorem ready_total_output_value :
  bitcoin_total_output_value_env_rep m env (extBase e) [(bD, oD, oD + 8); (bT, 0 + 440, 0 + 440 + 8)].
Proof.
  open_ready. exists bD, oD, bT, 0, (out_tot val (Z.to_nat (Int.unsigned nov))).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact max488|].
  split; [exact R0|]. split; [exact B440|]. split; [exact ready_total_out|reflexivity].
Qed.

Theorem ready_fee : bitcoin_fee_env_rep m env (extBase e) [(bD, oD, oD + 8); (bT, 0 + 432, 0 + 448)].
Proof.
  open_ready. exists bD, oD, bT, 0, (in_tot data (Z.to_nat (Int.unsigned niv))),
    (out_tot val (Z.to_nat (Int.unsigned nov))).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact max488|].
  split; [exact R0|]. split; [exact B432|]. split; [exact B440|].
  split; [exact ready_total_in|]. split; [exact ready_total_out|reflexivity].
Qed.

Lemma ready_final :
  Mem.load Mint8unsigned m bT (0 + 480) = Some (Vint (bool_int (forallb sequence_final (sigTxIn tx)))).
Proof.
  open_ready. rewrite <- (final_link (sigTxIn tx) data), HLi; [exact B480|].
  intros j x Hj. exact (proj1 (proj2 (HI j x Hj))).
Qed.

Theorem ready_tx_is_final :
  bitcoin_tx_is_final_env_rep m env (extBase e) [(bD, oD, oD + 8); (bT, 0 + 480, 0 + 481)].
Proof.
  open_ready. exists bD, oD, bT, 0.
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact max488|].
  split; [exact R0|]. split; [exact ready_final|reflexivity].
Qed.

Theorem ready_lock : bitcoin_lock_env_rep m env (extBase e) [(bD, oD, oD + 8); (bT, 0 + 472, 0 + 481)].
Proof.
  open_ready. exists bD, oD, bT, 0, (Int64.repr (Int.unsigned lt)).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact max488|].
  split; [exact R0|]. split; [exact ready_final|]. split; [exact B472|].
  split; [|reflexivity].
  rewrite El. apply repr32_unsigned.
Qed.

Theorem ready_check_lock : bitcoin_check_lock_env_rep m env (extBase e).
Proof. eexists. exact ready_lock. Qed.

Lemma ready_index_bound : Z.of_nat (Bitcoin.envIx (extBase e)) <= 4294967295.
Proof.
  open_ready. pose proof (Bitcoin.envIxBounded (extBase e)) as HBd. fold tx in HBd.
  pose proof (Int.unsigned_range_2 niv) as HV. change Int.max_unsigned with 4294967295 in HV.
  rewrite HLi in HBd. lia.
Qed.

Theorem ready_current_index : bitcoin_current_index_env_rep m env (extBase e).
Proof.
  open_ready. exists bD, oD, (Int64.repr (Z.of_nat (Bitcoin.envIx (extBase e)))).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact RIx|].
  apply Int64.unsigned_repr. pose proof ready_index_bound.
  change Int64.max_unsigned with 18446744073709551615. lia.
Qed.

(** *** Hash getters *)
Lemma getter_intro (hash_of : ext_environment -> hash256) (pdelta hdelta psz : Z) (bt : block) :
  Mem.load Mptr m bD (oD + pdelta) = Some (Vptr bt Ptrofs.zero) ->
  uint32_array_at m bt hdelta (hash256_reg (hash_of e)) ->
  0 <= psz <= Ptrofs.max_unsigned ->
  hash_getter_rep hash_of pdelta hdelta psz m env e
    [(bD, oD + pdelta, oD + pdelta + 8); (bt, 0 + hdelta, 0 + hdelta + 32)].
Proof.
  intros HL HA Hp. exists bD, oD, bt, 0.
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact HL|]. split; [rewrite Z.add_0_l; exact HA|reflexivity].
Qed.

Lemma ptr0 : Mem.load Mptr m bD (oD + 0) = Some (Vptr bT Ptrofs.zero).
Proof. open_ready. rewrite Z.add_0_r. exact R0. Qed.
Lemma ptr8 : Mem.load Mptr m bD (oD + 8) = Some (Vptr bE Ptrofs.zero).
Proof. open_ready. exact R8. Qed.
Lemma b432 : 0 <= 432 <= Ptrofs.max_unsigned.
Proof. change Ptrofs.max_unsigned with 18446744073709551615. lia. Qed.
Lemma b176 : 0 <= 176 <= Ptrofs.max_unsigned.
Proof. change Ptrofs.max_unsigned with 18446744073709551615. lia. Qed.

Lemma ready_tx_hashes :
  uint32_array_at m bT 16 (hash256_reg (words_hash_of 3 5 (output_values_of e))) /\
  uint32_array_at m bT 48 (hash256_reg (words_hash_of 5 5 (output_scripts_of e))) /\
  uint32_array_at m bT 80 (hash256_reg (outputs_hash_of e)) /\
  uint32_array_at m bT 112 (hash256_reg (input_outpoints_hash_of e)) /\
  uint32_array_at m bT 144 (hash256_reg (words_hash_of 3 5 (input_values_of e))) /\
  uint32_array_at m bT 176 (hash256_reg (words_hash_of 5 5 (input_scripts_of e))) /\
  uint32_array_at m bT 208 (hash256_reg (input_utxos_hash_of e)) /\
  uint32_array_at m bT 240 (hash256_reg (words_hash_of 2 5 (input_sequences_of e))) /\
  uint32_array_at m bT 272 (hash256_reg (input_annexes_hash_of e)) /\
  uint32_array_at m bT 304 (hash256_reg (words_hash_of 5 5 (input_script_sigs_of e))) /\
  uint32_array_at m bT 336 (hash256_reg (inputs_hash_of e)) /\
  uint32_array_at m bT 368 (hash256_reg (tx_hash_of e)).
Proof.
  pose proof HR as (_ & _ & _ & _ & HB & _ & HD & _).
  exact (tx_cached_hashes e m bT niv nov ver lt txb data val spb HB HD).
Qed.

Lemma ready_tap_hashes :
  uint32_array_at m bE 8 (hash256_reg (tapleaf_hash_of e)) /\
  uint32_array_at m bE 40 (hash256_reg (words_hash_of 5 3 (tappath_of e))) /\
  uint32_array_at m bE 72 (hash256_reg (tap_env_hash_of e)).
Proof.
  pose proof HR as (_ & _ & _ & _ & _ & HTb & _ & HDt).
  exact (tapenv_cached_hashes e m bE nb cb0 kb cmrb pb HTb HDt).
Qed.

Theorem ready_output_values_hash :
  hash_getter_rep (fun e => words_hash_of 3 5 (output_values_of e)) 0 16 432 m env e
    [(bD, oD + 0, oD + 0 + 8); (bT, 0 + 16, 0 + 16 + 32)].
Proof. apply getter_intro; [exact ptr0|exact (proj1 ready_tx_hashes)|exact b432]. Qed.
Theorem ready_output_scripts_hash :
  hash_getter_rep (fun e => words_hash_of 5 5 (output_scripts_of e)) 0 48 432 m env e
    [(bD, oD + 0, oD + 0 + 8); (bT, 0 + 48, 0 + 48 + 32)].
Proof. apply getter_intro; [exact ptr0|exact (proj1 (proj2 ready_tx_hashes))|exact b432]. Qed.
Theorem ready_outputs_hash :
  hash_getter_rep outputs_hash_of 0 80 432 m env e [(bD, oD + 0, oD + 0 + 8); (bT, 0 + 80, 0 + 80 + 32)].
Proof. apply getter_intro; [exact ptr0|exact (proj1 (proj2 (proj2 ready_tx_hashes)))|exact b432]. Qed.
Theorem ready_input_outpoints_hash :
  hash_getter_rep input_outpoints_hash_of 0 112 432 m env e
    [(bD, oD + 0, oD + 0 + 8); (bT, 0 + 112, 0 + 112 + 32)].
Proof. apply getter_intro; [exact ptr0|exact (proj1 (proj2 (proj2 (proj2 ready_tx_hashes))))|exact b432]. Qed.
Theorem ready_input_values_hash :
  hash_getter_rep (fun e => words_hash_of 3 5 (input_values_of e)) 0 144 432 m env e
    [(bD, oD + 0, oD + 0 + 8); (bT, 0 + 144, 0 + 144 + 32)].
Proof.
  apply getter_intro; [exact ptr0|exact (proj1 (proj2 (proj2 (proj2 (proj2 ready_tx_hashes)))))|exact b432].
Qed.
Theorem ready_input_scripts_hash :
  hash_getter_rep (fun e => words_hash_of 5 5 (input_scripts_of e)) 0 176 432 m env e
    [(bD, oD + 0, oD + 0 + 8); (bT, 0 + 176, 0 + 176 + 32)].
Proof.
  apply getter_intro; [exact ptr0|exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 ready_tx_hashes))))))|exact b432].
Qed.
Theorem ready_input_utxos_hash :
  hash_getter_rep input_utxos_hash_of 0 208 432 m env e [(bD, oD + 0, oD + 0 + 8); (bT, 0 + 208, 0 + 208 + 32)].
Proof.
  apply getter_intro; [exact ptr0
    |exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ready_tx_hashes)))))))|exact b432].
Qed.
Theorem ready_input_sequences_hash :
  hash_getter_rep (fun e => words_hash_of 2 5 (input_sequences_of e)) 0 240 432 m env e
    [(bD, oD + 0, oD + 0 + 8); (bT, 0 + 240, 0 + 240 + 32)].
Proof.
  apply getter_intro; [exact ptr0
    |exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ready_tx_hashes))))))))|exact b432].
Qed.
Theorem ready_input_annexes_hash :
  hash_getter_rep input_annexes_hash_of 0 272 432 m env e
    [(bD, oD + 0, oD + 0 + 8); (bT, 0 + 272, 0 + 272 + 32)].
Proof.
  apply getter_intro; [exact ptr0
    |exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ready_tx_hashes)))))))))|exact b432].
Qed.
Theorem ready_input_script_sigs_hash :
  hash_getter_rep (fun e => words_hash_of 5 5 (input_script_sigs_of e)) 0 304 432 m env e
    [(bD, oD + 0, oD + 0 + 8); (bT, 0 + 304, 0 + 304 + 32)].
Proof.
  apply getter_intro; [exact ptr0
    |exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ready_tx_hashes))))))))))
    |exact b432].
Qed.
Theorem ready_inputs_hash :
  hash_getter_rep inputs_hash_of 0 336 432 m env e [(bD, oD + 0, oD + 0 + 8); (bT, 0 + 336, 0 + 336 + 32)].
Proof.
  apply getter_intro; [exact ptr0
    |exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ready_tx_hashes)))))))))))
    |exact b432].
Qed.
Theorem ready_tx_hash :
  hash_getter_rep tx_hash_of 0 368 432 m env e [(bD, oD + 0, oD + 0 + 8); (bT, 0 + 368, 0 + 368 + 32)].
Proof.
  apply getter_intro; [exact ptr0
    |exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ready_tx_hashes)))))))))))
    |exact b432].
Qed.

Theorem ready_tapleaf_hash :
  hash_getter_rep tapleaf_hash_of 8 8 176 m env e [(bD, oD + 8, oD + 8 + 8); (bE, 0 + 8, 0 + 8 + 32)].
Proof. apply getter_intro; [exact ptr8|exact (proj1 ready_tap_hashes)|exact b176]. Qed.
Theorem ready_tappath_hash :
  hash_getter_rep (fun e => words_hash_of 5 3 (tappath_of e)) 8 40 176 m env e
    [(bD, oD + 8, oD + 8 + 8); (bE, 0 + 40, 0 + 40 + 32)].
Proof. apply getter_intro; [exact ptr8|exact (proj1 (proj2 ready_tap_hashes))|exact b176]. Qed.
Theorem ready_tap_env_hash :
  hash_getter_rep tap_env_hash_of 8 72 176 m env e [(bD, oD + 8, oD + 8 + 8); (bE, 0 + 72, 0 + 72 + 32)].
Proof. apply getter_intro; [exact ptr8|exact (proj2 (proj2 ready_tap_hashes))|exact b176]. Qed.

Theorem ready_internal_key :
  hash_getter_rep extInternalKey 8 104 176 m env e [(bD, oD + 8, oD + 8 + 8); (bE, 0 + 104, 0 + 104 + 32)].
Proof.
  apply getter_intro; [exact ptr8| |exact b176].
  open_ready. apply u32_of_nth. intros i Hi. rewrite hash256_len in Hi. rewrite DK. apply TKey, Hi.
Qed.

Theorem ready_sig_all_hash :
  env_hash_rep sig_all_hash_of 16 m env e [(bD, oD + 16, oD + 16 + 32)].
Proof.
  open_ready. exists bD, oD. split; [reflexivity|]. split; [lia|]. split; [lia|].
  split; [exact RSig|reflexivity].
Qed.

(** The transaction id is copied from the raw structure, never computed by
    the C library: that the 32 bytes supplied are the id of the transaction
    is an input requirement. *)
Theorem ready_transaction_id :
  tm_words txb = hash256_reg (extTxid e) ->
  hash_getter_rep extTxid 0 400 432 m env e [(bD, oD + 0, oD + 0 + 8); (bT, 0 + 400, 0 + 400 + 32)].
Proof.
  intros HId. apply getter_intro; [exact ptr0| |exact b432].
  open_ready. apply u32_of_nth. intros i Hi. rewrite hash256_len in Hi. rewrite <- HId. apply G400, Hi.
Qed.

(** *** Taproot scalars *)
Theorem ready_script_cmr :
  bitcoin_script_cmr_env_rep m env (extBase e) [(bD, oD + 8, oD + 16); (bE, 0 + 136, 0 + 168)].
Proof.
  open_ready. exists bD, oD, bE, 0.
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [change Ptrofs.max_unsigned with 18446744073709551615; lia|].
  split; [exact R8|]. split; [|reflexivity].
  rewrite Z.add_0_l. apply u32_of_nth. intros i Hi. rewrite hash256_len in Hi.
  rewrite <- (state_regs_hash (Bitcoin.envScriptCMR (extBase e))), Dc. apply TCmr, Hi.
Qed.

Theorem ready_tapleaf_version :
  bitcoin_tapleaf_version_env_rep m env e [(bD, oD + 8, oD + 16)].
Proof.
  open_ready. exists bD, oD, bE, 0.
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [change Ptrofs.max_unsigned with 18446744073709551615; lia|].
  split; [exact R8|]. split; [|reflexivity].
  rewrite <- (word8_value_small _ (extTapleafVersion_range e)), Dv. exact TVer.
Qed.

(** The path pointer of the allocated taproot environment is null for an
    empty path ([path = NULL] in [mallocTapEnv]); the accepted relation asks
    for a pointer, so it is established for non-empty paths. *)
Theorem ready_tappath :
  0 < Int.unsigned nb ->
  bitcoin_tappath_env_rep m env e
    [(bD, oD + 8, oD + 16); (bE, 0 + 0, 0 + 8); (bE, 176, 176 + 32 * Z.of_nat (length (extTappath e)))].
Proof.
  intros Hnb. open_ready.
  pose proof (Int.unsigned_range_2 nb) as HN. change Int.max_unsigned with 4294967295 in HN.
  pose proof (extTappath_len e) as HPL.
  exists bD, oD, bE, 0, bE, 176.
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [change Ptrofs.max_unsigned with 18446744073709551615; lia|].
  split; [lia|]. split; [change Ptrofs.max_unsigned with 18446744073709551615; lia|].
  split; [exact R8|].
  split.
  { rewrite Z.add_0_l. unfold te_path_value in TP0.
    destruct (Z.eq_dec (Int.unsigned nb) 0) as [E0|_]; [lia|exact TP0]. }
  split.
  { rewrite Z.add_0_l, DLn, Z2Nat.id, Int.repr_unsigned by lia. exact TLen. }
  split; [|reflexivity].
  intros j h Hj. unfold hash_elem_rep. apply u32_of_nth. intros i Hi. rewrite hash256_len in Hi.
  rewrite <- (DP j h Hj).
  assert (Hjn : (j < Z.to_nat (Int.unsigned nb))%nat) by (rewrite <- DLn; apply nth_error_Some; congruence).
  apply TArr; assumption.
Qed.
End Ready.
