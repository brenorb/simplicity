(** The indexed and current-input environment relations of the accepted
    Bitcoin application jets hold for the [txEnv] left by the real builders
    ([env_ready]).  Pure consequences of [env_ready]; the three SHA-based
    jets additionally need the SHA start-up state ([sha_globals_ok]). *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Values Memory.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_uint32_array_init C.jet_sha_add_n_calls C.jet_sha_hash_closed.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_ext_current_spec.
Require Import C.jet_bitcoin_indexed_scalar C.jet_bitcoin_indexed_scalar_jets.
Require Import C.jet_bitcoin_indexed_ptr C.jet_bitcoin_indexed_ptr_jets.
Require Import C.jet_bitcoin_current_jets C.jet_bitcoin_current_ptr_jets.
Require Import C.jet_bitcoin_ext_ptr_jets C.jet_bitcoin_input_value_local C.jet_bitcoin_distance_local.
Require Import C.jet_bitcoin_annex_local C.jet_bitcoin_current_annex_local.
Require Import C.jet_sha_add_n_exec C.jet_bitcoin_input_hash_jet C.jet_bitcoin_input_utxo_hash_jet C.jet_bitcoin_output_hash_jet.
Require Import C.jet_bitcoin_env_tomidstate C.jet_bitcoin_env_hashbuffer.
Require Import C.jet_bitcoin_env_tx_indefs C.jet_bitcoin_env_tx.
Require Import C.jet_bitcoin_env_tx_link C.jet_bitcoin_env_build C.jet_bitcoin_env_relations.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 120.

Section Ready.
Variables (m : mem) (bD : block) (oD : Z) (bT bE : block) (e : ext_environment).
Variables (niv nov ver lt : int) (txb : list int) (data : nat -> in_data) (val : nat -> int64).
Variables (spb : nat -> list int) (nb cb0 : int) (kb cmrb : list int) (pb : nat -> list int).
Hypothesis HR : env_ready m bD oD bT bE e niv nov ver lt txb data val spb nb cb0 kb cmrb pb.
Hypothesis HoD : 0 <= oD /\ oD + 56 <= Ptrofs.max_unsigned.

Let env := Vptr bD (Ptrofs.repr oD).
Let ni := Int.unsigned niv.
Let no := Int.unsigned nov.
Let OB := 488 + 160 * ni.

Lemma rng_ni : 0 <= ni <= 4294967295.
Proof. unfold ni. pose proof (Int.unsigned_range_2 niv) as H. change Int.max_unsigned with 4294967295 in H. exact H. Qed.
Lemma rng_no : 0 <= no <= 4294967295.
Proof. unfold no. pose proof (Int.unsigned_range_2 nov) as H. change Int.max_unsigned with 4294967295 in H. exact H. Qed.

Lemma len_in : Z.of_nat (length (sigTxIn (Bitcoin.envTx (extBase e)))) = ni.
Proof. destruct HR as (_ & _ & _ & _ & _ & _ & (HLi & _) & _). rewrite HLi. pose proof rng_ni. unfold ni in *. lia. Qed.
Lemma len_out : Z.of_nat (length (sigTxOut (Bitcoin.envTx (extBase e)))) = no.
Proof. destruct HR as (_ & _ & _ & _ & _ & _ & (_ & HLo & _) & _). rewrite HLo. pose proof rng_no. unfold no in *. lia. Qed.

Lemma env_ptr : Mem.load Mptr m bD (oD + 0) = Some (Vptr bT (Ptrofs.repr 0)).
Proof. destruct HR as (R0 & _). rewrite Z.add_0_r. exact R0. Qed.
Lemma env_ix : Mem.load Mint64 m bD (oD + 48) = Some (Vlong (Int64.repr (Z.of_nat (Bitcoin.envIx (extBase e))))).
Proof. destruct HR as (_ & _ & _ & RIx & _). exact RIx. Qed.
Lemma ix_value : Int64.unsigned (Int64.repr (Z.of_nat (Bitcoin.envIx (extBase e)))) = Z.of_nat (Bitcoin.envIx (extBase e)).
Proof.
  apply Int64.unsigned_repr.
  pose proof (ready_index_bound m bD oD bT bE e niv nov ver lt txb data val spb nb cb0 kb cmrb pb HR).
  change Int64.max_unsigned with 18446744073709551615. lia.
Qed.

Lemma tx_fields :
  Mem.load Mptr m bT (0 + 0) = Some (Vptr bT (Ptrofs.repr 488)) /\
  Mem.load Mptr m bT (0 + 8) = Some (Vptr bT (Ptrofs.repr OB)) /\
  Mem.load Mint64 m bT (0 + 448) = Some (Vlong (Int64.repr ni)) /\
  Mem.load Mint64 m bT (0 + 456) = Some (Vlong (Int64.repr no)) /\
  Mem.load Mint64 m bT (0 + 464) = Some (Vlong (Int64.repr (Int.unsigned ver))) /\
  (forall j, (Z.of_nat j < ni) -> in_rec m bT (488 + 160 * Z.of_nat j) (data j)) /\
  (forall j, (Z.of_nat j < no) ->
     Mem.load Mint64 m bT (OB + 40 * Z.of_nat j) = Some (Vlong (val j)) /\
     forall i, (i < 8)%nat ->
       Mem.load Mint32 m bT (OB + 40 * Z.of_nat j + 8 + 4 * Z.of_nat i) =
         Some (Vint (nth i (hash_buffer_regs (spb j)) Int.zero))).
Proof.
  destruct HR as (_ & _ & _ & _ & HB & _). unfold tx_built in HB. cbv beta zeta in HB.
  destruct HB as (B0 & B8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B448 & B456 & B464 &
                  _ & _ & BIn & BOut).
  pose proof rng_ni. pose proof rng_no.
  repeat (split; [assumption|]). split.
  - intros j Hj. apply BIn. unfold ni in *. lia.
  - intros j Hj. apply BOut. unfold no in *. lia.
Qed.

Lemma cnt_in : Int64.unsigned (Int64.repr ni) = ni.
Proof. apply Int64.unsigned_repr. pose proof rng_ni. change Int64.max_unsigned with 18446744073709551615. lia. Qed.
Lemma cnt_out : Int64.unsigned (Int64.repr no) = no.
Proof. apply Int64.unsigned_repr. pose proof rng_no. change Int64.max_unsigned with 18446744073709551615. lia. Qed.

Lemma bound_in : 0 <= 488 /\ 488 + 160 * ni <= Ptrofs.max_unsigned.
Proof. pose proof rng_ni. change Ptrofs.max_unsigned with 18446744073709551615. lia. Qed.
Lemma bound_out : 0 <= OB /\ OB + 40 * no <= Ptrofs.max_unsigned.
Proof. pose proof rng_ni. pose proof rng_no. unfold OB. change Ptrofs.max_unsigned with 18446744073709551615. lia. Qed.
Lemma max488' : 0 + 488 <= Ptrofs.max_unsigned.
Proof. change Ptrofs.max_unsigned with 18446744073709551615. lia. Qed.

(** The record of input [j], for an index valid in any of the per-input lists. *)
Lemma rec_of {A} (l : list A) j (x : A) :
  Z.of_nat (length l) = ni -> nth_error l j = Some x -> in_rec m bT (488 + 160 * Z.of_nat j) (data j).
Proof.
  intros HL Hj. apply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 tx_fields)))))).
  assert (j < length l)%nat by (apply nth_error_Some; congruence). lia.
Qed.

Lemma len_sh : Z.of_nat (length (extInScriptHash e)) = ni.
Proof. rewrite (extInScriptHash_len e). exact len_in. Qed.
Lemma len_ss : Z.of_nat (length (extInScriptSigHash e)) = ni.
Proof. rewrite (extInScriptSigHash_len e). exact len_in. Qed.
Lemma len_an : Z.of_nat (length (extInAnnexHash e)) = ni.
Proof. rewrite (extInAnnexHash_len e). exact len_in. Qed.

Lemma desc_in j x : nth_error (sigTxIn (Bitcoin.envTx (extBase e))) j = Some x ->
  d_val (data j) = sigTxiValue x /\ d_sq (data j) = sigTxiSequence x /\
  d_ix (data j) = opIndex (sigTxiPreviousOutpoint x) /\
  tm_words (d_txb (data j)) = hash256_reg (opHash (sigTxiPreviousOutpoint x)).
Proof. destruct HR as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & HI & _) & _). apply HI. Qed.

(** *** Elements *)
Lemma el_sequence j x : nth_error (sigTxIn (Bitcoin.envTx (extBase e))) j = Some x ->
  Mem.load Mint64 m bT (488 + 160 * Z.of_nat j + 144) = Some (Vlong (Int64.repr (Int.unsigned (sigTxiSequence x)))).
Proof.
  intros Hj. destruct (rec_of _ j x len_in Hj) as (_ & _ & _ & _ & _ & _ & R7 & _).
  destruct (desc_in j x Hj) as (_ & E2 & _). rewrite <- E2. exact R7.
Qed.

Lemma el_value j x : nth_error (sigTxIn (Bitcoin.envTx (extBase e))) j = Some x ->
  Mem.load Mint64 m bT (488 + 160 * Z.of_nat j + 104) = Some (Vlong (sigTxiValue x)).
Proof.
  intros Hj. destruct (rec_of _ j x len_in Hj) as (_ & _ & _ & _ & R5 & _).
  destruct (desc_in j x Hj) as (E1 & _). rewrite <- E1. exact R5.
Qed.

Lemma el_outpoint j x : nth_error (sigTxIn (Bitcoin.envTx (extBase e))) j = Some x ->
  outpoint_rep m bT (488 + 160 * Z.of_nat j + 64) x.
Proof.
  intros Hj. destruct (rec_of _ j x len_in Hj) as (_ & _ & R3 & R4 & _).
  destruct (desc_in j x Hj) as (_ & _ & E3 & E4). split.
  - unfold outpoint_words. apply u32_of_nth. intros i Hi. rewrite hash256_len in Hi. rewrite <- E4. apply R3, Hi.
  - unfold outpoint_ix. rewrite <- E3. replace (488 + 160 * Z.of_nat j + 64 + 32) with (488 + 160 * Z.of_nat j + 96) by lia.
    exact R4.
Qed.

Lemma el_script_hash j h : nth_error (extInScriptHash e) j = Some h ->
  hash_elem_rep m bT (488 + 160 * Z.of_nat j + 112) h.
Proof.
  intros Hj. destruct (rec_of _ j h len_sh Hj) as (_ & _ & _ & _ & _ & R6 & _).
  destruct HR as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & HSc & _) & _).
  unfold hash_elem_rep. apply u32_of_nth. intros i Hi. rewrite hash256_len in Hi.
  rewrite <- (HSc j h Hj). apply R6, Hi.
Qed.

Lemma el_script_sig_hash j h : nth_error (extInScriptSigHash e) j = Some h ->
  hash_elem_rep m bT (488 + 160 * Z.of_nat j + 32) h.
Proof.
  intros Hj. destruct (rec_of _ j h len_ss Hj) as (_ & R2 & _).
  destruct HR as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & HSs & _) & _).
  unfold hash_elem_rep. apply u32_of_nth. intros i Hi. rewrite hash256_len in Hi.
  rewrite <- (HSs j h Hj). apply R2, Hi.
Qed.

Lemma el_annex j o : nth_error (extInAnnexHash e) j = Some o ->
  annex_elem_rep m bT (488 + 160 * Z.of_nat j) o.
Proof.
  intros Hj. destruct (rec_of _ j o len_an Hj) as (R1 & _ & _ & _ & _ & _ & _ & R8).
  destruct HR as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & HAn & _) & _).
  pose proof (HAn j o Hj) as Ha. split.
  - destruct o as [h|]; [destruct Ha as [E1 _]|]; rewrite ?E1, ?Ha in R8; exact R8.
  - intros h ->. destruct Ha as [_ E2]. unfold hash_elem_rep. apply u32_of_nth.
    intros i Hi. rewrite hash256_len in Hi. rewrite <- E2.
    replace (488 + 160 * Z.of_nat j + 4 * Z.of_nat i) with (488 + 160 * Z.of_nat j + 4 * Z.of_nat i) by lia.
    apply R1, Hi.
Qed.

Lemma desc_out j o : nth_error (sigTxOut (Bitcoin.envTx (extBase e))) j = Some o ->
  val j = txoValue o /\ hash_buffer_regs (spb j) = hash256_reg (byteStringHash (txoScript o)).
Proof. destruct HR as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & HO) & _). apply HO. Qed.

Lemma out_at j o : nth_error (sigTxOut (Bitcoin.envTx (extBase e))) j = Some o ->
  Mem.load Mint64 m bT (OB + 40 * Z.of_nat j) = Some (Vlong (txoValue o)) /\
  uint32_array_at m bT (OB + 40 * Z.of_nat j + 8) (hash256_reg (byteStringHash (txoScript o))).
Proof.
  intros Hj. destruct (desc_out j o Hj) as (E1 & E2).
  assert (Hlt : Z.of_nat j < no).
  { rewrite <- len_out. assert (j < length (sigTxOut (Bitcoin.envTx (extBase e))))%nat
      by (apply nth_error_Some; congruence). lia. }
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 tx_fields))))) j Hlt) as (HV & HS). split.
  - rewrite <- E1. exact HV.
  - apply u32_of_nth. intros i Hi. rewrite hash256_len in Hi. rewrite <- E2. apply HS, Hi.
Qed.

(** *** Input relations *)
Theorem ready_input_sequence : exists fp,
  indexed_scalar_rep (fun e => sigTxIn (Bitcoin.envTx e)) (fun txi => Int.unsigned (sigTxiSequence txi))
    160 144 0 448 m env (extBase e) fp.
Proof.
  eexists. exists bD, oD, bT, 0, bT, 488, (Int64.repr ni).
  pose proof bound_in. pose proof tx_fields as (F0 & _ & F448 & _).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact max488'|].
  split; [lia|]. split; [rewrite len_in; lia|]. split; [exact env_ptr|]. split; [exact F0|].
  split; [exact F448|]. split; [rewrite len_in; exact cnt_in|].
  split; [intros j x Hj; exact (el_sequence j x Hj)|reflexivity].
Qed.

Theorem ready_input_value : exists fp, bitcoin_input_value_env_rep m env (extBase e) fp.
Proof.
  eexists. exists bD, oD, bT, 0, bT, 488, (Int64.repr ni).
  pose proof bound_in. pose proof tx_fields as (F0 & _ & F448 & _).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact max488'|].
  split; [lia|]. split; [rewrite len_in; lia|]. split; [exact env_ptr|]. split; [exact F0|].
  split; [exact F448|]. split; [rewrite len_in; exact cnt_in|].
  split; [intros j x Hj; exact (el_value j x Hj)|reflexivity].
Qed.

Theorem ready_input_prev_outpoint : exists fp,
  indexed_ptr_rep (fun e => sigTxIn (Bitcoin.envTx e)) outpoint_rep 160 64 0 448 m env (extBase e) fp.
Proof.
  eexists. exists bD, oD, bT, 0, bT, 488, (Int64.repr ni).
  pose proof bound_in. pose proof tx_fields as (F0 & _ & F448 & _).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact max488'|].
  split; [lia|]. split; [rewrite len_in; lia|]. split; [exact env_ptr|]. split; [exact F0|].
  split; [exact F448|]. split; [rewrite len_in; exact cnt_in|].
  split; [intros j x Hj; exact (el_outpoint j x Hj)|reflexivity].
Qed.

Theorem ready_input_script_hash : exists fp,
  indexed_ptr_rep extInScriptHash hash_elem_rep 160 112 0 448 m env e fp.
Proof.
  eexists. exists bD, oD, bT, 0, bT, 488, (Int64.repr ni).
  pose proof bound_in. pose proof tx_fields as (F0 & _ & F448 & _).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact max488'|].
  split; [lia|]. split; [rewrite len_sh; lia|]. split; [exact env_ptr|]. split; [exact F0|].
  split; [exact F448|]. split; [rewrite len_sh; exact cnt_in|].
  split; [intros j x Hj; exact (el_script_hash j x Hj)|reflexivity].
Qed.

Theorem ready_input_script_sig_hash : exists fp,
  indexed_ptr_rep extInScriptSigHash hash_elem_rep 160 32 0 448 m env e fp.
Proof.
  eexists. exists bD, oD, bT, 0, bT, 488, (Int64.repr ni).
  pose proof bound_in. pose proof tx_fields as (F0 & _ & F448 & _).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact max488'|].
  split; [lia|]. split; [rewrite len_ss; lia|]. split; [exact env_ptr|]. split; [exact F0|].
  split; [exact F448|]. split; [rewrite len_ss; exact cnt_in|].
  split; [intros j x Hj; exact (el_script_sig_hash j x Hj)|reflexivity].
Qed.

Theorem ready_input_annex_hash : exists fp, bitcoin_input_annex_hash_env_rep m env e fp.
Proof.
  eexists. exists bD, oD, bT, 0, bT, 488, (Int64.repr ni).
  pose proof bound_in. pose proof tx_fields as (F0 & _ & F448 & _).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact max488'|].
  split; [lia|]. split; [rewrite len_an; lia|]. split; [exact env_ptr|]. split; [exact F0|].
  split; [exact F448|]. split; [rewrite len_an; exact cnt_in|].
  split; [intros j x Hj; exact (el_annex j x Hj)|reflexivity].
Qed.

(** *** Current-input relations *)
Theorem ready_current_value :
  current_scalar_rep (fun e => sigTxIn (Bitcoin.envTx e)) (fun txi => Int64.unsigned (sigTxiValue txi))
    160 104 0 448 m env (extBase e).
Proof.
  exists bD, oD, bT, 0, bT, 488, (Int64.repr ni), (Int64.repr (Z.of_nat (Bitcoin.envIx (extBase e)))).
  pose proof bound_in. pose proof tx_fields as (F0 & _ & F448 & _).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact max488'|].
  split; [lia|]. split; [rewrite len_in; lia|]. split; [exact env_ptr|]. split; [exact F0|].
  split; [exact F448|]. split; [exact env_ix|]. split; [rewrite len_in; exact cnt_in|].
  split; [exact ix_value|].
  intros j x Hj. rewrite Int64.repr_unsigned. exact (el_value j x Hj).
Qed.

Theorem ready_current_sequence :
  current_scalar_rep (fun e => sigTxIn (Bitcoin.envTx e)) (fun txi => Int.unsigned (sigTxiSequence txi))
    160 144 0 448 m env (extBase e).
Proof.
  exists bD, oD, bT, 0, bT, 488, (Int64.repr ni), (Int64.repr (Z.of_nat (Bitcoin.envIx (extBase e)))).
  pose proof bound_in. pose proof tx_fields as (F0 & _ & F448 & _).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact max488'|].
  split; [lia|]. split; [rewrite len_in; lia|]. split; [exact env_ptr|]. split; [exact F0|].
  split; [exact F448|]. split; [exact env_ix|]. split; [rewrite len_in; exact cnt_in|].
  split; [exact ix_value|].
  intros j x Hj. exact (el_sequence j x Hj).
Qed.

Theorem ready_current_prev_outpoint : exists fp,
  current_ptr_rep (fun e => sigTxIn (Bitcoin.envTx e)) Bitcoin.envIx outpoint_rep 160 64 0 448 m env (extBase e) fp.
Proof.
  eexists. exists bD, oD, bT, 0, bT, 488, (Int64.repr ni), (Int64.repr (Z.of_nat (Bitcoin.envIx (extBase e)))).
  pose proof bound_in. pose proof tx_fields as (F0 & _ & F448 & _).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact max488'|].
  split; [lia|]. split; [rewrite len_in; lia|]. split; [exact env_ptr|]. split; [exact F0|].
  split; [exact F448|]. split; [exact env_ix|]. split; [rewrite len_in; exact cnt_in|].
  split; [exact ix_value|].
  split; [intros j x Hj; exact (el_outpoint j x Hj)|reflexivity].
Qed.

Theorem ready_current_script_hash : exists fp,
  current_ptr_rep extInScriptHash ext_ix hash_elem_rep 160 112 0 448 m env e fp.
Proof.
  eexists. exists bD, oD, bT, 0, bT, 488, (Int64.repr ni), (Int64.repr (Z.of_nat (Bitcoin.envIx (extBase e)))).
  pose proof bound_in. pose proof tx_fields as (F0 & _ & F448 & _).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact max488'|].
  split; [lia|]. split; [rewrite len_sh; lia|]. split; [exact env_ptr|]. split; [exact F0|].
  split; [exact F448|]. split; [exact env_ix|]. split; [rewrite len_sh; exact cnt_in|].
  split; [exact ix_value|].
  split; [intros j x Hj; exact (el_script_hash j x Hj)|reflexivity].
Qed.

Theorem ready_current_script_sig_hash : exists fp,
  current_ptr_rep extInScriptSigHash ext_ix hash_elem_rep 160 32 0 448 m env e fp.
Proof.
  eexists. exists bD, oD, bT, 0, bT, 488, (Int64.repr ni), (Int64.repr (Z.of_nat (Bitcoin.envIx (extBase e)))).
  pose proof bound_in. pose proof tx_fields as (F0 & _ & F448 & _).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact max488'|].
  split; [lia|]. split; [rewrite len_ss; lia|]. split; [exact env_ptr|]. split; [exact F0|].
  split; [exact F448|]. split; [exact env_ix|]. split; [rewrite len_ss; exact cnt_in|].
  split; [exact ix_value|].
  split; [intros j x Hj; exact (el_script_sig_hash j x Hj)|reflexivity].
Qed.

Theorem ready_current_annex_hash : exists fp, bitcoin_current_annex_hash_env_rep m env e fp.
Proof.
  eexists. exists bD, oD, bT, 0, bT, 488, (Int64.repr ni), (Int64.repr (Z.of_nat (Bitcoin.envIx (extBase e)))).
  pose proof bound_in. pose proof tx_fields as (F0 & _ & F448 & _).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact max488'|].
  split; [lia|]. split; [rewrite len_an; lia|]. split; [exact env_ptr|]. split; [exact F0|].
  split; [exact F448|]. split; [exact env_ix|]. split; [rewrite len_an; exact cnt_in|].
  split; [exact ix_value|].
  split; [intros j x Hj; exact (el_annex j x Hj)|reflexivity].
Qed.

Theorem ready_distance : bitcoin_distance_env_rep m env (extBase e).
Proof.
  exists bD, oD, bT, 0, bT, 488, (Int64.repr ni), (Int64.repr (Z.of_nat (Bitcoin.envIx (extBase e)))),
    (Int64.repr (Int.unsigned ver)).
  pose proof bound_in. pose proof tx_fields as (F0 & _ & F448 & _ & F464 & _).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact max488'|].
  split; [lia|]. split; [rewrite len_in; lia|]. split; [exact env_ptr|]. split; [exact F0|].
  split; [exact F448|]. split; [exact F464|]. split; [exact env_ix|].
  split; [rewrite len_in; exact cnt_in|]. split; [exact ix_value|].
  split.
  { destruct HR as (_ & _ & _ & _ & _ & _ & (_ & _ & Ev & _) & _). rewrite Ev. apply repr32_unsigned. }
  intros j x Hj. exact (el_sequence j x Hj).
Qed.

(** *** Output relations *)
Theorem ready_output_value : exists fp,
  indexed_scalar_rep (fun e => sigTxOut (Bitcoin.envTx e)) (fun txo => Int64.signed (txoValue txo))
    40 0 8 456 m env (extBase e) fp.
Proof.
  eexists. exists bD, oD, bT, 0, bT, OB, (Int64.repr no).
  pose proof bound_out. pose proof tx_fields as (_ & F8 & _ & F456 & _).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact max488'|].
  split; [lia|]. split; [rewrite len_out; lia|]. split; [exact env_ptr|]. split; [exact F8|].
  split; [exact F456|]. split; [rewrite len_out; exact cnt_out|].
  split; [|reflexivity].
  intros j o Hj. rewrite Int64.repr_signed, Z.add_0_r. exact (proj1 (out_at j o Hj)).
Qed.

Theorem ready_output_script_hash : exists fp,
  indexed_ptr_rep (fun e => sigTxOut (Bitcoin.envTx e))
    (fun m b ofs txo => uint32_array_at m b ofs (script_hash_words txo)) 40 8 8 456 m env (extBase e) fp.
Proof.
  eexists. exists bD, oD, bT, 0, bT, OB, (Int64.repr no).
  pose proof bound_out. pose proof tx_fields as (_ & F8 & _ & F456 & _).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact max488'|].
  split; [lia|]. split; [rewrite len_out; lia|]. split; [exact env_ptr|]. split; [exact F8|].
  split; [exact F456|]. split; [rewrite len_out; exact cnt_out|].
  split; [|reflexivity].
  intros j o Hj. exact (proj2 (out_at j o Hj)).
Qed.

(** *** The SHA-based element hashes

    These three jets run SHA code, so their relations also carry the SHA
    start-up state [sha_globals_ok] (dispatch pointer and maximum counter),
    which is not part of the environment structure. *)
Theorem ready_input_hash : sha_globals_ok m -> exists fp, input_hash_rep m env e fp.
Proof.
  intros HG. eexists. exists bD, oD, bT, 0, bT, 488, (Int64.repr ni).
  pose proof bound_in. pose proof tx_fields as (F0 & _ & F448 & _).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact max488'|].
  split; [lia|]. split; [rewrite len_in; lia|]. split; [exact env_ptr|]. split; [exact F0|].
  split; [exact F448|]. split; [rewrite len_in; exact cnt_in|].
  split; [|split; [exact HG|reflexivity]].
  intros j txi ax Hj Ha.
  destruct (el_outpoint j txi Hj) as (O1 & O2). destruct (el_annex j ax Ha) as (A1 & A2).
  split; [exact O1|].
  split.
  { replace (488 + 160 * Z.of_nat j + 96) with (488 + 160 * Z.of_nat j + 64 + 32) by lia. exact O2. }
  split; [exact (el_sequence j txi Hj)|].
  split; [destruct ax; exact A1|].
  intros h Hh. rewrite Z.add_0_r. exact (A2 h Hh).
Qed.

Theorem ready_input_utxo_hash : sha_globals_ok m -> exists fp, input_utxo_hash_rep m env e fp.
Proof.
  intros HG. eexists. exists bD, oD, bT, 0, bT, 488, (Int64.repr ni).
  pose proof bound_in. pose proof tx_fields as (F0 & _ & F448 & _).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact max488'|].
  split; [lia|]. split; [rewrite len_in; lia|]. split; [exact env_ptr|]. split; [exact F0|].
  split; [exact F448|]. split; [rewrite len_in; exact cnt_in|].
  split; [|split; [exact HG|reflexivity]].
  intros j txi sh Hj Hs. split; [exact (el_value j txi Hj)|].
  replace (488 + 160 * Z.of_nat j + 104 + 8) with (488 + 160 * Z.of_nat j + 112) by lia.
  exact (el_script_hash j sh Hs).
Qed.

Theorem ready_output_hash : sha_globals_ok m -> exists fp, output_hash_rep m env e fp.
Proof.
  intros HG. eexists. exists bD, oD, bT, 0, bT, OB, (Int64.repr no).
  pose proof bound_out. pose proof tx_fields as (_ & F8 & _ & F456 & _).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact max488'|].
  split; [lia|]. split; [rewrite len_out; lia|]. split; [exact env_ptr|]. split; [exact F8|].
  split; [exact F456|]. split; [rewrite len_out; exact cnt_out|].
  split; [|split; [exact HG|reflexivity]].
  intros j o Hj. exact (out_at j o Hj).
Qed.
End Ready.
