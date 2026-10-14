(** [simplicity_bitcoin_mallocTransaction], the output block: statement
    shape, pointer arithmetic, and the loop invariant
      for (i = 0; i < tx->numOutputs; ++i) {
        copyOutput(&output[i], &rawTx->output[i]);
        tx->totalOutputValue += output[i].value;
        sha256_u64be(&ctx_outputValuesHash, output[i].value);
        sha256_hash(&ctx_outputScriptsHash, &output[i].scriptPubKey); } *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_sha256_iv_init C.jet_bitmachine_rep.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_add_n_init C.jet_sha_ctx8_model.
Require Import C.jet_sha_be32_write C.jet_sha_be64_exec C.jet_sha_uchars_prep C.jet_sha_uchars_exec C.jet_sha_ctx_abs.
Require Import C.jet_bitcoin_env_field_eval C.jet_bitcoin_env_hashbuffer C.jet_bitcoin_env_ctxo.
Require Import C.jet_bitcoin_env_ctxs C.jet_bitcoin_env_ctxs_ops C.jet_bitcoin_env_tapenv_prelude.
Require Import C.jet_bitcoin_env_tapenv_tail C.jet_bitcoin_env_copyoutput C.jet_bitcoin_env_copyinput.
Require Import C.jet_bitcoin_env_tx_prelude C.jet_bitcoin_env_tx_fill C.jet_bitcoin_env_tx_init.
Require Import C.jet_bitcoin_env_tx_txid C.jet_bitcoin_env_tx_inblock C.jet_bitcoin_env_tx_txhash.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Definition out_specs : list (ident * ident * ident * Z) :=
  [(__res__3, _ctx_outputValuesHash, _outputValuesHash, 16);
   (__res__2, _ctx_outputScriptsHash, _outputScriptsHash, 48);
   (__res__1, _ctx_outputsHash, _outputsHash, 80)].

Definition mt_out_tail : statement :=
  ltac:(let b := eval cbv delta [mt_outblock] in mt_outblock in
        let r := drop_seq 3%nat b in exact r).

Lemma mt_outblock_shape (bl : list (block * block)) : length bl = 3%nat ->
  mt_outblock = inits_stmt (mk_items out_specs bl) mt_out_tail.
Proof. intros H. do 4 (destruct bl as [|[? ?] bl]; try discriminate). reflexivity. Qed.

Definition mt_out_s1 : statement :=
  ltac:(let b := eval cbv delta [mt_out_tail] in mt_out_tail in
        lazymatch b with Ssequence (Ssequence _ (Sloop ?s1 _)) _ => exact s1 end).
Definition mt_out_s2 : statement :=
  ltac:(let b := eval cbv delta [mt_out_tail] in mt_out_tail in
        lazymatch b with Ssequence (Ssequence _ (Sloop _ ?s2)) _ => exact s2 end).
Definition mt_out_fin : statement :=
  ltac:(let b := eval cbv delta [mt_out_tail] in mt_out_tail in
        lazymatch b with Ssequence _ ?f => exact f end).

Lemma mt_out_tail_shape :
  mt_out_tail = Ssequence (Ssequence (Sset _i__1 (Ecast (Econst_int (Int.repr 0) tint) tulong))
                                      (Sloop mt_out_s1 mt_out_s2)) mt_out_fin.
Proof. reflexivity. Qed.

Lemma envu_rawTx_output : envu_field_at _rawBitcoinTransaction _output 16.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.

Lemma mt_sizeof_SOUT_Z : sizeof sha_ge SOUT = 40.
Proof. vm_compute; reflexivity. Qed.
Lemma mt_sizeof_ROUT_Z : sizeof sha_ge ROUT = 24.
Proof. vm_compute; reflexivity. Qed.

(** Separation of a context list depends only on blocks and output offsets. *)
Lemma ctxs_sep_shape bA (cs cs' : list ctx_entry) :
  map (fun c => (ctx_block c, ctx_out c)) cs' = map (fun c => (ctx_block c, ctx_out c)) cs ->
  ctxs_sep bA cs -> ctxs_sep bA cs'.
Proof.
  intros HM (NG & NM & H1 & H2).
  assert (HN : forall k c', nth_error cs' k = Some c' ->
    exists c, nth_error cs k = Some c /\ ctx_block c = ctx_block c' /\ ctx_out c = ctx_out c').
  { intros k c' Hk.
    pose proof (map_nth_error (fun c => (ctx_block c, ctx_out c)) k cs' Hk) as HE. rewrite HM in HE.
    rewrite nth_error_map in HE. destruct (nth_error cs k) as [c|]; [|discriminate].
    exists c. split; [reflexivity|]. cbn in HE. injection HE as E1 E2. split; assumption. }
  split; [exact NG|]. split; [exact NM|]. split.
  - intros k c' Hk. destruct (HN k c' Hk) as (c & Hc & <- & <-). exact (H1 k c Hc).
  - intros i j ci cj Hi Hj Hij. destruct (HN i ci Hi) as (c1 & Hc1 & <- & <-).
    destruct (HN j cj Hj) as (c2 & Hc2 & <- & <-). exact (H2 i j c1 c2 Hc1 Hc2 Hij).
Qed.

Lemma i64_add_repr a b : 0 <= a <= 1000000000000 -> 0 <= b <= 1000000000000 ->
  Int64.add (Int64.repr a) (Int64.repr b) = Int64.repr (a + b).
Proof.
  intros Ha Hb. unfold Int64.add.
  rewrite !Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia). reflexivity.
Qed.

Lemma i64_ltu_repr a b : 0 <= a <= 1000000000000 -> 0 <= b <= 1000000000000 ->
  Int64.ltu (Int64.repr a) (Int64.repr b) = if zlt a b then true else false.
Proof.
  intros Ha Hb. unfold Int64.ltu.
  rewrite !Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia). reflexivity.
Qed.

(** [base + i] for an array of [sz]-byte elements at offset [ob] of a block. *)
Lemma ptr_index_long ob sz k : 0 <= ob -> 0 <= sz <= 1000 -> 0 <= k <= 4294967295 ->
  ob + sz * k <= 18446744073709551615 ->
  Ptrofs.add (Ptrofs.repr ob) (Ptrofs.mul (Ptrofs.repr sz) (Ptrofs.of_int64 (Int64.repr k))) =
    Ptrofs.repr (ob + sz * k).
Proof.
  intros Ho Hs Hk Hb. unfold Ptrofs.of_int64.
  rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
  unfold Ptrofs.add, Ptrofs.mul.
  rewrite (Ptrofs.unsigned_repr sz), (Ptrofs.unsigned_repr k), (Ptrofs.unsigned_repr ob)
    by (change Ptrofs.max_unsigned with 18446744073709551615; lia).
  rewrite Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615; nia). reflexivity.
Qed.
