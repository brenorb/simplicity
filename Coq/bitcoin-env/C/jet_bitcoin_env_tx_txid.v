(** [simplicity_bitcoin_mallocTransaction], third part:
    [sha256_toMidstate(tx->txid.s, rawTx->txid)]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_add_n_init.
Require Import C.jet_env_store_words C.jet_bitcoin_env_field_eval C.jet_bitcoin_env_tomidstate.
Require Import C.jet_bitcoin_env_tapenv_prelude C.jet_bitcoin_env_tapenv_key C.jet_bitcoin_env_tapenv_fill.
Require Import C.jet_bitcoin_env_tx_prelude C.jet_bitcoin_env_tx_fill C.jet_bitcoin_env_tx_init.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

(** The body from the first [sha256_init]. *)
Definition mt_rest3 : statement :=
  ltac:(let b := eval cbv delta [mt_rest2] in mt_rest2 in
        let r := drop_seq 1%nat b in exact r).

Lemma envu_rawTx_txid : envu_field_at _rawBitcoinTransaction _txid 0.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.

Lemma envu_tx_txid : envu_field_at _bitcoinTransaction _txid 400.
Proof. exact (mt_hash_offsets 12 _txid eq_refl). Qed.

Local Opaque sha_ge.

Section Txid.
Variables (e : env) (bA braw btx : block) (oraw : Z) (otx : ptrofs) (txb : list int) (ni : Z).
Hypothesis HeT : e!_sha256_toMidstate = None.
Hypothesis Horaw : 0 <= oraw /\ oraw + 40 <= Ptrofs.max_unsigned.
Hypothesis NAtx : bA <> btx.
Hypothesis Hotx : Ptrofs.unsigned otx + 32 <= Ptrofs.max_unsigned.

Let rawv := Vptr braw (Ptrofs.repr oraw).

Theorem mt_txid le2 m :
  mt_le1 le2 rawv bA ni ->
  Mem.load Mptr m braw oraw = Some (Vptr btx otx) ->
  (forall i, (i < 32)%nat ->
     Mem.load Mint8unsigned m btx (Ptrofs.unsigned otx + Z.of_nat i) = Some (Vint (nth i txb Int.zero))) ->
  Mem.range_perm m bA 400 432 Cur Writable ->
  exists m' le3,
    store_words m bA 400 (tm_words txb) = Some m' /\
    mt_le1 le3 rawv bA ni /\
    (forall t le' mf out,
       Clight2.exec_stmt sha_ge e le3 m' mt_rest3 t le' mf out ->
       Clight2.exec_stmt sha_ge e le2 m mt_rest2 t le' mf out).
Proof.
  intros (HlRaw & HlTx & HlIn & HlOut) HTx HBytes PA.
  set (om := Ptrofs.repr 400).
  assert (Hom : Ptrofs.unsigned om = 400) by reflexivity.
  destruct (eval_sha256_toMidstate bA btx om otx txb NAtx Hotx) with (m := m) as (m' & HSt & HCall).
  { rewrite Hom. change Ptrofs.max_unsigned with 18446744073709551615. lia. }
  { rewrite Hom. exists 100. reflexivity. }
  { exact HBytes. }
  { rewrite Hom. exact PA. }
  rewrite Hom in HSt.
  set (le3 := PTree.set _t'18 (Vptr btx otx) le2).
  exists m', le3. split; [exact HSt|]. split.
  { unfold mt_le1, le3. rewrite !PTree.gso by discriminate. repeat split; assumption. }
  intros t le' mf out HRest.
  change mt_rest2 with (Ssequence (match mt_rest2 with Ssequence s _ => s | _ => Sskip end) mt_rest3).
  eapply exec_Sseq_1 with (t1 := E0) (t2 := t) (le1 := le3) (m1 := m'); [|exact HRest].
  cbv delta [mt_rest2] beta iota.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m).
  - apply exec_Sset. eapply eval_envu_field_value;
      [reflexivity|exact envu_rawTx_txid|reflexivity|apply eval_envu_deref_struct; exact HlRaw|].
    unfold rawv. rewrite envu_ptr_add_repr by lia. apply envu_loadv_repr; [lia|rewrite Z.add_0_r; exact HTx].
  - eapply te_call_toMidstate with (bm := bA) (om := om) (bh := btx) (oh := otx);
      [exact HeT| |reflexivity| |reflexivity|exact HCall].
    + apply ev_tx_mid_s; [|exact envu_tx_txid].
      unfold le3. rewrite PTree.gso by discriminate. exact HlTx.
    + apply eval_Etempvar. apply PTree.gss.
Qed.
End Txid.
