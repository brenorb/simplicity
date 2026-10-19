(** [simplicity_bitcoin_mallocTransaction]: the shape of the input block --
    eight context initialisations, the input loop, six finalisations and the
    two derived hashes -- and the eight live contexts after the
    initialisations. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_sha256_iv_init C.jet_bitmachine_rep.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_add_n_init C.jet_sha_ctx_abs.
Require Import C.jet_sha_uchars_prep C.jet_sha_uchars_exec.
Require Import C.jet_bitcoin_env_field_eval C.jet_bitcoin_env_ctxo C.jet_bitcoin_env_ctxs.
Require Import C.jet_bitcoin_env_tapenv_prelude C.jet_bitcoin_env_tx_prelude C.jet_bitcoin_env_tx_fill.
Require Import C.jet_bitcoin_env_tx_init C.jet_bitcoin_env_tx_txid.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

(** The eight input contexts: result temporary, context, member, offset. *)
Definition in_specs : list (ident * ident * ident * Z) :=
  [(__res__11, _ctx_inputOutpointsHash, _inputOutpointsHash, 112);
   (__res__10, _ctx_inputValuesHash, _inputValuesHash, 144);
   (__res__9, _ctx_inputScriptsHash, _inputScriptsHash, 176);
   (__res__8, _ctx_inputUTXOsHash, _inputUTXOsHash, 208);
   (__res__7, _ctx_inputSequencesHash, _inputSequencesHash, 240);
   (__res__6, _ctx_inputAnnexesHash, _inputAnnexesHash, 272);
   (__res__5, _ctx_inputScriptSigsHash, _inputScriptSigsHash, 304);
   (__res__4, _ctx_inputsHash, _inputsHash, 336)].

Definition mk_items (specs : list (ident * ident * ident * Z)) (bl : list (block * block)) : list init_item :=
  map (fun x => let '((r, c, f, d), (bR, bC)) := x in (r, c, f, d, bR, bC)) (combine specs bl).

(** [mt_rest3 = Ssequence mt_inblock mt_rest4]; the input block is the eight
    initialisations followed by [mt_in_tail] (loop, finalisations, derived
    hashes). *)
Definition mt_inblock : statement :=
  ltac:(let b := eval cbv delta [mt_rest3] in mt_rest3 in
        lazymatch b with Ssequence ?s _ => exact s end).
Definition mt_rest4 : statement :=
  ltac:(let b := eval cbv delta [mt_rest3] in mt_rest3 in
        lazymatch b with Ssequence _ ?r => exact r end).
Definition mt_in_tail : statement :=
  ltac:(let b := eval cbv delta [mt_inblock] in mt_inblock in
        let r := drop_seq 8%nat b in exact r).

Lemma mt_inblock_shape (bl : list (block * block)) : length bl = 8%nat ->
  mt_inblock = inits_stmt (mk_items in_specs bl) mt_in_tail.
Proof.
  intros H. do 9 (destruct bl as [|[? ?] bl]; try discriminate). reflexivity.
Qed.
