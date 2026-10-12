(** [simplicity_bitcoin_mallocTransaction], the output loop: invariant and
    one iteration.  Conditional on [memcpy_model]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_sha256_iv_init C.jet_bitmachine_rep.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_add_n_init C.jet_sha_ctx8_model.
Require Import C.jet_sha_be32_write C.jet_sha_be64_exec C.jet_sha_uchars_prep C.jet_sha_uchars_exec C.jet_sha_ctx_abs.
Require Import C.jet_bitcoin_env_field_eval C.jet_bitcoin_env_hashbuffer C.jet_bitcoin_env_ctxo.
Require Import C.jet_bitcoin_env_ctxs C.jet_bitcoin_env_ctxs_ops C.jet_bitcoin_env_ctxs_calls.
Require Import C.jet_bitcoin_env_tapenv_prelude C.jet_bitcoin_env_tapenv_tail.
Require Import C.jet_bitcoin_env_copyoutput C.jet_bitcoin_env_copyinput.
Require Import C.jet_bitcoin_env_tx_prelude C.jet_bitcoin_env_tx_fill C.jet_bitcoin_env_tx_init.
Require Import C.jet_bitcoin_env_tx_txid C.jet_bitcoin_env_tx_inblock C.jet_bitcoin_env_tx_txhash.
Require Import C.jet_bitcoin_env_tx_calls C.jet_bitcoin_env_tx_outdefs.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Local Opaque sha_ge.

(** A change of [bA] inside [lo, hi) only keeps the live contexts whose
    output fields lie outside it. *)
Lemma live_other_range m m' bA cs (live : nat -> Prop) lo hi :
  ctxs_live m bA cs live -> ctxs_sep bA cs ->
  (forall j cj, nth_error cs j = Some cj -> live j -> ctx_out cj + 32 <= lo \/ hi <= ctx_out cj) ->
  (forall ch b ofs, Mem.valid_block m b -> (b <> bA \/ ofs + size_chunk ch <= lo \/ hi <= ofs) ->
     Mem.load ch m' b ofs = Mem.load ch m b ofs) ->
  (forall b ofs kk p, Mem.perm m b ofs kk p -> Mem.perm m' b ofs kk p) ->
  ctxs_live m' bA cs live.
Proof.
  intros HC HSep HR HL HP.
  eapply live_other; [exact HC| |exact HP].
  intros j cj ch b ofs Hj Hl Hb.
  destruct (live_valid m bA cs live HC j cj Hj Hl) as (V1 & V2 & V3 & V4).
  destruct HSep as (NG & NM & H1 & _). destruct (H1 j cj Hj) as (D1 & _).
  destruct Hb as [->|[->|[->|[-> Hr]]]].
  - apply HL; [exact V1|left; exact D1].
  - apply HL; [exact V3|left; exact NG].
  - apply HL; [exact V4|left; exact NM].
  - apply HL; [exact V2|right]. destruct (HR j cj Hj Hl); lia.
Qed.

Section OutLoop.
Variable Hmodel : memcpy_model.
Variables (e : env) (bA bCO bCS bCV braw bro : block) (oraw oro ni no : Z).
Variables (val : nat -> int64) (bsp : nat -> block) (osp : nat -> ptrofs) (spb : nat -> list int).
Variables (oldb : block -> Prop) (m0 : mem).

Let rawv := Vptr braw (Ptrofs.repr oraw).
Let OB := 488 + 160 * ni.
Let Nn := Z.to_nat no.

Hypothesis HeCO : e!_ctx_outputsHash = Some (bCO, CTX).
Hypothesis HeCS : e!_ctx_outputScriptsHash = Some (bCS, CTX).
Hypothesis HeCV : e!_ctx_outputValuesHash = Some (bCV, CTX).
Hypothesis HeH : e!_sha256_hash = None.
Hypothesis HeU : e!_sha256_u64be = None.
Hypothesis HeCp : e!_copyOutput = None.
Hypothesis Hni : 0 <= ni <= 4294967295.
Hypothesis Hno : 0 <= no <= 4294967295.
Hypothesis Horaw : 0 <= oraw /\ oraw + 40 <= Ptrofs.max_unsigned.
Hypothesis Horo : 0 <= oro /\ oro + 24 * no <= Ptrofs.max_unsigned.

Fixpoint out_stV (k : nat) : list int * list int :=
  match k with
  | O => ([], sha256_iv_words)
  | S k' => absorb_i (fst (out_stV k')) (snd (out_stV k')) (c_be64_bytes (val k'))
  end.
Fixpoint out_stS (k : nat) : list int * list int :=
  match k with
  | O => ([], sha256_iv_words)
  | S k' => absorb_i (fst (out_stS k')) (snd (out_stS k')) (be_bytes (norm8 (hash_buffer_regs (spb k'))))
  end.
Fixpoint out_tot (k : nat) : int64 :=
  match k with
  | O => Int64.zero
  | S k' => Int64.add (out_tot k') (val k')
  end.

Definition out_cs (k : nat) (oS oV : bool) : list ctx_entry :=
  [(bCO, 80, [], sha256_iv_words, Int64.zero, false);
   (bCS, 48, fst (out_stS k), snd (out_stS k), Int64.repr (32 * Z.of_nat k), oS);
   (bCV, 16, fst (out_stV k), snd (out_stV k), Int64.repr (8 * Z.of_nat k), oV)].

Hypothesis HSepB : ctxs_sep bA (out_cs 0 false false).

Lemma out_sep (cs : list ctx_entry) :
  map (fun c => (ctx_block c, ctx_out c)) cs = [(bCO, 80); (bCS, 48); (bCV, 16)] -> ctxs_sep bA cs.
Proof. intros H. eapply ctxs_sep_shape; [|exact HSepB]. rewrite H. reflexivity. Qed.

Hypothesis Hold : forall b, oldb b -> Mem.valid_block m0 b /\ b <> bA /\ b <> bCO /\ b <> bCS /\ b <> bCV.
Hypothesis HoRaw : oldb braw.
Hypothesis HoRo : oldb bro.
Hypothesis HoSp : forall j, (j < Nn)%nat -> oldb (bsp j).
Hypothesis HRo : Mem.load Mptr m0 braw (oraw + 16) = Some (Vptr bro (Ptrofs.repr oro)).
Hypothesis HVals : forall j, (j < Nn)%nat -> Mem.load Mint64 m0 bro (oro + 24 * Z.of_nat j) = Some (Vlong (val j)).
Hypothesis HBufs : forall j, (j < Nn)%nat ->
  raw_buffer_at m0 bro (oro + 24 * Z.of_nat j + 8) (bsp j) (osp j) (spb j).
Hypothesis PA0 : Mem.range_perm m0 bA 0 (OB + 40 * no) Cur Writable.
Hypothesis VA0 : Mem.valid_block m0 bA.
Hypothesis HNo0 : Mem.load Mint64 m0 bA 456 = Some (Vlong (Int64.repr no)).

Definition out_inv (k : nat) (le : temp_env) (m : mem) : Prop :=
  le!_i__1 = Some (Vlong (Int64.repr (Z.of_nat k))) /\
  le!_tx = Some (Vptr bA Ptrofs.zero) /\
  le!_output = Some (Vptr bA (Ptrofs.repr OB)) /\
  le!_rawTx = Some rawv /\
  (exists oS oV, ctxs_live m bA (out_cs k oS oV) (fun _ => True)) /\
  Mem.load Mint64 m bA 440 = Some (Vlong (out_tot k)) /\
  (forall j, (j < k)%nat ->
     Mem.load Mint64 m bA (OB + 40 * Z.of_nat j) = Some (Vlong (val j)) /\
     forall i, (i < 8)%nat ->
       Mem.load Mint32 m bA (OB + 40 * Z.of_nat j + 8 + 4 * Z.of_nat i) =
         Some (Vint (nth i (hash_buffer_regs (spb j)) Int.zero))) /\
  (forall ch b ofs, oldb b -> Mem.load ch m b ofs = Mem.load ch m0 b ofs) /\
  (forall ch ofs, 0 <= ofs -> ofs + size_chunk ch <= OB ->
     (ofs + size_chunk ch <= 16 \/ (112 <= ofs /\ ofs + size_chunk ch <= 440) \/ 448 <= ofs) ->
     Mem.load ch m bA ofs = Mem.load ch m0 bA ofs) /\
  (forall b ofs kk p, Mem.perm m0 b ofs kk p -> Mem.perm m b ofs kk p) /\
  (forall b, Mem.valid_block m0 b -> Mem.valid_block m b).

Lemma ev_out_i le m k :
  le!_output = Some (Vptr bA (Ptrofs.repr OB)) -> le!_i__1 = Some (Vlong (Int64.repr k)) ->
  0 <= k <= 4294967295 ->
  eval_expr sha_ge e le m (Ebinop Oadd (Etempvar _output (tptr SOUT)) (Etempvar _i__1 tulong) (tptr SOUT))
    (Vptr bA (Ptrofs.repr (OB + 40 * k))).
Proof.
  intros Ho Hi Hk. eapply eval_Ebinop; [apply eval_Etempvar; exact Ho|apply eval_Etempvar; exact Hi|].
  rewrite <- (ptr_index_long OB 40 k) by (unfold OB; lia). rewrite <- mt_sizeof_SOUT_Z. reflexivity.
Qed.

Lemma ev_rout_i le m k :
  le!_t'7 = Some (Vptr bro (Ptrofs.repr oro)) -> le!_i__1 = Some (Vlong (Int64.repr k)) ->
  0 <= k <= 4294967295 -> oro <= 1000000000000 ->
  eval_expr sha_ge e le m (Ebinop Oadd (Etempvar _t'7 (tptr ROUT)) (Etempvar _i__1 tulong) (tptr ROUT))
    (Vptr bro (Ptrofs.repr (oro + 24 * k))).
Proof.
  intros Ho Hi Hk Hb. eapply eval_Ebinop; [apply eval_Etempvar; exact Ho|apply eval_Etempvar; exact Hi|].
  rewrite <- (ptr_index_long oro 24 k) by lia. rewrite <- mt_sizeof_ROUT_Z. reflexivity.
Qed.
End OutLoop.
