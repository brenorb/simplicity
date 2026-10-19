(** [simplicity_bitcoin_mallocTransaction], the input loop: statement shape,
    per-input data, the states of the six contexts the loop feeds, and the
    loop invariant. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_sha256_iv_init C.jet_bitmachine_rep.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_add_n_init C.jet_sha_ctx8_model.
Require Import C.jet_sha_be32_write C.jet_sha_be64_exec C.jet_sha_uchars_prep C.jet_sha_uchars_exec C.jet_sha_ctx_abs.
Require Import C.jet_bitcoin_env_field_eval C.jet_bitcoin_env_tomidstate C.jet_bitcoin_env_hashbuffer.
Require Import C.jet_bitcoin_env_ctxo C.jet_bitcoin_env_ctxs C.jet_bitcoin_env_ctxs_ops C.jet_bitcoin_env_ctxs_core.
Require Import C.jet_bitcoin_env_tapenv_prelude C.jet_bitcoin_env_tapenv_tail.
Require Import C.jet_bitcoin_env_copyoutput C.jet_bitcoin_env_copyinput.
Require Import C.jet_bitcoin_env_tx_prelude C.jet_bitcoin_env_tx_fill C.jet_bitcoin_env_tx_init.
Require Import C.jet_bitcoin_env_tx_txid C.jet_bitcoin_env_tx_inblock C.jet_bitcoin_env_tx_txhash.
Require Import C.jet_bitcoin_env_tx_outdefs.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 120.

Definition mt_in_s1 : statement :=
  ltac:(let b := eval cbv delta [mt_in_tail] in mt_in_tail in
        lazymatch b with Ssequence (Ssequence _ (Sloop ?s1 _)) _ => exact s1 end).
Definition mt_in_s2 : statement :=
  ltac:(let b := eval cbv delta [mt_in_tail] in mt_in_tail in
        lazymatch b with Ssequence (Ssequence _ (Sloop _ ?s2)) _ => exact s2 end).
Definition mt_in_fin : statement :=
  ltac:(let b := eval cbv delta [mt_in_tail] in mt_in_tail in
        lazymatch b with Ssequence _ ?f => exact f end).
(** The loop body after the copy, the total and the finality update: the
    context operations. *)
Definition mt_in_cond : statement :=
  ltac:(let b := eval cbv delta [mt_in_s1] in mt_in_s1 in lazymatch b with Ssequence ?c _ => exact c end).
Definition mt_in_pre : statement * statement * statement :=
  ltac:(let b := eval cbv delta [mt_in_s1] in mt_in_s1 in
        lazymatch b with Ssequence _ (Ssequence ?b1 (Ssequence ?b2 (Ssequence ?b3 _))) => exact (b1, b2, b3) end).
Definition mt_in_ops : statement :=
  ltac:(let b := eval cbv delta [mt_in_s1] in mt_in_s1 in
        lazymatch b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ ?r))) => exact r end).

Lemma mt_in_tail_shape :
  mt_in_tail = Ssequence (Ssequence (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
                                     (Sloop mt_in_s1 mt_in_s2)) mt_in_fin.
Proof. reflexivity. Qed.

Lemma mt_in_s1_shape :
  mt_in_s1 = Ssequence mt_in_cond
    (Ssequence (fst (fst mt_in_pre)) (Ssequence (snd (fst mt_in_pre)) (Ssequence (snd mt_in_pre) mt_in_ops))).
Proof. reflexivity. Qed.

(** Per-input data: what the raw input supplies and what [copyInput] stores. *)
Record in_data : Type := {
  d_vannex : val; d_has : int; d_areg : list int;
  d_btx : block; d_otx : ptrofs; d_txb : list int;
  d_val : int64;
  d_bsp : block; d_osp : ptrofs; d_spb : list int;
  d_bss : block; d_oss : ptrofs; d_ssb : list int;
  d_ix : int; d_sq : int }.

Section States.
Variable data : nat -> in_data.

Definition st0 : list int * list int := ([], sha256_iv_words).
Definition ab (st : list int * list int) (bs : list int) := absorb_i (fst st) (snd st) bs.

Fixpoint in_stOP (k : nat) : list int * list int :=
  match k with
  | O => st0
  | S k' => ab (ab (in_stOP k') (be_bytes (norm8 (tm_words (d_txb (data k'))))))
               (c_be32_bytes (Int64.repr (Int.unsigned (d_ix (data k')))))
  end.
Fixpoint in_stV (k : nat) : list int * list int :=
  match k with O => st0 | S k' => ab (in_stV k') (c_be64_bytes (d_val (data k'))) end.
Fixpoint in_stSc (k : nat) : list int * list int :=
  match k with O => st0 | S k' => ab (in_stSc k') (be_bytes (norm8 (hash_buffer_regs (d_spb (data k'))))) end.
Fixpoint in_stSeq (k : nat) : list int * list int :=
  match k with
  | O => st0
  | S k' => ab (in_stSeq k') (c_be32_bytes (Int64.repr (Int.unsigned (d_sq (data k')))))
  end.
Definition an_step (st : list int * list int) (d : in_data) : list int * list int :=
  if Int.eq (d_has d) Int.zero then ab st [Int.zero]
  else ab (ab st [Int.one]) (be_bytes (norm8 (d_areg d))).
Fixpoint in_stAn (k : nat) : list int * list int :=
  match k with O => st0 | S k' => an_step (in_stAn k') (data k') end.
Fixpoint in_nAn (k : nat) : int64 :=
  match k with
  | O => Int64.zero
  | S k' => if Int.eq (d_has (data k')) Int.zero then Int64.add (in_nAn k') (Int64.repr 1)
            else Int64.add (Int64.add (in_nAn k') (Int64.repr 1)) (Int64.repr 32)
  end.
Fixpoint in_stSS (k : nat) : list int * list int :=
  match k with O => st0 | S k' => ab (in_stSS k') (be_bytes (norm8 (hash_buffer_regs (d_ssb (data k'))))) end.
Fixpoint in_tot (k : nat) : int64 :=
  match k with O => Int64.zero | S k' => Int64.add (in_tot k') (d_val (data k')) end.
(** [tx->isFinal]: cleared by an input whose sequence is below 0xffffffff. *)
Fixpoint in_final (k : nat) : int :=
  match k with
  | O => Int.one
  | S k' => if Int64.ltu (Int64.repr (Int.unsigned (d_sq (data k')))) (Int64.repr 4294967295)
            then Int.zero else in_final k'
  end.
End States.

(** Byte counters, as the C code accumulates them. *)
Fixpoint in_cnt (step : Z) (k : nat) : int64 :=
  match k with O => Int64.zero | S k' => Int64.add (in_cnt step k') (Int64.repr step) end.
Fixpoint in_cntOP (k : nat) : int64 :=
  match k with O => Int64.zero | S k' => Int64.add (Int64.add (in_cntOP k') (Int64.repr 32)) (Int64.repr 4) end.

Definition mk_core (bx : block) (ob : Z) (st : list int * list int) (c : int64) : ctx_core :=
  (bx, ob, fst st, snd st, c).

(** The eight input contexts after [k] inputs, in the order [inits_exec]
    leaves them (last initialised first). *)
Definition in_cores (data : nat -> in_data) (bI bG bN bQ bU bS bV bP : block) (k : nat) : list ctx_core :=
  [mk_core bI 336 st0 Int64.zero;
   mk_core bG 304 (in_stSS data k) (in_cnt 32 k);
   mk_core bN 272 (in_stAn data k) (in_nAn data k);
   mk_core bQ 240 (in_stSeq data k) (in_cnt 4 k);
   mk_core bU 208 st0 Int64.zero;
   mk_core bS 176 (in_stSc data k) (in_cnt 32 k);
   mk_core bV 144 (in_stV data k) (in_cnt 8 k);
   mk_core bP 112 (in_stOP data k) (in_cntOP k)].

(** The [sigInput] record that [copyInput] leaves at offset [X] of [bA]. *)
Definition in_rec (m : mem) (bA : block) (X : Z) (d : in_data) : Prop :=
  (forall j, (j < 8)%nat -> Mem.load Mint32 m bA (X + 4 * Z.of_nat j) = Some (Vint (nth j (d_areg d) Int.zero))) /\
  (forall j, (j < 8)%nat ->
     Mem.load Mint32 m bA (X + 32 + 4 * Z.of_nat j) = Some (Vint (nth j (hash_buffer_regs (d_ssb d)) Int.zero))) /\
  (forall j, (j < 8)%nat ->
     Mem.load Mint32 m bA (X + 64 + 4 * Z.of_nat j) = Some (Vint (nth j (tm_words (d_txb d)) Int.zero))) /\
  Mem.load Mint64 m bA (X + 96) = Some (Vlong (Int64.repr (Int.unsigned (d_ix d)))) /\
  Mem.load Mint64 m bA (X + 104) = Some (Vlong (d_val d)) /\
  (forall j, (j < 8)%nat ->
     Mem.load Mint32 m bA (X + 112 + 4 * Z.of_nat j) = Some (Vint (nth j (hash_buffer_regs (d_spb d)) Int.zero))) /\
  Mem.load Mint64 m bA (X + 144) = Some (Vlong (Int64.repr (Int.unsigned (d_sq d)))) /\
  Mem.load Mint8unsigned m bA (X + 152) = Some (Vint (d_has d)).

Lemma in_rec_frame m m' bA X d :
  in_rec m bA X d ->
  (forall ch ofs, X <= ofs -> ofs + size_chunk ch <= X + 160 -> Mem.load ch m' bA ofs = Mem.load ch m bA ofs) ->
  in_rec m' bA X d.
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) HL. unfold in_rec.
  split; [intros j Hj; rewrite HL by (change (size_chunk Mint32) with 4; lia); apply H1, Hj|].
  split; [intros j Hj; rewrite HL by (change (size_chunk Mint32) with 4; lia); apply H2, Hj|].
  split; [intros j Hj; rewrite HL by (change (size_chunk Mint32) with 4; lia); apply H3, Hj|].
  split; [rewrite HL by (change (size_chunk Mint64) with 8; lia); exact H4|].
  split; [rewrite HL by (change (size_chunk Mint64) with 8; lia); exact H5|].
  split; [intros j Hj; rewrite HL by (change (size_chunk Mint32) with 4; lia); apply H6, Hj|].
  split; [rewrite HL by (change (size_chunk Mint64) with 8; lia); exact H7|].
  rewrite HL by (change (size_chunk Mint8unsigned) with 1; lia); exact H8.
Qed.

(** The [rawInput] at offset [o] of [bri] describes [d]; every block it
    refers to is one of the caller's ([oldb]). *)
Definition raw_in_at (oldb : block -> Prop) (m : mem) (bri : block) (o : Z) (d : in_data) : Prop :=
  Mem.load Mptr m bri o = Some (d_vannex d) /\
  ((d_vannex d = Vlong Int64.zero /\ d_has d = Int.zero /\ d_areg d = repeat Int.zero 8) \/
   (exists bax oax bad oad abs,
      d_vannex d = Vptr bax oax /\ d_has d = Int.one /\ d_areg d = hash_buffer_regs abs /\
      Ptrofs.unsigned oax + 16 <= Ptrofs.max_unsigned /\ oldb bax /\ oldb bad /\
      raw_buffer_at m bax (Ptrofs.unsigned oax) bad oad abs)) /\
  Mem.load Mptr m bri (o + 8) = Some (Vptr (d_btx d) (d_otx d)) /\ oldb (d_btx d) /\
  Ptrofs.unsigned (d_otx d) + 32 <= Ptrofs.max_unsigned /\
  (forall i, (i < 32)%nat ->
     Mem.load Mint8unsigned m (d_btx d) (Ptrofs.unsigned (d_otx d) + Z.of_nat i) = Some (Vint (nth i (d_txb d) Int.zero))) /\
  Mem.load Mint64 m bri (o + 16) = Some (Vlong (d_val d)) /\
  raw_buffer_at m bri (o + 24) (d_bsp d) (d_osp d) (d_spb d) /\ oldb (d_bsp d) /\
  raw_buffer_at m bri (o + 40) (d_bss d) (d_oss d) (d_ssb d) /\ oldb (d_bss d) /\
  Mem.load Mint32 m bri (o + 56) = Some (Vint (d_ix d)) /\
  Mem.load Mint32 m bri (o + 60) = Some (Vint (d_sq d)).

Lemma raw_in_frame (oldb : block -> Prop) m m' bri o d :
  raw_in_at oldb m bri o d -> oldb bri ->
  (forall ch b ofs, oldb b -> Mem.load ch m' b ofs = Mem.load ch m b ofs) ->
  (forall b, Mem.valid_block m b -> Mem.valid_block m' b) ->
  raw_in_at oldb m' bri o d.
Proof.
  intros (H1 & H2 & H3 & O3 & H4 & H5 & H6 & H7 & O7 & H8 & O8 & H9 & H10) Hbri HL HV. unfold raw_in_at.
  rewrite !HL by exact Hbri.
  split; [exact H1|]. split.
  { destruct H2 as [H2|(bax & oax & bad & oad & abs & E1 & E2 & E3 & E4 & Oa & Od & HB)]; [left; exact H2|right].
    exists bax, oax, bad, oad, abs. repeat (split; [assumption|]).
    eapply raw_buffer_at_frame; [exact HB| |exact HV].
    intros ch b' ofs [->| ->]; apply HL; assumption. }
  split; [exact H3|]. split; [exact O3|]. split; [exact H4|].
  split; [intros i Hi; rewrite HL by exact O3; apply H5, Hi|].
  split; [exact H6|].
  split; [eapply raw_buffer_at_frame; [exact H7| |exact HV]; intros ch b' ofs [->| ->]; apply HL; assumption|].
  split; [exact O7|].
  split; [eapply raw_buffer_at_frame; [exact H8| |exact HV]; intros ch b' ofs [->| ->]; apply HL; assumption|].
  split; [exact O8|]. split; assumption.
Qed.
