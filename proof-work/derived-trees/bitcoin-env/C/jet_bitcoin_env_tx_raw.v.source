(** The transaction built by [simplicity_bitcoin_mallocTransaction] against
    the raw-data meaning of the Bitcoin environment
    ([C.jet_bitcoin_raw_env]): when the memory the builder reads holds the
    bytes of a raw environment [R] (scripts, script signatures, annexes,
    output scripts), the logical environment [project_raw_environment R]
    is described by that memory, so the twelve cached hash fields are the
    canonical hashes of [R].  The script-hash facts are derived from the
    bytes with [hash_buffer_bytestring]; nothing about cached hashes is
    assumed. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Integers.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_raw_env.
Require Import C.jet_bitcoin_words_hash C.jet_bitcoin_composite_hash C.jet_bitcoin_tx_hash.
Require Import C.jet_bitcoin_env_tomidstate C.jet_bitcoin_env_hashbuffer C.jet_bitcoin_env_bytestring.
Require Import C.jet_uint32_array_init C.jet_sha_hash_closed.
Require Import C.jet_bitcoin_env_tx_indefs C.jet_bitcoin_env_tx C.jet_bitcoin_env_tx_link.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 120.

(** The data the builder reads is the raw environment [R]: counts, version,
    lock time, per-input scalars and previous txid, and the *bytes* of every
    script, script signature, annex and output script. *)
Definition raw_tx_holds (R : raw_bitcoin_environment) (niv nov ver lt : int) (txb : list int)
    (data : nat -> in_data) (val : nat -> int64) (spb : nat -> list int) : Prop :=
  let tx := Bitcoin.envTx (raw_base R) in
  length (sigTxIn tx) = Z.to_nat (Int.unsigned niv) /\
  length (sigTxOut tx) = Z.to_nat (Int.unsigned nov) /\
  ver = sigTxVersion tx /\ lt = sigTxLock tx /\
  (forall j x, nth_error (sigTxIn tx) j = Some x ->
     d_val (data j) = sigTxiValue x /\ d_sq (data j) = sigTxiSequence x /\
     d_ix (data j) = opIndex (sigTxiPreviousOutpoint x) /\
     tm_words (d_txb (data j)) = hash256_reg (opHash (sigTxiPreviousOutpoint x))) /\
  (forall j i, nth_error (raw_inputs R) j = Some i ->
     d_spb (data j) = map byte_int (raw_redeemed_script i) /\
     Zlength (raw_redeemed_script i) < 4294967296 /\
     d_ssb (data j) = map byte_int (raw_script_sig i) /\
     Zlength (raw_script_sig i) < 4294967296 /\
     match raw_annex i with
     | None => d_has (data j) = Int.zero
     | Some a => d_has (data j) = Int.one /\ d_areg (data j) = hash_buffer_regs (map byte_int a) /\
                 Zlength a < 4294967296
     end) /\
  (forall j o, nth_error (sigTxOut tx) j = Some o ->
     val j = txoValue o /\ spb j = map byte_int (txoScript o)).

Lemma nth_error_map_some {A B} (f : A -> B) (l : list A) j y :
  nth_error (map f l) j = Some y -> exists x, nth_error l j = Some x /\ y = f x.
Proof.
  rewrite nth_error_map. destruct (nth_error l j) as [x|]; [|discriminate].
  intros H. injection H as <-. exists x. split; reflexivity.
Qed.

Theorem raw_tx_describes (R : raw_bitcoin_environment) (Hpath : (length (raw_tap_path R) <= 128)%nat)
    niv nov ver lt txb data val spb :
  raw_tx_holds R niv nov ver lt txb data val spb ->
  tx_describes (project_raw_environment R Hpath) niv nov ver lt txb data val spb.
Proof.
  intros (HLi & HLo & Ev & El & HI & HRaw & HO).
  unfold tx_describes. cbn [project_raw_environment extBase extInScriptHash extInScriptSigHash extInAnnexHash].
  split; [exact HLi|]. split; [exact HLo|]. split; [exact Ev|]. split; [exact El|]. split; [exact HI|].
  split.
  { intros j h Hj. destruct (nth_error_map_some _ _ _ _ Hj) as (i & Hi & ->).
    destruct (HRaw j i Hi) as (E1 & B1 & _). rewrite E1. apply hash_buffer_bytestring. lia. }
  split.
  { intros j h Hj. destruct (nth_error_map_some _ _ _ _ Hj) as (i & Hi & ->).
    destruct (HRaw j i Hi) as (_ & _ & E2 & B2 & _). rewrite E2. apply hash_buffer_bytestring. lia. }
  split.
  { intros j a Hj. destruct (nth_error_map_some _ _ _ _ Hj) as (i & Hi & ->).
    destruct (HRaw j i Hi) as (_ & _ & _ & _ & HA). destruct (raw_annex i) as [ab|]; cbn [option_map].
    - destruct HA as (E1 & E2 & B3). split; [exact E1|]. rewrite E2. apply hash_buffer_bytestring. lia.
    - exact HA. }
  intros j o Hj. destruct (HO j o Hj) as (E1 & E2). split; [exact E1|].
  rewrite E2. apply hash_buffer_bytestring.
  pose proof (txoScript_bound o) as HB. change Int.modulus with 4294967296 in HB. lia.
Qed.

(** The headline statement against raw data. *)
Theorem mallocTransaction_raw_cached_hashes (Hmodel : jet_memcpy_model.memcpy_model)
    (R : raw_bitcoin_environment) (Hpath : (length (raw_tap_path R) <= 128)%nat)
    m braw oraw btx otx bri ori bro oro (niv nov ver lt : int) (txb : list int) (data : nat -> in_data)
    (val : nat -> int64) (bsp : nat -> Values.block) (osp : nat -> ptrofs) (spb : nat -> list int) :
  let e := project_raw_environment R Hpath in
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
  raw_tx_holds R niv nov ver lt txb data val spb ->
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
  intros e H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 HR.
  exact (mallocTransaction_cached_hashes Hmodel e m braw oraw btx otx bri ori bro oro niv nov ver lt txb
    data val bsp osp spb H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17
    (raw_tx_describes R Hpath niv nov ver lt txb data val spb HR)).
Qed.
