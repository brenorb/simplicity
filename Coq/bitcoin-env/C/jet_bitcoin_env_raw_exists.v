(** Readable raw memory always describes a raw environment: for any memory
    satisfying the input requirements of the two builders ([tx_readable],
    [tap_readable]) with at least one input, and any current-input index in
    range, there is a [raw_bitcoin_environment] [R] whose bytes are the ones
    in memory ([raw_tx_holds], [raw_tapenv_holds]).  The hypotheses of
    [build_environment] about [R] are therefore a definition of the logical
    environment, not assumptions about it. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Values Memory.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_sha_hash_closed C.jet_bitcoin_ext_prim C.jet_bitcoin_raw_env.
Require Import C.jet_bitcoin_env_tomidstate C.jet_bitcoin_env_hashbuffer C.jet_bitcoin_env_copyinput.
Require Import C.jet_bitcoin_env_stream C.jet_bitcoin_env_tapenv_describe C.jet_bitcoin_env_bytestring.
Require Import C.jet_bitcoin_env_tx_indefs C.jet_bitcoin_env_tx_raw C.jet_bitcoin_env_tapenv_raw.
Require Import C.jet_bitcoin_env_build.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 120.

Definition bytes_of (l : list int) : list byte := map (fun x => Byte.repr (Int.unsigned x)) l.
Definition small (l : list int) : Prop := Forall (fun x => 0 <= Int.unsigned x < 256) l.

Lemma bytes_of_inv l : small l -> map byte_int (bytes_of l) = l.
Proof.
  induction 1 as [|x l Hx _ IH]; [reflexivity|]. cbn [bytes_of map]. f_equal; [|exact IH].
  unfold byte_int. rewrite Byte.unsigned_repr by (change Byte.max_unsigned with 255; lia).
  apply Int.repr_unsigned.
Qed.

Lemma bytes_of_Zlength l : Zlength (bytes_of l) = Z.of_nat (length l).
Proof. rewrite Zlength_correct. unfold bytes_of. rewrite map_length. reflexivity. Qed.

Lemma load_byte_small m b o x : Mem.load Mint8unsigned m b o = Some (Vint x) -> 0 <= Int.unsigned x < 256.
Proof.
  intros HL. pose proof (Mem.load_cast _ _ _ _ _ HL) as HC. cbn in HC. injection HC as HC.
  rewrite HC. exact (Int.zero_ext_range 8 x ltac:(change Int.zwordsize with 32; lia)).
Qed.

Lemma buffer_small m b o bd od bs :
  raw_buffer_at m b o bd od bs -> small bs /\ Z.of_nat (length bs) < 4294967296.
Proof.
  intros (len & _ & _ & HLen & _ & _ & HB). split.
  - apply Forall_nth. intros i d Hi. rewrite (nth_indep bs d Int.zero Hi).
    exact (load_byte_small _ _ _ _ (HB i Hi)).
  - rewrite HLen. pose proof (Int.unsigned_range len) as HR. change Int.modulus with 4294967296 in HR. lia.
Qed.

Lemma fin_choice {A} (P : nat -> A -> Prop) : forall n,
  (forall j, (j < n)%nat -> exists x, P j x) ->
  exists l, length l = n /\ forall j x, nth_error l j = Some x -> P j x.
Proof.
  induction n as [|n IH]; intros H.
  - exists []. split; [reflexivity|]. intros [|j] x Hj; discriminate.
  - destruct (IH (fun j Hj => H j (Nat.lt_lt_succ_r _ _ Hj))) as (l & HL & HP).
    destruct (H n (Nat.lt_succ_diag_r n)) as (x & Hx).
    exists (l ++ [x]). split; [rewrite app_length, HL; cbn; lia|].
    intros j y Hj. destruct (Nat.lt_ge_cases j (length l)) as [Hlt|Hge].
    + rewrite nth_error_app1 in Hj by exact Hlt. exact (HP j y Hj).
    + rewrite nth_error_app2 in Hj by exact Hge.
      destruct (j - length l)%nat as [|k] eqn:E; cbn in Hj; [|destruct k; discriminate].
      injection Hj as <-. replace j with n by lia. exact Hx.
Qed.

Definition in_facts (d : in_data) (p : sigTxInput * raw_input_data) : Prop :=
  d_val d = sigTxiValue (fst p) /\ d_sq d = sigTxiSequence (fst p) /\
  d_ix d = opIndex (sigTxiPreviousOutpoint (fst p)) /\
  tm_words (d_txb d) = hash256_reg (opHash (sigTxiPreviousOutpoint (fst p))) /\
  d_spb d = map byte_int (raw_redeemed_script (snd p)) /\
  Zlength (raw_redeemed_script (snd p)) < 4294967296 /\
  d_ssb d = map byte_int (raw_script_sig (snd p)) /\
  Zlength (raw_script_sig (snd p)) < 4294967296 /\
  match raw_annex (snd p) with
  | None => d_has d = Int.zero
  | Some a => d_has d = Int.one /\ d_areg d = hash_buffer_regs (map byte_int a) /\ Zlength a < 4294967296
  end.

Lemma in_witness (oldb : block -> Prop) m bri o d :
  raw_in_at oldb m bri o d -> exists p, in_facts d p.
Proof.
  intros (_ & HA & _ & _ & _ & _ & _ & HSp & _ & HSs & _ & _ & _).
  destruct (buffer_small _ _ _ _ _ _ HSp) as (S1 & L1). destruct (buffer_small _ _ _ _ _ _ HSs) as (S2 & L2).
  set (txi := {| sigTxiPreviousOutpoint := {| opHash := mk_hash256 (tm_words (d_txb d)); opIndex := d_ix d |};
                 sigTxiValue := d_val d; sigTxiSequence := d_sq d |}).
  destruct HA as [(_ & Hh & _)|(bax & oax & bad & oad & abs & _ & Hh & Ha & _ & _ & _ & HB)].
  - exists (txi, {| raw_redeemed_script := bytes_of (d_spb d); raw_annex := None;
                    raw_script_sig := bytes_of (d_ssb d) |}).
    unfold in_facts. cbn [fst snd sigTxiValue sigTxiSequence sigTxiPreviousOutpoint opIndex opHash
      raw_redeemed_script raw_script_sig raw_annex txi].
    rewrite !bytes_of_inv, !bytes_of_Zlength by assumption.
    rewrite mk_hash256_reg by apply tm_words_length. repeat split; try reflexivity; assumption.
  - destruct (buffer_small _ _ _ _ _ _ HB) as (S3 & L3).
    exists (txi, {| raw_redeemed_script := bytes_of (d_spb d); raw_annex := Some (bytes_of abs);
                    raw_script_sig := bytes_of (d_ssb d) |}).
    unfold in_facts. cbn [fst snd sigTxiValue sigTxiSequence sigTxiPreviousOutpoint opIndex opHash
      raw_redeemed_script raw_script_sig raw_annex txi].
    rewrite !bytes_of_inv, !bytes_of_Zlength by assumption.
    rewrite mk_hash256_reg by apply tm_words_length. repeat split; try reflexivity; assumption.
Qed.

Lemma out_witness m b o bd od (v : int64) (bs : list int) :
  raw_buffer_at m b o bd od bs -> exists t : txOutput, v = txoValue t /\ bs = map byte_int (txoScript t).
Proof.
  intros HB. destruct (buffer_small _ _ _ _ _ _ HB) as (S1 & L1).
  assert (Hb : Zlength (bytes_of bs) < Int.modulus)
    by (rewrite bytes_of_Zlength; change Int.modulus with 4294967296; exact L1).
  exists {| txoValue := v; txoScript := bytes_of bs; txoScript_bound := Hb |}.
  cbn [txoValue txoScript]. split; [reflexivity|]. symmetry. apply bytes_of_inv, S1.
Qed.

Lemma nth_map_fst {A B} (l : list (A * B)) j x :
  nth_error (map fst l) j = Some x -> exists p, nth_error l j = Some p /\ x = fst p.
Proof. apply nth_error_map_some. Qed.

Theorem raw_environment_exists m braw oraw btx otx bri ori bro oro niv nov ver lt txb data val bsp osp spb
    brawT orawT bcb ocb bcm ocm nb cb0 kb cmrb pb (ixn : nat) :
  tx_readable m braw oraw btx otx bri ori bro oro niv nov ver lt txb data val bsp osp spb ->
  tap_readable m brawT orawT bcb ocb bcm ocm nb cb0 kb cmrb pb ->
  (ixn < Z.to_nat (Int.unsigned niv))%nat ->
  exists (R : raw_bitcoin_environment) (Hpath : (length (raw_tap_path R) <= 128)%nat),
    raw_tx_holds R niv nov ver lt txb data val spb /\
    raw_tapenv_holds R nb cb0 kb cmrb pb /\
    Bitcoin.envIx (raw_base R) = ixn.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIn & _ & _ & HOut) (_ & HN & _) Hix.
  pose proof (Int.unsigned_range_2 niv) as Hni. pose proof (Int.unsigned_range_2 nov) as Hno.
  change Int.max_unsigned with 4294967295 in Hni, Hno.
  set (Nn := Z.to_nat (Int.unsigned niv)) in *. set (Mn := Z.to_nat (Int.unsigned nov)) in *.
  destruct (fin_choice (fun j p => in_facts (data j) p) Nn) as (lp & HLp & HP).
  { intros j Hj. exact (in_witness _ _ _ _ _ (HIn j Hj)). }
  destruct (fin_choice (fun j (t : txOutput) => val j = txoValue t /\ spb j = map byte_int (txoScript t)) Mn)
    as (lo & HLo & HO).
  { intros j Hj. exact (out_witness _ _ _ _ _ (val j) _ (HOut j Hj)). }
  assert (BIn : 0 < Zlength (map fst lp) < Int.modulus).
  { rewrite Zlength_correct, map_length, HLp. change Int.modulus with 4294967296. unfold Nn in *. lia. }
  assert (BOut : 0 <= Zlength lo < Int.modulus).
  { rewrite Zlength_correct, HLo. change Int.modulus with 4294967296. unfold Mn. lia. }
  set (tx := {| sigTxVersion := ver; sigTxIn := map fst lp; sigTxOut := lo; sigTxLock := lt;
                sigTxInBounds := BIn; sigTxOutBounds := BOut |}).
  assert (HIxB : (ixn < length (sigTxIn tx))%nat) by (cbn [sigTxIn tx]; rewrite map_length, HLp; exact Hix).
  set (base := @Bitcoin.Build_environment tx ixn (mk_hash256 (tm_words cmrb)) HIxB).
  set (n := Z.to_nat (Int.unsigned nb)).
  set (path := map (fun j => mk_hash256 (tm_words (pb j))) (List.seq 0 n)).
  assert (HPL : (length path <= 128)%nat) by (unfold path; rewrite map_length, seq_length; unfold n; lia).
  assert (HRL : length (map snd lp) = length (sigTxIn (Bitcoin.envTx base))).
  { cbn [Bitcoin.envTx base sigTxIn tx]. rewrite !map_length. reflexivity. }
  exists {| raw_base := base; raw_inputs := map snd lp; raw_inputs_length := HRL;
            raw_leaf_version := Byte.repr (Int.unsigned (Int.and cb0 (Int.repr 254)));
            raw_tap_path := path; raw_internal_key := mk_hash256 (tm_words kb) |}, HPL.
  split; [|split; [|reflexivity]].
  - unfold raw_tx_holds. cbn [raw_base raw_inputs Bitcoin.envTx base sigTxIn sigTxOut sigTxVersion sigTxLock tx].
    split; [rewrite map_length; exact HLp|]. split; [exact HLo|]. split; [reflexivity|]. split; [reflexivity|].
    split.
    { intros j x Hj. destruct (nth_map_fst lp j x Hj) as (p & Hp & ->).
      destruct (HP j p Hp) as (E1 & E2 & E3 & E4 & _). repeat split; assumption. }
    split.
    { intros j i Hj. destruct (nth_error_map_some snd lp j i Hj) as (p & Hp & ->).
      destruct (HP j p Hp) as (_ & _ & _ & _ & E5 & E6 & E7 & E8 & E9).
      split; [exact E5|]. split; [exact E6|]. split; [exact E7|]. split; [exact E8|exact E9]. }
    exact HO.
  - unfold raw_tapenv_holds. cbn [raw_leaf_version raw_base Bitcoin.envScriptCMR base raw_tap_path raw_internal_key].
    split.
    { unfold byte_int. pose proof (and254_range cb0) as HR.
      rewrite Byte.unsigned_repr by (change Byte.max_unsigned with 255; lia). apply Int.repr_unsigned. }
    split; [apply mk_hash256_reg, tm_words_length|].
    split; [unfold path; rewrite map_length, seq_length; reflexivity|].
    split; [|apply mk_hash256_reg, tm_words_length].
    intros j h Hn. unfold path in Hn. rewrite nth_error_map in Hn.
    destruct (nth_error (List.seq 0 n) j) as [x|] eqn:E; [|discriminate].
    injection Hn as <-. pose proof (nth_error_In _ _ E) as HIn'. apply in_seq in HIn'.
    assert (x = j).
    { assert (Hj : (j < length (List.seq 0 n))%nat) by (apply nth_error_Some; congruence).
      rewrite seq_length in Hj. rewrite (nth_error_nth' _ 0%nat) in E by (rewrite seq_length; exact Hj).
      rewrite seq_nth in E by exact Hj. injection E as <-. reflexivity. }
    subst x. symmetry. apply mk_hash256_reg, tm_words_length.
Qed.

(** The builders on readable memory, with no hypothesis about a logical
    environment: one exists, and the resulting [txEnv] is ready for it. *)
Theorem build_environment_readable (Hmodel : jet_memcpy_model.memcpy_model) m
    braw oraw btx otx bri ori bro oro niv nov ver lt txb data val bsp osp spb
    brawT orawT bcb ocb bcm ocm nb cb0 kb cmrb pb bD oD (ixn : nat) :
  tx_readable m braw oraw btx otx bri ori bro oro niv nov ver lt txb data val bsp osp spb ->
  tap_readable m brawT orawT bcb ocb bcm ocm nb cb0 kb cmrb pb ->
  sha_started m ->
  (ixn < Z.to_nat (Int.unsigned niv))%nat ->
  0 <= oD /\ oD + 56 <= Ptrofs.max_unsigned -> (8 | oD) ->
  Mem.range_perm m bD oD (oD + 56) Cur Writable ->
  exists (R : raw_bitcoin_environment) (Hpath : (length (raw_tap_path R) <= 128)%nat) m1 bT m2 bE m3,
    Bitcoin.envIx (raw_base R) = ixn /\
    ClightBigstep.Clight2.eval_funcall jet_sha_linkage.sha_ge m
      (Ctypes.Internal jets_sha.f_simplicity_bitcoin_mallocTransaction)
      [Vptr braw (Ptrofs.repr oraw)] Events.E0 m1 (Vptr bT Ptrofs.zero) /\
    ClightBigstep.Clight2.eval_funcall jet_sha_linkage.sha_ge m1
      (Ctypes.Internal jets_sha.f_simplicity_bitcoin_mallocTapEnv)
      [Vptr brawT (Ptrofs.repr orawT)] Events.E0 m2 (Vptr bE Ptrofs.zero) /\
    ClightBigstep.Clight2.eval_funcall jet_sha_linkage.sha_ge m2
      (Ctypes.Internal jets_sha.f_simplicity_bitcoin_build_txEnv)
      [Vptr bD (Ptrofs.repr oD); Vptr bT Ptrofs.zero; Vptr bE Ptrofs.zero; Vlong (Int64.repr (Z.of_nat ixn))]
      Events.E0 m3 Vundef /\
    env_ready m3 bD oD bT bE (project_raw_environment R Hpath)
      niv nov ver lt txb data val spb nb cb0 kb cmrb pb /\
    (forall ch b ofs, Mem.valid_block m b -> (b <> bD \/ ofs + size_chunk ch <= oD \/ oD + 56 <= ofs) ->
       Mem.load ch m3 b ofs = Mem.load ch m b ofs).
Proof.
  intros HTx HTap HS Hix HoD HaD PD.
  destruct (raw_environment_exists m braw oraw btx otx bri ori bro oro niv nov ver lt txb data val bsp osp spb
    brawT orawT bcb ocb bcm ocm nb cb0 kb cmrb pb ixn HTx HTap Hix) as (R & Hpath & HR1 & HR2 & HIx).
  destruct (build_environment Hmodel R Hpath m braw oraw btx otx bri ori bro oro niv nov ver lt txb data val
    bsp osp spb brawT orawT bcb ocb bcm ocm nb cb0 kb cmrb pb bD oD HTx HTap HS HR1 HR2 HoD HaD PD)
    as (m1 & bT & m2 & bE & m3 & C1 & C2 & C3 & _ & _ & _ & HReady & HFr & _).
  rewrite HIx in C3.
  exists R, Hpath, m1, bT, m2, bE, m3. repeat (split; [assumption|]). exact HFr.
Qed.
