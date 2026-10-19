(** The Bitcoin environment as the C library builds it: the three real
    functions [simplicity_bitcoin_mallocTransaction],
    [simplicity_bitcoin_mallocTapEnv] and [simplicity_bitcoin_build_txEnv],
    run in sequence on memory holding the bytes of a raw environment [R],
    leave a [txEnv] structure whose transaction and taproot blocks hold the
    data and the canonical cached hashes of [project_raw_environment R]
    ([env_ready]).  Conditional on [memcpy_model] and the SHA start-up
    state; nothing about the environment structure is assumed. *)
From Coq Require Import ZArith List Lia PeanoNat Setoid Morphisms.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Values Memory Events.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_memcpy_model C.jet_bitmachine_rep C.jet_uint32_array_init C.jet_sha_add_n_calls.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_uchars_exec C.jet_sha_hash_closed.
Require Import C.jet_bitcoin_make_tapleaf_exec.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_raw_env.
Require Import C.jet_bitcoin_words_hash C.jet_bitcoin_composite_hash C.jet_bitcoin_tx_hash C.jet_bitcoin_sig_all_hash.
Require Import C.jet_bitcoin_tapleaf_hash_spec.
Require Import C.jet_bitcoin_env_tomidstate C.jet_bitcoin_env_hashbuffer C.jet_sha_ctx_abs C.jet_bitcoin_env_copyinput.
Require Import C.jet_bitcoin_env_tapenv_path C.jet_bitcoin_env_tapenv_tail.
Require Import C.jet_bitcoin_env_tapenv C.jet_bitcoin_env_tapenv_link C.jet_bitcoin_env_tapenv_raw.
Require Import C.jet_bitcoin_env_tx_indefs C.jet_bitcoin_env_tx_inexec C.jet_bitcoin_env_tx_outblock.
Require Import C.jet_bitcoin_env_tx_txhash C.jet_bitcoin_env_tx C.jet_bitcoin_env_tx_link C.jet_bitcoin_env_tx_raw.
Require Import C.jet_bitcoin_env_txenv C.jet_bitcoin_env_txenv_link C.jet_bitcoin_env_free.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 300.

Local Opaque sha_ge.

(** The built structures only speak about loads from their own block. *)
Ltac walk H HL :=
  lazymatch type of H with
  | _ /\ _ => let H1 := fresh in let H2 := fresh in destruct H as [H1 H2]; split; [walk H1 HL | walk H2 HL]
  | forall x : nat, _ => let x := fresh "j" in intros x; specialize (H x); walk H HL
  | ?P -> _ => let Hp := fresh in intros Hp; specialize (H Hp); walk H HL
  | Mem.load _ _ _ _ = _ => rewrite HL; exact H
  end.

Lemma tx_built_frame m m' bA niv nov ver lt txb data val spb :
  tx_built m bA niv nov ver lt txb data val spb ->
  (forall ch ofs, Mem.load ch m' bA ofs = Mem.load ch m bA ofs) ->
  tx_built m' bA niv nov ver lt txb data val spb.
Proof. intros H HL. unfold tx_built, in_rec in *. cbv beta zeta in *. walk H HL. Qed.

Lemma tapenv_built_frame m m' bA nb cb0 kb cmrb pb :
  tapenv_built m bA nb cb0 kb cmrb pb ->
  (forall ch ofs, Mem.load ch m' bA ofs = Mem.load ch m bA ofs) ->
  tapenv_built m' bA nb cb0 kb cmrb pb.
Proof. intros H HL. unfold tapenv_built in *. cbv beta zeta in *. walk H HL. Qed.

(** The stored taproot environment hash state in canonical terms. *)
Lemma tap_env_regs_link (e : ext_environment) nb cb0 kb cmrb pb :
  tapenv_describes e nb cb0 kb cmrb pb ->
  hash256_reg (tap_env_hash_of e) =
    te_tapenv_regs (make_tapleaf_regs (Int.and cb0 (Int.repr 254)) (tm_words cmrb))
      (te_tappath_regs pb (Z.to_nat (Int.unsigned nb))) (tm_words kb).
Proof.
  intros (Hv & Hc & HLn & HP & HK).
  pose proof (tapleaf_hash_link e _ _ Hv Hc) as E1.
  pose proof (tappath_hash_link e pb HP) as E2. rewrite HLn in E2.
  pose proof (tap_env_hash_link e) as E3. rewrite E1, E2, HK in E3. exact E3.
Qed.

(** Readable raw structures (the input requirements of the two builders). *)
Definition tx_readable (m : mem) braw oraw btx otx bri ori bro oro (niv nov ver lt : int) (txb : list int)
    (data : nat -> in_data) (val : nat -> int64) (bsp : nat -> block) (osp : nat -> ptrofs)
    (spb : nat -> list int) : Prop :=
  (0 <= oraw /\ oraw + 40 <= Ptrofs.max_unsigned) /\
  Mem.load Mptr m braw oraw = Some (Vptr btx otx) /\
  (0 < Int.unsigned niv -> Mem.load Mptr m braw (oraw + 8) = Some (Vptr bri (Ptrofs.repr ori))) /\
  (0 < Int.unsigned nov -> Mem.load Mptr m braw (oraw + 16) = Some (Vptr bro (Ptrofs.repr oro))) /\
  Mem.load Mint32 m braw (oraw + 24) = Some (Vint niv) /\
  Mem.load Mint32 m braw (oraw + 28) = Some (Vint nov) /\
  Mem.load Mint32 m braw (oraw + 32) = Some (Vint ver) /\
  Mem.load Mint32 m braw (oraw + 36) = Some (Vint lt) /\
  Ptrofs.unsigned otx + 32 <= Ptrofs.max_unsigned /\
  (forall i, (i < 32)%nat ->
     Mem.load Mint8unsigned m btx (Ptrofs.unsigned otx + Z.of_nat i) = Some (Vint (nth i txb Int.zero))) /\
  (0 <= ori /\ ori + 64 * Int.unsigned niv <= Ptrofs.max_unsigned) /\
  (forall j, (j < Z.to_nat (Int.unsigned niv))%nat ->
     raw_in_at (Mem.valid_block m) m bri (ori + 64 * Z.of_nat j) (data j)) /\
  (0 <= oro /\ oro + 24 * Int.unsigned nov <= Ptrofs.max_unsigned) /\
  (forall j, (j < Z.to_nat (Int.unsigned nov))%nat ->
     Mem.load Mint64 m bro (oro + 24 * Z.of_nat j) = Some (Vlong (val j))) /\
  (forall j, (j < Z.to_nat (Int.unsigned nov))%nat ->
     raw_buffer_at m bro (oro + 24 * Z.of_nat j + 8) (bsp j) (osp j) (spb j)).

Definition tap_readable (m : mem) braw oraw bcb ocb bcm ocm (nb cb0 : int) (kb cmrb : list int)
    (pb : nat -> list int) : Prop :=
  (0 <= oraw /\ oraw + 24 <= Ptrofs.max_unsigned) /\
  0 <= Int.unsigned nb <= 128 /\
  Mem.load Mptr m braw oraw = Some (Vptr bcb ocb) /\
  Mem.load Mptr m braw (oraw + 8) = Some (Vptr bcm ocm) /\
  Mem.load Mint8unsigned m braw (oraw + 16) = Some (Vint nb) /\
  Ptrofs.unsigned ocb + 33 + 32 * Int.unsigned nb <= Ptrofs.max_unsigned /\
  Mem.load Mint8unsigned m bcb (Ptrofs.unsigned ocb) = Some (Vint cb0) /\
  (forall i, (i < 32)%nat ->
     Mem.load Mint8unsigned m bcb (Ptrofs.unsigned ocb + 1 + Z.of_nat i) = Some (Vint (nth i kb Int.zero))) /\
  (forall j i, (j < Z.to_nat (Int.unsigned nb))%nat -> (i < 32)%nat ->
     Mem.load Mint8unsigned m bcb (Ptrofs.unsigned ocb + 33 + 32 * Z.of_nat j + Z.of_nat i) =
       Some (Vint (nth i (pb j) Int.zero))) /\
  Ptrofs.unsigned ocm + 32 <= Ptrofs.max_unsigned /\
  (forall i, (i < 32)%nat ->
     Mem.load Mint8unsigned m bcm (Ptrofs.unsigned ocm + Z.of_nat i) = Some (Vint (nth i cmrb Int.zero))).

(** The SHA unit's start-up state. *)
Definition sha_started (m : mem) : Prop :=
  sha_dispatch_ok m /\ Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter) /\ sha_tapleaf_tag_ok m.

(** What the three builders leave: the [txEnv] at [(bD, oD)], its
    transaction block [bT] and taproot block [bE], described by [e]. *)
Definition env_ready (m : mem) (bD : block) (oD : Z) (bT bE : block) (e : ext_environment)
    niv nov ver lt txb data val spb nb cb0 kb cmrb pb : Prop :=
  Mem.load Mptr m bD oD = Some (Vptr bT Ptrofs.zero) /\
  Mem.load Mptr m bD (oD + 8) = Some (Vptr bE Ptrofs.zero) /\
  uint32_array_at m bD (oD + 16) (hash256_reg (sig_all_hash_of e)) /\
  Mem.load Mint64 m bD (oD + 48) = Some (Vlong (Int64.repr (Z.of_nat (Bitcoin.envIx (extBase e))))) /\
  tx_built m bT niv nov ver lt txb data val spb /\
  tapenv_built m bE nb cb0 kb cmrb pb /\
  tx_describes e niv nov ver lt txb data val spb /\
  tapenv_describes e nb cb0 kb cmrb pb.

Theorem build_environment (Hmodel : memcpy_model) (R : raw_bitcoin_environment)
    (Hpath : (length (raw_tap_path R) <= 128)%nat) m
    braw oraw btx otx bri ori bro oro niv nov ver lt txb data val bsp osp spb
    brawT orawT bcb ocb bcm ocm nb cb0 kb cmrb pb bD oD :
  let e := project_raw_environment R Hpath in
  let ix := Int64.repr (Z.of_nat (Bitcoin.envIx (raw_base R))) in
  tx_readable m braw oraw btx otx bri ori bro oro niv nov ver lt txb data val bsp osp spb ->
  tap_readable m brawT orawT bcb ocb bcm ocm nb cb0 kb cmrb pb ->
  sha_started m ->
  raw_tx_holds R niv nov ver lt txb data val spb ->
  raw_tapenv_holds R nb cb0 kb cmrb pb ->
  0 <= oD /\ oD + 56 <= Ptrofs.max_unsigned -> (8 | oD) ->
  Mem.range_perm m bD oD (oD + 56) Cur Writable ->
  exists m1 bT m2 bE m3,
    Clight2.eval_funcall sha_ge m (Internal f_simplicity_bitcoin_mallocTransaction)
      [Vptr braw (Ptrofs.repr oraw)] E0 m1 (Vptr bT Ptrofs.zero) /\
    Clight2.eval_funcall sha_ge m1 (Internal f_simplicity_bitcoin_mallocTapEnv)
      [Vptr brawT (Ptrofs.repr orawT)] E0 m2 (Vptr bE Ptrofs.zero) /\
    Clight2.eval_funcall sha_ge m2 (Internal f_simplicity_bitcoin_build_txEnv)
      [Vptr bD (Ptrofs.repr oD); Vptr bT Ptrofs.zero; Vptr bE Ptrofs.zero; Vlong ix] E0 m3 Vundef /\
    ~ Mem.valid_block m bT /\ ~ Mem.valid_block m bE /\ bT <> bE /\
    env_ready m3 bD oD bT bE e niv nov ver lt txb data val spb nb cb0 kb cmrb pb /\
    (forall ch b ofs, Mem.valid_block m b -> (b <> bD \/ ofs + size_chunk ch <= oD \/ oD + 56 <= ofs) ->
       Mem.load ch m3 b ofs = Mem.load ch m b ofs) /\
    Mem.load Mptr m3 bT (-8) =
      Some (Vlong (Int64.repr (488 + 160 * Int.unsigned niv + 40 * Int.unsigned nov))) /\
    Mem.range_perm m3 bT (-8) (488 + 160 * Int.unsigned niv + 40 * Int.unsigned nov) Cur Freeable /\
    Mem.load Mptr m3 bE (-8) = Some (Vlong (Int64.repr (176 + 32 * Int.unsigned nb))) /\
    Mem.range_perm m3 bE (-8) (176 + 32 * Int.unsigned nb) Cur Freeable.
Proof.
  intros e ix (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15)
    (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11) (Hdisp & HMax & HTag) HRtx HRtap HoD HaD PD.
  pose proof (raw_tx_describes R Hpath niv nov ver lt txb data val spb HRtx) as HDtx. fold e in HDtx.
  pose proof (raw_tapenv_describes R Hpath nb cb0 kb cmrb pb HRtap) as HDtap. fold e in HDtap.
  assert (VG : Mem.valid_block m GC) by (eapply load_valid_block; exact Hdisp).
  assert (VM : Mem.valid_block m GM) by (eapply load_valid_block; exact HMax).
  assert (VT : Mem.valid_block m (sha_symbol_block _tagName__1))
    by (eapply load_valid_block; exact (HTag 0%nat ltac:(lia))).
  assert (VrawT : Mem.valid_block m brawT) by (eapply load_valid_block; exact T3).
  assert (Vcb : Mem.valid_block m bcb) by (eapply load_valid_block; exact T7).
  assert (Vcm : Mem.valid_block m bcm) by (eapply load_valid_block; exact (T11 0%nat ltac:(lia))).
  assert (VD : Mem.valid_block m bD) by (eapply Mem.perm_valid_block; apply (PD oD); lia).
  (* the transaction *)
  destruct (eval_mallocTransaction Hmodel m braw oraw btx otx bri ori bro oro niv nov ver lt txb data val
    bsp osp spb X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 Hdisp HMax)
    as (m1 & bT & HCall1 & HFresh1 & HBuilt1 & HL1 & HP1 & HV1 & HHdr1 & HPerm1).
  pose proof HBuilt1 as HB1. unfold tx_built in HB1. cbv beta zeta in HB1.
  destruct HB1 as (B0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R368 & _).
  assert (VT1 : Mem.valid_block m1 bT) by (eapply load_valid_block; exact B0).
  (* the taproot environment *)
  destruct (eval_mallocTapEnv Hmodel m1 brawT orawT bcb ocb bcm ocm nb cb0 kb cmrb pb T1 T2)
    as (m2 & bE & HCall2 & HFresh2 & HBuilt2 & HL2 & HP2 & HV2 & HHdr2 & HPerm2).
  { rewrite HL1 by exact VrawT. exact T3. }
  { rewrite HL1 by exact VrawT. exact T4. }
  { rewrite HL1 by exact VrawT. exact T5. }
  { exact T6. }
  { rewrite HL1 by exact Vcb. exact T7. }
  { intros i Hi. rewrite HL1 by exact Vcb. apply T8, Hi. }
  { intros j i Hj Hi. rewrite HL1 by exact Vcb. apply T9; assumption. }
  { exact T10. }
  { intros i Hi. rewrite HL1 by exact Vcm. apply T11, Hi. }
  { unfold sha_dispatch_ok. rewrite HL1 by exact VG. exact Hdisp. }
  { rewrite HL1 by exact VM. exact HMax. }
  { intros i Hi. rewrite HL1 by exact VT. apply HTag, Hi. }
  pose proof HBuilt2 as HB2. unfold tapenv_built in HB2. cbv beta zeta in HB2.
  destruct HB2 as (P0 & _ & _ & HEnv & _).
  assert (VE2 : Mem.valid_block m2 bE) by (eapply load_valid_block; exact P0).
  assert (NTE : bT <> bE) by (intros E0'; apply HFresh2; rewrite <- E0'; exact VT1).
  assert (NTD : bT <> bD) by (intros E0'; apply HFresh1; rewrite E0'; exact VD).
  assert (NED : bE <> bD) by (intros E0'; apply HFresh2; rewrite E0'; apply HV1, VD).
  (* the txEnv *)
  destruct (eval_build_txEnv Hmodel m2 bD oD bT 0 bE 0 ix
    (mt_txhash_regs (Int64.repr (Int.unsigned ver)) (Int64.repr (Int.unsigned lt))
       (in_regsI data (Z.to_nat (Int.unsigned niv))) (out_regsO (Int.unsigned nov) val spb)
       (in_regsU data (Z.to_nat (Int.unsigned niv))))
    (te_tapenv_regs (make_tapleaf_regs (Int.and cb0 (Int.repr 254)) (tm_words cmrb))
       (te_tappath_regs pb (Z.to_nat (Int.unsigned nb))) (tm_words kb)) HoD HaD)
    as (m3 & HCall3 & R0 & R8 & RSig & RIx & HL3 & HP3 & HV3).
  { intros o Ho. apply HP2, HP1, PD, Ho. }
  { change Ptrofs.max_unsigned with 18446744073709551615. lia. }
  { intros j Hj. rewrite HL2 by exact VT1. rewrite Z.add_0_l. apply R368, Hj. }
  { change Ptrofs.max_unsigned with 18446744073709551615. lia. }
  { intros j Hj. rewrite Z.add_0_l. apply HEnv, Hj. }
  { unfold sha_dispatch_ok. rewrite HL2 by (apply HV1, VG). rewrite HL1 by exact VG. exact Hdisp. }
  { rewrite HL2 by (apply HV1, VM). rewrite HL1 by exact VM. exact HMax. }
  assert (HIx : Z.of_nat (Bitcoin.envIx (extBase e)) <= Int.max_unsigned).
  { destruct HDtx as (HLi & _). pose proof (Bitcoin.envIxBounded (extBase e)) as HB.
    pose proof (Int.unsigned_range_2 niv) as HR. rewrite HLi in HB. lia. }
  assert (LT3 : forall ch ofs, Mem.load ch m3 bT ofs = Mem.load ch m1 bT ofs).
  { intros ch ofs. rewrite HL3 by (try (apply HV2, VT1); left; exact NTD). apply HL2, VT1. }
  assert (LE3 : forall ch ofs, Mem.load ch m3 bE ofs = Mem.load ch m2 bE ofs).
  { intros ch ofs. apply HL3; [exact VE2|left; exact NED]. }
  exists m1, bT, m2, bE, m3.
  split; [exact HCall1|]. split; [exact HCall2|]. split; [exact HCall3|].
  split; [exact HFresh1|].
  split; [intros Hv; apply HFresh2, HV1, Hv|].
  split; [exact NTE|].
  split.
  { unfold env_ready. split; [exact R0|]. split; [exact R8|].
    split.
    { apply u32_of_nth. intros i Hi. rewrite hash256_len in Hi.
      rewrite (sigall_link e HIx), (link_tx e niv nov ver lt txb data val spb HDtx),
        (tap_env_regs_link e nb cb0 kb cmrb pb HDtap).
      apply RSig, Hi. }
    split; [exact RIx|].
    split; [exact (tx_built_frame m1 m3 bT _ _ _ _ _ _ _ _ HBuilt1 LT3)|].
    split; [exact (tapenv_built_frame m2 m3 bE _ _ _ _ _ HBuilt2 LE3)|].
    split; [exact HDtx|exact HDtap]. }
  split.
  { intros ch b ofs Hb Hr. rewrite HL3 by (try (apply HV2, HV1, Hb); exact Hr).
    rewrite HL2 by (apply HV1, Hb). apply HL1, Hb. }
  split; [rewrite LT3; exact HHdr1|].
  split; [intros o Ho; apply HP3, HP2, HPerm1, Ho|].
  split; [rewrite LE3; exact HHdr2|].
  intros o Ho. apply HP3, HPerm2, Ho.
Qed.
