(** The tagged-hash preamble shared by the taproot operations of ops.c:
      ctx = sha256_init(tag.s); sha256_uchars(&ctx, tagName, n); sha256_finalize(&ctx);
      ctx1 = sha256_init(result.s); sha256_hash(&ctx1, &tag); sha256_hash(&ctx1, &tag);
    as a chain of calls on memory, ending in a context that has absorbed
    the 64-byte tag prefix.  Conditional on [memcpy_model]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import C.jet_exec C.jet_memcpy_model C.jet_readBit_layout C.jet_bitmachine_rep.
Require Import C.jet_uint32_array_init C.jet_sha256_iv_init.
Require C.jets.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_ctx8_model.
Require Import C.jet_sha_be32_exec C.jet_sha_be32_write C.jet_sha_be64_exec.
Require Import C.jet_sha_compress_uchar C.jet_sha_uchars_prep C.jet_sha_uchars_loop C.jet_sha_uchars_exec.
Require Import C.jet_sha_add_n_calls C.jet_sha_uchar_exec C.jet_sha_hash_exec C.jet_sha_finalize_exec.
Require Import C.jet_sha_tapdata_prep C.jet_sha_ctx_abs C.jet_sha_ctxi.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque sha_ge.
Set Default Timeout 120.

Definition tag_regs_of (tb : list int) : list int :=
  snd (absorb_i tb sha256_iv_words (sha_pad (Int64.repr (Z.of_nat (length tb))))).

Definition tagged_prefix (tb : list int) : list int :=
  SHA256.hash_block sha256_iv_words (tag_regs_of tb ++ tag_regs_of tb).

Lemma be_words_be_bytes_app a b : be_words (be_bytes a ++ be_bytes b) = a ++ b.
Proof. unfold be_bytes. rewrite <- flat_map_app. apply be_words_be_bytes. Qed.

Lemma tag_regs_of_length tb : (length tb < 64)%nat -> length (tag_regs_of tb) = 8%nat.
Proof. intros H. apply (absorb_i_len _ tb sha256_iv_words H eq_refl). Qed.

Ltac in_list := solve [cbn [In]; repeat first [left; reflexivity | right]].
Ltac ne :=
  let E := fresh in intro E;
  match goal with
  | H : ~ In ?a ?l |- _ => apply H; first [rewrite E; in_list | rewrite <- E; in_list]
  end.

Theorem tagged_ctx_mem (Hmodel : memcpy_model) m bR2 bC bT bR1 bC1 bRes TAG (tb : list int) :
  NoDup [bR2; bC; bT; bR1; bC1; bRes] ->
  Mem.valid_block m GC -> Mem.valid_block m GM -> Mem.valid_block m TAG ->
  ~ In GC [bR2; bC; bT; bR1; bC1; bRes] -> ~ In GM [bR2; bC; bT; bR1; bC1; bRes] ->
  ~ In TAG [bR2; bC; bT; bR1; bC1; bRes] ->
  Mem.valid_block m bT ->
  Mem.range_perm m bR2 0 88 Cur Freeable -> Mem.range_perm m bC 0 88 Cur Freeable ->
  Mem.range_perm m bT 0 32 Cur Freeable -> Mem.range_perm m bR1 0 88 Cur Freeable ->
  Mem.range_perm m bC1 0 88 Cur Freeable -> Mem.range_perm m bRes 0 32 Cur Freeable ->
  sha_dispatch_ok m -> Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter) ->
  (length tb < 56)%nat ->
  (forall i, (i < length tb)%nat ->
     Mem.load Mint8unsigned m TAG (Z.of_nat i) = Some (Vint (nth i tb Int.zero))) ->
  exists mi1 bytes1 m1 m2 m3 mi2 bytes2 m4 m5 m6,
    Clight2.eval_funcall sha_ge m (Internal jets.f_sha256_init)
      [Vptr bR2 Ptrofs.zero; Vptr bT (Ptrofs.repr 0)] E0 mi1 Vundef /\
    Mem.loadbytes mi1 bR2 0 88 = Some bytes1 /\ Mem.storebytes mi1 bC 0 bytes1 = Some m1 /\
    Clight2.eval_funcall sha_ge m1 (Internal f_sha256_uchars)
      [Vptr bC (Ptrofs.repr 0); Vptr TAG Ptrofs.zero; Vlong (Int64.repr (Z.of_nat (length tb)))] E0 m2
      (Vint (bit_int (negb (uc_overflow false Int64.zero (Int64.repr (Z.of_nat (length tb))))))) /\
    Clight2.eval_funcall sha_ge m2 (Internal f_sha256_finalize) [Vptr bC (Ptrofs.repr 0)] E0 m3
      (Vint (bit_int (negb (uc_overflow false Int64.zero (Int64.repr (Z.of_nat (length tb))))))) /\
    Clight2.eval_funcall sha_ge m3 (Internal jets.f_sha256_init)
      [Vptr bR1 Ptrofs.zero; Vptr bRes (Ptrofs.repr 0)] E0 mi2 Vundef /\
    Mem.loadbytes mi2 bR1 0 88 = Some bytes2 /\ Mem.storebytes mi2 bC1 0 bytes2 = Some m4 /\
    Clight2.eval_funcall sha_ge m4 (Internal f_sha256_hash)
      [Vptr bC1 (Ptrofs.repr 0); Vptr bT Ptrofs.zero] E0 m5 Vundef /\
    Clight2.eval_funcall sha_ge m5 (Internal f_sha256_hash)
      [Vptr bC1 (Ptrofs.repr 0); Vptr bT Ptrofs.zero] E0 m6 Vundef /\
    ctxi m6 bC1 bRes [] (tagged_prefix tb) (Int64.repr 64) false /\
    (forall ch b ofs, Mem.valid_block m b -> ~ In b [bR2; bC; bT; bR1; bC1; bRes] ->
       Mem.load ch m6 b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m6 b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m6 b).
Proof.
  intros ND VG VM VT NG NM NT VbT PR2 PC PT PR1 PC1 PRes Hdisp HMax Htb HTag.
  pose proof ND as ND0.
  apply NoDup_cons_iff in ND. destruct ND as [N1 ND].
  apply NoDup_cons_iff in ND. destruct ND as [N2 ND].
  apply NoDup_cons_iff in ND. destruct ND as [N3 ND].
  apply NoDup_cons_iff in ND. destruct ND as [N4 ND].
  apply NoDup_cons_iff in ND. destruct ND as [N5 _].
  set (T := tag_regs_of tb).
  assert (HTLen : length T = 8%nat) by (apply tag_regs_of_length; lia).
  (* the tag context *)
  destruct (ctxi_init bC bT ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) m bR2
    ltac:(ne) ltac:(ne) VG VM ltac:(ne) ltac:(ne) PR2 PC PT Hdisp HMax)
    as (mi1 & m1 & bytes1 & HInit1 & HLB1 & HSB1 & HA1 & HL1 & HP1 & HV1).
  assert (HTag1 : forall i, (i < length tb)%nat ->
    Mem.load Mint8unsigned m1 TAG (Ptrofs.unsigned Ptrofs.zero + Z.of_nat i) =
      Some (Vint (nth i tb Int.zero))).
  { intros i Hi. change (Ptrofs.unsigned Ptrofs.zero) with 0. rewrite Z.add_0_l.
    rewrite HL1; [apply HTag; exact Hi|exact VT|ne|ne|ne]. }
  pose proof (ctxi_uchars bC bT ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) Hmodel
    m1 TAG Ptrofs.zero [] sha256_iv_words tb Int64.zero false HA1 ltac:(ne) ltac:(ne)
    ltac:(change (Ptrofs.unsigned Ptrofs.zero) with 0;
          change Ptrofs.max_unsigned with 18446744073709551615; lia) HTag1) as HU.
  cbv zeta in HU. destruct HU as (m2 & HUc & HA2 & HL2 & HP2 & HV2).
  rewrite (absorb_i_small tb [] sha256_iv_words) in HA2 by (cbn [length]; lia).
  cbn [fst snd app] in HA2. rewrite Int64.add_zero_l in HA2.
  destruct (ctxi_finalize bC bT ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) Hmodel
    m2 tb sha256_iv_words _ _ HA2) as (m3 & HFin & HReg3 & HL3 & HP3 & HV3).
  fold (tag_regs_of tb) in HReg3. fold T in HReg3.
  assert (V3 : forall b, Mem.valid_block m b -> Mem.valid_block m3 b).
  { intros b Hv. apply HV3, HV2, HV1, Hv. }
  assert (P3 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m3 b ofs k p).
  { intros b ofs k p Hp. assert (Hp1 : Mem.perm m1 b ofs k p) by (apply HP1, Hp).
    assert (Hp2 : Mem.perm m2 b ofs k p) by (apply HP2; [eapply Mem.perm_valid_block; exact Hp1|exact Hp1]).
    apply HP3; [eapply Mem.perm_valid_block; exact Hp2|exact Hp2]. }
  assert (K3 : forall ch b ofs, Mem.valid_block m b -> b <> bR2 -> b <> bC -> b <> bT ->
    Mem.load ch m3 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hv H1 H2 H3.
    rewrite HL3; [|apply HV2, HV1, Hv|exact H2|exact H3].
    rewrite HL2; [|apply HV1, Hv|exact H2|exact H3].
    apply HL1; assumption. }
  (* the main context *)
  destruct (ctxi_init bC1 bRes ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) m3 bR1
    ltac:(ne) ltac:(ne) (V3 _ VG) (V3 _ VM) ltac:(ne) ltac:(ne)
    ltac:(intros ofs Hr0; apply P3, PR1, Hr0) ltac:(intros ofs Hr0; apply P3, PC1, Hr0)
    ltac:(intros ofs Hr0; apply P3, PRes, Hr0))
    as (mi2 & m4 & bytes2 & HInit2 & HLB2 & HSB2 & HA4 & HL4 & HP4 & HV4).
  { unfold sha_dispatch_ok. rewrite K3; [exact Hdisp|exact VG|ne|ne|ne]. }
  { rewrite K3; [exact HMax|exact VM|ne|ne|ne]. }
  assert (HT4 : forall j, (j < 8)%nat ->
    Mem.load Mint32 m4 bT (Ptrofs.unsigned Ptrofs.zero + 4 * Z.of_nat j) = Some (Vint (nth j T Int.zero))).
  { intros j Hj. change (Ptrofs.unsigned Ptrofs.zero) with 0.
    rewrite HL4; [apply HReg3; exact Hj|apply V3; exact VbT|ne|ne|ne]. }
  assert (HotM : Ptrofs.unsigned Ptrofs.zero + 32 <= Ptrofs.max_unsigned).
  { change (Ptrofs.unsigned Ptrofs.zero) with 0. change Ptrofs.max_unsigned with 18446744073709551615. lia. }
  pose proof (ctxi_hash bC1 bRes ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) Hmodel
    m4 bT Ptrofs.zero [] sha256_iv_words T Int64.zero false HA4 HTLen HotM HT4) as HH1.
  cbv zeta in HH1. destruct HH1 as (m5 & HHc5 & HA5 & HL5 & HP5 & HV5).
  assert (HbT : length (be_bytes T) = 32%nat) by (rewrite be_bytes_length, HTLen; reflexivity).
  rewrite (absorb_i_small (be_bytes T) [] sha256_iv_words) in HA5 by (rewrite HbT; cbn; lia).
  cbn [fst snd app] in HA5.
  assert (HT5 : forall j, (j < 8)%nat ->
    Mem.load Mint32 m5 bT (Ptrofs.unsigned Ptrofs.zero + 4 * Z.of_nat j) = Some (Vint (nth j T Int.zero))).
  { intros j Hj. rewrite HL5; [apply HT4; exact Hj|apply HV4, V3; exact VbT|ne|ne]. }
  pose proof (ctxi_hash bC1 bRes ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) Hmodel
    m5 bT Ptrofs.zero (be_bytes T) sha256_iv_words T _ _ HA5 HTLen HotM HT5) as HH2.
  cbv zeta in HH2. destruct HH2 as (m6 & HHc6 & HA6 & HL6 & HP6 & HV6).
  assert (HAbs : absorb_i (be_bytes T) sha256_iv_words (be_bytes T) = ([], tagged_prefix tb)).
  { rewrite (absorb_i_fill (be_bytes T) sha256_iv_words (be_bytes T)).
    - rewrite be_words_be_bytes_app. reflexivity.
    - rewrite HbT. reflexivity.
    - intro HN. rewrite HN in HbT. discriminate HbT. }
  rewrite HAbs in HA6. cbn [fst snd] in HA6.
  change (Int64.add (Int64.add Int64.zero (Int64.repr 32)) (Int64.repr 32)) with (Int64.repr 64) in HA6.
  assert (Hovf6 : uc_overflow (uc_overflow false Int64.zero (Int64.repr 32))
    (Int64.add Int64.zero (Int64.repr 32)) (Int64.repr 32) = false) by (vm_compute; reflexivity).
  rewrite Hovf6 in HA6.
  exists mi1, bytes1, m1, m2, m3, mi2, bytes2, m4, m5, m6.
  split; [exact HInit1|]. split; [exact HLB1|]. split; [exact HSB1|]. split; [exact HUc|].
  split; [exact HFin|]. split; [exact HInit2|]. split; [exact HLB2|]. split; [exact HSB2|].
  split; [exact HHc5|]. split; [exact HHc6|]. split; [exact HA6|].
  split; [|split].
  - intros ch b ofs Hv Hn.
    rewrite HL6; [|apply HV5, HV4, V3, Hv|ne|ne].
    rewrite HL5; [|apply HV4, V3, Hv|ne|ne].
    rewrite HL4; [|apply V3, Hv|ne|ne|ne].
    apply K3; [exact Hv|ne|ne|ne].
  - intros b ofs k p Hp. assert (Hp4 : Mem.perm m4 b ofs k p) by (apply HP4, P3, Hp).
    assert (Hp5 : Mem.perm m5 b ofs k p) by (apply HP5; [eapply Mem.perm_valid_block; exact Hp4|exact Hp4]).
    apply HP6; [eapply Mem.perm_valid_block; exact Hp5|exact Hp5].
  - intros b Hv. apply HV6, HV5, HV4, V3, Hv.
Qed.
