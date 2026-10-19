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
Set Default Timeout 60.

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

(** [lia] is slow in the presence of the large memory and context
    hypotheses of these proofs; keep only the arithmetic ones. *)
Ltac zkeep :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch T with
      | (_ <= _)%Z => fail
      | (_ < _)%Z => fail
      | (_ <= _ <= _)%Z => fail
      | (_ <= _ < _)%Z => fail
      | (_ < _ <= _)%Z => fail
      | (_ < _)%nat => fail
      | (_ <= _)%nat => fail
      | @eq Z _ _ => fail
      | @eq nat _ _ => fail
      | _ /\ _ => fail
      | _ \/ _ => fail
      | _ => clear H
      end
  end.
Ltac flia := zkeep; lia.

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
Hypothesis HoRo0 : 0 < no -> oldb bro.
Hypothesis HoSp : forall j, (j < Nn)%nat -> oldb (bsp j).
Hypothesis HRo0 : 0 < no -> Mem.load Mptr m0 braw (oraw + 16) = Some (Vptr bro (Ptrofs.repr oro)).
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
  (forall ch ofs, ofs + size_chunk ch <= OB ->
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
  0 <= k <= 4294967295 -> oro + 24 * k <= 18446744073709551615 ->
  eval_expr sha_ge e le m (Ebinop Oadd (Etempvar _t'7 (tptr ROUT)) (Etempvar _i__1 tulong) (tptr ROUT))
    (Vptr bro (Ptrofs.repr (oro + 24 * k))).
Proof.
  intros Ho Hi Hk Hb. eapply eval_Ebinop; [apply eval_Etempvar; exact Ho|apply eval_Etempvar; exact Hi|].
  rewrite <- (ptr_index_long oro 24 k) by lia. rewrite <- mt_sizeof_ROUT_Z. reflexivity.
Qed.
Lemma out_NnN : Z.of_nat Nn = no.
Proof. unfold Nn. apply Z2Nat.id. lia. Qed.

Lemma out_OB : 488 <= OB <= 1000000000000.
Proof. unfold OB. lia. Qed.

Lemma out_numOutputs le m :
  le!_tx = Some (Vptr bA Ptrofs.zero) ->
  (forall ch ofs, ofs + size_chunk ch <= OB ->
     (ofs + size_chunk ch <= 16 \/ (112 <= ofs /\ ofs + size_chunk ch <= 440) \/ 448 <= ofs) ->
     Mem.load ch m bA ofs = Mem.load ch m0 bA ofs) ->
  eval_expr sha_ge e le m (Efield TXD _numOutputs tulong) (Vlong (Int64.repr no)).
Proof.
  intros Hle HF. pose proof out_OB.
  eapply ev_tx_field with (delta := 456) (chunk := Mint64); [exact Hle|exact envu_tx_numOutputs|reflexivity|lia|].
  rewrite HF; [exact HNo0|change (size_chunk Mint64) with 8; lia|right; right; lia].
Qed.

Lemma out_exit le m : out_inv Nn le m ->
  exists le', out_inv Nn le' m /\
    Clight2.exec_stmt sha_ge e le m (Sloop mt_out_s1 mt_out_s2) E0 le' m Out_normal.
Proof.
  intros (Hi & Htx & Hout & Hraw & HC & HT & HO & HFo & HFa & HPm & HV).
  exists (PTree.set _t'8 (Vlong (Int64.repr no)) le). split.
  { unfold out_inv. rewrite !PTree.gso by discriminate. repeat (split; [assumption|]). assumption. }
  eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
  cbv delta [mt_out_s1] beta iota.
  eapply exec_Sseq_2; [|discriminate].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := PTree.set _t'8 (Vlong (Int64.repr no)) le) (m1 := m).
  - apply exec_Sset. apply out_numOutputs; assumption.
  - eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
    + eapply eval_Ebinop; [apply eval_Etempvar; rewrite PTree.gso by discriminate; exact Hi
                          |apply eval_Etempvar; apply PTree.gss|].
      change (Some (Val.of_bool (Int64.ltu (Int64.repr (Z.of_nat Nn)) (Int64.repr no))) = Some (Vint Int.zero)).
      rewrite out_NnN, i64_ltu_repr by lia. rewrite zlt_false by lia. reflexivity.
    + reflexivity.
    + apply exec_Sbreak.
Qed.

Lemma out_step k le m : (k < Nn)%nat -> out_inv k le m ->
  exists le1 m1 le' m',
    out_inv (S k) le' m' /\
    Clight2.exec_stmt sha_ge e le m mt_out_s1 E0 le1 m1 Out_normal /\
    Clight2.exec_stmt sha_ge e le1 m1 mt_out_s2 E0 le' m' Out_normal.
Proof.
  intros Hk (Hi & Htx & Hout & Hraw & (oS & oV & HC) & HT & HO & HFo & HFa & HPm & HV).
  pose proof out_NnN as HNn. pose proof out_OB as HOB.
  assert (Hpos : 0 < no) by (clear - Hk HNn; lia).
  pose proof (HoRo0 Hpos) as HoRo. pose proof (HRo0 Hpos) as HRo.
  set (kz := Z.of_nat k) in *.
  assert (Hkz : 0 <= kz < no) by (unfold kz; flia).
  set (X := OB + 40 * kz).
  destruct HSepB as (NG & NM & _).
  destruct (Hold braw HoRaw) as (Vraw & NrA & NrO & NrS & NrV).
  destruct (Hold bro HoRo) as (Vro & NoA & NoO & NoS & NoV).
  destruct (Hold (bsp k) (HoSp k Hk)) as (Vsp & NsA & NsO & NsS & NsV).
  pose proof (HC 0%nat _ eq_refl Logic.I) as HC0. cbn [ctx_holds] in HC0.
  destruct HC0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hdisp & HMax).
  destruct (HBufs k Hk) as (len & B1 & B2 & B3 & B4 & B5 & B6).
  fold kz in B1, B2.
  (* copyOutput(&output[i], &rawTx->output[i]) *)
  assert (Q1 : 0 <= X) by (unfold X; flia).
  assert (Q2 : X + 40 <= Ptrofs.max_unsigned)
    by (unfold X; change Ptrofs.max_unsigned with 18446744073709551615; flia).
  assert (Q3 : (8 | X)) by (unfold X, OB; exists (61 + 20 * ni + 5 * kz); flia).
  assert (Q4 : Mem.range_perm m bA X (X + 40) Cur Writable).
  { intros o Ho. apply HPm, PA0. unfold X in Ho. flia. }
  assert (Q10 : 0 <= oro + 24 * kz) by flia.
  assert (Q11 : oro + 24 * kz + 24 <= Ptrofs.max_unsigned) by flia.
  assert (Q12 : Mem.load Mint64 m bro (oro + 24 * kz) = Some (Vlong (val k))).
  { rewrite HFo by exact HoRo. apply HVals. exact Hk. }
  assert (Q13 : Mem.load Mptr m bro (oro + 24 * kz + 8) = Some (Vptr (bsp k) (osp k))).
  { rewrite HFo by exact HoRo. exact B1. }
  assert (Q14 : Mem.load Mint32 m bro (oro + 24 * kz + 16) = Some (Vint len)).
  { rewrite HFo by exact HoRo. replace (oro + 24 * kz + 16) with (oro + 24 * kz + 8 + 8) by flia. exact B2. }
  assert (Q17 : forall i, (i < length (spb k))%nat ->
    Mem.load Mint8unsigned m (bsp k) (Ptrofs.unsigned (osp k) + Z.of_nat i) = Some (Vint (nth i (spb k) Int.zero))).
  { intros i Hi8. rewrite HFo by (apply HoSp; exact Hk). apply B6, Hi8. }
  destruct (eval_copyOutput Hmodel m bA X bro (oro + 24 * kz) (bsp k) (osp k) (spb k) len (val k)
    Q1 Q2 Q3 Q4 (not_eq_sym NG) (not_eq_sym NM) NsA NoA (HV _ Vsp) Q10 Q11 Q12 Q13 Q14 B3 B4 Q17 Hdisp HMax)
    as (m1 & HCall1 & HVal1 & HSpk1 & HL1 & HP1 & HV1).
  set (cs := out_cs k oS oV) in *.
  assert (HSepC : ctxs_sep bA cs) by (apply out_sep; reflexivity).
  assert (HC1 : ctxs_live m1 bA cs (fun _ => True)).
  { eapply (live_other_range m m1 bA cs _ X (X + 40) HC HSepC); [|exact HL1|exact HP1].
    intros j cj Hj _. left. unfold cs, out_cs in Hj.
    destruct j as [|[|[|j]]]; cbn in Hj; try (injection Hj as <-; cbn [ctx_out]; unfold X; flia).
    destruct j; discriminate. }
  (* tx->totalOutputValue += output[i].value *)
  assert (HT1 : Mem.load Mint64 m1 bA 440 = Some (Vlong (out_tot k))).
  { rewrite HL1; [exact HT|apply HV, VA0|right; left; change (size_chunk Mint64) with 8; unfold X; flia]. }
  destruct (Mem.valid_access_store m1 Mint64 bA 440 (Vlong (Int64.add (out_tot k) (val k)))) as [m2 SS].
  { split; [|exists 55; reflexivity]. intros o Ho. change (size_chunk Mint64) with 8 in Ho.
    apply HP1, HPm, PA0. flia. }
  assert (HC2 : ctxs_live m2 bA cs (fun _ => True)).
  { eapply (live_other_range m1 m2 bA cs _ 440 448 HC1 HSepC).
    - intros j cj Hj _. left. unfold cs, out_cs in Hj.
      destruct j as [|[|[|j]]]; cbn in Hj; try (injection Hj as <-; cbn [ctx_out]; flia).
      destruct j; discriminate.
    - intros ch b ofs _ Hr. eapply Mem.load_store_other; [exact SS|].
      destruct Hr as [Hr|[Hr|Hr]]; [left; exact Hr|right; left; exact Hr|right; right; change (size_chunk Mint64) with 8; flia].
    - intros b ofs kk p Hp. eapply Mem.perm_store_1; [exact SS|exact Hp]. }
  (* sha256_u64be(&ctx_outputValuesHash, output[i].value) *)
  destruct (live_u64be Hmodel bA cs (fun _ => True) 2%nat bCV 16 (fst (out_stV k)) (snd (out_stV k))
    (Int64.repr (8 * kz)) oV HSepC eq_refl Logic.I m2 (val k) HC2)
    as (m3 & vr3 & HCall3 & HC3 & HL3 & HP3 & HV3).
  set (cs3 := upd cs 2 (bCV, 16, fst (out_stV (S k)), snd (out_stV (S k)),
    Int64.add (Int64.repr (8 * kz)) (Int64.repr 8), uc_overflow oV (Int64.repr (8 * kz)) (Int64.repr 8))) in *.
  assert (HSep3 : ctxs_sep bA cs3) by (apply out_sep; reflexivity).
  (* sha256_hash(&ctx_outputScriptsHash, &output[i].scriptPubKey) *)
  set (osk := Ptrofs.repr (X + 8)).
  assert (Hosk : Ptrofs.unsigned osk = X + 8).
  { apply Ptrofs.unsigned_repr. unfold X. change Ptrofs.max_unsigned with 18446744073709551615. flia. }
  assert (VA2 : Mem.valid_block m2 bA).
  { eapply Mem.store_valid_block_1; [exact SS|]. apply HV1, HV, VA0. }
  destruct (live_hash Hmodel bA cs3 (fun _ => True) 1%nat bCS 48 (fst (out_stS k)) (snd (out_stS k))
    (Int64.repr (32 * kz)) oS HSep3 eq_refl Logic.I m3 bA osk (norm8 (hash_buffer_regs (spb k))) HC3 eq_refl)
    as (m4 & HCall4 & HC4 & HL4 & HP4 & HV4).
  { rewrite Hosk. unfold X. change Ptrofs.max_unsigned with 18446744073709551615. flia. }
  { intros j Hj. rewrite Hosk, norm8_nth by exact Hj.
    rewrite HL3; [|exact VA2|exact (not_eq_sym (proj1 (proj2 (proj2 (proj2 (Hold _ HoRaw))))) ) || idtac|right; right; unfold X; flia].
    2:{ destruct HSepC as (_ & _ & H1c & _). destruct (H1c 2%nat _ eq_refl) as (D & _). exact (not_eq_sym D). }
    rewrite (Mem.load_store_other _ _ _ _ _ _ SS) by (right; right; change (size_chunk Mint64) with 8; unfold X; flia).
    apply HSpk1, Hj. }
  assert (NACV : bA <> bCV).
  { destruct HSepC as (_ & _ & H1c & _). destruct (H1c 2%nat _ eq_refl) as (D & _). exact (not_eq_sym D). }
  assert (NACS : bA <> bCS).
  { destruct HSepC as (_ & _ & H1c & _). destruct (H1c 1%nat _ eq_refl) as (D & _). exact (not_eq_sym D). }
  assert (VA3 : Mem.valid_block m3 bA) by (apply HV3, VA2).
  (* loads of bA through the four steps *)
  assert (KA : forall ch ofs,
    (ofs + size_chunk ch <= 16 \/ (112 <= ofs /\ ofs + size_chunk ch <= 440) \/ 448 <= ofs) ->
    (ofs + size_chunk ch <= X \/ X + 40 <= ofs) ->
    Mem.load ch m4 bA ofs = Mem.load ch m bA ofs).
  { intros ch ofs Hz Hx.
    rewrite HL4; [|exact VA3|exact NACS|right; flia].
    rewrite HL3; [|exact VA2|exact NACV|right; flia].
    rewrite (Mem.load_store_other _ _ _ _ _ _ SS) by (right; change (size_chunk Mint64) with 8; flia).
    apply HL1; [apply HV, VA0|right; exact Hx]. }
  set (le1 := PTree.set _t'8 (Vlong (Int64.repr no)) le).
  set (le2 := PTree.set _t'7 (Vptr bro (Ptrofs.repr oro)) le1).
  set (le3 := PTree.set _t'5 (Vlong (out_tot k)) le2).
  set (le4 := PTree.set _t'6 (Vlong (val k)) le3).
  set (le5 := PTree.set _t'4 (Vlong (val k)) le4).
  set (le6 := PTree.set _i__1 (Vlong (Int64.repr (Z.of_nat (S k)))) le5).
  assert (G1 : forall x, x <> _t'8 -> le1!x = le!x) by (intros x Hx; unfold le1; apply PTree.gso; exact Hx).
  assert (G2 : forall x, x <> _t'8 -> x <> _t'7 -> le2!x = le!x)
    by (intros x Hx Hy; unfold le2; rewrite PTree.gso by exact Hy; apply G1; exact Hx).
  assert (G5 : forall x, x <> _t'8 -> x <> _t'7 -> x <> _t'5 -> x <> _t'6 -> x <> _t'4 -> le5!x = le!x).
  { intros x H8 H7 H5 H6 H4. unfold le5, le4, le3. rewrite !PTree.gso by assumption. apply G2; assumption. }
  assert (Hi5 : le5!_i__1 = Some (Vlong (Int64.repr kz))) by (rewrite G5 by discriminate; exact Hi).
  assert (Ho5 : le5!_output = Some (Vptr bA (Ptrofs.repr OB))) by (rewrite G5 by discriminate; exact Hout).
  assert (Htx5 : le5!_tx = Some (Vptr bA Ptrofs.zero)) by (rewrite G5 by discriminate; exact Htx).
  assert (EvOut : forall lx mx, lx!_output = Some (Vptr bA (Ptrofs.repr OB)) ->
    lx!_i__1 = Some (Vlong (Int64.repr kz)) ->
    eval_expr sha_ge e lx mx
      (Ederef (Ebinop Oadd (Etempvar _output (tptr SOUT)) (Etempvar _i__1 tulong) (tptr SOUT)) SOUT)
      (Vptr bA (Ptrofs.repr X))).
  { intros lx mx H1 H2. eapply eval_Elvalue; [eapply eval_Ederef; apply ev_out_i; [exact H1|exact H2|flia]
                                             |apply deref_loc_copy; reflexivity]. }
  assert (EvVal : forall lx mx, lx!_output = Some (Vptr bA (Ptrofs.repr OB)) ->
    lx!_i__1 = Some (Vlong (Int64.repr kz)) -> Mem.load Mint64 mx bA X = Some (Vlong (val k)) ->
    eval_expr sha_ge e lx mx
      (Efield (Ederef (Ebinop Oadd (Etempvar _output (tptr SOUT)) (Etempvar _i__1 tulong) (tptr SOUT)) SOUT)
         _value tulong) (Vlong (val k))).
  { intros lx mx H1 H2 HLd. eapply eval_envu_field_value;
      [reflexivity|exact envu_sigOutput_value|reflexivity|apply EvOut; assumption|].
    rewrite envu_ptr_add_repr by (unfold X; change Ptrofs.max_unsigned with 18446744073709551615; flia).
    apply envu_loadv_repr; [unfold X; change Ptrofs.max_unsigned with 18446744073709551615; flia|].
    rewrite Z.add_0_r. exact HLd. }
  assert (HVal2 : Mem.load Mint64 m2 bA X = Some (Vlong (val k))).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ SS) by (right; right; change (size_chunk Mint64) with 8; unfold X; flia).
    exact HVal1. }
  exists le5, m4, le6, m4. split; [|split].
  - unfold out_inv. split; [apply PTree.gss|].
    unfold le6. rewrite !PTree.gso by discriminate.
    split; [exact Htx5|]. split; [exact Ho5|]. split; [rewrite G5 by discriminate; exact Hraw|].
    split.
    { exists (uc_overflow oS (Int64.repr (32 * kz)) (Int64.repr 32)),
             (uc_overflow oV (Int64.repr (8 * kz)) (Int64.repr 8)).
      unfold out_cs.
      replace (Int64.repr (32 * Z.of_nat (S k))) with (Int64.add (Int64.repr (32 * kz)) (Int64.repr 32))
        by (rewrite i64_add_repr by flia; f_equal; unfold kz; flia).
      replace (Int64.repr (8 * Z.of_nat (S k))) with (Int64.add (Int64.repr (8 * kz)) (Int64.repr 8))
        by (rewrite i64_add_repr by flia; f_equal; unfold kz; flia).
      exact HC4. }
    split.
    { cbn [out_tot]. rewrite HL4; [|exact VA3|exact NACS|right; right; flia].
      rewrite HL3; [|exact VA2|exact NACV|right; right; flia].
      rewrite (Mem.load_store_same _ _ _ _ _ _ SS). reflexivity. }
    split.
    { intros j Hj. destruct (Nat.eq_dec j k) as [->|Hne].
      - fold kz. fold X. split.
        + rewrite HL4; [|exact VA3|exact NACS|right; right; unfold X; flia].
          rewrite HL3; [|exact VA2|exact NACV|right; right; unfold X; flia]. exact HVal2.
        + intros i Hi8. rewrite HL4; [|exact VA3|exact NACS|right; right; unfold X; flia].
          rewrite HL3; [|exact VA2|exact NACV|right; right; unfold X; flia].
          rewrite (Mem.load_store_other _ _ _ _ _ _ SS) by (right; right; change (size_chunk Mint64) with 8; unfold X; flia).
          apply HSpk1, Hi8.
      - assert (Hjk : (j < k)%nat) by (clear - Hj Hne; lia). destruct (HO j Hjk) as [HOv HOs]. split.
        + rewrite KA; [exact HOv|right; right; flia|left; change (size_chunk Mint64) with 8; unfold X, kz; flia].
        + intros i Hi8. rewrite KA; [apply HOs, Hi8|right; right; flia
                                    |left; change (size_chunk Mint32) with 4; unfold X, kz; flia]. }
    split.
    { intros ch b ofs Hb. destruct (Hold b Hb) as (Vb & NbA & NbO & NbS & NbV).
      rewrite HL4; [|apply HV3; eapply Mem.store_valid_block_1; [exact SS|]; apply HV1, HV, Vb|exact NbS|left; exact NbA].
      rewrite HL3; [|eapply Mem.store_valid_block_1; [exact SS|]; apply HV1, HV, Vb|exact NbV|left; exact NbA].
      rewrite (Mem.load_store_other _ _ _ _ _ _ SS) by (left; exact NbA).
      rewrite HL1; [apply HFo, Hb|apply HV, Vb|left; exact NbA]. }
    split.
    { intros ch ofs HB Hz. rewrite KA; [apply HFa; assumption|exact Hz|left; unfold X; flia]. }
    split.
    { intros b ofs kk p Hp.
      assert (Hp2 : Mem.perm m2 b ofs kk p) by (eapply Mem.perm_store_1; [exact SS|apply HP1, HPm, Hp]).
      assert (Hp3 : Mem.perm m3 b ofs kk p) by (apply HP3; [eapply Mem.perm_valid_block; exact Hp2|exact Hp2]).
      apply HP4; [eapply Mem.perm_valid_block; exact Hp3|exact Hp3]. }
    { intros b Hb. apply HV4, HV3. eapply Mem.store_valid_block_1; [exact SS|]. apply HV1, HV, Hb. }
  - cbv delta [mt_out_s1] beta iota.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
    { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
      - apply exec_Sset. apply out_numOutputs; assumption.
      - eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
        + eapply eval_Ebinop; [apply eval_Etempvar; rewrite G1 by discriminate; exact Hi
                              |apply eval_Etempvar; apply PTree.gss|].
          change (Some (Val.of_bool (Int64.ltu (Int64.repr kz) (Int64.repr no))) = Some (Vint Int.one)).
          rewrite i64_ltu_repr by flia. rewrite zlt_true by flia. reflexivity.
        + reflexivity.
        + apply exec_Sskip. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m1).
    { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m).
      - apply exec_Sset. eapply eval_envu_field_value;
          [reflexivity|exact envu_rawTx_output|reflexivity
          |apply eval_envu_deref_struct; rewrite G1 by discriminate; exact Hraw|].
        unfold rawv. rewrite envu_ptr_add_repr by flia. apply envu_loadv_repr; [flia|].
        rewrite HFo by exact HoRaw. exact HRo.
      - eapply ci_call_copyOutput with (b1 := bA) (o1 := Ptrofs.repr X) (b2 := bro) (o2 := Ptrofs.repr (oro + 24 * kz));
          [exact HeCp| |reflexivity| |reflexivity|exact HCall1].
        + apply ev_out_i; [rewrite G2 by discriminate; exact Hout|rewrite G2 by discriminate; exact Hi|flia].
        + apply ev_rout_i; [apply PTree.gss|rewrite G2 by discriminate; exact Hi|flia|].
          change Ptrofs.max_unsigned with 18446744073709551615 in Horo. flia. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := m2).
    { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m1).
      - apply exec_Sset. eapply ev_tx_field with (delta := 440) (chunk := Mint64);
          [rewrite G2 by discriminate; exact Htx|exact envu_tx_totalOutputValue|reflexivity|flia|exact HT1].
      - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := m1).
        + apply exec_Sset. apply EvVal; [| |exact HVal1].
          * unfold le3. rewrite PTree.gso by discriminate. rewrite G2 by discriminate. exact Hout.
          * unfold le3. rewrite PTree.gso by discriminate. rewrite G2 by discriminate. exact Hi.
        + eapply exec_Sassign with (v2 := Vlong (Int64.add (out_tot k) (val k)))
            (v := Vlong (Int64.add (out_tot k) (val k))).
          * eapply eval_envu_field_lvalue; [reflexivity|exact envu_tx_totalOutputValue|].
            apply eval_envu_deref_struct. unfold le4, le3. rewrite !PTree.gso by discriminate.
            rewrite G2 by discriminate. exact Htx.
          * eapply eval_Ebinop; [apply eval_Etempvar; unfold le4; rewrite PTree.gso by discriminate; apply PTree.gss
                                |apply eval_Etempvar; apply PTree.gss|reflexivity].
          * reflexivity.
          * eapply assign_loc_value; [reflexivity|]. unfold Mem.storev. rewrite mt_off by flia. exact SS. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le5) (m1 := m3).
    { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le5) (m1 := m2).
      - apply exec_Sset. apply EvVal; [| |exact HVal2].
        + unfold le4, le3. rewrite !PTree.gso by discriminate. rewrite G2 by discriminate. exact Hout.
        + unfold le4, le3. rewrite !PTree.gso by discriminate. rewrite G2 by discriminate. exact Hi.
      - eapply mt_call_u64be with (bx := bCV) (x := val k);
          [exact HeU|exact HeCV|apply eval_Etempvar; apply PTree.gss|reflexivity|exact HCall3]. }
    eapply mt_call_hash with (bx := bCS) (bt := bA) (ot := osk);
      [exact HeH|exact HeCS| |reflexivity|exact HCall4].
    unfold osk. rewrite <- envu_ptr_add_repr by (unfold X; change Ptrofs.max_unsigned with 18446744073709551615; flia).
    eapply eval_Eaddrof. eapply eval_envu_field_lvalue; [reflexivity|exact envu_sigOutput_scriptPubKey|].
    apply EvOut; assumption.
  - cbv delta [mt_out_s2] beta iota.
    apply exec_Sset. eapply eval_Ebinop; [apply eval_Etempvar; exact Hi5|apply eval_Econst_int|].
    change (Some (Vlong (Int64.add (Int64.repr kz) (Int64.repr 1))) = Some (Vlong (Int64.repr (Z.of_nat (S k))))).
    rewrite i64_add_repr by flia. replace (Z.of_nat (S k)) with (kz + 1) by (unfold kz; flia). reflexivity.
Qed.

Theorem out_loop d : forall k le m, (k + d = Nn)%nat -> out_inv k le m ->
  exists le' m', out_inv Nn le' m' /\
    Clight2.exec_stmt sha_ge e le m (Sloop mt_out_s1 mt_out_s2) E0 le' m' Out_normal.
Proof.
  induction d as [|d IH]; intros k le m Hkd HI.
  - replace k with Nn in HI by lia. destruct (out_exit le m HI) as (le' & HI' & HE).
    exists le', m. split; assumption.
  - destruct (out_step k le m ltac:(lia) HI) as (le1 & m1 & le2 & m2 & HI2 & H1 & H2).
    destruct (IH (S k) le2 m2 ltac:(lia) HI2) as (le' & m' & HI' & HE).
    exists le', m'. split; [exact HI'|].
    change E0 with (E0 ** E0 ** E0).
    eapply exec_Sloop_loop; [exact H1|constructor|exact H2|exact HE].
Qed.
End OutLoop.
