(** [simplicity_bitcoin_mallocTapEnv], the tap-path loop
      for (int i = 0; i < env->pathLen; ++i) {
        sha256_toMidstate(path[i].s, &rawEnv->controlBlock[33+32*i]);
        sha256_hash(&ctx, &path[i]);
      }
    Each iteration stores one 32-byte branch hash as a midstate in the path
    array and absorbs it into the context whose output is
    [env->tappathHash].  Conditional on [memcpy_model]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_uint32_array_init C.jet_sha256_iv_init.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_add_n_init C.jet_sha_be32_exec C.jet_sha_ctx8_model.
Require Import C.jet_sha_be32_write C.jet_sha_uchars_prep C.jet_sha_uchars_exec C.jet_sha_add_n_calls C.jet_sha_hash_exec C.jet_sha_ctx_abs.
Require Import C.jet_env_store_words C.jet_bitcoin_env_field_eval C.jet_bitcoin_env_tomidstate C.jet_bitcoin_env_ctxo.
Require Import C.jet_bitcoin_env_tapenv_prelude C.jet_bitcoin_env_tapenv_key C.jet_bitcoin_env_tapenv_fill.
Require Import C.jet_bitcoin_env_tapenv_cmr.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Definition te_p5 : statement :=
  ltac:(let b := eval cbv delta [te_rest4] in te_rest4 in
        lazymatch b with Ssequence ?s _ => exact s end).
Definition te_loop_s1 : statement :=
  ltac:(let b := eval cbv delta [te_p5] in te_p5 in
        lazymatch b with Ssequence _ (Ssequence (Ssequence _ (Sloop ?s1 _)) _) => exact s1 end).
Definition te_loop_s2 : statement :=
  ltac:(let b := eval cbv delta [te_p5] in te_p5 in
        lazymatch b with Ssequence _ (Ssequence (Ssequence _ (Sloop _ ?s2)) _) => exact s2 end).

Lemma ptr_byte_offset_big (o : ptrofs) (i : Z) :
  0 <= i <= 1000000 -> Ptrofs.unsigned o + i <= Ptrofs.max_unsigned ->
  Ptrofs.unsigned (Ptrofs.add o (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr i)))) =
    Ptrofs.unsigned o + i.
Proof.
  intros Hi Hm. pose proof (Ptrofs.unsigned_range o) as HO.
  assert (HI : Ptrofs.of_ints (Int.repr i) = Ptrofs.repr i).
  { unfold Ptrofs.of_ints. rewrite Int.signed_repr; [reflexivity|].
    change Int.min_signed with (-2147483648). change Int.max_signed with 2147483647. lia. }
  rewrite HI, Ptrofs.mul_commut, Ptrofs.mul_one.
  unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr i) by
    (change Ptrofs.max_unsigned with 18446744073709551615 in *; lia).
  apply Ptrofs.unsigned_repr. lia.
Qed.

Lemma te_cb_index k : 0 <= k <= 128 ->
  Int.add (Int.repr 33) (Int.mul (Int.repr 32) (Int.repr k)) = Int.repr (33 + 32 * k).
Proof.
  intros Hk. unfold Int.add, Int.mul.
  rewrite (Int.unsigned_repr 32), (Int.unsigned_repr k), (Int.unsigned_repr 33)
    by (change Int.max_unsigned with 4294967295; lia).
  rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia). reflexivity.
Qed.

Lemma te_path_index k : 0 <= k <= 128 ->
  Ptrofs.add (Ptrofs.repr 176) (Ptrofs.mul (Ptrofs.repr 32) (Ptrofs.of_ints (Int.repr k))) =
    Ptrofs.repr (176 + 32 * k).
Proof.
  intros Hk.
  assert (HI : Ptrofs.of_ints (Int.repr k) = Ptrofs.repr k).
  { unfold Ptrofs.of_ints. rewrite Int.signed_repr; [reflexivity|].
    change Int.min_signed with (-2147483648). change Int.max_signed with 2147483647. lia. }
  rewrite HI. unfold Ptrofs.add, Ptrofs.mul.
  rewrite (Ptrofs.unsigned_repr 32), (Ptrofs.unsigned_repr k), (Ptrofs.unsigned_repr 176)
    by (change Ptrofs.max_unsigned with 18446744073709551615; lia).
  rewrite Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615; lia). reflexivity.
Qed.

Lemma te_counter_add k : 0 <= k <= 128 ->
  Int64.add (Int64.repr (32 * k)) (Int64.repr 32) = Int64.repr (32 * (k + 1)).
Proof.
  intros Hk. unfold Int64.add.
  rewrite !Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
  f_equal. lia.
Qed.

Local Opaque sha_ge.

Lemma ev_path_i e le m bA k :
  le!_path = Some (Vptr bA (Ptrofs.repr 176)) -> le!_i = Some (Vint (Int.repr k)) -> 0 <= k <= 128 ->
  eval_expr sha_ge e le m (Ebinop Oadd (Etempvar _path (tptr MID)) (Etempvar _i tint) (tptr MID))
    (Vptr bA (Ptrofs.repr (176 + 32 * k))).
Proof.
  intros Hp Hi Hk. eapply eval_Ebinop; [apply eval_Etempvar; exact Hp|apply eval_Etempvar; exact Hi|].
  rewrite <- (te_path_index k Hk), <- te_sizeof_MID_Z. reflexivity.
Qed.

Lemma te_call_hash e le m m' bx (a2 : expr) bt ot :
  e!_sha256_hash = None -> e!_ctx = Some (bx, CTX) ->
  eval_expr sha_ge e le m a2 (Vptr bt ot) -> typeof a2 = tptr MID ->
  Clight2.eval_funcall sha_ge m (Internal f_sha256_hash) [Vptr bx (Ptrofs.repr 0); Vptr bt ot] E0 m' Vundef ->
  Clight2.exec_stmt sha_ge e le m
    (Scall None (Evar _sha256_hash (Tfunction (Tcons CTXP (Tcons (tptr MID) Tnil)) tvoid cc_default))
       [Eaddrof (Evar _ctx CTX) CTXP; a2]) E0 le m' Out_normal.
Proof.
  intros He Hc H2 T2 HC. change le with (set_opttemp None Vundef le) at 2.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_hash) Ptrofs.zero)
    (vargs := [Vptr bx Ptrofs.zero; Vptr bt ot]) (f := Internal f_sha256_hash).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact He|exact sha_hash_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; exact Hc|reflexivity|].
    eapply eval_Econs; [exact H2|rewrite T2; reflexivity|apply eval_Enil].
  - exact sha_hash_funct.
  - reflexivity.
  - exact HC.
Qed.

Lemma te_int_succ k : 0 <= k <= 128 -> Int.add (Int.repr k) (Int.repr 1) = Int.repr (k + 1).
Proof.
  intros Hk. unfold Int.add.
  rewrite !Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia). reflexivity.
Qed.

Section Loop.
Variable Hmodel : memcpy_model.
Variables (e : env) (bC bA braw bcb : block) (oraw : Z) (ocb : ptrofs) (nb : int) (pb : nat -> list int) (m0 : mem).
Hypothesis HeT : e!_sha256_toMidstate = None.
Hypothesis HeH : e!_sha256_hash = None.
Hypothesis HeCtx : e!_ctx = Some (bC, CTX).
Hypothesis NAC : bA <> bC.
Hypothesis NGC : GC <> bC.
Hypothesis NGA : GC <> bA.
Hypothesis NMC : GM <> bC.
Hypothesis NMA : GM <> bA.
Hypothesis NAcb : bA <> bcb.
Hypothesis NrC : braw <> bC.
Hypothesis NrA : braw <> bA.
Hypothesis NcC : bcb <> bC.
Hypothesis Horaw : 0 <= oraw /\ oraw + 24 <= Ptrofs.max_unsigned.
Hypothesis HN : 0 <= Int.unsigned nb <= 128.

Let rawv := Vptr braw (Ptrofs.repr oraw).
Let N := Int.unsigned nb.
Let Nn := Z.to_nat N.

Hypothesis HCb : Mem.load Mptr m0 braw oraw = Some (Vptr bcb ocb).
Hypothesis Hocb : Ptrofs.unsigned ocb + 33 + 32 * N <= Ptrofs.max_unsigned.
Hypothesis HPb : forall j i, (j < Nn)%nat -> (i < 32)%nat ->
  Mem.load Mint8unsigned m0 bcb (Ptrofs.unsigned ocb + 33 + 32 * Z.of_nat j + Z.of_nat i) =
    Some (Vint (nth i (pb j) Int.zero)).
Hypothesis HPl : Mem.load Mint8unsigned m0 bA 168 = Some (Vint nb).
Hypothesis PA : Mem.range_perm m0 bA 0 (176 + 32 * N) Cur Writable.
Hypothesis Vraw : Mem.valid_block m0 braw.
Hypothesis Vcb : Mem.valid_block m0 bcb.
Hypothesis VA : Mem.valid_block m0 bA.

(** The context state after absorbing the first [k] branch hashes. *)
Fixpoint te_st (k : nat) : list int * list int :=
  match k with
  | O => ([], sha256_iv_words)
  | S k' => absorb_i (fst (te_st k')) (snd (te_st k')) (be_bytes (tm_words (pb k')))
  end.

Definition te_inv (k : nat) (le : temp_env) (m : mem) : Prop :=
  le!_i = Some (Vint (Int.repr (Z.of_nat k))) /\
  le!_env = Some (Vptr bA Ptrofs.zero) /\
  le!_path = Some (te_path_value N bA) /\
  le!_rawEnv = Some rawv /\
  (exists ovf, ctxo m bC bA 40 (fst (te_st k)) (snd (te_st k)) (Int64.repr (32 * Z.of_nat k)) ovf) /\
  (forall j i, (j < k)%nat -> (i < 8)%nat ->
     Mem.load Mint32 m bA (176 + 32 * Z.of_nat j + 4 * Z.of_nat i) = Some (Vint (nth i (tm_words (pb j)) Int.zero))) /\
  (forall ch b ofs, Mem.valid_block m0 b -> b <> bC ->
     (b <> bA \/ ofs + size_chunk ch <= 40 \/ (72 <= ofs /\ ofs + size_chunk ch <= 176)) ->
     Mem.load ch m b ofs = Mem.load ch m0 b ofs) /\
  (forall b ofs kk p, Mem.perm m0 b ofs kk p -> Mem.perm m b ofs kk p) /\
  (forall b, Mem.valid_block m0 b -> Mem.valid_block m b).

Lemma te_lt k : Z.of_nat k <= 128 ->
  Int.lt (Int.repr (Z.of_nat k)) nb = if zlt (Z.of_nat k) (Int.unsigned nb) then true else false.
Proof.
  intros Hk. pose proof HN as HN'. unfold Int.lt.
  rewrite Int.signed_repr
    by (change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia).
  rewrite Int.signed_eq_unsigned by (change Int.max_signed with 2147483647; lia).
  reflexivity.
Qed.
Lemma te_NnN : Z.of_nat Nn = N.
Proof. unfold Nn. apply Z2Nat.id. unfold N. pose proof HN. lia. Qed.

Lemma te_pathLen_env le m :
  le!_env = Some (Vptr bA Ptrofs.zero) ->
  (forall ch b ofs, Mem.valid_block m0 b -> b <> bC ->
     (b <> bA \/ ofs + size_chunk ch <= 40 \/ (72 <= ofs /\ ofs + size_chunk ch <= 176)) ->
     Mem.load ch m b ofs = Mem.load ch m0 b ofs) ->
  eval_expr sha_ge e le m (Efield ENV _pathLen tuchar) (Vint nb).
Proof.
  intros Hle HF. eapply ev_env_field with (delta := 168) (chunk := Mint8unsigned);
    [exact Hle|exact envu_bitcoinTapEnv_pathLen|reflexivity|lia|].
  rewrite HF; [exact HPl|exact VA|exact NAC|]. right; right. cbn. lia.
Qed.

Lemma te_loop_exit le m : te_inv Nn le m ->
  exists le', te_inv Nn le' m /\
    Clight2.exec_stmt sha_ge e le m (Sloop te_loop_s1 te_loop_s2) E0 le' m Out_normal.
Proof.
  intros (Hi & Henv & Hpath & Hraw & HC & HP & HF & HPm & HV).
  exists (PTree.set _t'4 (Vint nb) le). split.
  { unfold te_inv. rewrite !PTree.gso by discriminate. repeat split; assumption. }
  eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
  cbv delta [te_loop_s1] beta iota.
  eapply exec_Sseq_2; [|discriminate].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := PTree.set _t'4 (Vint nb) le) (m1 := m).
  - apply exec_Sset. apply te_pathLen_env; assumption.
  - eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
    + eapply eval_Ebinop; [apply eval_Etempvar; rewrite PTree.gso by discriminate; exact Hi
                          |apply eval_Etempvar; apply PTree.gss|].
      change (Some (Val.of_bool (Int.lt (Int.repr (Z.of_nat Nn)) nb)) = Some (Vint Int.zero)).
      rewrite te_lt by (rewrite te_NnN; unfold N; pose proof HN; lia).
      rewrite te_NnN. fold N. rewrite zlt_false by lia. reflexivity.
    + reflexivity.
    + apply exec_Sbreak.
Qed.

Lemma te_loop_step k le m : (k < Nn)%nat -> te_inv k le m ->
  exists le1 m1 le' m',
    te_inv (S k) le' m' /\
    Clight2.exec_stmt sha_ge e le m te_loop_s1 E0 le1 m1 Out_normal /\
    Clight2.exec_stmt sha_ge e le1 m1 te_loop_s2 E0 le' m' Out_normal.
Proof.
  intros Hk (Hi & Henv & Hpath & Hraw & (ovf & HC) & HP & HF & HPm & HV).
  pose proof te_NnN as HNn. pose proof HN as HN'. fold N in HN'.
  set (kz := Z.of_nat k) in *.
  assert (Hkz : 0 <= kz < N) by (unfold kz; lia).
  assert (HpathV : le!_path = Some (Vptr bA (Ptrofs.repr 176))).
  { rewrite Hpath. unfold te_path_value. destruct (Z.eq_dec N 0); [lia|reflexivity]. }
  set (oh := Ptrofs.add ocb (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr (33 + 32 * kz))))).
  assert (Hoh : Ptrofs.unsigned oh = Ptrofs.unsigned ocb + 33 + 32 * kz).
  { unfold oh. rewrite ptr_byte_offset_big by lia. lia. }
  set (pk := Ptrofs.repr (176 + 32 * kz)).
  assert (Hpk : Ptrofs.unsigned pk = 176 + 32 * kz).
  { apply Ptrofs.unsigned_repr. change Ptrofs.max_unsigned with 18446744073709551615. lia. }
  assert (VAm : Mem.valid_block m bA) by (apply HV, VA).
  (* sha256_toMidstate(path[i].s, controlBlock + 33 + 32*i) *)
  destruct (eval_sha256_toMidstate bA bcb pk oh (pb k) NAcb) with (m := m) as (m1 & HSt & HCallT).
  { rewrite Hoh. lia. }
  { rewrite Hpk. change Ptrofs.max_unsigned with 18446744073709551615. lia. }
  { rewrite Hpk. exists (44 + 8 * kz). lia. }
  { intros i Hi32. rewrite Hoh. rewrite HF; [apply HPb; [exact Hk|exact Hi32]|exact Vcb|exact NcC|].
    left. congruence. }
  { rewrite Hpk. intros o Ho. apply HPm, PA. lia. }
  rewrite Hpk in HSt.
  assert (HLenW : length (tm_words (pb k)) = 8%nat) by reflexivity.
  assert (L1 : forall ch b ofs,
    (b <> bA \/ ofs + size_chunk ch <= 176 + 32 * kz \/ 176 + 32 * kz + 32 <= ofs) ->
    Mem.load ch m1 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hc. apply (store_words_load_other _ _ _ _ _ HSt). rewrite HLenW.
    destruct Hc as [Hc|[Hc|Hc]]; [left; exact Hc|right; left; exact Hc|right; right; lia]. }
  assert (P1 : forall b ofs kk p, Mem.perm m b ofs kk p -> Mem.perm m1 b ofs kk p).
  { intros b ofs kk p Hp. apply (store_words_perm _ _ _ _ _ HSt). exact Hp. }
  assert (V1 : forall b, Mem.valid_block m b -> Mem.valid_block m1 b).
  { intros b Hb. unfold Mem.valid_block. rewrite (store_words_nextblock _ _ _ _ _ HSt). exact Hb. }
  assert (Hob40 : 0 <= 40 /\ 40 + 32 <= Ptrofs.max_unsigned)
    by (change Ptrofs.max_unsigned with 18446744073709551615; lia).
  assert (HC1 : ctxo m1 bC bA 40 (fst (te_st k)) (snd (te_st k)) (Int64.repr (32 * kz)) ovf).
  { eapply (ctxo_other bC bA 40) with (m := m); try eassumption.
    - intros ch b ofs Hb. apply L1.
      destruct Hb as [->|[->|[->|[-> Hr]]]];
        [left; congruence|left; exact NGA|left; exact NMA|right; left; lia].
    - intros b ofs kk p _ Hp. apply P1, Hp. }
  assert (HW1 : forall j, (j < 8)%nat ->
    Mem.load Mint32 m1 bA (Ptrofs.unsigned pk + 4 * Z.of_nat j) = Some (Vint (nth j (tm_words (pb k)) Int.zero))).
  { intros j Hj. rewrite Hpk. apply (u32_nth m1 bA (176 + 32 * kz) (tm_words (pb k))).
    - eapply store_words_loads. exact HSt.
    - rewrite HLenW. exact Hj. }
  assert (HpkM : Ptrofs.unsigned pk + 32 <= Ptrofs.max_unsigned)
    by (rewrite Hpk; change Ptrofs.max_unsigned with 18446744073709551615; lia).
  (* sha256_hash(&ctx, &path[i]) *)
  edestruct (ctxo_hash bC bA 40) with (m := m1) (bt := bA) (ot := pk) (regsH := tm_words (pb k))
    as (m2 & HCallH & HC2 & HL2 & HP2 & HV2); try eassumption.
  set (le1 := PTree.set _t'4 (Vint nb) le).
  set (le2 := PTree.set _t'3 (Vptr bcb ocb) le1).
  set (le3 := PTree.set _i (Vint (Int.repr (Z.of_nat (S k)))) le2).
  assert (Hi2 : le2!_i = Some (Vint (Int.repr kz))).
  { unfold le2, le1. rewrite !PTree.gso by discriminate. exact Hi. }
  assert (Hp2 : le2!_path = Some (Vptr bA (Ptrofs.repr 176))).
  { unfold le2, le1. rewrite !PTree.gso by discriminate. exact HpathV. }
  exists le2, m2, le3, m2. split; [|split].
  - unfold te_inv. split; [apply PTree.gss|].
    split; [unfold le3, le2, le1; rewrite !PTree.gso by discriminate; exact Henv|].
    split; [unfold le3, le2, le1; rewrite !PTree.gso by discriminate; exact Hpath|].
    split; [unfold le3, le2, le1; rewrite !PTree.gso by discriminate; exact Hraw|].
    split.
    { eexists. cbn [te_st].
      replace (Int64.repr (32 * Z.of_nat (S k))) with (Int64.add (Int64.repr (32 * kz)) (Int64.repr 32)).
      - exact HC2.
      - rewrite te_counter_add by lia. f_equal. unfold kz. lia. }
    split.
    { intros j i Hj Hi8.
      rewrite HL2; [|apply V1, VAm|exact NAC|right; right; lia].
      destruct (Nat.eq_dec j k) as [->|Hne].
      - fold kz. rewrite <- Hpk. apply HW1. exact Hi8.
      - rewrite L1 by (right; left; change (size_chunk Mint32) with 4; unfold kz; lia).
        apply HP; [lia|exact Hi8]. }
    split.
    { intros ch b ofs Hb NbC Hr.
      rewrite HL2; [|apply V1, HV, Hb|exact NbC|destruct Hr as [Hr|[Hr|Hr]]; [left; exact Hr|right; left; exact Hr|right; right; lia]].
      rewrite L1 by (destruct Hr as [Hr|[Hr|Hr]]; [left; exact Hr|right; left; lia|right; left; lia]).
      apply HF; assumption. }
    split.
    { intros b ofs kk p Hp. apply HP2; [eapply Mem.perm_valid_block; apply P1, HPm, Hp|apply P1, HPm, Hp]. }
    { intros b Hb. apply HV2, V1, HV, Hb. }
  - cbv delta [te_loop_s1] beta iota.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
      * apply exec_Sset. apply te_pathLen_env; assumption.
      * eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
        -- eapply eval_Ebinop; [apply eval_Etempvar; unfold le1; rewrite PTree.gso by discriminate; exact Hi
                               |apply eval_Etempvar; apply PTree.gss|].
           change (Some (Val.of_bool (Int.lt (Int.repr (Z.of_nat k)) nb)) = Some (Vint Int.one)).
           rewrite te_lt by (fold kz; lia). fold kz. fold N. rewrite zlt_true by lia. reflexivity.
        -- reflexivity.
        -- apply exec_Sskip.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m1).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m).
        -- apply exec_Sset. apply (te_cb_expr e le1 m braw oraw bcb ocb Horaw).
           ++ unfold le1. rewrite PTree.gso by discriminate. exact Hraw.
           ++ rewrite HF; [exact HCb|exact Vraw|exact NrC|left; exact NrA].
        -- eapply te_call_toMidstate with (bm := bA) (om := pk) (bh := bcb) (oh := oh);
             [exact HeT| |reflexivity| |reflexivity|exact HCallT].
           ++ pose proof (eval_envu_field_array e le2 m
                (Ederef (Ebinop Oadd (Etempvar _path (tptr MID)) (Etempvar _i tint) (tptr MID)) MID)
                _sha256_midstate _s 0 A8 bA pk eq_refl envu_sha256_midstate_s
                ltac:(intros chunk; discriminate) eq_refl) as HE.
              rewrite Ptrofs.add_zero in HE. apply HE.
              eapply eval_Elvalue; [eapply eval_Ederef; apply ev_path_i; [exact Hp2|exact Hi2|lia]
                                   |apply deref_loc_copy; reflexivity].
           ++ eapply eval_Ebinop with (v2 := Vint (Int.repr (33 + 32 * kz)));
                [apply eval_Etempvar; apply PTree.gss| |reflexivity].
              eapply eval_Ebinop with (v1 := Vint (Int.repr 33)) (v2 := Vint (Int.mul (Int.repr 32) (Int.repr kz)));
                [apply eval_Econst_int
                |eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; exact Hi2|reflexivity]
                |].
              rewrite <- te_cb_index by lia. reflexivity.
      * eapply te_call_hash with (bx := bC) (bt := bA) (ot := pk);
          [exact HeH|exact HeCtx| |reflexivity|exact HCallH].
        apply ev_path_i; [exact Hp2|exact Hi2|lia].
  - cbv delta [te_loop_s2] beta iota.
    apply exec_Sset.
    eapply eval_Ebinop; [apply eval_Etempvar; exact Hi2|apply eval_Econst_int|].
    change (Some (Vint (Int.add (Int.repr kz) (Int.repr 1))) = Some (Vint (Int.repr (Z.of_nat (S k))))).
    rewrite te_int_succ by lia. replace (Z.of_nat (S k)) with (kz + 1) by (unfold kz; lia). reflexivity.
Qed.

Theorem te_loop_exec d : forall k le m, (k + d = Nn)%nat -> te_inv k le m ->
  exists le' m', te_inv Nn le' m' /\
    Clight2.exec_stmt sha_ge e le m (Sloop te_loop_s1 te_loop_s2) E0 le' m' Out_normal.
Proof.
  induction d as [|d IH]; intros k le m Hkd HI.
  - replace k with Nn in HI by lia. destruct (te_loop_exit le m HI) as (le' & HI' & HE).
    exists le', m. split; assumption.
  - destruct (te_loop_step k le m ltac:(lia) HI) as (le1 & m1 & le2 & m2 & HI2 & H1 & H2).
    destruct (IH (S k) le2 m2 ltac:(lia) HI2) as (le' & m' & HI' & HE).
    exists le', m'. split; [exact HI'|].
    change E0 with (E0 ** E0 ** E0).
    eapply exec_Sloop_loop; [exact H1|constructor|exact H2|exact HE].
Qed.
End Loop.
