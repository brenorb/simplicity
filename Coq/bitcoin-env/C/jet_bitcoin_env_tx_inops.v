(** [simplicity_bitcoin_mallocTransaction], the input loop: the context
    operations of one iteration (after [copyInput] and the two updates of
    [tx]).  Conditional on [memcpy_model]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_sha256_iv_init C.jet_bitmachine_rep.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_add_n_init C.jet_sha_ctx8_model.
Require Import C.jet_sha_be32_write C.jet_sha_be64_exec C.jet_sha_uchars_prep C.jet_sha_uchars_exec C.jet_sha_ctx_abs.
Require Import C.jet_bitcoin_env_field_eval C.jet_bitcoin_env_tomidstate C.jet_bitcoin_env_hashbuffer C.jet_bitcoin_env_ctxo.
Require Import C.jet_bitcoin_env_ctxs C.jet_bitcoin_env_ctxs_ops C.jet_bitcoin_env_ctxs_calls C.jet_bitcoin_env_ctxs_core.
Require Import C.jet_bitcoin_env_tapenv_prelude C.jet_bitcoin_env_tapenv_tail.
Require Import C.jet_bitcoin_env_copyoutput C.jet_bitcoin_env_copyinput_fill C.jet_bitcoin_env_copyinput.
Require Import C.jet_bitcoin_env_tx_prelude C.jet_bitcoin_env_tx_fill C.jet_bitcoin_env_tx_init.
Require Import C.jet_bitcoin_env_tx_txid C.jet_bitcoin_env_tx_inblock C.jet_bitcoin_env_tx_txhash.
Require Import C.jet_bitcoin_env_tx_calls C.jet_bitcoin_env_tx_outdefs C.jet_bitcoin_env_tx_outloop.
Require Import C.jet_bitcoin_env_tx_indefs.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 120.

Local Opaque sha_ge.

Notation DIN := (Ederef (Ebinop Oadd (Etempvar _input (tptr SIN)) (Etempvar _i tulong) (tptr SIN)) SIN).

(** Members of a structure at [base] of block [b]. *)
Lemma ev_sub e le m a sid f delta sid2 b base :
  typeof a = Tstruct sid noattr -> envu_field_at sid f delta ->
  eval_expr sha_ge e le m a (Vptr b (Ptrofs.repr base)) ->
  0 <= base -> 0 <= delta -> base + delta <= Ptrofs.max_unsigned ->
  eval_expr sha_ge e le m (Efield a f (Tstruct sid2 noattr)) (Vptr b (Ptrofs.repr (base + delta))).
Proof.
  intros HT HF HA H0 H1 H2. rewrite <- envu_ptr_add_repr by lia.
  eapply eval_Elvalue; [eapply eval_envu_field_lvalue; eassumption|apply deref_loc_copy; reflexivity].
Qed.

Lemma ev_ld e le m a sid f delta ty chunk b base v :
  typeof a = Tstruct sid noattr -> envu_field_at sid f delta -> access_mode ty = By_value chunk ->
  eval_expr sha_ge e le m a (Vptr b (Ptrofs.repr base)) ->
  0 <= base -> 0 <= delta -> base + delta <= Ptrofs.max_unsigned ->
  Mem.load chunk m b (base + delta) = Some v ->
  eval_expr sha_ge e le m (Efield a f ty) v.
Proof.
  intros HT HF HM HA H0 H1 H2 HL.
  eapply eval_envu_field_value; [exact HT|exact HF|exact HM|exact HA|].
  rewrite envu_ptr_add_repr by lia. apply envu_loadv_repr; [lia|exact HL].
Qed.

Lemma ev_adr e le m a sid f delta ty b base :
  typeof a = Tstruct sid noattr -> envu_field_at sid f delta ->
  eval_expr sha_ge e le m a (Vptr b (Ptrofs.repr base)) ->
  0 <= base -> 0 <= delta -> base + delta <= Ptrofs.max_unsigned ->
  eval_expr sha_ge e le m (Eaddrof (Efield a f ty) (tptr ty)) (Vptr b (Ptrofs.repr (base + delta))).
Proof.
  intros HT HF HA H0 H1 H2. rewrite <- envu_ptr_add_repr by lia.
  eapply eval_Eaddrof. eapply eval_envu_field_lvalue; eassumption.
Qed.

Lemma mt_call_uchar e le m m' (id : ident) bx (n x : int) vr :
  e!_sha256_uchar = None -> e!id = Some (bx, CTX) -> Int.zero_ext 8 n = x ->
  Clight2.eval_funcall sha_ge m (Internal f_sha256_uchar) [Vptr bx (Ptrofs.repr 0); Vint x] E0 m' vr ->
  Clight2.exec_stmt sha_ge e le m
    (Scall None (Evar _sha256_uchar (Tfunction (Tcons CTXP (Tcons tuchar Tnil)) tbool cc_default))
       [Eaddrof (Evar id CTX) CTXP; Econst_int n tint]) E0 le m' Out_normal.
Proof.
  intros He Hc Hx HC. change le with (set_opttemp None vr le) at 2.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_uchar) Ptrofs.zero)
    (vargs := [Vptr bx Ptrofs.zero; Vint x]) (f := Internal f_sha256_uchar).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact He|exact sha_uchar_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; exact Hc|reflexivity|].
    eapply eval_Econs; [apply eval_Econst_int|rewrite <- Hx; reflexivity|apply eval_Enil].
  - exact sha_uchar_funct.
  - reflexivity.
  - exact HC.
Qed.

Lemma upd_upd {A} (l : list A) : forall k (x y : A), upd (upd l k x) k y = upd l k y.
Proof. induction l as [|a l IH]; intros [|k] x y; cbn; try reflexivity. f_equal. apply IH. Qed.

Definition an_cnt (c : int64) (d : in_data) : int64 :=
  if Int.eq (d_has d) Int.zero then Int64.add c (Int64.repr 1)
  else Int64.add (Int64.add c (Int64.repr 1)) (Int64.repr 32).

Ltac ls_cores H := lazymatch type of H with LS _ _ ?c _ => c end.
Ltac inb := cbn [In]; repeat (first [left; reflexivity | right]).

(** [if (input[i].hasAnnex) { uchar 1; hash annexHash } else { uchar 0 }] *)
Section Annex.
Variable Hmodel : memcpy_model.
Variables (e : env) (bA bN : block) (cores : list ctx_core) (live : nat -> Prop) (kN : nat).
Variables (l regs : list int) (c : int64) (X : Z) (d : in_data).
Hypothesis HeN : e!_ctx_inputAnnexesHash = Some (bN, CTX).
Hypothesis HeH : e!_sha256_hash = None.
Hypothesis HeUc : e!_sha256_uchar = None.
Hypothesis Hk : nth_error cores kN = Some (bN, 272, l, regs, c).
Hypothesis Hlive : live kN.
Hypothesis HXb : 0 <= X /\ X + 160 <= Ptrofs.max_unsigned.

Lemma in_annex le m :
  eval_expr sha_ge e le m DIN (Vptr bA (Ptrofs.repr X)) ->
  le!_t'9 = Some (Vint (d_has d)) ->
  LS m bA cores live ->
  (forall mx, mfrP (opP bA bN 272) m mx -> eval_expr sha_ge e le mx DIN (Vptr bA (Ptrofs.repr X))) ->
  (forall mx, mfrP (opP bA bN 272) m mx -> forall j, (j < 8)%nat ->
     Mem.load Mint32 mx bA (X + 4 * Z.of_nat j) = Some (Vint (nth j (d_areg d) Int.zero))) ->
  exists m',
    Clight2.exec_stmt sha_ge e le m
      (Sifthenelse (Etempvar _t'9 tbool)
         (Ssequence
            (Scall None (Evar _sha256_uchar (Tfunction (Tcons CTXP (Tcons tuchar Tnil)) tbool cc_default))
               [Eaddrof (Evar _ctx_inputAnnexesHash CTX) CTXP; Econst_int (Int.repr 1) tint])
            (Scall None (Evar _sha256_hash (Tfunction (Tcons CTXP (Tcons (tptr MID) Tnil)) tvoid cc_default))
               [Eaddrof (Evar _ctx_inputAnnexesHash CTX) CTXP; Eaddrof (Efield DIN _annexHash MID) (tptr MID)]))
         (Scall None (Evar _sha256_uchar (Tfunction (Tcons CTXP (Tcons tuchar Tnil)) tbool cc_default))
            [Eaddrof (Evar _ctx_inputAnnexesHash CTX) CTXP; Econst_int (Int.repr 0) tint]))
      E0 le m' Out_normal /\
    LS m' bA (upd cores kN (bN, 272, fst (an_step (l, regs) d), snd (an_step (l, regs) d), an_cnt c d)) live /\
    mfrP (opP bA bN 272) m m'.
Proof.
  intros HD Ht9 HLS HDx HAx. unfold an_step, an_cnt.
  destruct (Int.eq (d_has d) Int.zero) eqn:Ehas.
  - destruct (LS_uchar Hmodel bA cores live kN bN 272 l regs c Hk Hlive m Int.zero HLS eq_refl)
      as (m1 & vr1 & HCall1 & HLS1 & HF1).
    exists m1. split; [|split; [exact HLS1|exact HF1]].
    eapply exec_Sifthenelse with (v1 := Vint (d_has d)) (b := false).
    + apply eval_Etempvar. exact Ht9.
    + cbn. rewrite Ehas. reflexivity.
    + eapply mt_call_uchar; [exact HeUc|exact HeN|reflexivity|exact HCall1].
  - destruct (LS_uchar Hmodel bA cores live kN bN 272 l regs c Hk Hlive m Int.one HLS eq_refl)
      as (m1 & vr1 & HCall1 & HLS1 & HF1).
    set (x1 := (bN, 272, fst (absorb_i l regs [Int.one]), snd (absorb_i l regs [Int.one]),
                Int64.add c (Int64.repr 1)) : ctx_core) in *.
    assert (Hk1 : nth_error (upd cores kN x1) kN = Some x1) by (eapply nth_error_upd_same; exact Hk).
    set (oA := Ptrofs.repr (X + 0)).
    assert (HoA : Ptrofs.unsigned oA = X) by (unfold oA; rewrite Z.add_0_r; apply Ptrofs.unsigned_repr; lia).
    destruct (LS_hash Hmodel bA (upd cores kN x1) live kN bN 272 _ _ _ Hk1 Hlive m1 bA oA (norm8 (d_areg d)) HLS1 eq_refl)
      as (m2 & HCall2 & HLS2 & HF2).
    { rewrite HoA. lia. }
    { intros j Hj. rewrite HoA, norm8_nth by exact Hj. apply (HAx m1 HF1 j Hj). }
    rewrite upd_upd in HLS2.
    exists m2. split; [|split; [exact HLS2|exact (mfrP_trans _ _ _ _ HF1 HF2)]].
    eapply exec_Sifthenelse with (v1 := Vint (d_has d)) (b := true).
    + apply eval_Etempvar. exact Ht9.
    + cbn. rewrite Ehas. reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m1).
      * eapply mt_call_uchar; [exact HeUc|exact HeN|reflexivity|exact HCall1].
      * eapply mt_call_hash with (bx := bN) (bt := bA) (ot := oA); [exact HeH|exact HeN| |reflexivity|exact HCall2].
        unfold oA. eapply ev_adr; [reflexivity|exact envu_sigInput_annexHash|apply (HDx m1 HF1)|lia|lia|lia].
Qed.
End Annex.

Section InOps.
Variable Hmodel : memcpy_model.
Variables (e : env) (bA bI bG bN bQ bU bS bV bP : block) (data : nat -> in_data) (k : nat).

Let kz := Z.of_nat k.
Let X := 488 + 160 * kz.
Let blocks := [bI; bG; bN; bQ; bU; bS; bV; bP].
Local Notation d := (data k).
Local Notation allL := (fun _ : nat => True).

Hypothesis HeP : e!_ctx_inputOutpointsHash = Some (bP, CTX).
Hypothesis HeV : e!_ctx_inputValuesHash = Some (bV, CTX).
Hypothesis HeS : e!_ctx_inputScriptsHash = Some (bS, CTX).
Hypothesis HeQ : e!_ctx_inputSequencesHash = Some (bQ, CTX).
Hypothesis HeN : e!_ctx_inputAnnexesHash = Some (bN, CTX).
Hypothesis HeG : e!_ctx_inputScriptSigsHash = Some (bG, CTX).
Hypothesis HeH : e!_sha256_hash = None.
Hypothesis HeU4 : e!_sha256_u32be = None.
Hypothesis HeU8 : e!_sha256_u64be = None.
Hypothesis HeUc : e!_sha256_uchar = None.
Hypothesis Hkz : kz <= 4294967295.

Theorem in_ops le m :
  le!_input = Some (Vptr bA (Ptrofs.repr 488)) -> le!_i = Some (Vlong (Int64.repr kz)) ->
  LS m bA (in_cores data bI bG bN bQ bU bS bV bP k) allL ->
  in_rec m bA X d ->
  exists le' m',
    Clight2.exec_stmt sha_ge e le m mt_in_ops E0 le' m' Out_normal /\
    (forall x, x <> _t'9 -> x <> _t'10 -> x <> _t'11 -> x <> _t'12 -> le'!x = le!x) /\
    LS m' bA (in_cores data bI bG bN bQ bU bS bV bP (S k)) allL /\
    mfrP (rngP bA blocks 112 368) m m'.
Proof.
  intros Hin Hi HLS HRec.
  assert (Hkz0 : 0 <= kz) by (unfold kz; lia).
  assert (HXb : 488 <= X /\ X + 160 <= Ptrofs.max_unsigned).
  { unfold X. change Ptrofs.max_unsigned with 18446744073709551615. lia. }
  unfold in_cores, mk_core in HLS.
  let cc := ls_cores HLS in
  destruct (LS_facts bA cc allL 0%nat _ _ _ _ _ eq_refl Logic.I m HLS) as (_ & _ & N0 & _ & VA & _).
  let cc := ls_cores HLS in
  destruct (LS_facts bA cc allL 1%nat _ _ _ _ _ eq_refl Logic.I m HLS) as (_ & _ & N1 & _).
  let cc := ls_cores HLS in
  destruct (LS_facts bA cc allL 2%nat _ _ _ _ _ eq_refl Logic.I m HLS) as (_ & _ & N2 & _).
  let cc := ls_cores HLS in
  destruct (LS_facts bA cc allL 3%nat _ _ _ _ _ eq_refl Logic.I m HLS) as (_ & _ & N3 & _).
  let cc := ls_cores HLS in
  destruct (LS_facts bA cc allL 4%nat _ _ _ _ _ eq_refl Logic.I m HLS) as (_ & _ & N4 & _).
  let cc := ls_cores HLS in
  destruct (LS_facts bA cc allL 5%nat _ _ _ _ _ eq_refl Logic.I m HLS) as (_ & _ & N5 & _).
  let cc := ls_cores HLS in
  destruct (LS_facts bA cc allL 6%nat _ _ _ _ _ eq_refl Logic.I m HLS) as (_ & _ & N6 & _).
  let cc := ls_cores HLS in
  destruct (LS_facts bA cc allL 7%nat _ _ _ _ _ eq_refl Logic.I m HLS) as (_ & _ & N7 & _).
  assert (NAb : ~ In bA blocks).
  { unfold blocks. cbn [In]. intros HIn. repeat (destruct HIn as [E|HIn]; [contradiction|]). exact HIn. }
  set (Q := rngP bA blocks 112 368).
  assert (RL : forall mi, mfrP Q m mi -> forall ch ofs, 368 <= ofs -> Mem.load ch mi bA ofs = Mem.load ch m bA ofs).
  { intros mi (L & _ & _) ch ofs Ho. apply L; [exact VA|]. split; [exact NAb|right; right; exact Ho]. }
  assert (RecI : forall mi, mfrP Q m mi -> in_rec mi bA X d).
  { intros mi Hmi. eapply in_rec_frame; [exact HRec|]. intros ch ofs H1 H2. apply (RL mi Hmi). lia. }
  assert (EvD : forall lx mx, lx!_input = Some (Vptr bA (Ptrofs.repr 488)) -> lx!_i = Some (Vlong (Int64.repr kz)) ->
    eval_expr sha_ge e lx mx DIN (Vptr bA (Ptrofs.repr X))).
  { intros lx mx H1 H2. eapply eval_Elvalue; [eapply eval_Ederef|apply deref_loc_copy; reflexivity].
    eapply eval_Ebinop; [apply eval_Etempvar; exact H1|apply eval_Etempvar; exact H2|].
    unfold X. rewrite <- (ptr_index_long 488 160 kz) by lia. rewrite <- ci_sizeof_SIN. reflexivity. }
  assert (Opq : forall bx ob mi mj, In bx blocks -> 112 <= ob -> ob + 32 <= 368 ->
    mfrP Q m mi -> mfrP (opP bA bx ob) mi mj -> mfrP Q m mj).
  { intros bx ob mi mj H1 H2 H3 H4 H5. eapply mfrP_trans; [exact H4|]. eapply opP_rng; eassumption. }
  pose proof (mfrP_refl Q m) as G0.
  destruct HRec as (RA & RG & RT & RIx & RVal & RSp & RSq & RHas).
  (* sha256_hash(&ctx_inputOutpointsHash, &input[i].prevOutpoint.txid) *)
  set (oT := Ptrofs.repr (X + 64 + 0)).
  assert (HoT : Ptrofs.unsigned oT = X + 64) by (unfold oT; rewrite Z.add_0_r; apply Ptrofs.unsigned_repr; lia).
  let cc := ls_cores HLS in
  destruct (LS_hash Hmodel bA cc allL 7%nat bP 112 _ _ _ eq_refl Logic.I m bA oT (norm8 (tm_words (d_txb d))) HLS eq_refl)
    as (m1 & HCall1 & HLS1 & HF1).
  { rewrite HoT. lia. }
  { intros j Hj. rewrite HoT, norm8_nth by exact Hj. apply RT, Hj. }
  cbn [upd] in HLS1.
  assert (G1 : mfrP Q m m1) by (eapply (Opq bP 112 m m1); [unfold blocks; inb|lia|lia|exact G0|exact HF1]).
  (* sha256_u32be(&ctx_inputOutpointsHash, input[i].prevOutpoint.ix) *)
  let cc := ls_cores HLS1 in
  destruct (LS_u32be Hmodel bA cc allL 7%nat bP 112 _ _ _ eq_refl Logic.I m1 (Int64.repr (Int.unsigned (d_ix d))) HLS1)
    as (m2 & vr2 & HCall2 & HLS2 & HF2).
  cbn [upd] in HLS2.
  assert (G2 : mfrP Q m m2) by (eapply (Opq bP 112 m1 m2); [unfold blocks; inb|lia|lia|exact G1|exact HF2]).
  (* sha256_u64be(&ctx_inputValuesHash, input[i].txo.value) *)
  let cc := ls_cores HLS2 in
  destruct (LS_u64be Hmodel bA cc allL 6%nat bV 144 _ _ _ eq_refl Logic.I m2 (d_val d) HLS2)
    as (m3 & vr3 & HCall3 & HLS3 & HF3).
  cbn [upd] in HLS3.
  assert (G3 : mfrP Q m m3) by (eapply (Opq bV 144 m2 m3); [unfold blocks; inb|lia|lia|exact G2|exact HF3]).
  (* sha256_hash(&ctx_inputScriptsHash, &input[i].txo.scriptPubKey) *)
  set (oS := Ptrofs.repr (X + 104 + 8)).
  assert (HoS : Ptrofs.unsigned oS = X + 112).
  { unfold oS. replace (X + 104 + 8) with (X + 112) by lia. apply Ptrofs.unsigned_repr. lia. }
  let cc := ls_cores HLS3 in
  destruct (LS_hash Hmodel bA cc allL 5%nat bS 176 _ _ _ eq_refl Logic.I m3 bA oS
              (norm8 (hash_buffer_regs (d_spb d))) HLS3 eq_refl)
    as (m4 & HCall4 & HLS4 & HF4).
  { rewrite HoS. lia. }
  { intros j Hj. rewrite HoS, norm8_nth by exact Hj.
    rewrite (RL m3 G3) by lia. apply RSp, Hj. }
  cbn [upd] in HLS4.
  assert (G4 : mfrP Q m m4) by (eapply (Opq bS 176 m3 m4); [unfold blocks; inb|lia|lia|exact G3|exact HF4]).
  (* sha256_u32be(&ctx_inputSequencesHash, input[i].sequence) *)
  let cc := ls_cores HLS4 in
  destruct (LS_u32be Hmodel bA cc allL 3%nat bQ 240 _ _ _ eq_refl Logic.I m4 (Int64.repr (Int.unsigned (d_sq d))) HLS4)
    as (m5 & vr5 & HCall5 & HLS5 & HF5).
  cbn [upd] in HLS5.
  assert (G5 : mfrP Q m m5) by (eapply (Opq bQ 240 m4 m5); [unfold blocks; inb|lia|lia|exact G4|exact HF5]).
  (* the annex *)
  set (le1 := PTree.set _t'12 (Vlong (Int64.repr (Int.unsigned (d_ix d)))) le).
  set (le2 := PTree.set _t'11 (Vlong (d_val d)) le1).
  set (le3 := PTree.set _t'10 (Vlong (Int64.repr (Int.unsigned (d_sq d)))) le2).
  set (le4 := PTree.set _t'9 (Vint (d_has d)) le3).
  assert (Hin4 : le4!_input = Some (Vptr bA (Ptrofs.repr 488))).
  { unfold le4, le3, le2, le1. rewrite !PTree.gso by discriminate. exact Hin. }
  assert (Hi4 : le4!_i = Some (Vlong (Int64.repr kz))).
  { unfold le4, le3, le2, le1. rewrite !PTree.gso by discriminate. exact Hi. }
  assert (Opn : forall mi mx, mfrP Q m mi -> mfrP (opP bA bN 272) mi mx -> mfrP Q m mx).
  { intros mi mx H1 H2. eapply (Opq bN 272 mi mx); [unfold blocks; inb|lia|lia|exact H1|exact H2]. }
  let cc := ls_cores HLS5 in
  destruct (in_annex Hmodel e bA bN cc allL 2%nat _ _ _ X d HeN HeH HeUc eq_refl Logic.I
              ltac:(lia) le4 m5 (EvD le4 m5 Hin4 Hi4) (PTree.gss _ _ _) HLS5)
    as (m6 & HExec6 & HLS6 & HF6).
  { intros mx _. apply EvD; assumption. }
  { intros mx Hmx j Hj. rewrite (RL mx (Opn m5 mx G5 Hmx)) by lia. apply RA, Hj. }
  cbn [upd] in HLS6.
  assert (G6 : mfrP Q m m6) by (exact (Opn m5 m6 G5 HF6)).
  (* sha256_hash(&ctx_inputScriptSigsHash, &input[i].scriptSigHash) *)
  set (oG := Ptrofs.repr (X + 32)).
  assert (HoG : Ptrofs.unsigned oG = X + 32) by (unfold oG; apply Ptrofs.unsigned_repr; lia).
  let cc := ls_cores HLS6 in
  destruct (LS_hash Hmodel bA cc allL 1%nat bG 304 _ _ _ eq_refl Logic.I m6 bA oG
              (norm8 (hash_buffer_regs (d_ssb d))) HLS6 eq_refl)
    as (m7 & HCall7 & HLS7 & HF7).
  { rewrite HoG. lia. }
  { intros j Hj. rewrite HoG, norm8_nth by exact Hj. rewrite (RL m6 G6) by lia. apply RG, Hj. }
  cbn [upd] in HLS7.
  assert (G7 : mfrP Q m m7) by (eapply (Opq bG 304 m6 m7); [unfold blocks; inb|lia|lia|exact G6|exact HF7]).
  exists le4, m7. split; [|split; [|split; [|exact G7]]].
  - cbv delta [mt_in_ops] beta iota.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m1).
    { eapply mt_call_hash with (bx := bP) (bt := bA) (ot := oT); [exact HeH|exact HeP| |reflexivity|exact HCall1].
      unfold oT. eapply ev_adr; [reflexivity|exact envu_outpoint_txid| |lia|lia|lia].
      eapply ev_sub; [reflexivity|exact envu_sigInput_prevOutpoint|apply EvD; assumption|lia|lia|lia]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m2).
    { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m1).
      - apply exec_Sset. eapply ev_ld with (chunk := Mint64) (base := X + 64);
          [reflexivity|exact envu_outpoint_ix|reflexivity| |lia|lia|lia|].
        + eapply ev_sub; [reflexivity|exact envu_sigInput_prevOutpoint|apply EvD; assumption|lia|lia|lia].
        + replace (X + 64 + 32) with (X + 96) by lia. rewrite (RL m1 G1) by lia. exact RIx.
      - eapply mt_call_u32be with (bx := bP); [exact HeU4|exact HeP|apply eval_Etempvar; apply PTree.gss|reflexivity|exact HCall2]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m3).
    { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m2).
      - apply exec_Sset. eapply ev_ld with (chunk := Mint64) (base := X + 104);
          [reflexivity|exact envu_sigOutput_value|reflexivity| |lia|lia|lia|].
        + eapply ev_sub; [reflexivity|exact envu_sigInput_txo| |lia|lia|lia].
          apply EvD; unfold le1; rewrite PTree.gso by discriminate; assumption.
        + rewrite Z.add_0_r. rewrite (RL m2 G2) by lia. exact RVal.
      - eapply mt_call_u64be with (bx := bV); [exact HeU8|exact HeV|apply eval_Etempvar; apply PTree.gss|reflexivity|exact HCall3]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m4).
    { eapply mt_call_hash with (bx := bS) (bt := bA) (ot := oS); [exact HeH|exact HeS| |reflexivity|exact HCall4].
      unfold oS. eapply ev_adr; [reflexivity|exact envu_sigOutput_scriptPubKey| |lia|lia|lia].
      eapply ev_sub; [reflexivity|exact envu_sigInput_txo| |lia|lia|lia].
      apply EvD; unfold le2, le1; rewrite !PTree.gso by discriminate; assumption. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m5).
    { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m4).
      - apply exec_Sset. eapply ev_ld with (chunk := Mint64) (base := X);
          [reflexivity|exact envu_sigInput_sequence|reflexivity| |lia|lia|lia|].
        + apply EvD; unfold le2, le1; rewrite !PTree.gso by discriminate; assumption.
        + rewrite (RL m4 G4) by lia. exact RSq.
      - eapply mt_call_u32be with (bx := bQ); [exact HeU4|exact HeQ|apply eval_Etempvar; apply PTree.gss|reflexivity|exact HCall5]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := m6).
    { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := m5).
      - apply exec_Sset. eapply ev_ld with (chunk := Mint8unsigned) (base := X);
          [reflexivity|exact envu_sigInput_hasAnnex|reflexivity| |lia|lia|lia|].
        + apply EvD; unfold le3, le2, le1; rewrite !PTree.gso by discriminate; assumption.
        + rewrite (RL m5 G5) by lia. exact RHas.
      - exact HExec6. }
    eapply mt_call_hash with (bx := bG) (bt := bA) (ot := oG); [exact HeH|exact HeG| |reflexivity|exact HCall7].
    unfold oG. eapply ev_adr; [reflexivity|exact envu_sigInput_scriptSigHash|apply EvD; assumption|lia|lia|lia].
  - intros x H9 H10 H11 H12. unfold le4, le3, le2, le1. rewrite !PTree.gso by assumption. reflexivity.
  - unfold in_cores, mk_core. exact HLS7.
Qed.
End InOps.
