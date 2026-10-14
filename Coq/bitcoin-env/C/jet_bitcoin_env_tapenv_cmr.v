(** [simplicity_bitcoin_mallocTapEnv], fourth part:
    [sha256_toMidstate(env->scriptCMR.s, rawEnv->scriptCMR)], and the
    expressions over the allocated structure shared by the later parts. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_add_n_init C.jet_sha_be32_exec.
Require Import C.jet_env_store_words C.jet_bitcoin_env_field_eval C.jet_bitcoin_env_tomidstate.
Require Import C.jet_bitcoin_env_tapenv_prelude C.jet_bitcoin_env_tapenv_key C.jet_bitcoin_env_tapenv_fill.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Notation ENV := (Ederef (Etempvar _env (tptr TE)) TE).

(** The body after the script CMR has been stored. *)
Definition te_rest4 : statement :=
  ltac:(let b := eval cbv delta [te_rest3] in te_rest3 in
        let r := drop_seq 1%nat b in exact r).

Local Opaque sha_ge.

(** [env->f] for a midstate member, as an address, and [env->f.s]. *)
Lemma ev_env_mid_addr e le m bA f delta :
  le!_env = Some (Vptr bA Ptrofs.zero) -> envu_field_at _bitcoinTapEnv f delta ->
  eval_expr sha_ge e le m (Eaddrof (Efield ENV f MID) (tptr MID))
    (Vptr bA (Ptrofs.add Ptrofs.zero (Ptrofs.repr delta))).
Proof.
  intros Hle Hf. eapply eval_Eaddrof.
  eapply eval_envu_field_lvalue; [reflexivity|exact Hf|apply eval_envu_deref_struct; exact Hle].
Qed.

Lemma ev_env_mid_s e le m bA f delta :
  le!_env = Some (Vptr bA Ptrofs.zero) -> envu_field_at _bitcoinTapEnv f delta ->
  eval_expr sha_ge e le m (Efield (Efield ENV f MID) _s A8)
    (Vptr bA (Ptrofs.add Ptrofs.zero (Ptrofs.repr delta))).
Proof.
  intros Hle Hf.
  pose proof (eval_envu_field_array e le m (Efield ENV f MID) _sha256_midstate _s 0 A8 bA
    (Ptrofs.add Ptrofs.zero (Ptrofs.repr delta)) eq_refl envu_sha256_midstate_s
    ltac:(intros chunk; discriminate) eq_refl) as HE.
  rewrite Ptrofs.add_zero in HE. apply HE.
  eapply eval_envu_field_struct; [reflexivity|exact Hf|apply eval_envu_deref_struct; exact Hle].
Qed.

(** A scalar member of [*env]. *)
Lemma ev_env_field e le m bA f delta ty chunk v :
  le!_env = Some (Vptr bA Ptrofs.zero) -> envu_field_at _bitcoinTapEnv f delta ->
  access_mode ty = By_value chunk -> 0 <= delta <= 200 ->
  Mem.load chunk m bA delta = Some v ->
  eval_expr sha_ge e le m (Efield ENV f ty) v.
Proof.
  intros Hle Hf Hacc Hd HL.
  eapply eval_envu_field_value; [reflexivity|exact Hf|exact Hacc|apply eval_envu_deref_struct; exact Hle|].
  unfold Mem.loadv. rewrite te_off by exact Hd. exact HL.
Qed.

Section Cmr.
Variables (e : env) (braw : block) (oraw : Z) (bA bcm : block) (ocm : ptrofs) (cmrb : list int) (N : Z).
Hypothesis HeT : e!_sha256_toMidstate = None.
Hypothesis Horaw : 0 <= oraw /\ oraw + 24 <= Ptrofs.max_unsigned.
Hypothesis HAcm : bA <> bcm.
Hypothesis Hocm : Ptrofs.unsigned ocm + 32 <= Ptrofs.max_unsigned.

Let rawv := Vptr braw (Ptrofs.repr oraw).

Theorem te_cmr le3 m :
  te_le2 le3 rawv N bA ->
  Mem.load Mptr m braw (oraw + 8) = Some (Vptr bcm ocm) ->
  (forall i, (i < 32)%nat ->
     Mem.load Mint8unsigned m bcm (Ptrofs.unsigned ocm + Z.of_nat i) = Some (Vint (nth i cmrb Int.zero))) ->
  Mem.range_perm m bA 136 168 Cur Writable ->
  exists m' le4,
    store_words m bA 136 (tm_words cmrb) = Some m' /\
    te_le2 le4 rawv N bA /\
    (forall t le' mf out,
       Clight2.exec_stmt sha_ge e le4 m' te_rest4 t le' mf out ->
       Clight2.exec_stmt sha_ge e le3 m te_rest3 t le' mf out).
Proof.
  intros (HlRaw & HlEnv & HlPath) HCm HBytes PA.
  set (om := Ptrofs.add Ptrofs.zero (Ptrofs.repr 136)).
  assert (Hom : Ptrofs.unsigned om = 136) by (apply te_off; lia).
  destruct (eval_sha256_toMidstate bA bcm om ocm cmrb HAcm Hocm) with (m := m) as (m' & HSt & HCall).
  { rewrite Hom. change Ptrofs.max_unsigned with 18446744073709551615. lia. }
  { rewrite Hom. exists 34. reflexivity. }
  { exact HBytes. }
  { rewrite Hom. exact PA. }
  rewrite Hom in HSt.
  set (le4 := PTree.set _t'5 (Vptr bcm ocm) le3).
  exists m', le4. split; [exact HSt|]. split.
  { unfold te_le2, le4. rewrite !PTree.gso by discriminate. repeat split; assumption. }
  intros t le' mf out HRest.
  change te_rest3 with (Ssequence (match te_rest3 with Ssequence s _ => s | _ => Sskip end) te_rest4).
  eapply exec_Sseq_1 with (t1 := E0) (t2 := t) (le1 := le4) (m1 := m'); [|exact HRest].
  cbv delta [te_rest3] beta iota.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := m).
  - apply exec_Sset. eapply eval_envu_field_value;
      [reflexivity|exact envu_rawBitcoinTapEnv_scriptCMR|reflexivity|apply eval_envu_deref_struct; exact HlRaw|].
    unfold rawv. rewrite envu_ptr_add_repr by lia. apply envu_loadv_repr; [lia|exact HCm].
  - eapply te_call_toMidstate with (bm := bA) (om := om) (bh := bcm) (oh := ocm);
      [exact HeT| |reflexivity| |reflexivity|exact HCall].
    + apply ev_env_mid_s; [|exact envu_bitcoinTapEnv_scriptCMR].
      unfold le4. rewrite PTree.gso by discriminate. exact HlEnv.
    + apply eval_Etempvar. apply PTree.gss.
Qed.
End Cmr.
