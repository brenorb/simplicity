(** Discharge the public remainder's calls from owned initial storage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Clight ClightBigstep Integers Values Memory Events Maps.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_gej_public_entry C.jet_secp_gej_public_body.
Require Import C.jet_secp_gej_infinity_owned C.jet_secp_write_gej_infinity C.jet_secp_literal_infinity.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_frame C.jet_frame_inv C.jet_output_layout.
Require Simplicity.Translate Simplicity.Alg.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem exec_gej_public_rest_owned le m0 bd dbase bw edge cursor N bi (rc : Z) m ba bl :
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m0 bd dbase bw edge cursor N -> 768 <= N ->
  finv m0 bd dbase bw edge cursor N bi m false [] ->
  Mem.range_perm m ba 0 128 Cur Freeable ->
  Mem.range_perm m bl 0 16 Cur Freeable -> ba <> bl ->
  xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  exists mf,
    Clight2.exec_stmt secp_ge (gej_public_env bl ba) le m gej_public_rest E0 le mf
      (Out_return (Some (Vint Int.one, tint))) /\
    finv m0 bd dbase bw edge cursor N bi mf true
      (Simplicity.Translate.encode (@literal_gej_infinity Simplicity.Alg.CoreFunSem tt)) /\
    Mem.range_perm mf ba 0 128 Cur Freeable /\
    Mem.range_perm mf bl 0 16 Cur Freeable /\
    lframe (fun b _ => b <> ba /\ b <> bl /\ ~ extA m0 bd bw bi b) m mf.
Proof.
  intros HD HO HN HI HPA HPL HAB HS.
  assert (HNEA : ~ extA m0 bd bw bi ba) by (exact (HS 0%nat ltac:(simpl;lia))).
  assert (HNEL : ~ extA m0 bd bw bi bl) by (exact (HS 1%nat ltac:(simpl;lia))).
  assert (HWritable : Mem.range_perm m ba 0 128 Cur Writable).
  { intros ofs HF; eapply Mem.perm_implies; [apply HPA;exact HF|constructor]. }
  destruct (eval_gej_infinity_initializer_owned m ba 0 ltac:(lia)
    ltac:(exists 0;reflexivity)
    ltac:(change Ptrofs.max_unsigned with 18446744073709551615;lia) HWritable)
    as (mi & HC & HX & HY & HZ & HFlag & HLoads & HPerm & HValid).
  assert (HE : eqext m0 bd bw bi m mi).
  { split.
    - intros chunk b ofs HV HF. apply HLoads; left.
      intro E; subst b; apply HNEA.
      apply (HF ofs); pose proof (size_chunk_pos chunk);lia.
    - split.
      + intros b ofs k p HV HF HP; apply (proj2 (HPerm b ofs k p));exact HP.
      + exact HValid. }
  assert (HIi : finv m0 bd dbase bw edge cursor N bi mi false []).
  { eapply finv_stable; [exact HO|exact HI|exact HE]. }
  assert (HPAi : Mem.range_perm mi ba 0 128 Cur Freeable).
  { intros ofs HF; apply (proj2 (HPerm ba ofs Cur Freeable)); apply HPA;exact HF. }
  assert (HPLi : Mem.range_perm mi bl 0 16 Cur Freeable).
  { intros ofs HF; apply (proj2 (HPerm bl ofs Cur Freeable)); apply HPL;exact HF. }
  assert (HS1 : xsep (extA m0 bd bw bi) [(ba,0)]).
  { intros r HR; destruct r; [exact HNEA|simpl in HR;lia]. }
  destruct (eval_write_gej_infinity_literal m0 bd dbase bw edge cursor N bi rc mi ba
    HO HN HIi HX HY HZ HPAi HS1) as (mf & HW & HFin & HFree & HFrame).
  assert (HVL : Mem.valid_block mi bl).
  { eapply Mem.perm_valid_block; apply (HPLi 0);lia. }
  exists mf; split.
  - eapply exec_gej_public_rest_from_calls; [exact HD|exact HC|exact HW].
  - split; [exact HFin|]. split; [exact HFree|]. split.
    + intros ofs HF. destruct HFrame as (_ & HP & _).
      apply (HP bl ofs Cur Freeable HVL); [split;[congruence|exact HNEL]|].
      apply HPLi;exact HF.
    + eapply lframe_trans.
      * split.
        -- intros chunk b ofs HV HF;apply HLoads;left.
           pose proof (HF ofs ltac:(pose proof (size_chunk_pos chunk);lia)) as [HA _];exact HA.
        -- split.
           ++ intros b ofs k p HV HF HP;apply (proj2 (HPerm b ofs k p));exact HP.
           ++ exact HValid.
      * eapply lframe_implies;[exact HFrame|].
        intros b ofs (HA & HL & HE') HV;split;assumption.
Qed.
Print Assumptions exec_gej_public_rest_owned.
