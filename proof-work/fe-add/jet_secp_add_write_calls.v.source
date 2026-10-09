(** Original add helper followed by original wide writer, from stored reader
    results and a read-only frame invariant. Public readers/entry/free remain
    to be composed; no add/write execution or output premise is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Word.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_frame C.jet_frame_inv C.jet_output_layout C.jet_secp_fe_math C.jet_secp_fe_nv.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_local_regions C.jet_secp_local_call.
Require Import C.jet_secp_canonical_normalize C.jet_secp_field_add C.jet_secp_field_add_storage.
Require Import C.jet_secp_field_add_values C.jet_secp_add_normalized_owned C.jet_secp_field_add_writer_bridge.
Require Import C.jet_secp_literal_add_program C.jet_secp_negate_writer_bridge.
Require Import C.jet_secp_write_fe_wide_values C.jet_secp_write_fe_wide_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_normalize literal_fe_add Simplicity.Translate.encode.

Theorem eval_add_write_calls m0 bd dbase bw edge cursor N bi (rc : Z) m ba bb
    (a b : Ty.tySem (Word 8)) :
  write_frame_at m0 bd dbase bw edge cursor N -> 256 <= N -> ba <> bb ->
  fe_at m ba 0 (map Int64.repr (fe_limbs_of
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem a)))) ->
  fe_at m bb 0 (map Int64.repr (fe_limbs_of
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem b)))) ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bb 0 40 Cur Freeable ->
  xsep (extA m0 bd bw bi) [(ba,0);(bb,0)] ->
  finv m0 bd dbase bw edge cursor N bi m false [] ->
  exists mn mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add)
      [Vptr ba Ptrofs.zero; Vptr bb Ptrofs.zero] E0 mn Vundef /\
    Clight2.eval_funcall secp_ge mn (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase); Vptr ba Ptrofs.zero] E0 mf Vundef /\
    finv m0 bd dbase bw edge cursor N bi mf true
      (Simplicity.Translate.encode (@literal_fe_add Alg.CoreFunSem (a,b))) /\
    Mem.range_perm mf ba 0 40 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
    lframe (fun b' pos => ~ foot [(ba,0);(bb,0)] (map rshape field_add_initial_regs) b' pos) m mn /\
    lframe (frame (extA m0 bd bw bi) [(ba,0)] local_write_initial_regs mn) mn mf.
Proof.
  intros HO HN HSeparate HA HB HFA HFB HS HI.
  destruct (eval_field_add_from_normalized_fields m ba bb a b HSeparate HA HB HFA HFB)
    as (mn & HAdd & HField & HOutput & HFreeA & HFreeB & HAddFrame).
  assert (HExt : lframe (fun b' _ => extA m0 bd bw bi b') m mn).
  { eapply lframe_implies; [exact HAddFrame|].
    intros b' pos HE HV (r & s & d & ch & HGet & HCell & HBlock & HRange).
    destruct r as [|[|r]].
    - change (b' = ba) in HBlock. subst b'. exact (HS 0%nat ltac:(cbn; lia) HE).
    - change (b' = bb) in HBlock. subst b'. exact (HS 1%nat ltac:(cbn; lia) HE).
    - cbn [field_add_initial_regs map nth_error] in HGet. destruct r; discriminate. }
  assert (HFIN : finv m0 bd dbase bw edge cursor N bi mn false []).
  { eapply finv_stable; [exact HO|exact HI|exact HExt]. }
  set (rho := normalized_add_rho a b).
  set (wrho := wide_fe_rho (add_value rho 0) (add_value rho 1)
    (add_value rho 2) (add_value rho 3) (add_value rho 4) rc).
  assert (HWI : invA m0 bd dbase bw edge cursor N bi rc false [] 256 wrho [] mn).
  { change (Int64.repr rc = Int64.repr rc /\
      finv m0 bd dbase bw edge cursor N bi mn false [] /\ 256 <= N /\ 0 <= 256).
    split; [reflexivity|]. split; [exact HFIN|]. split; [exact HN|lia]. }
  pose proof (add_writer_initial_rep rho rc mn ba HField HFreeA) as HRep.
  destruct (normalized_add_reader_facts a b) as (HBounds & HVA & HVB).
  pose proof (add_writer_limb_bounds rho HBounds) as HBound.
  assert (HSW : xsep (extA m0 bd bw bi) [(ba,0)]).
  { intros r Hr. destruct r as [|r]; [exact (HS 0%nat ltac:(cbn; lia))|cbn in Hr; lia]. }
  destruct (eval_local_wide_write_fe m0 bd dbase bw edge cursor N bi rc
    (add_value rho 0) (add_value rho 1) (add_value rho 2) (add_value rho 3)
    (add_value rho 4) false [] mn [(ba,0)] HO
    (HBound 0%nat ltac:(lia)) (HBound 1%nat ltac:(lia)) (HBound 2%nat ltac:(lia))
    (HBound 3%nat ltac:(lia)) (HBound 4%nat ltac:(lia)) HRep HSW HWI)
    as (mf & HWrite & HFinal & HFinalRep & HWriteFrame).
  fold rho in HOutput. rewrite HOutput in HFinal.
  change (finv m0 bd dbase bw edge cursor N bi mf true
    (Simplicity.Translate.encode (@literal_fe_add Alg.CoreFunSem (a,b)))) in HFinal.
  pose proof (wide_local_final_freeable _ ba mf bd (Ptrofs.repr dbase) HFinalRep) as HFinalA.
  assert (HValidB : Mem.valid_block mn bb).
  { eapply Mem.perm_valid_block. apply (HFreeB 0). lia. }
  assert (HFinalB : Mem.range_perm mf bb 0 40 Cur Freeable).
  { intros pos HPos. apply (proj1 (proj2 HWriteFrame)); [exact HValidB| |apply HFreeB; exact HPos].
    split; [exact HValidB|]. split.
    - apply no_local_write_foot. congruence.
    - exact (HS 1%nat ltac:(cbn; lia)). }
  exists mn, mf. split; [exact HAdd|]. split; [exact HWrite|].
  split; [exact HFinal|]. split; [exact HFinalA|]. split; [exact HFinalB|].
  split; assumption.
Qed.
Print Assumptions eval_add_write_calls.
