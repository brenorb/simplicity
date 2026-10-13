(** Full helper output: unchanged X/Z, actual negative Y, flag and framing.
    Canonical Simplicity/public writer composition remains separate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_local_regions C.jet_secp_write_fe_numeric C.jet_secp_field_negate_storage.
Require Import C.jet_secp_point_write_run C.jet_secp_gej_negate_call_frame.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma gej_negate_preserved_coordinate k m mf b limbs :
  k <> PointY -> length limbs = 5%nat ->
  fe_at m b (point_coordinate_offset k) limbs ->
  Mem.range_perm mf b 0 128 Cur Freeable ->
  (forall chunk ofs,
    (ofs+size_chunk chunk <= 40 \/ 80 <= ofs) ->
    (ofs+size_chunk chunk <= 120 \/ 124 <= ofs) ->
    Mem.load chunk mf b ofs = Mem.load chunk m b ofs) ->
  fe_at mf b (point_coordinate_offset k) limbs.
Proof.
  intros HK HLen (HB & HA & HM & HP & HL) HFree HLoads.
  split; [exact HB|]. split; [exact HA|]. split; [exact HM|]. split.
  - apply freeable_range_writable; intros pos HPos.
    apply HFree; pose proof (point_coordinate_offset_bounds k); lia.
  - intros i x HN.
    assert (HIndex : (i < 5)%nat).
    { rewrite <- HLen; apply (proj1 (nth_error_Some _ _)); rewrite HN; discriminate. }
    rewrite HLoads; [apply HL;exact HN| |].
    + destruct k; cbn [point_coordinate_offset]; change (size_chunk Mint64) with 8;
        [left;lia|contradiction|right;lia].
    + left; change (size_chunk Mint64) with 8.
      pose proof (point_coordinate_offset_bounds k); lia.
Qed.

Theorem eval_gej_negate_point_output m b value flag xlimbs zlimbs :
  0 <= value < 2^256 ->
  length xlimbs = 5%nat -> length zlimbs = 5%nat ->
  fe_at m b 0 xlimbs ->
  fe_at m b 40 (map Int64.repr (fe_limbs_of value)) ->
  fe_at m b 80 zlimbs ->
  Mem.range_perm m b 0 128 Cur Freeable ->
  Mem.load Mint32 m b 120 = Some (Vint flag) ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_neg)
      [Vptr b Ptrofs.zero;Vptr b Ptrofs.zero] E0 mf Vundef /\
    fe_at mf b 0 xlimbs /\
    fe_at mf b 40 (negate_values (write_fe_rho value 0)) /\
    fe_at mf b 80 zlimbs /\
    Mem.range_perm mf b 0 128 Cur Freeable /\
    Mem.load Mint32 mf b 120 = Some (Vint flag) /\
    lframe (fun bx _ => bx <> b) m mf.
Proof.
  intros HV HXLen HZLen HX HY HZ HFree HFlag.
  destruct (eval_gej_negate_framed_call m b value flag HV HY HFree HFlag)
    as (mf & HCall & HYF & HFreeF & HFlagF & HLoads & HFrame).
  exists mf; split; [exact HCall|]. split.
  - exact (gej_negate_preserved_coordinate PointX m mf b xlimbs
      ltac:(discriminate) HXLen HX HFreeF HLoads).
  - split; [exact HYF|]. split.
    + exact (gej_negate_preserved_coordinate PointZ m mf b zlimbs
        ltac:(discriminate) HZLen HZ HFreeF HLoads).
    + split; [exact HFreeF|]; split; assumption.
Qed.
Timeout 60 Print Assumptions eval_gej_negate_point_output.
