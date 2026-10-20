(** Four actual fe_mul calls in the original rescale order.  Other fields,
    the flag and caller ownership are carried through their derived frames. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_state C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns.
Require Import C.jet_secp_point_write_run C.jet_secp_point_mul_run C.jet_secp_point_mul_storage
  C.jet_secp_point_mul_numeric C.jet_secp_point_mul_preservation.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words.

Theorem rescale_four_multiply_calls x y z s ss m bp bs bz flag :
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  square_input_bounds s -> square_input_bounds ss ->
  bp <> bs -> bp <> bz -> bs <> bz ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  fe_at m bs 0 (words5 s) -> fe_at m bz 0 (words5 ss) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bs 0 40 Cur Freeable ->
  Mem.range_perm m bz 0 40 Cur Freeable -> Mem.load Mint32 m bp 120 = Some (Vint flag) ->
  exists m1 m2 m3 mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
      [Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr bz Ptrofs.zero] E0 m1 Vundef /\
    Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_fe_mul)
      [Vptr bp (Ptrofs.repr 40);Vptr bp (Ptrofs.repr 40);Vptr bz Ptrofs.zero] E0 m2 Vundef /\
    Clight2.eval_funcall secp_ge m2 (Internal f_secp256k1_fe_mul)
      [Vptr bp (Ptrofs.repr 40);Vptr bp (Ptrofs.repr 40);Vptr bs Ptrofs.zero] E0 m3 Vundef /\
    Clight2.eval_funcall secp_ge m3 (Internal f_secp256k1_fe_mul)
      [Vptr bp (Ptrofs.repr 80);Vptr bp (Ptrofs.repr 80);Vptr bs Ptrofs.zero] E0 mf Vundef /\
    fe_at mf bp 0 (words5 (point_mul_words x ss)) /\
    fe_at mf bp 40 (words5 (point_mul_words (point_mul_words y ss) s)) /\
    fe_at mf bp 80 (words5 (point_mul_words z s)) /\
    fe_at mf bs 0 (words5 s) /\ Mem.load Mint32 mf bp 120 = Some (Vint flag) /\
    Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
    Mem.range_perm mf bz 0 40 Cur Freeable /\
    square_input_bounds (point_mul_words x ss) /\
    square_input_bounds (point_mul_words (point_mul_words y ss) s) /\
    square_input_bounds (point_mul_words z s) /\
    lframe (fun b _ => b <> bp /\ b <> bs /\ b <> bz) m mf.
Proof.
  intros BX BY BZ BS BSS HPS HPZ HSZ HX HY HZ HS HSS HFP HFS HFZ HFlag.
  assert (HV0 : Mem.valid_block m bp) by (eapply Mem.perm_valid_block; apply (HFP 0); lia).
  destruct (eval_point_mul_numeric PointX x ss m bp bz BX BSS HPZ HX HFP HSS HFZ)
    as (m1 & C1 & X1 & P1 & ZZ1 & ZF1 & V1 & BX1 & F1).
  pose proof (point_mul_other_field PointX PointY m m1 bp bz y ltac:(discriminate) HPZ HY P1 F1) as Y1.
  pose proof (point_mul_other_field PointX PointZ m m1 bp bz z ltac:(discriminate) HPZ HZ P1 F1) as Z1.
  pose proof (point_mul_external_field PointX m m1 bp bz bs s (not_eq_sym HPS) HSZ HS F1) as S1.
  pose proof (point_mul_external_free PointX m m1 bp bz bs 40 (not_eq_sym HPS) HSZ ltac:(lia) HFS F1) as SF1.
  pose proof (point_mul_flag PointX m m1 bp bz flag HPZ HV0 HFlag F1) as Flag1.
  pose proof (proj2 (proj2 F1) bp HV0) as HV1.

  destruct (eval_point_mul_numeric PointY y ss m1 bp bz BY BSS HPZ Y1 P1 ZZ1 ZF1)
    as (m2 & C2 & Y2 & P2 & ZZ2 & ZF2 & V2 & BY2 & F2).
  pose proof (point_mul_other_field PointY PointX m1 m2 bp bz (point_mul_words x ss)
    ltac:(discriminate) HPZ X1 P2 F2) as X2.
  pose proof (point_mul_other_field PointY PointZ m1 m2 bp bz z ltac:(discriminate) HPZ Z1 P2 F2) as Z2.
  pose proof (point_mul_external_field PointY m1 m2 bp bz bs s (not_eq_sym HPS) HSZ S1 F2) as S2.
  pose proof (point_mul_external_free PointY m1 m2 bp bz bs 40 (not_eq_sym HPS) HSZ ltac:(lia) SF1 F2) as SF2.
  pose proof (point_mul_flag PointY m1 m2 bp bz flag HPZ HV1 Flag1 F2) as Flag2.
  pose proof (proj2 (proj2 F2) bp HV1) as HV2.

  destruct (eval_point_mul_numeric PointY (point_mul_words y ss) s m2 bp bs BY2 BS HPS Y2 P2 S2 SF2)
    as (m3 & C3 & Y3 & P3 & S3 & SF3 & V3 & BY3 & F3).
  pose proof (point_mul_other_field PointY PointX m2 m3 bp bs (point_mul_words x ss)
    ltac:(discriminate) HPS X2 P3 F3) as X3.
  pose proof (point_mul_other_field PointY PointZ m2 m3 bp bs z ltac:(discriminate) HPS Z2 P3 F3) as Z3.
  pose proof (point_mul_external_free PointY m2 m3 bp bs bz 40 (not_eq_sym HPZ) (not_eq_sym HSZ)
    ltac:(lia) ZF2 F3) as ZF3.
  pose proof (point_mul_flag PointY m2 m3 bp bs flag HPS HV2 Flag2 F3) as Flag3.
  pose proof (proj2 (proj2 F3) bp HV2) as HV3.

  destruct (eval_point_mul_numeric PointZ z s m3 bp bs BZ BS HPS Z3 P3 S3 SF3)
    as (mf & C4 & Z4 & P4 & S4 & SF4 & V4 & BZ4 & F4).
  pose proof (point_mul_other_field PointZ PointX m3 mf bp bs (point_mul_words x ss)
    ltac:(discriminate) HPS X3 P4 F4) as X4.
  pose proof (point_mul_other_field PointZ PointY m3 mf bp bs (point_mul_words (point_mul_words y ss) s)
    ltac:(discriminate) HPS Y3 P4 F4) as Y4.
  pose proof (point_mul_external_free PointZ m3 mf bp bs bz 40 (not_eq_sym HPZ) (not_eq_sym HSZ)
    ltac:(lia) ZF3 F4) as ZF4.
  pose proof (point_mul_flag PointZ m3 mf bp bs flag HPS HV3 Flag3 F4) as Flag4.
  exists m1, m2, m3, mf.
  split; [exact C1|]; split; [exact C2|]; split; [exact C3|]; split; [exact C4|].
  split; [exact X4|]; split; [exact Y4|]; split; [exact Z4|]; split; [exact S4|]; split; [exact Flag4|].
  split; [exact P4|]; split; [exact SF4|]; split; [exact ZF4|].
  split; [exact BX1|]; split; [exact BY3|]; split; [exact BZ4|].
  eapply lframe_trans.
  - eapply lframe_implies; [eapply point_mul_external_frame; exact F1|]; intros b ofs (HNoP & HNoS & HNoZ) _; split; assumption.
  - eapply lframe_trans.
    + eapply lframe_implies; [eapply point_mul_external_frame; exact F2|]; intros b ofs (HNoP & HNoS & HNoZ) _; split; assumption.
    + eapply lframe_trans.
      * eapply lframe_implies; [eapply point_mul_external_frame; exact F3|]; intros b ofs (HNoP & HNoS & HNoZ) _; split; assumption.
      * eapply lframe_implies; [eapply point_mul_external_frame; exact F4|]; intros b ofs (HNoP & HNoS & HNoZ) _; split; assumption.
Qed.
