(** Strengthened helper body: retained coordinate loads, validity and framing. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_exec C.jet_sx_expr C.jet_sx_state C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_local_regions.
Require Import C.jet_secp_write_fe_numeric C.jet_secp_field_negate_storage.
Require Import C.jet_secp_point_write_run C.jet_secp_point_write_preservation.
Require Import C.jet_secp_gej_negate_fields C.jet_secp_gej_negate_flag C.jet_secp_gej_negate_prefix.
Require Import C.jet_secp_gej_negate_y_tail C.jet_secp_gej_negate_prefix_frame.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem exec_gej_negate_body_framed le m b value flag :
  le!_r = Some (Vptr b Ptrofs.zero) ->
  le!_a = Some (Vptr b Ptrofs.zero) ->
  0 <= value < 2^256 ->
  fe_at m b 40 (map Int64.repr (fe_limbs_of value)) ->
  Mem.range_perm m b 0 128 Cur Freeable ->
  Mem.load Mint32 m b 120 = Some (Vint flag) ->
  exists mf,
    Clight2.exec_stmt secp_ge empty_env le m (fn_body f_secp256k1_gej_neg) E0
      (PTree.set _t'1 (Vint flag) le) mf Out_normal /\
    fe_at mf b 40 (negate_values (write_fe_rho value 0)) /\
    Mem.range_perm mf b 0 128 Cur Freeable /\
    Mem.load Mint32 mf b 120 = Some (Vint flag) /\
    (forall chunk ofs,
      (ofs+size_chunk chunk <= 40 \/ 80 <= ofs) ->
      (ofs+size_chunk chunk <= 120 \/ 124 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    lframe (fun bx _ => bx <> b) m mf.
Proof.
  intros HR HA HV HField HFree HFlag.
  assert (HValid : Mem.valid_block m b).
  { eapply Mem.perm_valid_block; apply (HFree 0); lia. }
  destruct (exec_gej_negate_prefix_framed le m b flag HR HA HFree HFlag)
    as (mi & mx & my & mz & HI & HX & HY & HZ & HFlagZ & HFreeZ & HLoads & HPrefixFrame).
  assert (HFieldZ : fe_at mz b 40 (map Int64.repr (fe_limbs_of value))).
  { destruct HField as (HB & HAL & HM & HP & HL).
    split; [exact HB|]. split; [exact HAL|]. split; [exact HM|]. split.
    - apply freeable_range_writable; intros pos HPos; apply HFreeZ; lia.
    - intros i x HN.
      assert (HIndex : (i < 5)%nat).
      { change (i < length (map Int64.repr (fe_limbs_of value)))%nat.
        apply (proj1 (nth_error_Some _ _)); rewrite HN; discriminate. }
      rewrite HLoads; [apply HL;exact HN|exact HValid|].
      right;left;change (40+8*Z.of_nat i+8 <= 0+120); lia. }
  assert (HR' : (PTree.set _t'1 (Vint flag) le)!_r = Some (Vptr b Ptrofs.zero)).
  { rewrite PTree.gso by discriminate; exact HR. }
  destruct (exec_gej_negate_y_tail_owned (PTree.set _t'1 (Vint flag) le)
    mz b value HR' HV HFieldZ HFreeZ) as (mf & HTail & HFieldF & HFreeF & HFrame).
  exists mf; split.
  - rewrite gej_negate_helper_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mi)
      (le1 := PTree.set _t'1 (Vint flag) le); [exact HI|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mx)
      (le1 := PTree.set _t'1 (Vint flag) le); [exact HX|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := my)
      (le1 := PTree.set _t'1 (Vint flag) le); [exact HY|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mz)
      (le1 := PTree.set _t'1 (Vint flag) le); [exact HZ|exact HTail].
  - split; [exact HFieldF|]. split; [exact HFreeF|]. split.
    { rewrite (proj1 HFrame Mint32 b 120).
    + exact HFlagZ.
    + eapply Mem.perm_valid_block; apply (HFreeZ 0); lia.
    + intros pos HPos HFoot.
      destruct (point_write_foot_bounds PointY b b pos HFoot) as [_ HRange].
      change (120 <= pos < 120+4) in HPos; change (40 <= pos < 40+40) in HRange; lia. }
    split.
    + intros chunk ofs HNotY HNotFlag.
      rewrite (proj1 HFrame chunk b ofs).
      * apply HLoads; [exact HValid|right;exact HNotFlag].
      * eapply Mem.perm_valid_block; apply (HFreeZ 0); lia.
      * intros pos HPos HFoot.
        destruct (point_write_foot_bounds PointY b b pos HFoot) as [_ HRange].
        change (40 <= pos < 80) in HRange.
        destruct HNotY; lia.
    + eapply lframe_trans; [exact HPrefixFrame|].
      eapply lframe_implies; [exact HFrame|].
      intros bx pos HOther _ HFoot.
      destruct (point_write_foot_bounds PointY b bx pos HFoot) as [HE _]; contradiction.
Qed.
Timeout 60 Print Assumptions exec_gej_negate_body_framed.
