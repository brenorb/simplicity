(** Execute the complete original helper body from storage, not assumed calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Require Import C.jet_secp_multiply_checkpoint_columns C.jet_secp_square_columns C.jet_secp_square_numeric.
Require Import C.jet_secp_field_read_preservation C.jet_secp_curve_frame.
Require Import C.jet_secp_field_pair_multiply C.jet_secp_x_equiv_prefix C.jet_secp_x_equiv_copy.
Require Import C.jet_secp_x_equiv_tail C.jet_secp_x_equiv_statements.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words field_pair_product.

Theorem exec_x_equiv_body_owned q x z le m bp bq br br2 :
  square_input_bounds q -> square_input_bounds x -> square_input_bounds z ->
  bp<>bq -> br<>bp -> br<>bq -> br2<>bp -> br2<>bq -> br2<>br ->
  le!_a = Some (Vptr bp Ptrofs.zero) -> le!_x = Some (Vptr bq Ptrofs.zero) ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 80 (words5 z) -> fe_at m bq 0 (words5 q) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bq 0 40 Cur Freeable ->
  Mem.range_perm m br 0 40 Cur Freeable -> Mem.range_perm m br2 0 40 Cur Freeable ->
  exists mf,
    Clight2.exec_stmt secp_ge (x_equiv_helper_env br br2) le m
      (fn_body f_secp256k1_gej_eq_x_var) E0
      (PTree.set _t'1 (Vint (if Z.eqb (radix_value x mod feP)
        ((radix_value z*radix_value z*radix_value q) mod feP) then Int.one else Int.zero)) le) mf
      (Out_return (Some (Vint (if Z.eqb (radix_value x mod feP)
        ((radix_value z*radix_value z*radix_value q) mod feP) then Int.one else Int.zero),tint))) /\
    Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bq 0 40 Cur Freeable /\
    Mem.range_perm mf br 0 40 Cur Freeable /\ Mem.range_perm mf br2 0 40 Cur Freeable /\
    lframe (fun b _ => b<>bp /\ b<>bq /\ b<>br /\ b<>br2) m mf.
Proof.
  intros BQ BX BZ HPQ HRP HRQ HR2P HR2Q HR2R HA HQ HX HZ Hq HFP HFQ HFR HFR2.
  destruct (x_equiv_square_multiply_calls q x z m bp bq br BQ BZ HPQ HRP HRQ
    HX HZ Hq HFP HFQ HFR)
    as (ms & mm & CS & CM & RM & QM & XM & RFM & QFM & PFM & VM & BM & FM).
  pose proof (curve_keep_free _ m mm br2 40 ltac:(lia) HFR2 FM
    ltac:(intro pos;repeat split;assumption)) as R2FM.
  destruct (exec_x_equiv_copy_owned (x_equiv_helper_env br br2) le mm bp br2 x
    eq_refl HA ltac:(congruence) XM R2FM) as (mc & CC & R2C & R2FC & FC).
  pose proof (field_at_lframe mm mc br 0 _ _ RM FC ltac:(intro pos;congruence)) as RC.
  pose proof (curve_keep_free _ mm mc br 40 ltac:(lia) RFM FC ltac:(intro pos;congruence)) as RFC.
  pose proof (curve_keep_free _ mm mc bp 128 ltac:(lia) PFM FC ltac:(intro pos;congruence)) as PFC.
  pose proof (curve_keep_free _ mm mc bq 40 ltac:(lia) QFM FC ltac:(intro pos;congruence)) as QFC.
  destruct (x_equiv_normalize_equal_calls (field_pair_product (square_words z) q) x mc br br2
    ltac:(congruence) ltac:(intros i HI;exact (proj2 (BM i HI))) BX RC R2C RFC R2FC)
    as (mn & mf & CN & CE & RFF & R2FF & FT).
  pose proof (curve_keep_free _ mc mf bp 128 ltac:(lia) PFC FT
    ltac:(intro pos;split;congruence)) as PFF.
  pose proof (curve_keep_free _ mc mf bq 40 ltac:(lia) QFC FT
    ltac:(intro pos;split;congruence)) as QFF.
  change (radix_value (field_pair_product (square_words z) q) mod feP =
    (radix_value z*radix_value z*radix_value q) mod feP) in VM.
  rewrite VM, Z.eqb_sym in CE.
  exists mf. split.
  - rewrite x_equiv_helper_body_source.
    eapply exec_x_equiv_body_from_calls; eassumption.
  - split;[exact PFF|]. split;[exact QFF|]. split;[exact RFF|]. split;[exact R2FF|].
    eapply lframe_trans.
    + eapply lframe_implies;[exact FM|]. intros b pos (HNP & HNQ & HNR & HNR2) HV.
      repeat split;assumption.
    + eapply lframe_trans.
      * eapply lframe_implies;[exact FC|]. intros b pos (HNP & HNQ & HNR & HNR2) HV;exact HNR2.
      * eapply lframe_implies;[exact FT|]. intros b pos (HNP & HNQ & HNR & HNR2) HV;split;assumption.
Qed.
Print Assumptions exec_x_equiv_body_owned.
