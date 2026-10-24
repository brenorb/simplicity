(** Original fe_inv_var suffix: unpack an already canonical signed62 result
    and reclaim the actual two caller locals. This does not execute or assume
    correctness of the preceding modular-inverse call. The output is the
    separate, base-zero owned field used by the caller's local field value. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_fe_inv_statements C.jet_secp_curve_statements C.jet_secp_curve_frame.
Require Import C.jet_secp_signed62_storage C.jet_secp_signed62_repack C.jet_secp_signed62_numeric.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma fe_inv_local_blocks bt bs : blocks_of_env secp_ge (fe_inv_env bt bs) =
  [(bs,0,40);(bt,0,40)].
Proof. reflexivity. Qed.

Theorem exec_fe_inv_unpack_and_free le m bt bs bd w :
  le!_r=Some(Vptr bd Ptrofs.zero) -> bt<>bs -> bd<>bt -> bd<>bs ->
  signed62_normalized w -> fe_at m bs 0 (words5 w) ->
  Mem.range_perm m bs 0 40 Cur Freeable ->
  Mem.range_perm m bt 0 40 Cur Freeable ->
  Mem.range_perm m bd 0 40 Cur Freeable -> exists mf mr,
  Clight2.exec_stmt secp_ge (fe_inv_env bt bs) le m fe_inv_unpack E0 le mf Out_normal /\
  Mem.free_list mf (blocks_of_env secp_ge (fe_inv_env bt bs))=Some mr /\
  fe_at mr bd 0 (words5 (fe_repack_words false w)) /\
  Mem.range_perm mr bd 0 40 Cur Freeable /\
  fe_limbs_ok (Int64.unsigned (fe_repack_words false w 0%nat))
    (Int64.unsigned (fe_repack_words false w 1%nat))
    (Int64.unsigned (fe_repack_words false w 2%nat))
    (Int64.unsigned (fe_repack_words false w 3%nat))
    (Int64.unsigned (fe_repack_words false w 4%nat)) /\
  radix_value (fe_repack_words false w)=signed62_unsigned_value w /\
  lframe (fun b _=>b<>bd /\ b<>bt /\ b<>bs) m mr.
Proof.
  intros HR TS DT DS Bound Field FS FT FD.
  destruct (eval_fe_from_signed62_value w m bd bs Bound DS FD Field FS)
    as (mf & Call & Out & Inp & FDF & FSF & Limbs & Value & Frame).
  assert (FTF : Mem.range_perm mf bt 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FT|exact Frame|];intros;split;congruence. }
  assert (Exec : Clight2.exec_stmt secp_ge (fe_inv_env bt bs) le m fe_inv_unpack E0 le mf Out_normal).
  { unfold fe_inv_unpack;eapply exec_curve_call with
      (vargs:=[Vptr bd Ptrofs.zero;Vptr bs Ptrofs.zero]) (v:=Vundef).
    - unfold secp_pure;repeat (first [left;reflexivity|right]).
    - reflexivity.
    - eapply eval_Econs;[apply eval_Etempvar;exact HR|reflexivity|].
      eapply eval_Econs;[unfold fe_inv_s_address;apply eval_Eaddrof;apply eval_Evar_local;reflexivity|
        reflexivity|apply eval_Enil].
    - exact Call. }
  destruct (free_list_exists [(bs,0,40);(bt,0,40)] mf) as (mr & Free & Unchanged).
  - cbn;repeat constructor;cbn;intuition congruence.
  - intros b lo hi [Eq|[Eq|Nil]];[inversion Eq;subst;exact FSF|inversion Eq;subst;exact FTF|contradiction].
  - assert (Freed : lframe (fun b _=>b<>bt /\ b<>bs) mf mr).
    { eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
      intros b pos [NotT NotS] Valid;cbn;intuition congruence. }
    assert (Result : fe_at mr bd 0 (words5 (fe_repack_words false w))).
    { eapply curve_keep_field_range;[reflexivity|exact Out|exact Freed|];intros;split;assumption. }
    assert (FDR : Mem.range_perm mr bd 0 40 Cur Freeable).
    { eapply curve_keep_free;[lia|exact FDF|exact Freed|];intros;split;assumption. }
    assert (WholeFrame : lframe (fun b _=>b<>bd /\ b<>bt /\ b<>bs) m mr).
    { eapply lframe_trans; eapply lframe_implies;[exact Frame| |exact Freed|];
        intros b pos [NotD [NotT NotS]] Valid;split;assumption. }
    exists mf,mr;rewrite fe_inv_local_blocks;repeat first [assumption|split].
Qed.
