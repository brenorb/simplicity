(** Public X-equivalence reads q first, then (x,y,z), with one output bit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Memory Events Values.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_exec C.jet_encoding C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv.
Require Import C.jet_readBit_layout C.jet_sx_exec C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_frame.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_wrapper_run C.jet_secp_public_body.
Require Import C.jet_secp_multiply_input_reader C.jet_secp_multiply_input_input C.jet_secp_multiply_normalize_bridge.
Require Import C.jet_secp_square_spec_bridge C.jet_secp_rescale_public_reads C.jet_secp_point_three_reads.
Require Import C.jet_secp_read_gej_fields C.jet_secp_canonical_zero C.jet_secp_field_read_preservation.
Require Import C.jet_secp_curve_frame C.jet_secp_read_fe_cursor_capacity.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge canonical_fe_is_zero.

Lemma x_equiv_read_limbs q :
  map Int64.repr (C.jet_secp_fe_math.fe_limbs_of (normalized_value q)) = point_canonical_limbs q.
Proof. reflexivity. Qed.

Theorem eval_x_equiv_public_reads m0 bd dbase bw outedge cursor N bi edge rc
    (q x y z : tySem (Word 8)) m bp bq bl :
  write_frame_at m0 bd dbase bw outedge cursor N -> 1<=N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits q)) ->
  frame_input_cells_at m0 bi edge (rc+256) (map Some (frame_input_word_bits x)) ->
  frame_input_cells_at m0 bi edge (rc+512) (map Some (frame_input_word_bits y)) ->
  frame_input_cells_at m0 bi edge (rc+768) (map Some (frame_input_word_bits z)) ->
  0<=rc -> rc+1024<=Int64.max_unsigned ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bq 0 40 Cur Freeable ->
  Mem.range_perm m bl 0 16 Cur Freeable -> frame_fields_at m bl 0 bi edge rc ->
  bp<>bl -> bq<>bl -> bp<>bq -> xsep (extA m0 bd bw bi) [(bp,0);(bq,0);(bl,0)] ->
  finv m0 bd dbase bw outedge cursor N bi m false [] ->
  exists mq mr,
    Clight2.eval_funcall secp_ge m (Internal f_read_fe) [Vptr bq Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mq Vundef /\
    Clight2.eval_funcall secp_ge mq (Internal f_read_gej) [Vptr bp Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef /\
    fe_at mr bp 0 (words5 (square_reader_rho x)) /\
    fe_at mr bp 80 (words5 (square_reader_rho z)) /\ fe_at mr bq 0 (words5 (square_reader_rho q)) /\
    Mem.load Mint32 mr bp 120 = Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z)))) /\
    Mem.range_perm mr bp 0 128 Cur Freeable /\ Mem.range_perm mr bq 0 40 Cur Freeable /\
    Mem.range_perm mr bl 0 16 Cur Freeable /\ finv m0 bd dbase bw outedge cursor N bi mr false [] /\
    lframe (rescale_locals_outside m0 bd bw bi bp bq bl) m mr.
Proof.
  intros HO HN HQ HX HY HZ Hrc HM HFP HFQ HFL HSource HPL HQL HPQ HSep HFin.
  assert (HSQ : xsep (extA m0 bd bw bi) [(bq,0);(bl,0)]).
  { intros [|[|r]] HI;[exact (HSep 1%nat ltac:(cbn;lia))|exact (HSep 2%nat ltac:(cbn;lia))|cbn in HI;lia]. }
  assert (HSP : xsep (extA m0 bd bw bi) [(bp,0);(bl,0)]).
  { intros [|[|r]] HI;[exact (HSep 0%nat ltac:(cbn;lia))|exact (HSep 2%nat ltac:(cbn;lia))|cbn in HI;lia]. }
  destruct (eval_read_fe_with_cursor_capacity m0 bd dbase bw outedge cursor N 1 bi edge rc q m bq bl
    HO ltac:(lia) HN HQ Hrc ltac:(lia) HFQ HFL HSource HQL HSQ HFin)
    as (mq & CQ & FQ & QFQ & FLQ & SrcQ & FinQ & FrameQ).
  rewrite x_equiv_read_limbs in FQ.
  assert (HVP : Mem.valid_block m bp) by (eapply Mem.perm_valid_block;apply (HFP 0);lia).
  pose proof (reader_preserves_other (extA m0 bd bw bi) bq bl bi (Ptrofs.repr edge) m mq bp
    HPQ HPL (HSep 0%nat ltac:(cbn;lia)) HVP FrameQ) as FPQ.
  pose proof (curve_keep_free _ m mq bp 128 ltac:(lia) HFP FPQ ltac:(intros;reflexivity)) as PFQ.
  assert (HInv : invA m0 bd dbase bw outedge cursor N bi (rc+256) false [] 1
    (read_fe_rho (frame_input_word_bits x) (rc+256)) [] mq).
  { split;[reflexivity|]. split;[exact FinQ|]. split;[exact HN|cbn;lia]. }
  assert (HY' : frame_input_cells_at m0 bi edge (rc+256+256) (map Some (frame_input_word_bits y)))
    by (replace (rc+256+256) with (rc+512) by lia;exact HY).
  assert (HZ' : frame_input_cells_at m0 bi edge (rc+256+512) (map Some (frame_input_word_bits z)))
    by (replace (rc+256+512) with (rc+768) by lia;exact HZ).
  destruct (eval_read_gej_canonical_fields m0 bd dbase bw outedge cursor N 1 bi edge (rc+256)
    x y z mq bp bl HO HX HY' HZ' ltac:(lia) ltac:(lia) PFQ FLQ SrcQ HPL HSP HInv)
    as (mr & CP & FX & FY & FZ & Flag & SrcR & PFR & FLR & InvR & FrameP).
  assert (FQP : lframe (fun b _ => b=bq) mq mr).
  { eapply lframe_implies;[exact FrameP|]. intros b pos -> HV.
    unfold secp_locals_outside;repeat split;try congruence.
    exact (HSep 1%nat ltac:(cbn;lia)). }
  pose proof (field_at_lframe mq mr bq 0 _ _ FQ FQP ltac:(intros;reflexivity)) as FQR.
  pose proof (curve_keep_free _ mq mr bq 40 ltac:(lia) QFQ FQP ltac:(intros;reflexivity)) as QFR.
  rewrite !rescale_reader_limbs in FX,FZ,FQR.
  destruct InvR as [_ [FinR _]].
  exists mq,mr. split;[exact CQ|]. split;[exact CP|]. split;[exact FX|]. split;[exact FZ|].
  split;[exact FQR|]. split;[exact Flag|]. split;[exact PFR|]. split;[exact QFR|].
  split;[exact FLR|]. split;[exact FinR|].
  eapply lframe_trans.
  - eapply lframe_implies;[exact FrameQ|]. intros b pos (HNP & HNQ & HNL & HNE) HV.
    split;[exact HV|]. split;[|exact HNE]. intro HF.
    apply two_read_foot_owner in HF;destruct HF;contradiction.
  - eapply lframe_implies;[exact FrameP|]. intros b pos (HNP & HNQ & HNL & HNE) HV.
    unfold secp_locals_outside;repeat split;assumption.
Qed.
