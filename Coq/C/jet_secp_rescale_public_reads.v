(** Four unrestricted input words through the actual point and field readers.
    The fourth reader preserves the already-read point and infinity flag. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Memory Events Values.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_toZ C.jet_exec C.jet_encoding C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv.
Require Import C.jet_readBit_layout.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_frame C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp C.jet_secp_wrapper_run.
Require Import C.jet_secp_public_body C.jet_secp_read_gej_fields C.jet_secp_point_three_reads.
Require Import C.jet_secp_multiply_input_reader C.jet_secp_multiply_input_input
  C.jet_secp_multiply_writer_bridge C.jet_secp_multiply_normalize_bridge C.jet_secp_square_spec_bridge.
Require Import C.jet_secp_canonical_zero.
Require Import C.jet_secp_canonical_normalize C.jet_secp_fe_math C.jet_secp_b32_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge canonical_fe_is_zero canonical_fe_normalize.

Definition rescale_locals_outside m0 bd bw bi bp bc bl (b : block) (_ : Z) :=
  b <> bp /\ b <> bc /\ b <> bl /\ ~ extA m0 bd bw bi b.
Lemma rescale_reader_limbs x : point_canonical_limbs x = words5 (square_reader_rho x).
Proof.
  unfold point_canonical_limbs, square_reader_rho, normalized_value.
  generalize (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem x)).
  intro value; reflexivity.
Qed.

Theorem eval_rescale_public_reads m0 bd dbase bw outedge cursor N bi edge rc
    (x y z s : tySem (Word 8)) m bp bc bl :
  write_frame_at m0 bd dbase bw outedge cursor N -> 768 <= N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits x)) ->
  frame_input_cells_at m0 bi edge (rc+256) (map Some (frame_input_word_bits y)) ->
  frame_input_cells_at m0 bi edge (rc+512) (map Some (frame_input_word_bits z)) ->
  frame_input_cells_at m0 bi edge (rc+768) (map Some (frame_input_word_bits s)) ->
  0 <= rc -> rc+1024 <= Int64.max_unsigned ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bc 0 40 Cur Freeable ->
  Mem.range_perm m bl 0 16 Cur Freeable -> frame_fields_at m bl 0 bi edge rc ->
  bp <> bl -> bc <> bl -> bp <> bc -> xsep (extA m0 bd bw bi) [(bp,0);(bc,0);(bl,0)] ->
  finv m0 bd dbase bw outedge cursor N bi m false [] ->
  exists mr ms,
    Clight2.eval_funcall secp_ge m (Internal f_read_gej) [Vptr bp Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef /\
    Clight2.eval_funcall secp_ge mr (Internal f_read_fe) [Vptr bc Ptrofs.zero;Vptr bl Ptrofs.zero] E0 ms Vundef /\
    fe_at ms bp 0 (words5 (square_reader_rho x)) /\ fe_at ms bp 40 (words5 (square_reader_rho y)) /\
    fe_at ms bp 80 (words5 (square_reader_rho z)) /\ fe_at ms bc 0 (words5 (square_reader_rho s)) /\
    Mem.load Mint32 ms bp 120 = Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z)))) /\
    Mem.range_perm ms bp 0 128 Cur Freeable /\ Mem.range_perm ms bc 0 40 Cur Freeable /\
    Mem.range_perm ms bl 0 16 Cur Freeable /\ finv m0 bd dbase bw outedge cursor N bi ms false [] /\
    lframe (rescale_locals_outside m0 bd bw bi bp bc bl) m ms.
Proof.
  intros HO HN HX HY HZ HS Hrc HM HFP HFC HFL HSource HPL HCL HPC HSep HFin.
  assert (HSP : xsep (extA m0 bd bw bi) [(bp,0);(bl,0)]).
  { intros [|[|r]] HI; [exact (HSep 0%nat ltac:(cbn;lia))|exact (HSep 2%nat ltac:(cbn;lia))|cbn in HI;lia]. }
  assert (HSC : xsep (extA m0 bd bw bi) [(bc,0);(bl,0)]).
  { intros [|[|r]] HI; [exact (HSep 1%nat ltac:(cbn;lia))|exact (HSep 2%nat ltac:(cbn;lia))|cbn in HI;lia]. }
  assert (HInv : invA m0 bd dbase bw outedge cursor N bi rc false [] 768
    (read_fe_rho (frame_input_word_bits x) rc) [] m).
  { split; [reflexivity|]; split; [exact HFin|]; split; [exact HN|cbn;lia]. }
  destruct (eval_read_gej_canonical_fields m0 bd dbase bw outedge cursor N 768 bi edge rc x y z m bp bl
    HO HX HY HZ Hrc ltac:(lia) HFP HFL HSource HPL HSP HInv)
    as (mr & CPoint & FX & FY & FZ & Flag & SrcR & FPR & FLR & InvR & FrameP).
  assert (HVC : Mem.valid_block m bc) by (eapply Mem.perm_valid_block; apply (HFC 0); lia).
  assert (HCF : lframe (fun b _ => b = bc) m mr).
  { eapply lframe_implies; [exact FrameP|].
    intros b pos -> HV; unfold secp_locals_outside; repeat split; try congruence.
    exact (HSep 1%nat ltac:(cbn;lia)). }
  assert (FCR : Mem.range_perm mr bc 0 40 Cur Freeable).
  { intros pos HP; apply (proj1 (proj2 HCF)); [exact HVC|reflexivity|apply HFC;exact HP]. }
  destruct InvR as [_ [FinR _]].
  change (finv m0 bd dbase bw outedge cursor N bi mr false []) in FinR.
  destruct (eval_read_fe_with_cursor m0 bd dbase bw outedge cursor N bi edge (rc+768) s mr bc bl
    HO ltac:(lia) HS ltac:(lia) ltac:(lia) FCR FLR SrcR HCL HSC FinR)
    as (ms & CScale & FC & FCS & FLS & SrcS & FinS & FrameC).
  assert (HVP : Mem.valid_block mr bp) by (eapply Mem.perm_valid_block; apply (FPR 0);lia).
  pose proof (reader_preserves_other (extA m0 bd bw bi) bc bl bi (Ptrofs.repr edge) mr ms bp
    HPC HPL (HSep 0%nat ltac:(cbn;lia)) HVP FrameC) as HPF.
  rewrite !rescale_reader_limbs in FX, FY, FZ.
  change (fe_at ms bc 0 (point_canonical_limbs s)) in FC.
  rewrite rescale_reader_limbs in FC.
  exists mr, ms; split; [exact CPoint|]; split; [exact CScale|].
  split; [eapply fe_at_on_unchanged_block; [exact FX|exact HPF]|].
  split; [eapply fe_at_on_unchanged_block; [exact FY|exact HPF]|].
  split; [eapply fe_at_on_unchanged_block; [exact FZ|exact HPF]|].
  split; [exact FC|]; split.
  { rewrite (proj1 HPF Mint32 bp 120 HVP); [exact Flag|intros; reflexivity]. }
  split.
  { intros pos HP; apply (proj1 (proj2 HPF)); [exact HVP|reflexivity|apply FPR; exact HP]. }
  split; [exact FCS|]; split; [exact FLS|]; split; [exact FinS|].
  eapply lframe_trans.
  - eapply lframe_implies; [exact FrameP|]; intros b pos (HNP & HNC & HNL & HNE) HV.
    unfold secp_locals_outside; repeat split; assumption.
  - eapply lframe_implies; [exact FrameC|]; intros b pos (HNP & HNC & HNL & HNE) HV.
    split; [exact HV|]; split; [|exact HNE].
    intro HF; apply two_read_foot_owner in HF; destruct HF; contradiction.
Qed.
