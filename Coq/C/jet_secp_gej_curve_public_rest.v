(** Original projective wrapper remainder, deriving reader, helper and writer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Clight ClightBigstep Integers Values Memory Events Maps.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit Simplicity.Translate.
Require Import C.jet_exec C.jet_readBit_layout C.jet_encoding C.jet_input_layout C.jet_output_layout.
Require Import C.jet_frame_layout C.jet_frame_inv C.jet_sx_mem C.jet_sx_exec C.jet_secp_frame.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_wrapper_run C.jet_secp_public_body.
Require Import C.jet_secp_read_gej_fields C.jet_secp_curve_literal C.jet_secp_gej_curve_literal_bridge.
Require Import C.jet_secp_gej_public_entry C.jet_secp_gej_curve_public_statements C.jet_secp_bit_writer.
Import ListNotations Clightdefs Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_gej_is_on_curve secp_ge Simplicity.Translate.encode.

Theorem exec_gej_curve_public_rest_owned le m0 bd dbase bw outedge cursor N bi edge rc
    (x y z : tySem (Word 8)) m ba bl :
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m0 bd dbase bw outedge cursor N -> 1<=N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits x)) ->
  frame_input_cells_at m0 bi edge (rc+256) (map Some (frame_input_word_bits y)) ->
  frame_input_cells_at m0 bi edge (rc+512) (map Some (frame_input_word_bits z)) ->
  0<=rc -> rc+768<=Int64.max_unsigned ->
  Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
  frame_fields_at m bl 0 bi edge rc -> ba<>bl ->
  xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  finv m0 bd dbase bw outedge cursor N bi m false [] ->
  exists mf,
    Clight2.exec_stmt secp_ge (gej_public_env bl ba) le m gej_curve_public_rest E0
      (PTree.set _t'1 (Vint (bit_int (Bit.toBool (@literal_gej_is_on_curve Alg.CoreFunSem ((x,y),z))))) le)
      mf (Out_return (Some (Vint Int.one,tint))) /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (Simplicity.Translate.encode (@literal_gej_is_on_curve Alg.CoreFunSem ((x,y),z))) /\
    Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf bl 0 16 Cur Freeable /\
    lframe (secp_locals_outside m0 bd bw bi ba bl) m mf.
Proof.
  intros HD HO HN HX HY HZ Hrc HM HFA HFL HSource HSep HXS HFin.
  assert (HI : invA m0 bd dbase bw outedge cursor N bi rc false [] 1
    (read_fe_rho (frame_input_word_bits x) rc) [] m).
  { split; [reflexivity|]. split; [exact HFin|]. split; [exact HN|cbn;lia]. }
  destruct (eval_read_gej_canonical_fields m0 bd dbase bw outedge cursor N 1 bi edge rc
    x y z m ba bl HO HX HY HZ Hrc HM HFA HFL HSource HSep HXS HI)
    as (mr & HR & FX & FY & FZ & Flag & SrcR & FAR & FLR & InvR & FrameR).
  destruct (eval_gej_curve_literal x y z mr ba FX FY FZ FAR)
    as (mn & HC & FAN & FrameC).
  assert (HVL : Mem.valid_block mr bl) by (eapply Mem.perm_valid_block; apply (FLR 0);lia).
  assert (FLN : Mem.range_perm mn bl 0 16 Cur Freeable).
  { intros pos HPos; apply (proj1 (proj2 FrameC)); [exact HVL|congruence|apply FLR;exact HPos]. }
  assert (ExtC : eqext m0 bd bw bi mr mn).
  { eapply lframe_implies; [exact FrameC|].
    intros b pos HE HV HB; subst b; exact (HXS 0%nat ltac:(cbn;lia) HE). }
  destruct InvR as [_ [FinR _]].
  change (finv m0 bd dbase bw outedge cursor N bi mr false []) in FinR.
  assert (FinN : finv m0 bd dbase bw outedge cursor N bi mn false []).
  { eapply finv_stable; eassumption. }
  set (bit := Bit.toBool (@literal_gej_is_on_curve Alg.CoreFunSem ((x,y),z))).
  destruct (eval_secp_writeBit_from_invariant m0 bd dbase bw outedge cursor N bi mn bit HO HN FinN)
    as (mf & HW & FinW & FrameW & PermW).
  assert (HVD : Mem.valid_block m0 bd).
  { pose proof HO as [_ [[HE _] _]]. exact (load_valid _ _ _ _ _ HE). }
  assert (HVW : Mem.valid_block m0 bw).
  { destruct (write_frame_at_head m0 bd dbase bw outedge cursor N ltac:(lia) HO)
      as [_ [_ [_ [w HL]]]]. exact (load_valid _ _ _ _ _ HL). }
  exists mf. split.
  - eapply exec_gej_curve_public_rest_from_calls; eassumption.
  - split.
    + assert (HE : Simplicity.Translate.encode (@literal_gej_is_on_curve Alg.CoreFunSem ((x,y),z)) =
        [Some bit]).
      { unfold bit. destruct (@literal_gej_is_on_curve Alg.CoreFunSem ((x,y),z)); reflexivity. }
      rewrite HE; exact FinW.
    + split.
      * intros pos HPos; apply PermW; apply FAN; exact HPos.
      * split.
        -- intros pos HPos; apply PermW; apply FLN; exact HPos.
        -- eapply lframe_trans; [exact FrameR|].
           eapply lframe_trans.
           ++ eapply lframe_implies; [exact FrameC|].
              intros b pos [HA _] HV; exact HA.
           ++ eapply lframe_implies; [exact FrameW|].
              intros b pos [HA [HL HE]] HV; unfold extA,fext in HE.
              split; intro HB; subst b; apply HE; split;
                [left;reflexivity|exact HVD|right;left;reflexivity|exact HVW].
Qed.
Print Assumptions exec_gej_curve_public_rest_owned.
