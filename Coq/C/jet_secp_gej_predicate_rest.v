(** Actual public point-predicate remainder from initial owned state. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Clight ClightBigstep Integers Values Memory Events Maps.
Require Import Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit Simplicity.Translate.
Require Import C.jet_exec C.jet_readBit_layout C.jet_encoding C.jet_input_layout C.jet_output_layout.
Require Import C.jet_frame_layout C.jet_frame_inv C.jet_sx_mem C.jet_sx_exec C.jet_secp_frame.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_wrapper_run.
Require Import C.jet_secp_public_body C.jet_secp_odd_body C.jet_secp_bit_writer.
Require Import C.jet_secp_canonical_zero C.jet_secp_zero_rest C.jet_secp_gej_public_entry.
Require Import C.jet_secp_gej_flag_read C.jet_secp_read_gej_owned C.jet_secp_gej_predicate_body.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge canonical_fe_is_zero.

Theorem exec_gej_predicate_rest_owned le m0 bd dbase bw outedge cursor N bi edge rc
    (x y z : Ty.tySem (Word 8)) m ba bl :
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m0 bd dbase bw outedge cursor N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits x)) ->
  frame_input_cells_at m0 bi edge (rc+256) (map Some (frame_input_word_bits y)) ->
  frame_input_cells_at m0 bi edge (rc+512) (map Some (frame_input_word_bits z)) ->
  0 <= rc -> rc+768 <= Int64.max_unsigned ->
  Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
  frame_fields_at m bl 0 bi edge rc -> ba <> bl ->
  xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  invA m0 bd dbase bw outedge cursor N bi rc false [] 1
    (read_fe_rho (frame_input_word_bits x) rc) [] m ->
  exists mf,
    Clight2.exec_stmt secp_ge (gej_public_env bl ba) le m gej_predicate_rest E0
      (PTree.set _t'1 (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z)))) le)
      mf (Out_return (Some (Vint Int.one, tint))) /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (Simplicity.Translate.encode (@canonical_fe_is_zero Alg.CoreFunSem z)) /\
    Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf bl 0 16 Cur Freeable /\
    lframe (secp_locals_outside m0 bd bw bi ba bl) m mf.
Proof.
  intros HD HO HX HY HZ Hrc HM HFA HFL HSource HSep HXS HI.
  destruct (eval_read_gej_canonical_owned m0 bd dbase bw outedge cursor N 1 bi edge rc
    x y z m ba bl HO HX HY HZ Hrc HM HFA HFL HSource HSep HXS HI)
    as (mr & HRead & HFlag & HSourceR & HFreeAR & HFreeLR & HInvR & HReadFrame).
  pose proof (eval_gej_flag_accessor mr ba 0
    (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z))) ltac:(lia)
    ltac:(change Ptrofs.max_unsigned with 18446744073709551615;lia) HFlag) as HAccessor.
  set (bit := Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z)).
  destruct HInvR as [_ [HCurrent [HCapacity _]]].
  change (finv m0 bd dbase bw outedge cursor N bi mr false []) in HCurrent.
  change (1 <= N) in HCapacity.
  destruct (eval_secp_writeBit_from_invariant m0 bd dbase bw outedge cursor N bi mr bit
    HO HCapacity HCurrent) as (mf & HWrite & HFinal & HWriteFrame & HWritePerms).
  assert (HValidDst : Mem.valid_block m0 bd).
  { pose proof HO as [_ [[HE _] _]]. exact (load_valid _ _ _ _ _ HE). }
  assert (HValidWords : Mem.valid_block m0 bw).
  { destruct (write_frame_at_head m0 bd dbase bw outedge cursor N ltac:(lia) HO)
      as [_ [_ [_ [w HL]]]]. exact (load_valid _ _ _ _ _ HL). }
  exists mf; split.
  - unfold gej_predicate_rest.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := le).
    + apply exec_gej_predicate_read; exact HRead.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mf)
        (le1 := PTree.set _t'1 (Vint (bit_int bit)) le).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
          (le1 := PTree.set _t'1 (Vint (bit_int bit)) le).
        -- apply exec_gej_predicate_flag; exact HAccessor.
        -- eapply exec_secp_bit_write_in_env.
           ++ reflexivity.
           ++ rewrite PTree.gso by discriminate; exact HD.
           ++ apply PTree.gss.
           ++ exact HWrite.
      * apply exec_Sreturn_some; constructor.
  - split.
    + rewrite canonical_zero_encoded; exact HFinal.
    + split.
      * intros pos HPos; apply HWritePerms; apply HFreeAR; exact HPos.
      * split.
        -- intros pos HPos; apply HWritePerms; apply HFreeLR; exact HPos.
        -- eapply lframe_trans; [exact HReadFrame|].
           eapply lframe_implies; [exact HWriteFrame|].
           intros b pos [HA [HL HE]] HV. unfold extA, fext in HE.
           split; intro HB; subst b; apply HE; split;
             [left;reflexivity|exact HValidDst|right;left;reflexivity|exact HValidWords].
Qed.
Timeout 60 Print Assumptions exec_gej_predicate_rest_owned.
