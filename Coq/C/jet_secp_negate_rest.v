(** Reader, in-place negation, writer and return of the original public body. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Values Memory Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_public_copy C.jet_secp_public_body.
Require Import C.jet_sx_state C.jet_sx_exec C.jet_sx_mem C.jet_secp_frame C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_encoding C.jet_frame_inv.
Require Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Translate.
Require Import C.jet_secp_wrapper_run C.jet_secp_local_regions C.jet_secp_local_call.
Require Import C.jet_secp_canonical_negate C.jet_secp_negate_body C.jet_secp_negate_after_read.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_negate Simplicity.Translate.encode.

Theorem exec_secp_fe_negate_rest_canonical le m0 bd dbase bw outedge cursor N bi edge rc
    (value : Ty.tySem (Word.Word 8)) m ba bl :
  le!jets_secp._dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m0 bd dbase bw outedge cursor N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits value)) ->
  0 <= rc -> rc + 256 <= Int64.max_unsigned ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
  frame_fields_at m bl 0 bi edge rc -> ba <> bl ->
  xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  invA m0 bd dbase bw outedge cursor N bi rc false [] 256
    (read_fe_rho (frame_input_word_bits value) rc) [] m ->
  exists mw,
    Clight2.exec_stmt secp_ge (secp_public_env bl ba) le m secp_fe_negate_rest E0 le mw
      (Out_return (Some (Vint Int.one, tint))) /\
    finv m0 bd dbase bw outedge cursor N bi mw true
      (Simplicity.Translate.encode (@canonical_fe_negate Alg.CoreFunSem value)) /\
    Mem.range_perm mw ba 0 40 Cur Freeable /\ Mem.range_perm mw bl 0 16 Cur Freeable /\
    lframe (secp_locals_outside m0 bd bw bi ba bl) m mw.
Proof.
  intros HDst HOutput HInput HCursor HMax HFieldFree HFrameFree HFields HSeparate HSep HInv.
  destruct (eval_local_read_fe_canonical m0 bd dbase bw outedge cursor N bi edge rc value m ba bl
    HOutput HInput HCursor HMax HFieldFree HFrameFree HFields HSeparate HSep HInv)
    as [mr [HRead [HField [HFreeA [HFreeL [HReadInv HReadFrame]]]]]].
  destruct (eval_negate_write_after_read_field m0 bd dbase bw outedge cursor N bi edge rc value mr ba bl
    HOutput HField HFreeA HFreeL HSeparate HSep HReadInv)
    as (mn & mw & HNeg & HWrite & HFinal & HFinalFreeA & HFinalFreeL & HWriteFrame).
  exists mw; split.
  - unfold secp_fe_negate_rest.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := le).
    + apply exec_secp_public_read; exact HRead.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mn) (le1 := le).
      * apply exec_secp_public_negate; exact HNeg.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mw) (le1 := le).
        -- apply exec_secp_public_write with (bd := bd) (dbase := dbase); assumption.
        -- apply exec_Sreturn_some; constructor.
  - split; [exact HFinal|]; split; [exact HFinalFreeA|]; split; [exact HFinalFreeL|].
    eapply lframe_trans.
    + eapply lframe_implies; [exact HReadFrame|].
      intros b pos [HA [HL HE]] HValid; split; [exact HValid|]; split; [|exact HE].
      apply no_local_read_foot; assumption.
    + eapply lframe_implies; [exact HWriteFrame|].
      intros b pos [HA [HL HE]] HValid; split; [exact HValid|]; split; [|exact HE].
      apply no_local_write_foot; assumption.
Qed.
Print Assumptions exec_secp_fe_negate_rest_canonical.
