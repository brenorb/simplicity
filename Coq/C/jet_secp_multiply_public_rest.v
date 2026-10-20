(** All public-body helper executions derived from the original input/frame facts. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers Values Memory AST Ctypes Clight ClightBigstep Maps Events.
Require Import Simplicity.Word.
Require Simplicity.Translate.
Require Import C.jet_encoding C.jet_frame_layout C.jet_output_layout C.jet_frame_inv.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_multiply_input_input C.jet_secp_multiply_input_pair C.jet_secp_multiply_input_compose C.jet_secp_multiply_public_layout C.jet_secp_multiply_public_calls.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge input_product_word pair_rho normalized_value Simplicity.Translate.encode.

Theorem exec_original_public_rest le m0 bd dbase bw outedge cursor N bi edge rc
    (x y : Ty.tySem (Word 8)) m ba bb bl :
  le!jets_secp._dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m0 bd dbase bw outedge cursor N -> 256 <= N ->
  frame_input_cells_at m0 bi edge rc
    (@Simplicity.Translate.encode (Ty.Prod (Word 8) (Word 8)) (x, y)) ->
  0 <= rc -> rc + 512 <= Int64.max_unsigned ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bb 0 40 Cur Freeable ->
  Mem.range_perm m bl 0 16 Cur Freeable -> frame_fields_at m bl 0 bi edge rc ->
  ba <> bb -> ba <> bl -> bb <> bl ->
  xsep (extA m0 bd bw bi) [(ba, 0); (bb, 0); (bl, 0)] ->
  finv m0 bd dbase bw outedge cursor N bi m false [] ->
  exists mw,
    Clight2.exec_stmt secp_ge (public_env bl ba bb) le m rest_stmt E0 le mw
      (Out_return (Some (Vint Int.one, tint))) /\
    finv m0 bd dbase bw outedge cursor N bi mw true
      (@Simplicity.Translate.encode (Word 8) (input_product_word x y)) /\
    Mem.range_perm mw ba 0 40 Cur Freeable /\ Mem.range_perm mw bb 0 40 Cur Freeable /\
    Mem.range_perm mw bl 0 16 Cur Freeable /\
    lframe (pair_locals_outside (extA m0 bd bw bi) ba bb bl) m mw.
Proof.
  intros HD HO HC HInput HCursor HMax HFA HFB HFL HFields HDAB HDAL HDBL HS HI.
  destruct (eval_original_read_pair_mul_write m0 bd dbase bw outedge cursor N bi edge rc
    x y m ba bb bl HO HC HInput HCursor HMax HFA HFB HFL HFields HDAB HDAL HDBL HS HI)
    as (ma & mr & mm & mf & HA & HB & HM & HW & HFinal & HFreeA & HFreeB & HFreeL & HNext & HF).
  exists mf; split.
  - eapply exec_four_call_body; eassumption.
  - split; [exact HFinal|]; split; [exact HFreeA|]; split; [exact HFreeB|]; split; assumption.
Qed.
