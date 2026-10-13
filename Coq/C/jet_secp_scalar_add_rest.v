(** Original scalar-add statement suffix: two reads, add, write and return.
    Actual helper executions are derived from initial frames and local storage. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Values Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_encoding C.jet_input_layout C.jet_frame_layout C.jet_output_layout C.jet_frame_inv.
Require Import C.jet_sx_mem C.jet_sx_exec C.jet_secp_frame C.jet_secp_wrapper_run.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_canonical_scalar_add.
Require Import C.jet_secp_scalar_add_call_chain C.jet_secp_scalar_add_body.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_scalar_add encode.

Theorem exec_scalar_add_rest_literal le m0 bd dbase bw outedge cursor N bi edge rc
    (a b : Ty.tySem (Word 8)) m ba bb bl :
  le!jets_secp._dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m0 bd dbase bw outedge cursor N ->
  frame_input_cells_at m0 bi edge rc (@encode (Ty.Prod (Word 8) (Word 8)) (a,b)) ->
  0 <= rc -> rc+512 <= Int64.max_unsigned ->
  Mem.range_perm m ba 0 32 Cur Freeable -> Mem.range_perm m bb 0 32 Cur Freeable ->
  Mem.range_perm m bl 0 16 Cur Freeable -> frame_fields_at m bl 0 bi edge rc ->
  ba <> bb -> ba <> bl -> bb <> bl ->
  xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  xsep (extA m0 bd bw bi) [(bb,0);(bl,0)] ->
  invA m0 bd dbase bw outedge cursor N bi rc false [] 256
    (read_fe_rho (frame_input_word_bits a) rc) [] m ->
  exists mf,
    Clight2.exec_stmt secp_ge (scalar_add_public_env bl ba bb) le m scalar_add_rest E0 le mf
      (Out_return (Some (Vint Int.one, tint))) /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (encode (@canonical_scalar_add Alg.CoreFunSem (a,b))) /\
    Mem.range_perm mf ba 0 32 Cur Freeable /\
    Mem.range_perm mf bb 0 32 Cur Freeable /\
    Mem.range_perm mf bl 0 16 Cur Freeable /\
    lframe (fun bx _ => bx <> ba /\ bx <> bb /\ bx <> bl /\
      ~ extA m0 bd bw bi bx) m mf.
Proof.
  intros HDst HO HI Hrc HM HFA HFB HFL HSource HAB HAL HBL HXSA HXSB HInv.
  destruct (eval_scalar_add_read_read_add_write m0 bd dbase bw outedge cursor N bi edge rc
    a b m ba bb bl HO HI Hrc HM HFA HFB HFL HSource HAB HAL HBL HXSA HXSB HInv)
    as (ma & mb & mn & mf & ret & HReadA & HReadB & HAdd & HWrite & HFinal &
      HFinalA & HFinalB & HCursorFinal & HFinalL & HFrame).
  exists mf. split.
  - eapply exec_scalar_add_rest_calls; eassumption.
  - split; [exact HFinal|]. split; [exact HFinalA|].
    split; [exact HFinalB|]. split; assumption.
Qed.
Print Assumptions exec_scalar_add_rest_literal.

