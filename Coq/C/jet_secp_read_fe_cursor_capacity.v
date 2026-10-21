(** A reader's input width does not impose the output frame's capacity. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Values Memory Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv C.jet_encoding.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_mem C.jet_sx_exec C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_wrapper_run C.jet_secp_local_regions C.jet_secp_multiply_input_reader.
Require Import C.jet_secp_multiply_input_input C.jet_secp_local_call C.jet_secp_fe_nv C.jet_secp_fe_math.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem eval_read_fe_with_cursor_capacity m0 bd dbase bw outedge cursor N cap bi edge rc
    (x : Ty.tySem (Word 8)) m ba bl :
  write_frame_at m0 bd dbase bw outedge cursor N -> 0<=cap -> cap<=N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits x)) ->
  0<=rc -> rc+256<=Int64.max_unsigned ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
  frame_fields_at m bl 0 bi edge rc -> ba<>bl ->
  xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  finv m0 bd dbase bw outedge cursor N bi m false [] ->
  exists mr,
    Clight2.eval_funcall secp_ge m (Internal f_read_fe)
      [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef /\
    fe_at mr ba 0 (map Int64.repr (fe_limbs_of (normalized_value x))) /\
    Mem.range_perm mr ba 0 40 Cur Freeable /\ Mem.range_perm mr bl 0 16 Cur Freeable /\
    frame_fields_at mr bl 0 bi edge (rc+256) /\
    finv m0 bd dbase bw outedge cursor N bi mr false [] /\
    lframe (frame (extA m0 bd bw bi) [(ba,0);(bl,0)]
      (local_read_initial_regs bi (Ptrofs.repr edge)) m) m mr.
Proof.
  intros HO HCap HC HX HCursor HMax HFA HFL HFields HD HS HFinv.
  assert (HI : invA m0 bd dbase bw outedge cursor N bi rc false [] cap
    (read_fe_rho (frame_input_word_bits x) rc) [] m).
  { change (Int64.repr rc = Int64.repr rc /\
      finv m0 bd dbase bw outedge cursor N bi m false [] /\ cap<=N /\ 0<=cap).
    split;[reflexivity|]. split;[exact HFinv|]. split;assumption. }
  pose proof (local_read_initial_rep_from_storage (frame_input_word_bits x) rc m ba bl bi edge
    HFA HFL HFields HD) as HR.
  destruct (eval_local_read_fe m0 bd dbase bw outedge cursor N bi edge rc
    (frame_input_word_bits x) [] cap HO HX HCursor
    ltac:(rewrite frame_input_word_bits_length;exact HMax)
    ltac:(rewrite frame_input_word_bits_length;reflexivity)
    m [(ba,0);(bl,0)] HR HS HI) as (mr & HCall & HRep & HInv & HF).
  destruct (local_read_final_field mr ba bl bi edge rc x HRep) as (HValue & HFreeA & HFreeL).
  pose proof (local_read_final_cursor (frame_input_word_bits x) rc mr ba bl bi edge HRep) as HNext.
  destruct HInv as [_ [HFin _]].
  exists mr. split;[exact HCall|]. split;[exact HValue|]. split;[exact HFreeA|].
  split;[exact HFreeL|]. split;[exact HNext|]. split;[exact HFin|exact HF].
Qed.
Print Assumptions eval_read_fe_with_cursor_capacity.
