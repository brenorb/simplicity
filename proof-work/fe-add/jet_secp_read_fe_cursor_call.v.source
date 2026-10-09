(** Original reader call, canonical field and updated actual source frame. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_encoding C.jet_input_layout C.jet_output_layout C.jet_frame_layout C.jet_frame_inv.
Require Import C.jet_secp_wrapper_run C.jet_secp_local_regions C.jet_secp_local_call.
Require Import C.jet_secp_canonical_normalize C.jet_secp_read_fe_source.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_normalize.

Theorem eval_read_fe_canonical_with_source m0 bd dbase bw outedge cursor N cap bi edge rc
    (value : Ty.tySem (Word 8)) m ba bl :
  write_frame_at m0 bd dbase bw outedge cursor N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits value)) ->
  0 <= rc -> rc + 256 <= Int64.max_unsigned ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
  frame_fields_at m bl 0 bi edge rc -> ba <> bl ->
  xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  invA m0 bd dbase bw outedge cursor N bi rc false [] cap
    (read_fe_rho (frame_input_word_bits value) rc) [] m ->
  exists mr,
    Clight2.eval_funcall secp_ge m (Internal f_read_fe)
      [Vptr ba Ptrofs.zero; Vptr bl Ptrofs.zero] E0 mr Vundef /\
    fe_at mr ba 0 (map Int64.repr (fe_limbs_of
      (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)))) /\
    frame_fields_at mr bl 0 bi edge (rc+256) /\
    Mem.range_perm mr ba 0 40 Cur Freeable /\ Mem.range_perm mr bl 0 16 Cur Freeable /\
    invA m0 bd dbase bw outedge cursor N bi rc false [] cap
      (read_fe_rho (frame_input_word_bits value) rc) (read_fe_log bi (Ptrofs.repr edge)) mr /\
    lframe (frame (extA m0 bd bw bi) [(ba,0);(bl,0)]
      (local_read_initial_regs bi (Ptrofs.repr edge)) m) m mr.
Proof.
  intros HO HI Hrc HM HFreeA HFreeL HFields HSep HXS HInv.
  assert (HLength : length (frame_input_word_bits value) = 256%nat).
  { rewrite frame_input_word_bits_length; reflexivity. }
  assert (HM' : rc + Z.of_nat (length (frame_input_word_bits value)) <= Int64.max_unsigned).
  { rewrite HLength; exact HM. }
  pose proof (local_read_initial_rep_from_storage (frame_input_word_bits value) rc m ba bl bi edge
    HFreeA HFreeL HFields HSep) as HRep.
  destruct (eval_local_read_fe m0 bd dbase bw outedge cursor N bi edge rc
    (frame_input_word_bits value) [] cap HO HI Hrc HM' HLength m [(ba,0);(bl,0)] HRep HXS HInv)
    as (mr & HExec & HFinal & HFinalInv & HFrame).
  destruct (local_read_final_field mr ba bl bi edge rc value HFinal) as (HField & HFA & HFL).
  pose proof (local_read_final_source_fields mr ba bl bi edge rc
    (read_fe_rho (frame_input_word_bits value) rc) eq_refl HFinal) as HSource.
  exists mr. split; [exact HExec|]. split; [exact HField|].
  split; [exact HSource|]. split; [exact HFA|]. split; [exact HFL|].
  split; assumption.
Qed.
Print Assumptions eval_read_fe_canonical_with_source.
