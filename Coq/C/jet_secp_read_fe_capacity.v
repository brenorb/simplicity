(** The 256-bit reader with independent output capacity, for predicate jets. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_encoding C.jet_input_layout C.jet_output_layout C.jet_frame_layout C.jet_frame_inv.
Require Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Translate.
Require Import C.jet_secp_wrapper_run C.jet_secp_local_regions C.jet_secp_local_call C.jet_secp_canonical_normalize.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_normalize Simplicity.Translate.encode.

Theorem eval_local_read_fe_canonical_capacity m0 bd dbase bw outedge cursor N cap bi edge rc
    (value : Ty.tySem (Word.Word 8)) m ba bl :
  write_frame_at m0 bd dbase bw outedge cursor N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits value)) ->
  0 <= rc -> rc + 256 <= Int64.max_unsigned ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
  frame_fields_at m bl 0 bi edge rc -> ba <> bl ->
  xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  invA m0 bd dbase bw outedge cursor N bi rc false [] cap
    (read_fe_rho (frame_input_word_bits value) rc) [] m ->
  exists mr,
    Clight2.eval_funcall secp_ge m (Internal f_read_fe) [Vptr ba Ptrofs.zero; Vptr bl Ptrofs.zero] E0 mr Vundef /\
    fe_at mr ba 0 (map Int64.repr (fe_limbs_of
      (@Word.ToZ.Theory.toZ (Word.WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)))) /\
    Mem.range_perm mr ba 0 40 Cur Freeable /\ Mem.range_perm mr bl 0 16 Cur Freeable /\
    invA m0 bd dbase bw outedge cursor N bi rc false [] cap
      (read_fe_rho (frame_input_word_bits value) rc) (read_fe_log bi (Ptrofs.repr edge)) mr /\
    lframe (frame (extA m0 bd bw bi) [(ba,0);(bl,0)]
      (local_read_initial_regs bi (Ptrofs.repr edge)) m) m mr.
Proof.
  intros HOutput HInput HCursor HMax HFieldFree HFrameFree HFields HSeparate HSep HInv.
  assert (HLength : length (frame_input_word_bits value) = 256%nat).
  { rewrite frame_input_word_bits_length; reflexivity. }
  assert (HMax' : rc + Z.of_nat (length (frame_input_word_bits value)) <= Int64.max_unsigned).
  { rewrite HLength; exact HMax. }
  pose proof (local_read_initial_rep_from_storage (frame_input_word_bits value) rc m ba bl bi edge
    HFieldFree HFrameFree HFields HSeparate) as HRep.
  destruct (eval_local_read_fe m0 bd dbase bw outedge cursor N bi edge rc (frame_input_word_bits value)
    [] cap HOutput HInput HCursor HMax' HLength m [(ba,0);(bl,0)] HRep HSep HInv)
    as [mr [HExec [HFinal [HFinalInv HFrame]]]].
  destruct (local_read_final_field mr ba bl bi edge rc value HFinal) as [HValue [HFreeA HFreeL]].
  exists mr; split; [exact HExec|]; split; [exact HValue|]; split; [exact HFreeA|];
    split; [exact HFreeL|]; split; assumption.
Qed.
