(** Two actual original reader calls from initial frames and owned locals.
    No intermediate source cursor, first-field preservation or second-call
    execution is assumed. Public allocation/entry/cleanup remains separate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_encoding C.jet_input_layout C.jet_output_layout C.jet_frame_layout C.jet_frame_inv.
Require Import C.jet_secp_wrapper_run C.jet_secp_local_regions C.jet_secp_public_body.
Require Import C.jet_secp_canonical_normalize C.jet_secp_read_fe_cursor_call.
Require Import C.jet_secp_read_fe_rebase C.jet_secp_field_read_preservation.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_normalize.

Theorem eval_add_two_readers m0 bd dbase bw outedge cursor N cap bi edge rc
    (a b : Ty.tySem (Word 8)) m ba bb bl :
  write_frame_at m0 bd dbase bw outedge cursor N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits a)) ->
  frame_input_cells_at m0 bi edge (rc+256) (map Some (frame_input_word_bits b)) ->
  0 <= rc -> rc+512 <= Int64.max_unsigned ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bb 0 40 Cur Freeable ->
  Mem.range_perm m bl 0 16 Cur Freeable -> frame_fields_at m bl 0 bi edge rc ->
  ba <> bb -> ba <> bl -> bb <> bl ->
  xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  xsep (extA m0 bd bw bi) [(bb,0);(bl,0)] ->
  invA m0 bd dbase bw outedge cursor N bi rc false [] cap
    (read_fe_rho (frame_input_word_bits a) rc) [] m ->
  exists ma mb,
    Clight2.eval_funcall secp_ge m (Internal f_read_fe)
      [Vptr ba Ptrofs.zero; Vptr bl Ptrofs.zero] E0 ma Vundef /\
    Clight2.eval_funcall secp_ge ma (Internal f_read_fe)
      [Vptr bb Ptrofs.zero; Vptr bl Ptrofs.zero] E0 mb Vundef /\
    fe_at mb ba 0 (map Int64.repr (fe_limbs_of
      (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem a)))) /\
    fe_at mb bb 0 (map Int64.repr (fe_limbs_of
      (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem b)))) /\
    frame_fields_at mb bl 0 bi edge (rc+512) /\
    Mem.range_perm mb ba 0 40 Cur Freeable /\ Mem.range_perm mb bb 0 40 Cur Freeable /\
    Mem.range_perm mb bl 0 16 Cur Freeable /\
    invA m0 bd dbase bw outedge cursor N bi (rc+256) false [] cap
      (read_fe_rho (frame_input_word_bits b) (rc+256))
      (read_fe_log bi (Ptrofs.repr edge)) mb /\
    lframe (frame (extA m0 bd bw bi) [(ba,0);(bl,0)]
      (local_read_initial_regs bi (Ptrofs.repr edge)) m) m ma /\
    lframe (frame (extA m0 bd bw bi) [(bb,0);(bl,0)]
      (local_read_initial_regs bi (Ptrofs.repr edge)) ma) ma mb.
Proof.
  intros HO HA HB Hrc HM HFA HFB HFL HSource HAB HAL HBL HXSA HXSB HInv.
  destruct (eval_read_fe_canonical_with_source m0 bd dbase bw outedge cursor N cap
    bi edge rc a m ba bl HO HA Hrc ltac:(lia) HFA HFL HSource HAL HXSA HInv)
    as (ma & HCallA & HFieldA & HSourceA & HFreeA & HFreeL & HInvA & HFrameA).
  assert (HValidB : Mem.valid_block m bb).
  { eapply Mem.perm_valid_block. apply (HFB 0). lia. }
  assert (HOutsideB : forall pos, frame (extA m0 bd bw bi) [(ba,0);(bl,0)]
    (local_read_initial_regs bi (Ptrofs.repr edge)) m bb pos).
  { intro pos. unfold frame. split; [exact HValidB|]. split.
    - apply no_local_read_foot; [congruence|exact HBL].
    - exact (HXSB 0%nat ltac:(cbn; lia)). }
  assert (HFreeB : Mem.range_perm ma bb 0 40 Cur Freeable).
  { intros pos HPos. apply (proj1 (proj2 HFrameA));
      [exact HValidB|apply HOutsideB|apply HFB; exact HPos]. }
  pose proof (read_fe_final_inv_to_next_initial m0 bd dbase bw outedge cursor N bi
    edge rc (rc+256) cap a b ma HInvA) as HNext.
  destruct (eval_read_fe_canonical_with_source m0 bd dbase bw outedge cursor N cap
    bi edge (rc+256) b ma bb bl HO HB ltac:(lia) ltac:(lia)
    HFreeB HFreeL HSourceA HBL HXSB HNext)
    as (mb & HCallB & HFieldB & HSourceB & HFinalB & HFinalL & HInvB & HFrameB).
  destruct (field_preserved_across_other_read ma mb m0 bd bw bi ba bb bl edge _
    HAB HAL (HXSA 0%nat ltac:(cbn; lia)) HFieldA HFreeA HFrameB)
    as [HFinalFieldA HFinalA].
  replace (rc+256+256) with (rc+512) in HSourceB by lia.
  exists ma, mb. split; [exact HCallA|]. split; [exact HCallB|].
  split; [exact HFinalFieldA|]. split; [exact HFieldB|].
  split; [exact HSourceB|]. split; [exact HFinalA|].
  split; [exact HFinalB|]. split; [exact HFinalL|].
  split; [exact HInvB|]. split; assumption.
Qed.
Print Assumptions eval_add_two_readers.
