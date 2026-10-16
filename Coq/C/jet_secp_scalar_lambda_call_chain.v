(** Original read / borrowed-global multiplication / write, retaining the literal lambda term. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_exec C.jet_sx_mem
  C.jet_secp_linkage C.jets_secp C.jet_secp_frame C.jet_secp_wrapper_run
  C.jet_frame_layout C.jet_frame_inv C.jet_input_layout C.jet_output_layout C.jet_encoding
  C.jet_secp_local_regions C.jet_secp_public_body C.jet_secp_scalar_public_rest
  C.jet_secp_scalar_public_entry C.jet_secp_scalar_reader_run
  C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_writer_run
  C.jet_secp_scalar_writer_exec C.jet_secp_scalar_read_write
  C.jet_secp_scalar_add_reader_support C.jet_secp_scalar_writer_word.
Require Import C.jet_secp_scalar_lambda_global C.jet_secp_canonical_scalar_lambda
  C.jet_secp_scalar_lambda_readonly C.jet_secp_scalar_lambda_read_state
  C.jet_clight_readonly_frame.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge canonical_scalar_multiply_lambda encode.

Theorem eval_scalar_read_lambda_write_canonical m0 bd dbase bw outedge cursor N bi edge rc
    (value : Ty.tySem (Word 8)) m ba bl :
  write_frame_at m0 bd dbase bw outedge cursor N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits value)) ->
  0 <= rc -> rc + 256 <= Int64.max_unsigned ->
  Mem.range_perm m ba 0 32 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
  frame_fields_at m bl 0 bi edge rc -> ba <> bl ->
  xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  invA m0 bd dbase bw outedge cursor N bi rc false [] 256
    (read_fe_rho (frame_input_word_bits value) rc) [] m ->
  scalar_lambda_global_rep m0 -> scalar_lambda_global_rep m ->
  readonly_region_bounds m scalar_lambda_block 0 32 ->
  scalar_lambda_block <> ba -> scalar_lambda_block <> bl ->
  exists mr mn mf,
    Clight2.eval_funcall secp_ge m (Internal f_read_scalar)
      [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef /\
    Clight2.eval_funcall secp_ge mr (Internal f_secp256k1_scalar_mul)
      [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr scalar_lambda_block Ptrofs.zero] E0 mn Vundef /\
    Clight2.eval_funcall secp_ge mn (Internal f_write_scalar)
      [Vptr bd (Ptrofs.repr dbase);Vptr ba Ptrofs.zero] E0 mf Vundef /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (encode (@canonical_scalar_multiply_lambda Alg.CoreFunSem value)) /\
    Mem.range_perm mf ba 0 32 Cur Freeable /\
    frame_fields_at mf bl 0 bi edge (rc+256) /\
    Mem.range_perm mf bl 0 16 Cur Freeable /\
    lframe (secp_locals_outside m0 bd bw bi ba bl) m mf.
Proof.
  intros HO HI Hrc HM HA HL HS HSeparate HSep HInv HG0 HG HB HGlobalNotA HGlobalNotL.
  destruct (eval_read_scalar_canonical_with_source m0 bd dbase bw outedge cursor N 256 bi edge rc
    value m ba bl HO HI Hrc HM HA HL HS HSeparate HSep HInv)
    as (mr & HRead & HScalar & HCursorR & HFreeAR & HFreeLR & HInvR & HReadFrame).
  assert (HCurrentR : finv m0 bd dbase bw outedge cursor N bi mr false []).
  { destruct HInvR as (_ & HCurrent & _); exact HCurrent. }
  destruct (scalar_lambda_global_after_reader m0 bd dbase bw outedge cursor N bi edge
    m mr ba bl HG0 HG HB HGlobalNotA HGlobalNotL HRead HCurrentR HReadFrame) as (HGR & HBR).
  destruct (eval_scalar_lambda_tight_frame mr ba value HScalar HFreeAR
    ltac:(intro HE; apply HGlobalNotA; symmetry; exact HE) HGR HBR)
    as (mn & HSquare & HWriterRep & HFreeAN & HGN & HBN & HSquareFrame).
  assert (HSquareExt : lframe (fun b _ => extA m0 bd bw bi b) mr mn).
  { eapply lframe_implies; [exact HSquareFrame|].
    intros b pos HExt HV HFoot; pose proof (scalar_writer_foot_block ba b pos HFoot) as HEq; subst b.
    exact ((HSep 0%nat ltac:(cbn; lia)) HExt). }
  assert (HInvN : invA m0 bd dbase bw outedge cursor N bi rc false [] 256
      (read_fe_rho (frame_input_word_bits value) rc)
      (scalar_reader_log bi (Ptrofs.repr edge)) mn).
  { eapply invA_stable; [exact HO|exact HInvR|exact HSquareExt]. }
  assert (HValidLR : Mem.valid_block mr bl) by (eapply load_valid; exact (proj1 HCursorR)).
  assert (HOutsideL : forall pos,
      ~ foot [(ba,0)] (map rshape scalar_writer_initial_regs) bl pos).
  { intros pos HFoot; apply HSeparate; symmetry; exact (scalar_writer_foot_block ba bl pos HFoot). }
  assert (HCursorN : frame_fields_at mn bl 0 bi edge (rc+256)).
  { destruct HCursorR as [HE HC]; split;
      rewrite (proj1 HSquareFrame) by (auto; intros; apply HOutsideL); assumption. }
  assert (HFreeLN : Mem.range_perm mn bl 0 16 Cur Freeable).
  { intros pos HPos; eapply (proj1 (proj2 HSquareFrame));
      [exact HValidLR|apply HOutsideL|apply HFreeLR; exact HPos]. }
  assert (HValidLN : Mem.valid_block mn bl).
  { exact ((proj2 (proj2 HSquareFrame)) bl HValidLR). }
  set (wrho := scalar_limb_rho (@toZ (WordToZ 8) (@canonical_scalar_multiply_lambda Alg.CoreFunSem value))).
  assert (HWriteSep : xsep (extA m0 bd bw bi) [(ba,0)]).
  { intros r Hr; destruct r as [|r]; [apply (HSep 0%nat); cbn; lia|cbn in Hr; lia]. }
  assert (HWriteInv : jet_secp_scalar_writer_exec.scalar_write_inv
      m0 bd dbase bw outedge cursor N bi (Int64.unsigned (wrho 0%nat)) false [] wrho [] mn).
  { destruct HInvN as [_ [HCurrent [HCap _]]].
    change (finv m0 bd dbase bw outedge cursor N bi mn false []) in HCurrent.
    unfold jet_secp_scalar_writer_exec.scalar_write_inv, invA.
    split; [symmetry; apply Int64.repr_unsigned|].
    split; [exact HCurrent|]; split; [exact HCap|cbn; lia]. }
  destruct (eval_write_scalar_word m0 bd dbase bw outedge cursor N bi (Int64.unsigned (wrho 0%nat))
    (@canonical_scalar_multiply_lambda Alg.CoreFunSem value) false [] mn [(ba,0)] HO HWriterRep HWriteSep HWriteInv)
    as (mf & HWrite & HWrittenRep & HWritten & HWriteFrame).
  assert (HFreeA : Mem.range_perm mf ba 0 32 Cur Freeable).
  { destruct (rep_free_region _ _ _ _ 0 32 HWrittenRep ltac:(change (0 < 1)%nat; lia) eq_refl)
      as [_ HFree]; exact HFree. }
  assert (HFrameL : forall pos, frame (extA m0 bd bw bi) [(ba,0)] scalar_writer_initial_regs mn bl pos).
  { intro pos; split; [exact HValidLN|]; split.
    - exact (HOutsideL pos).
    - exact (HSep 1%nat ltac:(cbn; lia)). }
  assert (HCursorF : frame_fields_at mf bl 0 bi edge (rc+256)).
  { destruct HCursorN as [HE HC]; split;
      rewrite (proj1 HWriteFrame) by (auto; intros; apply HFrameL); assumption. }
  assert (HFreeLF : Mem.range_perm mf bl 0 16 Cur Freeable).
  { intros pos HPos; eapply (proj1 (proj2 HWriteFrame));
      [exact HValidLN|apply HFrameL|apply HFreeLN; exact HPos]. }
  exists mr,mn,mf; split; [exact HRead|]; split; [exact HSquare|]; split; [exact HWrite|];
    split; [exact HWritten|]; split; [exact HFreeA|]; split; [exact HCursorF|]; split; [exact HFreeLF|].
  eapply lframe_trans.
  - eapply lframe_implies; [exact HReadFrame|].
    intros b pos [HNotA [HNotL HNotExt]] HV.
    split; [exact HV|]; split; [eapply scalar_locals_not_foot; eassumption|exact HNotExt].
  - eapply lframe_trans.
    + eapply lframe_implies; [exact HSquareFrame|].
      intros b pos [HNotA [HNotL HNotExt]] HV HFoot.
      apply HNotA; exact (scalar_writer_foot_block ba b pos HFoot).
    + eapply lframe_implies; [exact HWriteFrame|].
      intros b pos [HNotA [HNotL HNotExt]] HV.
      split; [exact HV|]; split; [|exact HNotExt].
      intro HFoot; apply HNotA; exact (scalar_writer_foot_block ba b pos HFoot).
Qed.
