(* Both actual statements of read_scalar, with frame preservation derived. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_frame C.jet_secp_wrapper_run C.jet_secp_linkage C.jets_secp.
Require Import C.jet_output_layout C.jet_encoding C.jet_frame_bits.
Require Import C.jet_secp_fe_math C.jet_secp_input_bytes C.jet_secp_local_regions.
Require Import C.jet_secp_scalar_reader_run C.jet_secp_scalar_reader_set.
Require Import C.jet_secp_pure_oracle_frame.
Require Import C.jet_secp_scalar_reader_value C.jet_secp_scalar_overflow_numeric.
Require Import C.jet_secp_canonical_scalar.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma scalar_reader_first_shape bi edge :
  map rshape (sregs (scalar_reader_state bi edge)) =
  map rshape (sregs (scalar_reader_initial bi edge)).
Proof. reflexivity. Qed.

Section FRAME.
Variables (m0 : mem) (bd : block) (dbase : Z) (bw : block)
  (outedge cursor N : Z) (bi : block) (edge rc : Z) (ibits : list bool)
  (outs0 : list Simplicity.BitMachine.Cell) (cap : Z).
Hypothesis HOutput : write_frame_at m0 bd dbase bw outedge cursor N.
Hypothesis HInput : frame_input_cells_at m0 bi edge rc (map Some ibits).
Hypothesis HCursor : 0 <= rc.
Hypothesis HCursorMax : rc + Z.of_nat (length ibits) <= Int64.max_unsigned.
Hypothesis HLength : length ibits = 256%nat.
Local Definition rd_inv := invA m0 bd dbase bw outedge cursor N bi rc false outs0 cap.
Local Definition rd_ext := extA m0 bd bw bi.

Theorem exec_scalar_reader_body m layout e le :
  rep (read_fe_rho ibits rc) layout (sregs (scalar_reader_initial bi (Ptrofs.repr edge))) m ->
  tmatch (read_fe_rho ibits rc) layout scalar_reader_temps le ->
  ematch layout scalar_reader_venv e ->
  xsep rd_ext layout -> rd_inv (read_fe_rho ibits rc) [] m ->
  exists le' mf,
    Clight2.exec_stmt secp_ge e le m (fn_body f_read_scalar) E0 le' mf Out_normal /\
    rep (read_fe_rho ibits rc) layout (sregs (scalar_reader_set_state bi (Ptrofs.repr edge))) mf /\
    tmatch (read_fe_rho ibits rc) layout scalar_reader_temps le' /\
    rd_inv (read_fe_rho ibits rc) (scalar_reader_log bi (Ptrofs.repr edge)) mf /\
    lframe (frame rd_ext layout (sregs (scalar_reader_initial bi (Ptrofs.repr edge))) m) m mf.
Proof.
  intros HRep HTemps HEnv HSep HInv.
  destruct (exec_scalar_reader_first m0 bd dbase bw outedge cursor N bi edge rc ibits outs0 cap
    HOutput HInput HCursor HCursorMax HLength m layout e le HRep HTemps HEnv HSep HInv)
    as [le1 [m1 [HRead [HRep1 [HTemps1 [HInv1 HFrame1]]]]]].
  destruct (exec_scalar_reader_second (read_fe_rho ibits rc) layout bi (Ptrofs.repr edge)
    m1 e le1 HRep1 HTemps1 HEnv) as [mf [HSet [HFinal HFrame2]]].
  assert (HExternal : lframe (fun b _ => rd_ext b) m1 mf).
  { eapply pure_frame_external; [exact HRep1|exact HSep|].
    eapply lframe_implies; [exact HFrame2|].
    intros b ofs [HValid [HOutside _]] _; exact HOutside. }
  assert (HFinalInv : rd_inv (read_fe_rho ibits rc)
    (scalar_reader_log bi (Ptrofs.repr edge)) mf).
  { eapply invA_stable; [exact HOutput|exact HInv1|exact HExternal]. }
  exists le1, mf; split.
  - rewrite scalar_reader_body_exact.
    change E0 with (E0 ** E0).
    eapply exec_Sseq_1; [exact HRead|exact HSet].
  - split; [exact HFinal|]; split; [exact HTemps1|]; split; [exact HFinalInv|].
    eapply lframe_trans; [exact HFrame1|].
    eapply lframe_implies; [exact HFrame2|].
    intros b ofs [_ [HOutside _]] _.
    rewrite scalar_reader_first_shape; exact HOutside.
Qed.
Theorem exec_scalar_reader_body_numeric m layout e le :
  rep (read_fe_rho ibits rc) layout (sregs (scalar_reader_initial bi (Ptrofs.repr edge))) m ->
  tmatch (read_fe_rho ibits rc) layout scalar_reader_temps le ->
  ematch layout scalar_reader_venv e ->
  xsep rd_ext layout -> rd_inv (read_fe_rho ibits rc) [] m ->
  exists le' mf,
    Clight2.exec_stmt secp_ge e le m (fn_body f_read_scalar) E0 le' mf Out_normal /\
    (forall i, (i < 4)%nat ->
      Mem.load Mint64 mf (blk layout 0) (bas layout 0 + 8 * Z.of_nat i) =
        Some (Vlong (scalar_reader_limb (read_fe_rho ibits rc) (lay layout) i))) /\
    scalar_limb_value (scalar_reader_limb (read_fe_rho ibits rc) (lay layout)) =
      be_val (input_bytes 32 ibits) mod canonical_group_order /\
    rep (read_fe_rho ibits rc) layout (sregs (scalar_reader_set_state bi (Ptrofs.repr edge))) mf /\
    bas layout 2 = 0 /\ Mem.range_perm mf (blk layout 2) 0 32 Cur Freeable /\
    tmatch (read_fe_rho ibits rc) layout scalar_reader_temps le' /\
    rd_inv (read_fe_rho ibits rc) (scalar_reader_log bi (Ptrofs.repr edge)) mf /\
    lframe (frame rd_ext layout (sregs (scalar_reader_initial bi (Ptrofs.repr edge))) m) m mf.
Proof.
  intros HRep HTemps HEnv HSep HInv.
  destruct (exec_scalar_reader_body m layout e le HRep HTemps HEnv HSep HInv)
    as [le' [mf [HExec [HFinal [HTemp [HFinalInv HFrame]]]]]].
  destruct (rep_free_region (read_fe_rho ibits rc) layout
    (sregs (scalar_reader_set_state bi (Ptrofs.repr edge))) mf 2 32 HFinal)
    as [HBase HFree].
  - rewrite scalar_reader_set_regions; cbn [length]; lia.
  - rewrite scalar_reader_set_regions; reflexivity.
  - exists le', mf; split; [exact HExec|]; split.
    + apply scalar_reader_set_loads with (bi := bi) (edge := Ptrofs.repr edge); exact HFinal.
    + split; [apply scalar_reader_value_mod_group; exact HLength|].
      split; [exact HFinal|]; split; [exact HBase|]; split; [exact HFree|].
      split; [exact HTemp|]; split; assumption.
Qed.
End FRAME.
