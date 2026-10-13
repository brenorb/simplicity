(** Establish slice representation from field storage and ownership of the point. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep.
Require Import C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_write_fe_numeric.
Require Import C.jet_secp_write_fe_wide_values C.jet_secp_point_write_run.
Require Import C.jet_secp_point_write_exec C.jet_secp_write_fe_wide_exec.
Require Import C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_frame_inv C.jet_output_layout.
Require Import C.jet_sx_mem C.jet_sx_exec.
Require Simplicity.Translate.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma point_write_initial_rep k t0 t1 t2 t3 t4 rc m b :
  fe_at m b (point_coordinate_offset k) [t0;t1;t2;t3;t4] ->
  Mem.range_perm m b 0 128 Cur Freeable ->
  rep (wide_fe_rho t0 t1 t2 t3 t4 rc) [(b,0)] (point_write_initial_regs k) m.
Proof.
  intros (HB & HA & HM & HP & HL) HF.
  unfold point_write_initial_regs.
  apply (rep_add _ [] [] m b 0); [apply rep_nil|cbn;tauto|].
  apply region_with_freeable.
  - unfold region_ok. cbn [bas blk lay nth fst snd length app rcells rw rfree].
    split; [change (0 <= 0);lia|].
    split; [eapply Mem.perm_valid_block; apply (HF 0);lia|].
    split; [apply u64_cells_sorted;exact HB|]. split; [|exact I].
    apply Forall_forall. intros c HC.
    destruct (u64_cells_In _ _ _ HC) as (i & x & HN & ->).
    destruct (vars5_one_nth i x HN) as [HI ->].
    unfold cell_ok; cbn [bas blk lay nth fst snd cofs cchunk cval].
    change (size_chunk Mint64) with 8. change (align_chunk Mint64) with 8.
    rewrite !Z.add_0_l.
    assert (HIndex : 0 <= Z.of_nat i < 5) by (pose proof (Nat2Z.is_nonneg i);lia).
    split; [lia|]. split.
    + apply Z.divide_add_r; [exact HA|apply Z.divide_mul_l;exists 1;lia].
    + split.
      * intros ofs HOfs. apply HP;lia.
      * intros y HY. inversion HY; subst y. split; [|reflexivity].
        change (Mem.load Mint64 m b (point_coordinate_offset k + 8 * Z.of_nat i) =
          Some (Vlong (nth i [t0;t1;t2;t3;t4] Int64.zero))).
        apply HL. apply nth_error_nth'; exact HI.
  - reflexivity.
  - reflexivity.
  - exact HF.
  - exact (point_write_field_storage_size k).
Qed.
Print Assumptions point_write_initial_rep.

Theorem eval_point_write_from_owned_field m0 bd dbase bw edge cursor N bi rc
    t0 t1 t2 t3 t4 w0 outs0 k m b :
  write_frame_at m0 bd dbase bw edge cursor N ->
  Int64.unsigned t0 <= 2 ^ 60 -> Int64.unsigned t1 <= 2 ^ 60 ->
  Int64.unsigned t2 <= 2 ^ 60 -> Int64.unsigned t3 <= 2 ^ 60 -> Int64.unsigned t4 <= 2 ^ 60 ->
  fe_at m b (point_coordinate_offset k) [t0;t1;t2;t3;t4] ->
  Mem.range_perm m b 0 128 Cur Freeable ->
  xsep (extA m0 bd bw bi) [(b,0)] ->
  invA m0 bd dbase bw edge cursor N bi rc w0 outs0 256
    (wide_fe_rho t0 t1 t2 t3 t4 rc) [] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase); Vptr b (Ptrofs.repr (point_coordinate_offset k))] E0 mf Vundef /\
    finv m0 bd dbase bw edge cursor N bi mf true
      (outs0 ++ Simplicity.Translate.encode (wide_fe_output t0 t1 t2 t3 t4)) /\
    Mem.range_perm mf b 0 128 Cur Freeable /\
    lframe (frame (extA m0 bd bw bi) [(b,0)] (point_write_initial_regs k) m) m mf.
Proof.
  intros HO H0 H1 H2 H3 H4 HField HFree HS HI.
  eapply eval_point_wide_write_fe; try eassumption.
  apply point_write_initial_rep; assumption.
Qed.
Print Assumptions eval_point_write_from_owned_field.
