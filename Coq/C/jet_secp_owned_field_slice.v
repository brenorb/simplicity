(** Shared field slice within a real enclosing owned allocation of any size. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Integers Values Memory.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_write_fe_wide_values.
Require Import C.jet_secp_write_fe_numeric C.jet_secp_point_write_run C.jet_secp_point_write_initial.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition owned_field_slice offset size : list region :=
  [free_region (mkreg (u64_cells offset (vars5 1)) true None) size].

Lemma owned_field_cells_fit offset size :
  offset+40 <= size ->
  Forall (fun c => cofs c+size_chunk (cchunk c) <= size) (u64_cells offset (vars5 1)).
Proof.
  intro HS; apply Forall_forall; intros c HC.
  destruct (u64_cells_In _ _ _ HC) as (i & x & HN & ->).
  destruct (vars5_one_nth i x HN) as [HI ->].
  cbn [cofs cchunk]; change (size_chunk Mint64) with 8; lia.
Qed.

Lemma owned_field_slice_initial_rep offset size t0 t1 t2 t3 t4 rc m b :
  offset+40 <= size ->
  fe_at m b offset [t0;t1;t2;t3;t4] ->
  Mem.range_perm m b 0 size Cur Freeable ->
  rep (wide_fe_rho t0 t1 t2 t3 t4 rc) [(b,0)] (owned_field_slice offset size) m.
Proof.
  intros HS (HB & HA & HM & HP & HL) HF.
  unfold owned_field_slice.
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
        change (Mem.load Mint64 m b (offset + 8 * Z.of_nat i) =
          Some (Vlong (nth i [t0;t1;t2;t3;t4] Int64.zero))).
        apply HL. apply nth_error_nth'; exact HI.
  - reflexivity.
  - reflexivity.
  - exact HF.
  - exact (owned_field_cells_fit offset size HS).
Qed.
Print Assumptions owned_field_slice_initial_rep.
