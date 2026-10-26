(** Establish the original saver representation from actual coordinate loads,
    the infinity flag and two caller-owned allocations. No output bytes need
    initialization. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem
  C.jet_secp_fe_nv C.jet_secp_fe_b32 C.jet_secp_b32_exec C.jet_secp_local_regions
  C.jet_secp_field_add_initial C.jet_secp_multiply_input_input
  C.jet_secp_owned_slice_fields C.jet_secp_generator_save C.jet_secp_generator_save_storage
  C.jet_secp_generator_load_storage C.jet_secp_wrapper_storage.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma generator_save_field_region rho beta m r offset start :
  bas beta r=0 -> offset+40<=88 ->
  fe_at m (blk beta r) offset (field_values rho start) ->
  Mem.range_perm m (blk beta r) 0 88 Cur Freeable ->
  region_ok rho beta m r (mkreg (u64_cells offset (vars5 start)) true (Some 88)).
Proof.
  intros Base Fit (Ofs & Align & Max & Perm & Loads) Free.
  unfold region_ok;cbn [rcells rw rfree];rewrite Base.
  split;[lia|];split;[eapply Mem.perm_valid_block;apply (Free 0);lia|];
    split;[apply u64_cells_sorted;exact Ofs|];split.
  - apply Forall_forall;intros c Member.
    destruct (u64_cells_In _ _ _ Member) as (i & expr & Nth & ->).
    destruct (vars5_offset_nth start i expr Nth) as [Index ->].
    unfold cell_ok;cbn [cofs cchunk cval];rewrite Base,!Z.add_0_l.
    change (size_chunk Mint64) with 8;change (align_chunk Mint64) with 8.
    split;[lia|];split.
    + apply Z.divide_add_r;[exact Align|apply Z.divide_mul_l;exists 1;lia].
    + split;[intros pos Range;apply Perm;lia|].
      intros expr Same;injection Same as <-;split;[|reflexivity].
      apply Loads;unfold field_values.
      destruct i as [|[|[|[|[|i]]]]];try lia;cbn [nth_error];rewrite ?Nat.add_0_r;reflexivity.
  - split;[reflexivity|];split;[reflexivity|];split;[exact Free|].
    apply Forall_forall;intros c Member.
    destruct (u64_cells_In _ _ _ Member) as (i & expr & Nth & ->).
    destruct (vars5_offset_nth start i expr Nth) as [Index ->].
    cbn [cofs cchunk size_chunk];lia.
Qed.

Lemma generator_save_flag_region rho beta m r flag : bas beta r=0 ->
  Mem.range_perm m (blk beta r) 0 88 Cur Freeable ->
  Mem.load Mint32 m (blk beta r) 80=Some (Vint flag) ->
  region_ok rho beta m r (mkreg [mkcell 80 Mint32 (Some (XI flag))] true (Some 88)).
Proof.
  intros Base Free Load;unfold region_ok;cbn [rcells rw rfree];rewrite Base.
  split;[lia|];split;[eapply Mem.perm_valid_block;apply (Free 0);lia|];split;[reflexivity|];split.
  - constructor;[|constructor];unfold cell_ok;cbn [cofs cchunk cval size_chunk align_chunk];rewrite Base,!Z.add_0_l.
    split;[change Ptrofs.max_unsigned with 18446744073709551615;lia|];split;[exists 20;reflexivity|];split.
    + intros pos Range;eapply Mem.perm_implies;[apply Free;lia|constructor].
    + intros expr Same;injection Same as <-;split;[exact Load|reflexivity].
  - split;[reflexivity|];split;[reflexivity|];split;[exact Free|];repeat constructor;cbn;lia.
Qed.

Lemma generator_save_initial_from_fields rho flag m bp bg : bp<>bg ->
  fe_at m bp 0 (field_values rho 0) -> fe_at m bp 40 (field_values rho 5) ->
  Mem.load Mint32 m bp 80=Some (Vint flag) ->
  Mem.range_perm m bp 0 88 Cur Freeable -> Mem.range_perm m bg 0 64 Cur Freeable ->
  rep rho [(bp,0);(bg,0)] (generator_save_regs flag) m.
Proof.
  intros Sep X Y Flag FP FG.
  apply two_region_rep_separate;[reflexivity|exact Sep| |].
  - change (region_ok rho [(bp,0);(bg,0)] m 0
      (mkreg (u64_cells 0 (vars5 0)++(u64_cells 40 (vars5 5)++[mkcell 80 Mint32 (Some (XI flag))])) true (Some 88))).
    eapply owned_region_append.
    + apply generator_save_field_region;[reflexivity|lia|exact X|exact FP].
    + eapply owned_region_append.
      * apply generator_save_field_region;[reflexivity|lia|exact Y|exact FP].
      * apply generator_save_flag_region;[reflexivity|exact FP|exact Flag].
      * reflexivity.
    + reflexivity.
  - unfold region_ok;cbn [generator_save_buffer rcells rw rfree blk bas lay nth fst snd].
    split;[lia|];split;[eapply Mem.perm_valid_block;apply (FG 0);lia|];split;[reflexivity|];split.
    + apply Forall_map;apply Forall_forall;intros c Member.
      destruct (b32_byte_cells_in 64 0 0 c Member) as (i & Index & ->).
      apply writable_undefined_cell;cbn [cofs cchunk size_chunk align_chunk blk bas lay nth fst snd];
        rewrite !Z.add_0_l.
      * change Ptrofs.max_unsigned with 18446744073709551615;lia.
      * exists (Z.of_nat i);lia.
      * intros pos Range;eapply Mem.perm_implies;[apply FG;lia|constructor].
    + split;[reflexivity|];split;[reflexivity|];split;[exact FG|].
      apply Forall_map;apply Forall_forall;intros c Member.
      destruct (b32_byte_cells_in 64 0 0 c Member) as (i & Index & ->).
      cbn [cofs cchunk size_chunk];lia.
Qed.
