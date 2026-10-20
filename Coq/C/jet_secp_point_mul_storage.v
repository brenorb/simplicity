(** Original fe_mul from an actual field slice and a separate caller field.
    Event witnesses are constructed internally, never assumed by this caller. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_rep C.jet_sx_revalue_cells.
Require Import C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp C.jet_secp_local_regions C.jet_secp_b32_exec.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_field_add_initial.
Require Import C.jet_secp_point_write_run C.jet_secp_point_mul_run.
Require Import C.jet_secp_field_mul_word_math C.jet_secp_field_mul_word_model.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition point_mul_valuation (a b : nat -> int64) :=
  fm_rho (a 0%nat) (a 1%nat) (a 2%nat) (a 3%nat) (a 4%nat)
    (b 0%nat) (b 1%nat) (b 2%nat) (b 3%nat) (b 4%nat).
Definition point_mul_words (a b : nat -> int64) (i : nat) := nth i
  [fm_t0 (a 0%nat) (a 1%nat) (a 2%nat) (a 3%nat) (a 4%nat)
     (b 0%nat) (b 1%nat) (b 2%nat) (b 3%nat) (b 4%nat);
   fm_t1 (a 0%nat) (a 1%nat) (a 2%nat) (a 3%nat) (a 4%nat)
     (b 0%nat) (b 1%nat) (b 2%nat) (b 3%nat) (b 4%nat);
   fm_t2 (a 0%nat) (a 1%nat) (a 2%nat) (a 3%nat) (a 4%nat)
     (b 0%nat) (b 1%nat) (b 2%nat) (b 3%nat) (b 4%nat);
   fm_t3 (a 0%nat) (a 1%nat) (a 2%nat) (a 3%nat) (a 4%nat)
     (b 0%nat) (b 1%nat) (b 2%nat) (b 3%nat) (b 4%nat);
   fm_t4 (a 0%nat) (a 1%nat) (a 2%nat) (a 3%nat) (a 4%nat)
     (b 0%nat) (b 1%nat) (b 2%nat) (b 3%nat) (b 4%nat)] Int64.zero.

Lemma point_mul_valuation_first a b : words5 (point_mul_valuation a b) = words5 a.
Proof. reflexivity. Qed.
Lemma point_mul_valuation_second a b : field_values (point_mul_valuation a b) 5 = words5 b.
Proof. reflexivity. Qed.
Lemma point_mul_output_den a b beta :
  map (den (point_mul_valuation a b) (lay beta)) point_mul_out = map Vlong (words5 (point_mul_words a b)).
Proof. reflexivity. Qed.

Lemma owned_field_slice_region rho beta m r ofs size :
  bas beta r = 0 -> 0 < size -> ofs + 40 <= size ->
  fe_at m (blk beta r) ofs (words5 rho) -> Mem.range_perm m (blk beta r) 0 size Cur Freeable ->
  region_ok rho beta m r (mkreg (u64_cells ofs (vars5 0)) true (Some size)).
Proof.
  intros HB HSize HFit (HOfs & HA & HM & HP & HL) HF.
  unfold region_ok; cbn [rcells rw rfree]; rewrite HB.
  split; [lia|]; split.
  - eapply Mem.perm_valid_block; apply (HF 0); lia.
  - split; [apply u64_cells_sorted; exact HOfs|]; split.
    + apply Forall_forall; intros c HC.
      destruct (u64_cells_In _ _ _ HC) as (i & x & HN & ->).
      destruct (vars5_zero_nth i x HN) as [HI ->].
      unfold cell_ok; cbn [cofs cchunk cval]; rewrite HB, !Z.add_0_l.
      change (size_chunk Mint64) with 8; change (align_chunk Mint64) with 8.
      assert (HIndex : 0 <= Z.of_nat i < 5) by (pose proof (Nat2Z.is_nonneg i); lia).
      split; [lia|]; split.
      * apply Z.divide_add_r; [exact HA|apply Z.divide_mul_l; exists 1; lia].
      * split; [intros pos HPos; apply HP; lia|].
        intros y HY; inversion HY; subst y; split; [|reflexivity].
        apply HL; unfold words5; destruct i as [|[|[|[|[|i]]]]]; try lia; reflexivity.
    + split; [reflexivity|]; split; [reflexivity|]; split; [exact HF|].
      apply Forall_forall; intros c HC.
      destruct (u64_cells_In _ _ _ HC) as (i & x & HN & ->).
      destruct (vars5_zero_nth i x HN) as [HI ->].
      cbn [cofs cchunk]; change (size_chunk Mint64) with 8; lia.
Qed.

Lemma point_mul_initial_from_storage k a b m bp bs :
  bp <> bs -> fe_at m bp (point_coordinate_offset k) (words5 a) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> fe_at m bs 0 (words5 b) ->
  Mem.range_perm m bs 0 40 Cur Freeable ->
  rep (point_mul_valuation a b) [(bp,0);(bs,0)] (point_mul_regs k) m.
Proof.
  intros HNe HA HFA HB HFB.
  apply two_region_rep_separate; [reflexivity|exact HNe| |].
  - apply owned_field_slice_region; [reflexivity|lia|pose proof (point_coordinate_offset_bounds k); lia| |exact HFA].
    rewrite point_mul_valuation_first; exact HA.
  - apply region_with_freeable.
    + apply field_region_from_values; rewrite point_mul_valuation_second; exact HB.
    + reflexivity.
    + reflexivity.
    + exact HFB.
    + apply field_region_storage_size.
Qed.

Local Opaque secp_ge point_mul_valuation point_mul_words.
Lemma point_mul_result_fields k a b m mf bp bs :
  fe_at m bp (point_coordinate_offset k) (words5 a) ->
  rep (point_mul_valuation a b) [(bp,0);(bs,0)] (point_mul_out_regs k) mf ->
  fe_at mf bp (point_coordinate_offset k) (words5 (point_mul_words a b)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\
  fe_at mf bs 0 (words5 b) /\ Mem.range_perm mf bs 0 40 Cur Freeable.
Proof.
  intros (HOfs & HA & HM & HP & HL) HR.
  pose proof (rep_region _ _ _ mf 0 _ HR eq_refl) as H0.
  pose proof (rep_region _ _ _ mf 1 _ HR eq_refl) as H1.
  pose proof H0 as (_ & _ & _ & _ & _ & _ & HFP & _).
  pose proof H1 as (_ & _ & _ & _ & _ & _ & HFS & _).
  assert (HS : fe_at mf bs 0 (words5 b)).
  { pose proof (region_ok_revalue_u64 _ _ _ _ (vars5 5) true (Some 40) H1 eq_refl) as HV.
    assert (HD : map (den (point_mul_valuation a b) (lay [(bp,0);(bs,0)])) (vars5 5) =
      map Vlong (words5 b)).
    { Local Transparent point_mul_valuation. reflexivity. }
    rewrite (revalue_u64_machine_map _ _ _ _ HD) in HV.
    exact (u64_region_fe_at _ _ _ _ _ _ HV). }
  split; [|split; [exact HFP|split; assumption]].
  split; [exact HOfs|]; split; [exact HA|]; split; [exact HM|]; split.
  - apply freeable_range_writable; intros pos HPos; apply HFP.
    pose proof (point_coordinate_offset_bounds k); lia.
  - intros i x HN.
    assert (HI : (i < length (words5 (point_mul_words a b)))%nat).
    { apply nth_error_Some; rewrite HN; discriminate. }
    change (i < 5)%nat in HI.
    assert (HX : nth_error point_mul_out i = Some (nth i point_mul_out (XLv 0))).
    { apply nth_error_nth'; change (i < 5)%nat; exact HI. }
    pose proof (region_load _ _ mf 0 _ _ _ _ H0 (u64_cells_nth _ _ _ _ HX)) as HLoad.
    pose proof (f_equal (fun xs => nth_error xs i) (point_mul_output_den a b [(bp,0);(bs,0)])) as HD.
    cbv beta in HD.
    rewrite !nth_error_map, HX, HN in HD; injection HD as HD.
    change (den (point_mul_valuation a b) (lay [(bp,0);(bs,0)])
      (nth i point_mul_out (XLv 0)) = Vlong x) in HD.
    rewrite HD in HLoad; exact HLoad.
Qed.

Theorem eval_point_mul_from_storage k a b m bp bs :
  bp <> bs -> fe_at m bp (point_coordinate_offset k) (words5 a) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> fe_at m bs 0 (words5 b) ->
  Mem.range_perm m bs 0 40 Cur Freeable ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
      [Vptr bp (Ptrofs.repr (point_coordinate_offset k));
       Vptr bp (Ptrofs.repr (point_coordinate_offset k));Vptr bs Ptrofs.zero] E0 mf Vundef /\
    fe_at mf bp (point_coordinate_offset k) (words5 (point_mul_words a b)) /\
    Mem.range_perm mf bp 0 128 Cur Freeable /\ fe_at mf bs 0 (words5 b) /\
    Mem.range_perm mf bs 0 40 Cur Freeable /\
    lframe (fun bx pos => ~ foot [(bp,0);(bs,0)] (map rshape (point_mul_regs k)) bx pos) m mf.
Proof.
  intros HNe HA HFA HB HFB.
  pose proof (point_mul_initial_from_storage k a b m bp bs HNe HA HFA HB HFB) as HR.
  assert (HSol : Forall (C.jet_secp_u128_word_oracle.u128_evok (point_mul_valuation a b)) fe_mul_log).
  { Local Transparent point_mul_valuation. apply fm_solves. }
  destruct (eval_point_mul_symbolic k (point_mul_valuation a b) [(bp,0);(bs,0)] m HR HSol)
    as (mf & HC & HP & HF).
  destruct (point_mul_result_fields k a b m mf bp bs HA HP) as (HField & HFreeP & HScalar & HFreeS).
  exists mf; split; [exact HC|]; split; [exact HField|]; split; [exact HFreeP|].
  split; [exact HScalar|]; split; assumption.
Qed.
