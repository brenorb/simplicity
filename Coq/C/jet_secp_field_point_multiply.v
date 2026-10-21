(** Original in-place field multiplication by a coordinate in an owned point.
    The argument order is the actual C call: private destination first, point
    coordinate second.  Reuse the selected multiplication log and word facts. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_local_regions.
Require Import C.jet_secp_u128_word_oracle C.jet_secp_field_mul_word_model C.jet_secp_point_mul_run.
Require Import C.jet_secp_fe_math C.jet_secp_field_add_initial C.jet_sx_revalue_cells.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_point_mul_storage.
Require Import C.jet_secp_multiply_input_input C.jet_secp_point_write_run C.jet_secp_curve_mul.
Require Import C.jet_secp_b32_exec.
Require Import C.jet_secp_point_mul_numeric C.jet_secp_square_columns.
Require Import C.jet_secp_field_mul_word_math C.jet_secp_multiply_finish_product.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition field_point_mul_regs k : list region :=
  [free_region (fe_reg (vars5 0)) 40;
   mkreg (u64_cells (point_coordinate_offset k) (vars5 5)) true (Some 128)].
Definition field_point_mul_args k := [XP 0 0; XP 0 0; XP 1 (point_coordinate_offset k)].
Definition field_point_mul_run k := xfun (genv_cenv secp_ge) [] point_mul_table 400
  f_secp256k1_fe_mul (field_point_mul_args k) (field_point_mul_regs k) [] 10.
Definition field_point_mul_tree := Eval vm_compute in fun k => match k with
  | PointX => field_point_mul_run PointX | PointY => field_point_mul_run PointY
  | PointZ => field_point_mul_run PointZ end.
Definition field_point_mul_state k := match field_point_mul_tree k with
  | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition field_point_mul_out_regs k : list region :=
  [mkreg (u64_cells 0 point_mul_out) true (Some 40);
   mkreg (u64_cells (point_coordinate_offset k) (vars5 5)) true (Some 128)].

Lemma field_point_mul_run_eq k :
  field_point_mul_run k = Some (RDone (field_point_mul_state k) ONormal).
Proof. destruct k; reflexivity. Qed.
Lemma field_point_mul_log_eq k : slog (field_point_mul_state k) = fe_mul_log.
Proof. destruct k; reflexivity. Qed.
Lemma field_point_mul_out_eq k : sregs (field_point_mul_state k) = field_point_mul_out_regs k.
Proof. destruct k; reflexivity. Qed.
Lemma field_point_mul_return k : (stemps (field_point_mul_state k))!1%positive = None.
Proof. destruct k; reflexivity. Qed.

Local Opaque field_point_mul_state.
Theorem eval_field_point_mul_symbolic k rho beta m :
  rep rho beta (field_point_mul_regs k) m -> Forall (u128_evok rho) fe_mul_log -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
     Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
     Vptr (blk beta 1) (Ptrofs.repr (bas beta 1 + point_coordinate_offset k))] E0 mf Vundef /\
  rep rho beta (field_point_mul_out_regs k) mf /\
  lframe (fun b ofs => ~ foot beta (map rshape (field_point_mul_regs k)) b ofs) m mf.
Proof.
  intros HR HSol.
  destruct (xfun_top_sound secp_ge [] point_mul_table u128_evok u128_inv u128_ext
    ltac:(intros; exact I) ltac:(intros; contradiction) point_mul_table_ok
    400 f_secp256k1_fe_mul (field_point_mul_args k) (field_point_mul_regs k) [] 10
    (RDone (field_point_mul_state k) ONormal) (field_point_mul_run_eq k) rho beta m HR)
    as (mf & vres & HC & HP & HV & HS & _ & HF).
  - split; intros; discriminate.
  - intros r _ HE; exact HE.
  - exact I.
  - cbn [rsel fst]; rewrite field_point_mul_log_eq; exact HSol.
  - cbn [rsel fst] in HP, HV, HS; rewrite field_point_mul_return in HV; subst vres.
    rewrite field_point_mul_out_eq in HP.
    change (map (den rho (lay beta)) (field_point_mul_args k)) with
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0 + 0));
       Vptr (blk beta 0) (Ptrofs.repr (bas beta 0 + 0));
       Vptr (blk beta 1) (Ptrofs.repr (bas beta 1 + point_coordinate_offset k))] in HC.
    rewrite !Z.add_0_r in HC.
    exists mf; split; [exact HC|]. split; [exact HP|].
    eapply lframe_implies; [exact HF|].
    intros b ofs HOutside HValid; split; [exact HValid|]. split; [exact HOutside|intros HE; exact HE].
Qed.

Lemma owned_field_values_slice_region rho beta m r start ofs size :
  bas beta r = 0 -> 0 < size -> ofs + 40 <= size ->
  fe_at m (blk beta r) ofs (field_values rho start) ->
  Mem.range_perm m (blk beta r) 0 size Cur Freeable ->
  region_ok rho beta m r (mkreg (u64_cells ofs (vars5 start)) true (Some size)).
Proof.
  intros HB HSize HFit (HOfs & HA & HM & HP & HL) HF.
  unfold region_ok; cbn [rcells rw rfree]; rewrite HB.
  split; [lia|]; split.
  - eapply Mem.perm_valid_block; apply (HF 0); lia.
  - split; [apply u64_cells_sorted; exact HOfs|]; split.
    + apply Forall_forall; intros c HC.
      destruct (u64_cells_In _ _ _ HC) as (i & x & HN & ->).
      destruct (vars5_offset_nth start i x HN) as [HI ->].
      unfold cell_ok; cbn [cofs cchunk cval]; rewrite HB, !Z.add_0_l.
      change (size_chunk Mint64) with 8; change (align_chunk Mint64) with 8.
      assert (HIndex : 0 <= Z.of_nat i < 5) by (pose proof (Nat2Z.is_nonneg i); lia).
      split; [lia|]; split.
      * apply Z.divide_add_r; [exact HA|apply Z.divide_mul_l; exists 1; lia].
      * split; [intros pos HPos; apply HP; lia|].
        intros y HY; inversion HY; subst y; split; [|reflexivity].
        apply HL; unfold field_values; destruct i as [|[|[|[|[|i]]]]]; try lia;
          cbn [nth_error]; rewrite ?Nat.add_0_r; reflexivity.
    + split; [reflexivity|]; split; [reflexivity|]; split; [exact HF|].
      apply Forall_forall; intros c HC.
      destruct (u64_cells_In _ _ _ HC) as (i & x & HN & ->).
      destruct (vars5_offset_nth start i x HN) as [HI ->].
      cbn [cofs cchunk]; change (size_chunk Mint64) with 8; lia.
Qed.

Lemma field_point_mul_initial k a b m bout bin :
  bout <> bin -> fe_at m bout 0 (words5 a) -> Mem.range_perm m bout 0 40 Cur Freeable ->
  fe_at m bin (point_coordinate_offset k) (words5 b) -> Mem.range_perm m bin 0 128 Cur Freeable ->
  rep (point_mul_valuation a b) [(bout,0);(bin,0)] (field_point_mul_regs k) m.
Proof.
  intros HNe HA HFA HB HFB.
  apply two_region_rep_separate; [reflexivity|exact HNe| |].
  - apply owned_field_slice_region; [reflexivity|lia|lia| |exact HFA].
    rewrite point_mul_valuation_first; exact HA.
  - apply owned_field_values_slice_region; [reflexivity|lia| | |exact HFB].
    + pose proof (point_coordinate_offset_bounds k); lia.
    + rewrite point_mul_valuation_second; exact HB.
Qed.

Lemma field_point_mul_fields k a b m mf bout bin :
  fe_at m bin (point_coordinate_offset k) (words5 b) ->
  rep (point_mul_valuation a b) [(bout,0);(bin,0)] (field_point_mul_out_regs k) mf ->
  fe_at mf bout 0 (words5 (point_mul_words a b)) /\
  Mem.range_perm mf bout 0 40 Cur Freeable /\
  fe_at mf bin (point_coordinate_offset k) (words5 b) /\
  Mem.range_perm mf bin 0 128 Cur Freeable.
Proof.
  intros (HO & HA & HM & HP & HL) HR.
  pose proof (rep_region _ _ _ mf 0 _ HR eq_refl) as H0.
  pose proof (rep_region _ _ _ mf 1 _ HR eq_refl) as H1.
  pose proof H0 as (_ & _ & _ & _ & _ & _ & HF0 & _).
  pose proof H1 as (_ & _ & _ & _ & _ & _ & HF1 & _).
  split.
  - pose proof (region_ok_revalue_u64 _ _ _ _ point_mul_out true (Some 40) H0 eq_refl) as HV.
    rewrite (revalue_u64_machine_map _ _ _ _ (point_mul_output_den a b [(bout,0);(bin,0)])) in HV.
    exact (u64_region_fe_at _ [(bout,0);(bin,0)] mf 0 (point_mul_words a b) (Some 40) HV).
  - split; [exact HF0|]. split; [|exact HF1].
    split; [exact HO|]; split; [exact HA|]; split; [exact HM|]; split.
    + apply freeable_range_writable; intros pos HPos; apply HF1.
      pose proof (point_coordinate_offset_bounds k); lia.
    + intros i x HN.
      assert (HI : (i<5)%nat).
      { assert (HH : (i < length (words5 b))%nat) by (apply nth_error_Some;rewrite HN;discriminate).
        exact HH. }
      assert (HX : nth_error (vars5 5) i = Some (XLv ((5+i)%nat))).
      { destruct i as [|[|[|[|[|i]]]]]; try lia; reflexivity. }
      pose proof (region_load _ _ mf 1 _ _ _ _ H1 (u64_cells_nth _ _ _ _ HX)) as HLoad.
      change (Mem.load Mint64 mf bin (point_coordinate_offset k+8*Z.of_nat i) =
        Some (den (point_mul_valuation a b) (lay [(bout,0);(bin,0)]) (XLv ((5+i)%nat)))) in HLoad.
      destruct i as [|[|[|[|[|i]]]]]; try lia;
        cbn [words5 nth_error] in HN; inversion HN; subst x; exact HLoad.
Qed.

Theorem eval_field_point_mul_from_storage k a b m bout bin :
  bout <> bin -> fe_at m bout 0 (words5 a) -> Mem.range_perm m bout 0 40 Cur Freeable ->
  fe_at m bin (point_coordinate_offset k) (words5 b) -> Mem.range_perm m bin 0 128 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr bout Ptrofs.zero; Vptr bout Ptrofs.zero; Vptr bin (Ptrofs.repr (point_coordinate_offset k))]
    E0 mf Vundef /\
  fe_at mf bout 0 (words5 (point_mul_words a b)) /\ Mem.range_perm mf bout 0 40 Cur Freeable /\
  fe_at mf bin (point_coordinate_offset k) (words5 b) /\ Mem.range_perm mf bin 0 128 Cur Freeable /\
  lframe (fun bx pos => ~ foot [(bout,0);(bin,0)] (map rshape (field_point_mul_regs k)) bx pos) m mf.
Proof.
  intros HNe HA HFA HB HFB.
  destruct (eval_field_point_mul_symbolic k (point_mul_valuation a b) [(bout,0);(bin,0)] m
    (field_point_mul_initial k a b m bout bin HNe HA HFA HB HFB) (fm_solves _ _ _ _ _ _ _ _ _ _))
    as (mf & HC & HP & HF).
  destruct (field_point_mul_fields k a b m mf bout bin HB HP) as (FO & FOF & FI & FIF).
  exists mf; split;[exact HC|]. split;[exact FO|]. split;[exact FOF|].
  split;[exact FI|]. split;assumption.
Qed.

Lemma field_point_mul_foot k bout bin bx pos :
  foot [(bout,0);(bin,0)] (map rshape (field_point_mul_regs k)) bx pos ->
  (bx=bout /\ 0<=pos<40) \/
  (bx=bin /\ point_coordinate_offset k<=pos<point_coordinate_offset k+40).
Proof.
  intros (r & sh & d & ch & HN & HC & HB & HO).
  destruct r as [|[|r]].
  - left;split;[exact HB|].
    cbn [field_point_mul_regs map nth_error rshape free_region fe_reg rcells rw rfree] in HN;
      injection HN as <-.
    cbn [fst map cshape cofs cchunk u64_cells vars5] in HC.
    destruct HC as [HC|[HC|[HC|[HC|[HC|HC]]]]]; try contradiction;
      inversion HC; subst d ch; cbn [bas lay nth snd] in HO;
      change (size_chunk Mint64) with 8 in HO; lia.
  - right;split;[exact HB|].
    cbn [field_point_mul_regs map nth_error rshape rcells rw rfree] in HN;
      injection HN as <-.
    cbn [fst map cshape cofs cchunk u64_cells vars5] in HC.
    destruct HC as [HC|[HC|[HC|[HC|[HC|HC]]]]]; try contradiction;
      inversion HC; subst d ch; cbn [bas lay nth snd] in HO;
      change (size_chunk Mint64) with 8 in HO; lia.
  - destruct r;discriminate HN.
Qed.

Theorem eval_field_point_mul_numeric k a b m bout bin :
  square_input_bounds a -> square_input_bounds b -> bout<>bin ->
  fe_at m bout 0 (words5 a) -> Mem.range_perm m bout 0 40 Cur Freeable ->
  fe_at m bin (point_coordinate_offset k) (words5 b) -> Mem.range_perm m bin 0 128 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr bout Ptrofs.zero; Vptr bout Ptrofs.zero; Vptr bin (Ptrofs.repr (point_coordinate_offset k))]
    E0 mf Vundef /\
  fe_at mf bout 0 (words5 (point_mul_words a b)) /\ Mem.range_perm mf bout 0 40 Cur Freeable /\
  fe_at mf bin (point_coordinate_offset k) (words5 b) /\ Mem.range_perm mf bin 0 128 Cur Freeable /\
  radix_value (point_mul_words a b) mod feP = (radix_value a * radix_value b) mod feP /\
  square_input_bounds (point_mul_words a b) /\
  (forall i, (i<5)%nat -> Int64.unsigned (point_mul_words a b i)<
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) /\
  lframe (fun bx pos => ~((bx=bout /\ 0<=pos<40) \/
    (bx=bin /\ point_coordinate_offset k<=pos<point_coordinate_offset k+40))) m mf.
Proof.
  intros BA BB HNe HA HFA HB HFB.
  destruct (eval_field_point_mul_from_storage k a b m bout bin HNe HA HFA HB HFB)
    as (mf & HC & FO & FOF & FI & FIF & HF).
  destruct (curve_mul_value_bounds a b (field_operand_from_bounds a BA)
    (field_operand_from_bounds b BB)) as [HV HBnd].
  exists mf;split;[exact HC|]. split;[exact FO|]. split;[exact FOF|].
  split;[exact FI|]. split;[exact FIF|]. split;[exact HV|].
  split;[exact (proj2 (point_mul_value_and_bounds a b BA BB))|]. split;[exact HBnd|].
  eapply lframe_implies;[exact HF|]. intros bx pos HOutside HValid HFoot.
  apply HOutside;exact (field_point_mul_foot k bout bin bx pos HFoot).
Qed.
