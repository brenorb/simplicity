(** The original three-address fe_mul with a readonly SWU constant as its
    first input. Reuse the checked multiplication log, arithmetic and actual
    u128 oracles; change only the proof's input ownership metadata. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Memory Values Events Maps.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem
  C.jet_sx_revalue_cells C.jet_borrowed_region C.jet_secp_multiply_borrowed_transport
  C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_swu_startup C.jet_secp_swu_candidates C.jet_secp_field_product_owned
  C.jet_secp_point_mul_run C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric
  C.jet_secp_u128_word_oracle C.jet_secp_field_mul_word_model C.jet_secp_owned_slice_fields
  C.jet_secp_b32_exec C.jet_secp_fe_b32 C.jet_secp_field_add_initial
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_field_mul_small C.jet_secp_curve_mul C.jet_secp_curve_frame
  C.jet_secp_local_regions C.jet_secp_field_point_multiply C.jet_secp_square_columns
  C.jet_clight_internal_preserve C.jet_clight_internal_frame C.jet_clight_readonly_frame
  C.jet_secp_closed_helpers C.jet_secp_scalar_io_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge swu_constant_block swu_constant_digits.

Definition swu_product_regs := borrow_at 1 field_product_regs.
Definition swu_product_state := borrow_state 1 field_product_state.
Definition swu_product_out_regs := borrow_at 1 field_product_out_regs.
Lemma swu_product_run_eq :
  xfun (genv_cenv secp_ge) [] point_mul_table 400 f_secp256k1_fe_mul
    field_product_args swu_product_regs [] 10=Some (RDone swu_product_state ONormal).
Proof. vm_compute;reflexivity. Qed.
Lemma swu_product_log_eq : slog swu_product_state=fe_mul_log.
Proof. reflexivity. Qed.
Lemma swu_product_out_eq : sregs swu_product_state=swu_product_out_regs.
Proof. reflexivity. Qed.
Lemma swu_product_return : (stemps swu_product_state)!1%positive=None.
Proof. reflexivity. Qed.
Local Opaque swu_product_state.
Lemma eval_swu_product_symbolic rho beta m : rep rho beta swu_product_regs m ->
  Forall (u128_evok rho) fe_mul_log -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));
     Vptr (blk beta 2) (Ptrofs.repr (bas beta 2))] E0 mf Vundef /\
  rep rho beta swu_product_out_regs mf /\
  lframe (fun b pos=>~foot beta (map rshape swu_product_regs) b pos) m mf.
Proof.
  intros HR HSol.
  destruct (xfun_top_sound secp_ge [] point_mul_table u128_evok u128_inv u128_ext
    ltac:(intros;exact I) ltac:(intros;contradiction) point_mul_table_ok
    400 f_secp256k1_fe_mul field_product_args swu_product_regs [] 10
    (RDone swu_product_state ONormal) swu_product_run_eq rho beta m HR)
    as (mf & result & HC & HP & HV & HS & _ & HL).
  - split;intros;discriminate.
  - intros r _ HE;exact HE.
  - exact I.
  - cbn [rsel fst];rewrite swu_product_log_eq;exact HSol.
  - cbn [rsel fst] in HP,HV;rewrite swu_product_return in HV;subst result.
    change (map (den rho (lay beta)) field_product_args) with
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+0));
       Vptr (blk beta 2) (Ptrofs.repr (bas beta 2+0))] in HC.
    rewrite !Z.add_0_r in HC;rewrite swu_product_out_eq in HP.
    exists mf;split;[exact HC|];split;[exact HP|].
    eapply lframe_implies;[exact HL|].
    intros b pos HOutside HValid;split;[exact HValid|];split;[exact HOutside|intros HE;exact HE].
Qed.

Lemma swu_product_initial d w m bo bw : bo<>bw -> swu_constant_state d m ->
  Mem.range_perm m bo 0 40 Cur Freeable -> fe_at m bw 0 (words5 w) ->
  Mem.range_perm m bw 0 40 Cur Freeable ->
  rep (point_mul_valuation (swu_constant_digits d) w)
    [(bo,0);(swu_constant_block d,0);(bw,0)] swu_product_regs m.
Proof.
  intros OB State FO W FW.
  assert (OG:bo<>swu_constant_block d)
    by (apply (swu_constant_separate d m bo State);apply (FO 0);lia).
  assert (WG:bw<>swu_constant_block d)
    by (apply (swu_constant_separate d m bw State);apply (FW 0);lia).
  set (rho:=point_mul_valuation (swu_constant_digits d) w).
  set (beta:=[(bo,0);(swu_constant_block d,0);(bw,0)]).
  assert (H0:region_ok rho beta m 0 (free_region fe_undef 40)).
  { apply region_with_freeable.
    - apply region_fe_undefined_from_storage;cbn [beta bas blk lay nth fst snd];
        [lia|exists 0;reflexivity|change (40<=18446744073709551615);lia|
         apply freeable_range_writable;exact FO].
    - reflexivity.
    - reflexivity.
    - exact FO.
    - apply fe_undef_storage_size. }
  assert (H1:region_ok rho beta m 1 (borrowed_region (fe_reg (vars5 0)))).
  { destruct State as [Read [Loads Bounds]];unfold borrowed_region;apply region_u64.
    - change (0<=0);lia.
    - exists 0;reflexivity.
    - change (40<=18446744073709551615);lia.
    - exact (swu_constant_valid d m (conj Read (conj Loads Bounds))).
    - exact Read.
    - intros i x Nth;destruct (vars5_zero_nth i x Nth) as [Index ->];split;[|reflexivity].
      change (Mem.load Mint64 m (swu_constant_block d) (8*Z.of_nat i)=Some (Vlong (rho i))).
      unfold rho;destruct i as [|[|[|[|[|i]]]]];try lia;apply Loads;lia. }
  assert (H2:region_ok rho beta m 2 (free_region (fe_reg (vars5 5)) 40)).
  { apply owned_field_values_slice_region;[reflexivity|lia|lia| |exact FW].
    unfold rho;rewrite point_mul_valuation_second;exact W. }
  split;[reflexivity|];split.
  - intros r1 r2 reg1 reg2 Ne E1 E2.
    assert (B1:(r1<3)%nat)
      by (change (r1<length swu_product_regs)%nat;apply nth_error_Some;congruence).
    assert (B2:(r2<3)%nat)
      by (change (r2<length swu_product_regs)%nat;apply nth_error_Some;congruence).
    destruct r1 as [|[|[|r1]]],r2 as [|[|[|r2]]];try lia;
      left;cbn [beta blk lay nth fst];congruence.
  - intros r reg At;destruct r as [|[|[|r]]];
      cbn [swu_product_regs borrow_at field_product_regs nth_error upd] in At;
      try (destruct r;discriminate At);inversion At;subst reg;assumption.
Qed.
Lemma swu_product_fields d w m bo bw :
  rep (point_mul_valuation (swu_constant_digits d) w)
    [(bo,0);(swu_constant_block d,0);(bw,0)] swu_product_out_regs m ->
  fe_at m bo 0 (words5 (point_mul_words (swu_constant_digits d) w)) /\
  fe_at m bw 0 (words5 w) /\ Mem.range_perm m bo 0 40 Cur Freeable /\
  Mem.range_perm m bw 0 40 Cur Freeable.
Proof.
  intro Rep;pose proof (rep_region _ _ _ m 0 _ Rep eq_refl) as H0.
  pose proof (rep_region _ _ _ m 2 _ Rep eq_refl) as H2.
  pose proof H0 as (_ & _ & _ & _ & _ & _ & FO & _).
  pose proof H2 as (_ & _ & _ & _ & _ & _ & FW & _);split.
  - eapply owned_region_field_slice with (exprs:=point_mul_out) (size:=40)
      (rho:=point_mul_valuation (swu_constant_digits d) w)
      (beta:=[(bo,0);(swu_constant_block d,0);(bw,0)]) (r:=0%nat);
      [exact H0|lia|exists 0;reflexivity|lia|change (40<=18446744073709551615);lia|
       reflexivity|reflexivity| |].
    + intros c At;exact At.
    + apply point_mul_output_den.
  - split.
    + eapply owned_region_field_slice with (exprs:=vars5 5) (size:=40)
        (rho:=point_mul_valuation (swu_constant_digits d) w)
        (beta:=[(bo,0);(swu_constant_block d,0);(bw,0)]) (r:=2%nat);
        [exact H2|lia|exists 0;reflexivity|lia|change (40<=18446744073709551615);lia|
         reflexivity|reflexivity| |].
      * intros c At;exact At.
      * reflexivity.
    + split;assumption.
Qed.
Lemma swu_constant_square_bounds d : square_input_bounds (swu_constant_digits d).
Proof.
  intros i Index;pose proof (swu_constant_limb_bounds d i Index);
    unfold square_input_bounds;destruct (Nat.eqb i 4);lia.
Qed.
Lemma swu_product_closed : closed_stmtb secp_closed_helpers (fn_body f_secp256k1_fe_mul)=true.
Proof. vm_compute;reflexivity. Qed.

Theorem eval_swu_constant_product d w m bo bw : bo<>bw -> swu_startup m ->
  square_input_bounds w -> Mem.range_perm m bo 0 40 Cur Freeable ->
  fe_at m bw 0 (words5 w) -> Mem.range_perm m bw 0 40 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr bo Ptrofs.zero;Vptr (swu_constant_block d) Ptrofs.zero;Vptr bw Ptrofs.zero] E0 mf Vundef /\
  fe_at mf bo 0 (words5 (point_mul_words (swu_constant_digits d) w)) /\
  fe_at mf bw 0 (words5 w) /\ Mem.range_perm mf bo 0 40 Cur Freeable /\
  Mem.range_perm mf bw 0 40 Cur Freeable /\ swu_startup mf /\
  radix_value (point_mul_words (swu_constant_digits d) w) mod feP=
    ((if d then swu_d_constant else swu_negc_constant)*radix_value w) mod feP /\
  mul_small_input_bounds (point_mul_words (swu_constant_digits d) w) /\
  lframe (fun b _=>b<>bo /\ b<>bw) m mf /\ readonly_preserved m mf.
Proof.
  intros OB Ready WB FO W FW.
  destruct (eval_swu_product_symbolic (point_mul_valuation (swu_constant_digits d) w)
    [(bo,0);(swu_constant_block d,0);(bw,0)] m
    (swu_product_initial d w m bo bw OB (proj1 Ready d) FO W FW)
    (fm_solves _ _ _ _ _ _ _ _ _ _)) as (mf & Call & Rep & Frame).
  destruct (swu_product_fields d w mf bo bw Rep) as (Out & Input & OutFree & InputFree).
  assert (Preserved:readonly_preserved m mf).
  { eapply secp_closed_function_preserved;[exact swu_product_closed|reflexivity|exact Call]. }
  pose proof (preserved_readonly_block_frame m mf (swu_constant_block d) Preserved
    (swu_constant_valid d m (proj1 Ready d))
    (readonly_bounds_not_writable _ _ _ _ (proj2 (proj2 (proj1 Ready d))))) as GlobalFrame.
  destruct (curve_mul_value_bounds (swu_constant_digits d) w
    (field_operand_from_bounds _ (swu_constant_square_bounds d)) (field_operand_from_bounds w WB))
    as [Value Bounds];rewrite swu_constant_radix in Value.
  exists mf;split;[exact Call|];split;[exact Out|];split;[exact Input|];
    split;[exact OutFree|];split;[exact InputFree|];split;
    [apply (swu_startup_preserved m mf Ready Preserved)|];
    split;[exact Value|];split;[exact Bounds|];split;[|exact Preserved].
  eapply lframe_add_block;[exact Frame|exact GlobalFrame|].
  intros b pos NG [NO NW] Foot.
  destruct Foot as (r & sh & ofs & chunk & At & Cell & E & Range).
  destruct r as [|[|[|r]]];[apply NO;exact E|apply NG;exact E|apply NW;exact E|
    destruct r;discriminate At].
Qed.
