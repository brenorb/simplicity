(** Actual in-place fe_add with an initialized readonly SWU constant.
    Reuse the original addition state and shared sum lemmas. Only the second
    region's ownership metadata changes; no writable-global premise is used. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Memory Values Events Maps.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure
  C.jet_sx_mem C.jet_sx_rep C.jet_sx_revalue_cells C.jet_borrowed_region
  C.jet_secp_multiply_borrowed_transport C.jet_secp_linkage C.jets_secp
  C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_swu_startup C.jet_secp_swu_candidates
  C.jet_secp_field_add C.jet_secp_field_add_initial C.jet_secp_field_add_values
  C.jet_secp_field_add_scaled C.jet_secp_field_sum_bounds C.jet_secp_curve_tail_values
  C.jet_secp_field_mul_small C.jet_secp_owned_slice_fields C.jet_secp_field_point_multiply
  C.jet_secp_multiply_input_input C.jet_secp_multiply_normalize_bridge
  C.jet_secp_multiply_finish_product C.jet_secp_curve_frame C.jet_secp_local_regions
  C.jet_clight_internal_preserve C.jet_clight_internal_frame C.jet_clight_readonly_frame
  C.jet_secp_closed_helpers C.jet_secp_scalar_io_preserve C.jet_secp_fns C.jet_secp_square_columns.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge swu_constant_block swu_constant_digits.

Definition swu_add_regs := borrow_at 1 field_add_initial_regs.
Definition swu_add_state := borrow_state 1 field_add_state.
Definition swu_add_out := map add_limb_expr [0;1;2;3;4]%nat.
Definition swu_add_out_regs :=
  [mkreg (u64_cells 0 swu_add_out) true (Some 40);borrowed_region (fe_reg (vars5 6))].
Lemma swu_add_run_eq :
  xfun (genv_cenv secp_ge) [] (int_table secp_pure) 96 f_secp256k1_fe_add
    field_add_args swu_add_regs [] 11=Some (RDone swu_add_state ONormal).
Proof. vm_compute;reflexivity. Qed.
Lemma swu_add_output_shape : sregs swu_add_state=swu_add_out_regs.
Proof. reflexivity. Qed.
Lemma swu_add_return : (stemps swu_add_state)!1%positive=None.
Proof. reflexivity. Qed.
Lemma swu_add_output_den w c beta :
  map (den (curve_equal_rho w c) (lay beta)) swu_add_out=map Vlong (words5 (field_sum_words w c)).
Proof. reflexivity. Qed.
Local Lemma swu_add_rho_right w c i :
  (i<5)%nat -> curve_equal_rho w c (6+i)%nat=c i.
Proof. intro Index;destruct i as [|[|[|[|[|i]]]]];try lia;reflexivity. Qed.

Lemma swu_add_initial d w m bw : swu_constant_state d m -> fe_at m bw 0 (words5 w) ->
  Mem.range_perm m bw 0 40 Cur Freeable ->
  rep (curve_equal_rho w (swu_constant_digits d)) [(bw,0);(swu_constant_block d,0)] swu_add_regs m.
Proof.
  intros State Input Free.
  assert (Separate:bw<>swu_constant_block d) by
    (apply (swu_constant_separate d m bw State);apply (Free 0);lia).
  set (rho:=curve_equal_rho w (swu_constant_digits d)).
  set (beta:=[(bw,0);(swu_constant_block d,0)]).
  assert (H0:region_ok rho beta m 0 (free_region (fe_reg (vars5 1)) 40)).
  { apply owned_field_values_slice_region;[reflexivity|lia|lia| |exact Free].
    unfold rho;rewrite curve_equal_first;exact Input. }
  assert (H1:region_ok rho beta m 1 (borrowed_region (fe_reg (vars5 6)))).
  { destruct State as [Read [Loads Bounds]];unfold borrowed_region;apply region_u64.
    - change (0<=0);lia.
    - exists 0;reflexivity.
    - change (40<=18446744073709551615);lia.
    - exact (swu_constant_valid d m (conj Read (conj Loads Bounds))).
    - exact Read.
    - intros i x Nth;destruct (vars5_offset_nth 6 i x Nth) as [Index ->];split;[|reflexivity].
      change (Mem.load Mint64 m (swu_constant_block d) (8*Z.of_nat i)=Some (Vlong (rho (6+i)%nat))).
      unfold rho;rewrite swu_add_rho_right by exact Index;apply Loads;exact Index. }
  split;[reflexivity|];split.
  - intros r1 r2 reg1 reg2 Ne E1 E2.
    assert (B1:(r1<2)%nat) by
      (change (r1<length swu_add_regs)%nat;apply nth_error_Some;congruence).
    assert (B2:(r2<2)%nat) by
      (change (r2<length swu_add_regs)%nat;apply nth_error_Some;congruence).
    destruct r1 as [|[|r1]],r2 as [|[|r2]];try lia;left;cbn [beta blk lay nth fst];congruence.
  - intros r reg At;destruct r as [|[|r]];
      cbn [swu_add_regs borrow_at field_add_initial_regs nth_error upd] in At;
      try (destruct r;discriminate At);inversion At;subst reg;assumption.
Qed.
Local Opaque swu_add_state.
Lemma eval_swu_add_symbolic rho beta m : rep rho beta swu_add_regs m -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add)
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))]
    E0 mf Vundef /\ rep rho beta swu_add_out_regs mf /\
  lframe (fun b pos=>~foot beta (map rshape swu_add_regs) b pos) m mf.
Proof.
  intro HR;destruct (xfun_pure secp_ge secp_pure secp_pure_ok 96 f_secp256k1_fe_add
    field_add_args swu_add_regs 11 _ swu_add_run_eq eq_refl rho beta m HR)
    as (mf & result & Call & Rep & Ret & Shape & Frame).
  cbn [rsel fst] in Rep,Ret;rewrite swu_add_return in Ret;subst result.
  change (map (den rho (lay beta)) field_add_args) with
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+0))] in Call.
  rewrite !Z.add_0_r in Call;rewrite swu_add_output_shape in Rep.
  exists mf;split;[exact Call|];split;assumption.
Qed.
Lemma swu_add_result d w m bw :
  rep (curve_equal_rho w (swu_constant_digits d)) [(bw,0);(swu_constant_block d,0)] swu_add_out_regs m ->
  fe_at m bw 0 (words5 (field_sum_words w (swu_constant_digits d))) /\
  Mem.range_perm m bw 0 40 Cur Freeable.
Proof.
  intro Rep;pose proof (rep_region _ _ _ m 0 _ Rep eq_refl) as H0.
  pose proof H0 as (_ & _ & _ & _ & _ & _ & Free & _);split;[|exact Free].
  eapply owned_region_field_slice with (exprs:=swu_add_out) (size:=40)
    (rho:=curve_equal_rho w (swu_constant_digits d)) (beta:=[(bw,0);(swu_constant_block d,0)]) (r:=0%nat);
    [exact H0|lia|exists 0;reflexivity|lia|change (40<=18446744073709551615);lia|
     reflexivity|reflexivity| |].
  - intros c Member;exact Member.
  - apply swu_add_output_den.
Qed.
Lemma swu_add_closed : closed_stmtb secp_closed_helpers (fn_body f_secp256k1_fe_add)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma swu_constant_tight d : mul_small_input_bounds (swu_constant_digits d).
Proof.
  intros i Index;pose proof (swu_constant_limb_bounds d i Index);destruct (Nat.eqb i 4);lia.
Qed.

Theorem eval_swu_constant_add d w m bw : swu_startup m -> mul_small_input_bounds w ->
  fe_at m bw 0 (words5 w) -> Mem.range_perm m bw 0 40 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add)
    [Vptr bw Ptrofs.zero;Vptr (swu_constant_block d) Ptrofs.zero] E0 mf Vundef /\
  fe_at mf bw 0 (words5 (field_sum_words w (swu_constant_digits d))) /\
  Mem.range_perm mf bw 0 40 Cur Freeable /\
  radix_value (field_sum_words w (swu_constant_digits d))=
    radix_value w+(if d then swu_d_constant else swu_negc_constant) /\
  field_scaled_bounds 2 (field_sum_words w (swu_constant_digits d)) /\
  square_input_bounds (field_sum_words w (swu_constant_digits d)) /\ swu_startup mf /\
  lframe (fun b _=>b<>bw) m mf /\ readonly_preserved m mf.
Proof.
  intros Ready Bounds Input Free.
  destruct (eval_swu_add_symbolic (curve_equal_rho w (swu_constant_digits d))
    [(bw,0);(swu_constant_block d,0)] m (swu_add_initial d w m bw (proj1 Ready d) Input Free))
    as (mf & Call & Rep & Frame).
  destruct (swu_add_result d w mf bw Rep) as [Out Owned].
  assert (Preserved:readonly_preserved m mf) by
    (eapply secp_closed_function_preserved;[exact swu_add_closed|reflexivity|exact Call]).
  pose proof (preserved_readonly_block_frame m mf (swu_constant_block d) Preserved
    (swu_constant_valid d m (proj1 Ready d))
    (readonly_bounds_not_writable _ _ _ _ (proj2 (proj2 (proj1 Ready d))))) as GlobalFrame.
  pose proof (field_tight_scaled w Bounds) as WBound.
  pose proof (field_tight_scaled _ (swu_constant_tight d)) as CBound.
  pose proof (field_sum_scaled_bounds 1 1 w (swu_constant_digits d)
    ltac:(lia) ltac:(lia) ltac:(lia) WBound CBound) as SumBound.
  pose proof (field_sum_exact_value w (swu_constant_digits d)
    (field_sum_scaled_no_overflow 1 1 _ _ ltac:(lia) ltac:(lia) ltac:(lia) WBound CBound)) as Value.
  rewrite swu_constant_radix in Value.
  exists mf;split;[exact Call|];split;[exact Out|];split;[exact Owned|];split;[exact Value|];
    split;[exact SumBound|];split;[apply (field_scaled_loose 2 _ ltac:(lia) SumBound)|];split;
    [apply (swu_startup_preserved m mf Ready Preserved)|];split;[|exact Preserved].
  eapply lframe_add_block;[exact Frame|exact GlobalFrame|].
  intros b pos NG NW Foot;destruct Foot as (r & sh & ofs & chunk & At & Cell & E & Range).
  destruct r as [|[|r]];[apply NW;exact E|apply NG;exact E|destruct r;discriminate At].
Qed.
