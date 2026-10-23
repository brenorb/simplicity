(** Original projective-Z-times-field product in the actual operand order
    used by gej_add_zinv_var's az assignment. No commuted C call is substituted. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_local_regions
  C.jet_secp_u128_word_oracle C.jet_secp_field_mul_word_model C.jet_secp_point_mul_run
  C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric C.jet_secp_curve_mul
  C.jet_secp_field_point_multiply C.jet_secp_owned_slice_fields C.jet_secp_b32_exec
  C.jet_secp_fe_b32 C.jet_secp_field_add_initial C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_square_columns C.jet_secp_field_mul_small.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition zinv_z_product_regs :=
  [free_region fe_undef 40;mkreg (u64_cells 80 (vars5 0)) true (Some 128);free_region (fe_reg (vars5 5)) 40].
Definition zinv_z_product_args := [XP 0 0;XP 1 80;XP 2 0].
Definition zinv_z_product_run := xfun (genv_cenv secp_ge) [] point_mul_table 400
  f_secp256k1_fe_mul zinv_z_product_args zinv_z_product_regs [] 10.
Definition zinv_z_product_tree := Eval vm_compute in zinv_z_product_run.
Definition zinv_z_product_state := match zinv_z_product_tree with
  | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition zinv_z_product_out_regs :=
  [mkreg (u64_cells 0 point_mul_out) true (Some 40);
   mkreg (u64_cells 80 (vars5 0)) true (Some 128);free_region (fe_reg (vars5 5)) 40].
Lemma zinv_z_product_run_eq : zinv_z_product_run=Some (RDone zinv_z_product_state ONormal).
Proof. reflexivity. Qed.
Lemma zinv_z_product_log_eq : slog zinv_z_product_state=fe_mul_log.
Proof. reflexivity. Qed.
Lemma zinv_z_product_out_eq : sregs zinv_z_product_state=zinv_z_product_out_regs.
Proof. reflexivity. Qed.
Lemma zinv_z_product_return : (stemps zinv_z_product_state)!1%positive=None.
Proof. reflexivity. Qed.

Local Opaque zinv_z_product_state.
Theorem eval_zinv_z_product_symbolic rho beta m :
  rep rho beta zinv_z_product_regs m -> Forall (u128_evok rho) fe_mul_log -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+80));
     Vptr (blk beta 2) (Ptrofs.repr (bas beta 2))] E0 mf Vundef /\
  rep rho beta zinv_z_product_out_regs mf /\
  lframe (fun b pos=>~foot beta (map rshape zinv_z_product_regs) b pos) m mf.
Proof.
  intros HR HSol.
  destruct (xfun_top_sound secp_ge [] point_mul_table u128_evok u128_inv u128_ext
    ltac:(intros;exact I) ltac:(intros;contradiction) point_mul_table_ok
    400 f_secp256k1_fe_mul zinv_z_product_args zinv_z_product_regs [] 10
    (RDone zinv_z_product_state ONormal) zinv_z_product_run_eq rho beta m HR)
    as (mf & result & HC & HP & HV & HS & _ & HL).
  - split;intros;discriminate.
  - intros r _ HE;exact HE.
  - exact I.
  - cbn [rsel fst];rewrite zinv_z_product_log_eq;exact HSol.
  - cbn [rsel fst] in HP,HV;rewrite zinv_z_product_return in HV;subst result.
    change (map (den rho (lay beta)) zinv_z_product_args) with
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+80));
       Vptr (blk beta 2) (Ptrofs.repr (bas beta 2+0))] in HC.
    rewrite !Z.add_0_r in HC;rewrite zinv_z_product_out_eq in HP.
    exists mf;split;[exact HC|];split;[exact HP|].
    eapply lframe_implies;[exact HL|].
    intros b pos HOutside HValid;split;[exact HValid|];split;[exact HOutside|intros HE;exact HE].
Qed.

Lemma zinv_z_product_initial a b m bo ba bb : bo<>ba -> bo<>bb -> ba<>bb ->
  Mem.range_perm m bo 0 40 Cur Freeable -> fe_at m ba 80 (words5 a) -> Mem.range_perm m ba 0 128 Cur Freeable ->
  fe_at m bb 0 (words5 b) -> Mem.range_perm m bb 0 40 Cur Freeable ->
  rep (point_mul_valuation a b) [(bo,0);(ba,0);(bb,0)] zinv_z_product_regs m.
Proof.
  intros HOA HOB HAB HFO HA HFA HB HFB.
  assert (H0 : region_ok (point_mul_valuation a b) [(bo,0);(ba,0);(bb,0)] m 0 (free_region fe_undef 40)).
  { apply region_with_freeable.
    - apply region_fe_undefined_from_storage;cbn [bas blk lay nth fst snd].
      + lia.
      + exists 0;reflexivity.
      + change (40<=18446744073709551615);lia.
      + apply freeable_range_writable;exact HFO.
    - reflexivity.
    - reflexivity.
    - exact HFO.
    - apply fe_undef_storage_size. }
  assert (H1 : region_ok (point_mul_valuation a b) [(bo,0);(ba,0);(bb,0)] m 1 (mkreg (u64_cells 80 (vars5 0)) true (Some 128))).
  { apply owned_field_values_slice_region;[reflexivity|lia|lia| |exact HFA].
    exact HA. }
  assert (H2 : region_ok (point_mul_valuation a b) [(bo,0);(ba,0);(bb,0)] m 2 (free_region (fe_reg (vars5 5)) 40)).
  { apply owned_field_values_slice_region;[reflexivity|lia|lia| |exact HFB].
    rewrite point_mul_valuation_second;exact HB. }
  split;[reflexivity|];split.
  - intros r1 r2 reg1 reg2 HNe E1 E2.
    assert (B1 : (r1<3)%nat) by (change (r1<length zinv_z_product_regs)%nat;apply nth_error_Some;congruence).
    assert (B2 : (r2<3)%nat) by (change (r2<length zinv_z_product_regs)%nat;apply nth_error_Some;congruence).
    destruct r1 as [|[|[|r1]]],r2 as [|[|[|r2]]];try lia;left;cbn [blk lay nth fst];congruence.
  - intros r reg HG;destruct r as [|[|[|r]]];cbn [zinv_z_product_regs nth_error] in HG;
      try (destruct r;discriminate);inversion HG;subst reg;assumption.
Qed.

Lemma zinv_z_product_fields a b m bo ba bb :
  rep (point_mul_valuation a b) [(bo,0);(ba,0);(bb,0)] zinv_z_product_out_regs m ->
  fe_at m bo 0 (words5 (point_mul_words a b)) /\ fe_at m ba 80 (words5 a) /\ fe_at m bb 0 (words5 b) /\
  Mem.range_perm m bo 0 40 Cur Freeable /\ Mem.range_perm m ba 0 128 Cur Freeable /\ Mem.range_perm m bb 0 40 Cur Freeable.
Proof.
  intro HR.
  pose proof (rep_region _ _ _ m 0 _ HR eq_refl) as H0.
  pose proof (rep_region _ _ _ m 1 _ HR eq_refl) as H1.
  pose proof (rep_region _ _ _ m 2 _ HR eq_refl) as H2.
  pose proof H0 as (_ & _ & _ & _ & _ & _ & HF0 & _).
  pose proof H1 as (_ & _ & _ & _ & _ & _ & HF1 & _).
  pose proof H2 as (_ & _ & _ & _ & _ & _ & HF2 & _).
  split.
  - eapply owned_region_field_slice with (exprs:=point_mul_out) (size:=40)
      (rho:=point_mul_valuation a b) (beta:=[(bo,0);(ba,0);(bb,0)]) (r:=0%nat);
      [exact H0|lia|exists 0;reflexivity|lia|change (40<=18446744073709551615);lia|reflexivity|reflexivity| |].
    + intros c HC;exact HC.
    + apply point_mul_output_den.
  - split.
    + eapply owned_region_field_slice with (exprs:=vars5 0) (size:=128)
        (rho:=point_mul_valuation a b) (beta:=[(bo,0);(ba,0);(bb,0)]) (r:=1%nat);
        [exact H1|lia|exists 10;reflexivity|lia|change (128<=18446744073709551615);lia|reflexivity|reflexivity| |].
      * intros c HC;exact HC.
      * reflexivity.
    + split.
      * eapply owned_region_field_slice with (exprs:=vars5 5) (size:=40)
          (rho:=point_mul_valuation a b) (beta:=[(bo,0);(ba,0);(bb,0)]) (r:=2%nat);
          [exact H2|lia|exists 0;reflexivity|lia|change (40<=18446744073709551615);lia|reflexivity|reflexivity| |].
        -- intros c HC;exact HC.
        -- reflexivity.
      * repeat split;assumption.
Qed.

Theorem eval_zinv_z_product_owned a b m bo ba bb :
  square_input_bounds a -> square_input_bounds b -> bo<>ba -> bo<>bb -> ba<>bb ->
  Mem.range_perm m bo 0 40 Cur Freeable -> fe_at m ba 80 (words5 a) -> Mem.range_perm m ba 0 128 Cur Freeable ->
  fe_at m bb 0 (words5 b) -> Mem.range_perm m bb 0 40 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr bo Ptrofs.zero;Vptr ba (Ptrofs.repr 80);Vptr bb Ptrofs.zero] E0 mf Vundef /\
  fe_at mf bo 0 (words5 (point_mul_words a b)) /\ fe_at mf ba 80 (words5 a) /\ fe_at mf bb 0 (words5 b) /\
  Mem.range_perm mf bo 0 40 Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
  radix_value (point_mul_words a b) mod feP=(radix_value a*radix_value b) mod feP /\
  mul_small_input_bounds (point_mul_words a b) /\ lframe (fun bx pos=>bx<>bo /\ (bx<>ba \/ pos<80 \/ 120<=pos) /\ bx<>bb) m mf.
Proof.
  intros BA BB HOA HOB HAB HFO HA HFA HB HFB.
  destruct (eval_zinv_z_product_symbolic (point_mul_valuation a b) [(bo,0);(ba,0);(bb,0)] m
    (zinv_z_product_initial a b m bo ba bb HOA HOB HAB HFO HA HFA HB HFB)
    (fm_solves _ _ _ _ _ _ _ _ _ _)) as (mf & HC & HP & HL).
  destruct (zinv_z_product_fields a b mf bo ba bb HP) as (FO & FA & FB & FOF & FAF & FBF).
  destruct (curve_mul_value_bounds a b (field_operand_from_bounds a BA) (field_operand_from_bounds b BB)) as [HV HBounds].
  exists mf;split;[exact HC|];split;[exact FO|];split;[exact FA|];split;[exact FB|];
    split;[exact FOF|];split;[exact FAF|];split;[exact FBF|];split;[exact HV|];split;[exact HBounds|].
  eapply lframe_implies;[exact HL|];intros bx pos (NO & NA & NB) HV' (r & sh & d & ch & HN & HC' & HE & HR).
  destruct r as [|[|[|r]]].
  - apply NO;exact HE.
  - change (bx=ba) in HE;subst bx.
    cbn [zinv_z_product_regs map nth_error rshape rcells rw rfree] in HN;injection HN as <-.
    cbn [rshape rcells rw rfree fst map cshape cofs cchunk u64_cells vars5 In] in HC'.
    repeat match type of HC' with _ \/ _ => destruct HC' as [HC'|HC'] end;
      try contradiction;inversion HC';subst d ch;cbn [bas lay nth snd] in HR;
      change (size_chunk Mint64) with 8 in HR;destruct NA as [NA | [NA | NA]];try contradiction;lia.
  - apply NB;exact HE.
  - destruct r;discriminate HN.
Qed.
