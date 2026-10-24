(** Original affine-conversion cube multiplication: separate local output,
    Z at offset 80 in an owned point, and a separate squared temporary. *)
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

Definition affine_cube_regs :=
  [free_region fe_undef 40;mkreg (u64_cells 80 (vars5 0)) true (Some 128);free_region (fe_reg (vars5 5)) 40].
Definition affine_cube_args := [XP 0 0;XP 1 80;XP 2 0].
Definition affine_cube_run := xfun (genv_cenv secp_ge) [] point_mul_table 400
  f_secp256k1_fe_mul affine_cube_args affine_cube_regs [] 10.
Definition affine_cube_tree := Eval vm_compute in affine_cube_run.
Definition affine_cube_state := match affine_cube_tree with
  | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition affine_cube_out_regs :=
  [mkreg (u64_cells 0 point_mul_out) true (Some 40);
   mkreg (u64_cells 80 (vars5 0)) true (Some 128);free_region (fe_reg (vars5 5)) 40].
Lemma affine_cube_run_eq : affine_cube_run=Some (RDone affine_cube_state ONormal).
Proof. reflexivity. Qed.
Lemma affine_cube_log_eq : slog affine_cube_state=fe_mul_log.
Proof. reflexivity. Qed.
Lemma affine_cube_out_eq : sregs affine_cube_state=affine_cube_out_regs.
Proof. reflexivity. Qed.
Lemma affine_cube_return : (stemps affine_cube_state)!1%positive=None.
Proof. reflexivity. Qed.

Local Opaque affine_cube_state.
Lemma affine_cube_foot bo ba bb bx pos :
  foot [(bo,0);(ba,0);(bb,0)] (map rshape affine_cube_regs) bx pos ->
  (bx=bo /\ 0<=pos<40) \/ (bx=ba /\ 80<=pos<120) \/ (bx=bb /\ 0<=pos<40).
Proof.
  intros (r & sh & d & ch & HN & HC & HB & HO).
  destruct r as [|[|[|r]]].
  - left;split;[exact HB|].
    cbn [affine_cube_regs map nth_error rshape rcells rw rfree] in HN;injection HN as <-.
    cbn [fst map cshape cofs cchunk free_region fe_undef rcells] in HC.
    destruct HC as [HC|[HC|[HC|[HC|[HC|HC]]]]];try contradiction;
      inversion HC;subst d ch;cbn [bas lay nth snd] in HO;
      change (size_chunk Mint64) with 8 in HO;lia.
  - right;left;split;[exact HB|].
    cbn [affine_cube_regs map nth_error rshape rcells rw rfree] in HN;injection HN as <-.
    cbn [rcells u64_cells vars5 rshape map cshape cofs cchunk fst] in HC.
    destruct HC as [HC|[HC|[HC|[HC|[HC|HC]]]]];try contradiction;
      inversion HC;subst d ch;cbn [bas lay nth snd] in HO;
      change (size_chunk Mint64) with 8 in HO;lia.
  - right;right;split;[exact HB|].
    cbn [affine_cube_regs map nth_error rshape rcells rw rfree] in HN;injection HN as <-.
    cbn [free_region fe_reg rcells u64_cells vars5 rshape map cshape cofs cchunk fst] in HC.
    destruct HC as [HC|[HC|[HC|[HC|[HC|HC]]]]];try contradiction;
      inversion HC;subst d ch;cbn [bas lay nth snd] in HO;
      change (size_chunk Mint64) with 8 in HO;lia.
  - destruct r;discriminate HN.
Qed.

Theorem eval_affine_cube_symbolic rho beta m :
  rep rho beta affine_cube_regs m -> Forall (u128_evok rho) fe_mul_log -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+80));
     Vptr (blk beta 2) (Ptrofs.repr (bas beta 2))] E0 mf Vundef /\
  rep rho beta affine_cube_out_regs mf /\
  lframe (fun b pos=>~foot beta (map rshape affine_cube_regs) b pos) m mf.
Proof.
  intros HR HSol.
  destruct (xfun_top_sound secp_ge [] point_mul_table u128_evok u128_inv u128_ext
    ltac:(intros;exact I) ltac:(intros;contradiction) point_mul_table_ok
    400 f_secp256k1_fe_mul affine_cube_args affine_cube_regs [] 10
    (RDone affine_cube_state ONormal) affine_cube_run_eq rho beta m HR)
    as (mf & result & HC & HP & HV & HS & _ & HL).
  - split;intros;discriminate.
  - intros r _ HE;exact HE.
  - exact I.
  - cbn [rsel fst];rewrite affine_cube_log_eq;exact HSol.
  - cbn [rsel fst] in HP,HV;rewrite affine_cube_return in HV;subst result.
    change (map (den rho (lay beta)) affine_cube_args) with
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+80));
       Vptr (blk beta 2) (Ptrofs.repr (bas beta 2+0))] in HC.
    rewrite !Z.add_0_r in HC;rewrite affine_cube_out_eq in HP.
    exists mf;split;[exact HC|];split;[exact HP|].
    eapply lframe_implies;[exact HL|].
    intros b pos HOutside HValid;split;[exact HValid|];split;[exact HOutside|intros HE;exact HE].
Qed.

Lemma affine_cube_initial a b m bo ba bb : bo<>ba -> bo<>bb -> ba<>bb ->
  Mem.range_perm m bo 0 40 Cur Freeable -> fe_at m ba 80 (words5 a) -> Mem.range_perm m ba 0 128 Cur Freeable ->
  fe_at m bb 0 (words5 b) -> Mem.range_perm m bb 0 40 Cur Freeable ->
  rep (point_mul_valuation a b) [(bo,0);(ba,0);(bb,0)] affine_cube_regs m.
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
  { apply owned_field_slice_region;[reflexivity|lia|lia| |exact HFA].
    rewrite point_mul_valuation_first;exact HA. }
  assert (H2 : region_ok (point_mul_valuation a b) [(bo,0);(ba,0);(bb,0)] m 2 (free_region (fe_reg (vars5 5)) 40)).
  { apply owned_field_values_slice_region;[reflexivity|lia|lia| |exact HFB].
    rewrite point_mul_valuation_second;exact HB. }
  split;[reflexivity|];split.
  - intros r1 r2 reg1 reg2 HNe E1 E2.
    assert (B1 : (r1<3)%nat) by (change (r1<length affine_cube_regs)%nat;apply nth_error_Some;congruence).
    assert (B2 : (r2<3)%nat) by (change (r2<length affine_cube_regs)%nat;apply nth_error_Some;congruence).
    destruct r1 as [|[|[|r1]]],r2 as [|[|[|r2]]];try lia;left;cbn [blk lay nth fst];congruence.
  - intros r reg HG;destruct r as [|[|[|r]]];cbn [affine_cube_regs nth_error] in HG;
      try (destruct r;discriminate);inversion HG;subst reg;assumption.
Qed.

Lemma affine_cube_fields a b m bo ba bb :
  rep (point_mul_valuation a b) [(bo,0);(ba,0);(bb,0)] affine_cube_out_regs m ->
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

Theorem eval_affine_cube_owned a b m bo ba bb :
  square_input_bounds a -> square_input_bounds b -> bo<>ba -> bo<>bb -> ba<>bb ->
  Mem.range_perm m bo 0 40 Cur Freeable -> fe_at m ba 80 (words5 a) -> Mem.range_perm m ba 0 128 Cur Freeable ->
  fe_at m bb 0 (words5 b) -> Mem.range_perm m bb 0 40 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr bo Ptrofs.zero;Vptr ba (Ptrofs.repr 80);Vptr bb Ptrofs.zero] E0 mf Vundef /\
  fe_at mf bo 0 (words5 (point_mul_words a b)) /\ fe_at mf ba 80 (words5 a) /\ fe_at mf bb 0 (words5 b) /\
  Mem.range_perm mf bo 0 40 Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
  radix_value (point_mul_words a b) mod feP=(radix_value a*radix_value b) mod feP /\
  square_input_bounds (point_mul_words a b) /\
  lframe (fun bx pos=>~foot [(bo,0);(ba,0);(bb,0)] (map rshape affine_cube_regs) bx pos) m mf.
Proof.
  intros BA BB HOA HOB HAB HFO HA HFA HB HFB.
  destruct (eval_affine_cube_symbolic (point_mul_valuation a b) [(bo,0);(ba,0);(bb,0)] m
    (affine_cube_initial a b m bo ba bb HOA HOB HAB HFO HA HFA HB HFB)
    (fm_solves _ _ _ _ _ _ _ _ _ _)) as (mf & HC & HP & HL).
  destruct (affine_cube_fields a b mf bo ba bb HP) as (FO & FA & FB & FOF & FAF & FBF).
  destruct (curve_mul_value_bounds a b (field_operand_from_bounds a BA) (field_operand_from_bounds b BB)) as [HV HBounds].
  exists mf;split;[exact HC|];split;[exact FO|];split;[exact FA|];split;[exact FB|];
    split;[exact FOF|];split;[exact FAF|];split;[exact FBF|];split;[exact HV|];split.
  - exact (proj2 (point_mul_value_and_bounds a b BA BB)).
  - exact HL.
Qed.
