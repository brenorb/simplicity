(** Original fe_mul into an uninitialized private result from one affine
    coordinate and a separate private field. Shared for mixed U2 and S2. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_local_regions
  C.jet_secp_u128_word_oracle C.jet_secp_field_mul_word_model C.jet_secp_point_mul_run
  C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric C.jet_secp_field_point_multiply
  C.jet_secp_owned_slice_fields C.jet_secp_b32_exec C.jet_secp_fe_b32 C.jet_secp_field_add_initial
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_square_columns C.jet_secp_curve_square C.jet_secp_curve_mul
  C.jet_secp_curve_statements C.jet_secp_mixed_finite_start C.jet_secp_mixed_copy_weak.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition mixed_affine_product_regs y :=
  [free_region fe_undef 40;curve_square_input y;free_region (fe_reg (vars5 5)) 40].
Definition mixed_affine_product_args y := [XP 0 0;XP 1 (curve_square_offset y);XP 2 0].
Definition mixed_affine_product_run y := xfun (genv_cenv secp_ge) [] point_mul_table 400
  f_secp256k1_fe_mul (mixed_affine_product_args y) (mixed_affine_product_regs y) [] 10.
Definition mixed_affine_product_tree := Eval vm_compute in fun y : bool =>
  if y then mixed_affine_product_run true else mixed_affine_product_run false.
Definition mixed_affine_product_state y := match mixed_affine_product_tree y with
  | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition mixed_affine_product_out y :=
  [mkreg (u64_cells 0 point_mul_out) true (Some 40);curve_square_input y;free_region (fe_reg (vars5 5)) 40].
Lemma mixed_affine_product_run_eq y : mixed_affine_product_run y=Some (RDone (mixed_affine_product_state y) ONormal).
Proof. destruct y;reflexivity. Qed.
Lemma mixed_affine_product_log y : slog (mixed_affine_product_state y)=fe_mul_log.
Proof. destruct y;reflexivity. Qed.
Lemma mixed_affine_product_output y : sregs (mixed_affine_product_state y)=mixed_affine_product_out y.
Proof. destruct y;reflexivity. Qed.
Lemma mixed_affine_product_return y : (stemps (mixed_affine_product_state y))!1%positive=None.
Proof. destruct y;reflexivity. Qed.

Local Opaque mixed_affine_product_state.
Theorem eval_mixed_affine_product_symbolic y rho beta m :
  rep rho beta (mixed_affine_product_regs y) m -> Forall (u128_evok rho) fe_mul_log ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
     Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+curve_square_offset y));
     Vptr (blk beta 2) (Ptrofs.repr (bas beta 2))] E0 mf Vundef /\
  rep rho beta (mixed_affine_product_out y) mf /\
  lframe (fun b pos=>~foot beta (map rshape (mixed_affine_product_regs y)) b pos) m mf.
Proof.
  intros HR HSol.
  destruct (xfun_top_sound secp_ge [] point_mul_table u128_evok u128_inv u128_ext
    ltac:(intros;exact I) ltac:(intros;contradiction) point_mul_table_ok
    400 f_secp256k1_fe_mul (mixed_affine_product_args y) (mixed_affine_product_regs y) [] 10
    (RDone (mixed_affine_product_state y) ONormal) (mixed_affine_product_run_eq y) rho beta m HR)
    as (mf & result & HC & HP & HV & HS & _ & HL).
  - split;intros;discriminate.
  - intros r _ HE;exact HE.
  - exact I.
  - cbn [rsel fst];rewrite mixed_affine_product_log;exact HSol.
  - cbn [rsel fst] in HP,HV;rewrite mixed_affine_product_return in HV;subst result.
    change (map (den rho (lay beta)) (mixed_affine_product_args y)) with
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0));
       Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+curve_square_offset y));
       Vptr (blk beta 2) (Ptrofs.repr (bas beta 2+0))] in HC.
    rewrite !Z.add_0_r in HC;rewrite mixed_affine_product_output in HP.
    exists mf;split;[exact HC|];split;[exact HP|].
    eapply lframe_implies;[exact HL|];intros b pos HO HV';split;[exact HV'|];split;[exact HO|intros HE;exact HE].
Qed.

Definition mixed_affine_call (y : bool) := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
  [curve_local_address (if y then _s2 else _u2);
   Eaddrof (mixed_b_field (if y then _y else _x) curve_fe_type) (tptr curve_fe_type);
   curve_local_address _z12].
Definition mixed_after_s2 := match mixed_after_s1 with | Ssequence _ rest => rest | _ => Sskip end.
Lemma mixed_affine_calls_source : mixed_u2_stmt=mixed_affine_call false /\
  mixed_after_s1=Ssequence (mixed_affine_call true) mixed_after_s2.
Proof. split;reflexivity. Qed.

Lemma mixed_affine_product_initial y a b m bo ba bb : bo<>ba -> bo<>bb -> ba<>bb ->
  Mem.range_perm m bo 0 40 Cur Freeable ->
  fe_at m ba (curve_square_offset y) (words5 a) -> Mem.range_perm m ba 0 88 Cur Freeable ->
  fe_at m bb 0 (words5 b) -> Mem.range_perm m bb 0 40 Cur Freeable ->
  rep (point_mul_valuation a b) [(bo,0);(ba,0);(bb,0)] (mixed_affine_product_regs y) m.
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
    - repeat constructor;cbn;lia. }
  assert (H1 : region_ok (point_mul_valuation a b) [(bo,0);(ba,0);(bb,0)] m 1 (curve_square_input y)).
  { apply owned_field_slice_region;[reflexivity|lia|destruct y;cbn [curve_square_offset];lia| |exact HFA].
    rewrite point_mul_valuation_first;exact HA. }
  assert (H2 : region_ok (point_mul_valuation a b) [(bo,0);(ba,0);(bb,0)] m 2
    (free_region (fe_reg (vars5 5)) 40)).
  { apply owned_field_values_slice_region;[reflexivity|lia|lia| |exact HFB].
    rewrite point_mul_valuation_second;exact HB. }
  split;[reflexivity|];split.
  - intros r1 r2 reg1 reg2 HNe E1 E2.
    assert (B1 : (r1<3)%nat) by (change (r1<length (mixed_affine_product_regs y))%nat;apply nth_error_Some;congruence).
    assert (B2 : (r2<3)%nat) by (change (r2<length (mixed_affine_product_regs y))%nat;apply nth_error_Some;congruence).
    destruct r1 as [|[|[|r1]]],r2 as [|[|[|r2]]];try lia;left;cbn [blk lay nth fst];congruence.
  - intros r reg HG;destruct r as [|[|[|r]]];cbn [mixed_affine_product_regs nth_error] in HG;
      try (destruct r;discriminate);inversion HG;subst reg;assumption.
Qed.

Lemma mixed_affine_product_fields y a b m bo ba bb :
  rep (point_mul_valuation a b) [(bo,0);(ba,0);(bb,0)] (mixed_affine_product_out y) m ->
  fe_at m bo 0 (words5 (point_mul_words a b)) /\
  fe_at m ba (curve_square_offset y) (words5 a) /\ fe_at m bb 0 (words5 b) /\
  Mem.range_perm m bo 0 40 Cur Freeable /\ Mem.range_perm m ba 0 88 Cur Freeable /\ Mem.range_perm m bb 0 40 Cur Freeable.
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
    + eapply owned_region_field_slice with (exprs:=vars5 0) (size:=88)
        (rho:=point_mul_valuation a b) (beta:=[(bo,0);(ba,0);(bb,0)]) (r:=1%nat);
        [exact H1|destruct y;cbn [curve_square_offset];lia|
         destruct y;cbn [curve_square_offset];[exists 5|exists 0];reflexivity|
         destruct y;cbn [curve_square_offset];lia|change (88<=18446744073709551615);lia|
         reflexivity|reflexivity| |].
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

Lemma mixed_affine_product_foot y bo ba bb bx pos :
  foot [(bo,0);(ba,0);(bb,0)] (map rshape (mixed_affine_product_regs y)) bx pos ->
  bx=bo \/ (bx=ba /\ curve_square_offset y<=pos<curve_square_offset y+40) \/ bx=bb.
Proof.
  intros (r & sh & d & ch & HN & HC & HB & HP);destruct r as [|[|[|r]]].
  - left;exact HB.
  - right;left;split;[exact HB|].
    cbn [mixed_affine_product_regs map nth_error rshape curve_square_input rcells rw rfree] in HN;injection HN as <-.
    cbn [curve_square_input rshape rcells rw rfree fst map cshape cofs cchunk u64_cells vars5 In] in HC.
    repeat match type of HC with _ \/ _ => destruct HC as [HC|HC] end;
      try contradiction;inversion HC;subst d ch;cbn [bas lay nth snd] in HP;
      change (size_chunk Mint64) with 8 in HP;lia.
  - right;right;exact HB.
  - destruct r;discriminate HN.
Qed.

Theorem eval_mixed_affine_product y a b m bo ba bb :
  square_input_bounds a -> square_input_bounds b -> bo<>ba -> bo<>bb -> ba<>bb ->
  Mem.range_perm m bo 0 40 Cur Freeable ->
  fe_at m ba (curve_square_offset y) (words5 a) -> Mem.range_perm m ba 0 88 Cur Freeable ->
  fe_at m bb 0 (words5 b) -> Mem.range_perm m bb 0 40 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr bo Ptrofs.zero;Vptr ba (Ptrofs.repr (curve_square_offset y));Vptr bb Ptrofs.zero] E0 mf Vundef /\
  fe_at mf bo 0 (words5 (point_mul_words a b)) /\
  fe_at mf ba (curve_square_offset y) (words5 a) /\ fe_at mf bb 0 (words5 b) /\
  Mem.range_perm mf bo 0 40 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
  radix_value (point_mul_words a b) mod feP=(radix_value a*radix_value b) mod feP /\
  square_input_bounds (point_mul_words a b) /\
  lframe (fun bx pos=>bx<>bo /\ bx<>bb /\ (bx<>ba \/ pos<curve_square_offset y \/ curve_square_offset y+40<=pos)) m mf.
Proof.
  intros BA BB HOA HOB HAB HFO HA HFA HB HFB.
  destruct (eval_mixed_affine_product_symbolic y (point_mul_valuation a b) [(bo,0);(ba,0);(bb,0)] m
    (mixed_affine_product_initial y a b m bo ba bb HOA HOB HAB HFO HA HFA HB HFB)
    (fm_solves _ _ _ _ _ _ _ _ _ _)) as (mf & HC & HP & HL).
  destruct (mixed_affine_product_fields y a b mf bo ba bb HP) as (FO & FA & FB & FOF & FAF & FBF).
  exists mf;split;[exact HC|];split;[exact FO|];split;[exact FA|];split;[exact FB|];
    split;[exact FOF|];split;[exact FAF|];split;[exact FBF|];split.
  - exact (proj1 (point_mul_value_and_bounds a b BA BB)).
  - split;[exact (proj2 (point_mul_value_and_bounds a b BA BB))|].
    eapply lframe_implies;[exact HL|];intros bx pos (NO & NB & NA) HV HFoot.
    destruct (mixed_affine_product_foot y bo ba bb bx pos HFoot) as [HO|[[HE HR]|HB']];try congruence.
    subst bx;destruct NA as [HN|[HN|HN]];[contradiction|lia|lia].
Qed.

Theorem exec_mixed_affine_call (y : bool) a b e le m bo ba bb :
  e!(if y then _s2 else _u2)=Some (bo,curve_fe_type) -> e!_z12=Some (bb,curve_fe_type) ->
  le!_b=Some (Vptr ba Ptrofs.zero) -> e!_secp256k1_fe_mul=None ->
  square_input_bounds a -> square_input_bounds b -> bo<>ba -> bo<>bb -> ba<>bb ->
  Mem.range_perm m bo 0 40 Cur Freeable ->
  fe_at m ba (curve_square_offset y) (words5 a) -> Mem.range_perm m ba 0 88 Cur Freeable ->
  fe_at m bb 0 (words5 b) -> Mem.range_perm m bb 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m (mixed_affine_call y) E0 le mf Out_normal /\
  fe_at mf bo 0 (words5 (point_mul_words a b)) /\
  fe_at mf ba (curve_square_offset y) (words5 a) /\ fe_at mf bb 0 (words5 b) /\
  Mem.range_perm mf bo 0 40 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
  radix_value (point_mul_words a b) mod feP=(radix_value a*radix_value b) mod feP /\
  square_input_bounds (point_mul_words a b) /\
  lframe (fun bx pos=>bx<>bo /\ bx<>bb /\ (bx<>ba \/ pos<curve_square_offset y \/ curve_square_offset y+40<=pos)) m mf.
Proof.
  intros HO HZ HB HE BA BB HOA HOB HAB HFO HA HFA HField HFB.
  destruct (eval_mixed_affine_product y a b m bo ba bb BA BB HOA HOB HAB HFO HA HFA HField HFB)
    as (mf & HC & FO & FA & FB & FOF & FAF & FBF & Val & Bound & Frame).
  exists mf;split.
  - unfold mixed_affine_call;eapply exec_curve_call with
      (vargs:=[Vptr bo Ptrofs.zero;Vptr ba (Ptrofs.repr (curve_square_offset y));Vptr bb Ptrofs.zero]) (v:=Vundef).
    + unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
    + exact HE.
    + eapply eval_Econs;[apply eval_curve_local;exact HO|reflexivity|].
      eapply eval_Econs with (v1:=Vptr ba (Ptrofs.repr (curve_square_offset y))).
      * apply eval_Eaddrof;apply eval_mixed_b_field;[destruct y;cbn [curve_square_offset In];tauto|exact HB].
      * reflexivity.
      * eapply eval_Econs;[apply eval_curve_local;exact HZ|reflexivity|constructor].
    + exact HC.
  - split;[exact FO|];split;[exact FA|];split;[exact FB|];split;[exact FOF|];split;[exact FAF|];
      split;[exact FBF|];split;[exact Val|];split;assumption.
Qed.
