(** Original fe_mul writes point Y from two distinct private fields.  The
    destination belongs to the real 128-byte point; no offset allocation or
    substituted multiplication is used. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_local_regions.
Require Import C.jet_secp_u128_word_oracle C.jet_secp_field_mul_word_model C.jet_secp_point_mul_run
  C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric C.jet_secp_curve_mul
  C.jet_secp_field_point_multiply C.jet_secp_owned_slice_fields C.jet_secp_b32_exec.
Require Import C.jet_secp_field_add_initial C.jet_secp_multiply_normalize_bridge
  C.jet_secp_multiply_finish_product C.jet_secp_square_columns C.jet_secp_field_mul_small.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition point_y_product_holes := map (fun ofs => mkcell ofs Mint64 None) [40;48;56;64;72].
Definition point_y_product_regs :=
  [mkreg point_y_product_holes true (Some 128);
   free_region (fe_reg (vars5 0)) 40;free_region (fe_reg (vars5 5)) 40].
Definition point_y_product_args := [XP 0 40;XP 1 0;XP 2 0].
Definition point_y_product_run := xfun (genv_cenv secp_ge) [] point_mul_table 400
  f_secp256k1_fe_mul point_y_product_args point_y_product_regs [] 10.
Definition point_y_product_tree := Eval vm_compute in point_y_product_run.
Definition point_y_product_state := match point_y_product_tree with
  | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition point_y_product_out_regs :=
  [mkreg (u64_cells 40 point_mul_out) true (Some 128);
   free_region (fe_reg (vars5 0)) 40;free_region (fe_reg (vars5 5)) 40].

Lemma point_y_product_run_eq : point_y_product_run=Some (RDone point_y_product_state ONormal).
Proof. reflexivity. Qed.
Lemma point_y_product_log_eq : slog point_y_product_state=fe_mul_log.
Proof. reflexivity. Qed.
Lemma point_y_product_out_eq : sregs point_y_product_state=point_y_product_out_regs.
Proof. reflexivity. Qed.
Lemma point_y_product_return : (stemps point_y_product_state)!1%positive=None.
Proof. reflexivity. Qed.

Local Opaque point_y_product_state.
Theorem eval_point_y_product_symbolic rho beta m :
  rep rho beta point_y_product_regs m -> Forall (u128_evok rho) fe_mul_log ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+40));
     Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));
     Vptr (blk beta 2) (Ptrofs.repr (bas beta 2))] E0 mf Vundef /\
  rep rho beta point_y_product_out_regs mf /\
  lframe (fun b pos => ~foot beta (map rshape point_y_product_regs) b pos) m mf.
Proof.
  intros HR HSol.
  destruct (xfun_top_sound secp_ge [] point_mul_table u128_evok u128_inv u128_ext
    ltac:(intros;exact I) ltac:(intros;contradiction) point_mul_table_ok
    400 f_secp256k1_fe_mul point_y_product_args point_y_product_regs [] 10
    (RDone point_y_product_state ONormal) point_y_product_run_eq rho beta m HR)
    as (mf & result & HC & HP & HV & HS & _ & HL).
  - split;intros;discriminate.
  - intros r _ HE;exact HE.
  - exact I.
  - cbn [rsel fst];rewrite point_y_product_log_eq;exact HSol.
  - cbn [rsel fst] in HP,HV;rewrite point_y_product_return in HV;subst result.
    change (map (den rho (lay beta)) point_y_product_args) with
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+40));
       Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+0));
       Vptr (blk beta 2) (Ptrofs.repr (bas beta 2+0))] in HC.
    rewrite !Z.add_0_r in HC;rewrite point_y_product_out_eq in HP.
    exists mf;split;[exact HC|];split;[exact HP|].
    eapply lframe_implies;[exact HL|].
    intros b pos HOutside HValid;split;[exact HValid|];split;[exact HOutside|intros HE;exact HE].
Qed.

Lemma point_y_product_initial a b m bp ba bb : bp<>ba -> bp<>bb -> ba<>bb ->
  Mem.range_perm m bp 0 128 Cur Freeable ->
  fe_at m ba 0 (words5 a) -> Mem.range_perm m ba 0 40 Cur Freeable ->
  fe_at m bb 0 (words5 b) -> Mem.range_perm m bb 0 40 Cur Freeable ->
  rep (point_mul_valuation a b) [(bp,0);(ba,0);(bb,0)] point_y_product_regs m.
Proof.
  intros HPA HPB HAB HFP HA HFA HB HFB.
  assert (H0 : region_ok (point_mul_valuation a b) [(bp,0);(ba,0);(bb,0)] m 0
    (mkreg point_y_product_holes true (Some 128))).
  { unfold region_ok;cbn [rcells rw rfree bas blk lay nth fst snd].
    split;[lia|];split.
    - eapply Mem.perm_valid_block;apply (HFP 0);lia.
    - split;[reflexivity|];split.
      + apply Forall_forall;intros c HC;cbn [point_y_product_holes map In] in HC.
        repeat match type of HC with _ \/ _ => destruct HC as [HC|HC] end;
          try contradiction;subst c;apply writable_undefined_cell;
          cbn [bas blk lay nth fst snd size_chunk align_chunk];try (change Ptrofs.max_unsigned with 18446744073709551615;lia).
        all: try (apply freeable_range_writable;intros pos HP;apply HFP;lia).
        all: match goal with |- (8|?n) => exists (n/8);reflexivity end.
      + split;[reflexivity|];split;[reflexivity|];split;[exact HFP|].
        repeat constructor;cbn;lia. }
  assert (H1 : region_ok (point_mul_valuation a b) [(bp,0);(ba,0);(bb,0)] m 1
    (free_region (fe_reg (vars5 0)) 40)).
  { apply owned_field_slice_region;[reflexivity|lia|lia| |exact HFA].
    rewrite point_mul_valuation_first;exact HA. }
  assert (H2 : region_ok (point_mul_valuation a b) [(bp,0);(ba,0);(bb,0)] m 2
    (free_region (fe_reg (vars5 5)) 40)).
  { apply owned_field_values_slice_region;[reflexivity|lia|lia| |exact HFB].
    rewrite point_mul_valuation_second;exact HB. }
  split;[reflexivity|];split.
  - intros r1 r2 reg1 reg2 HNe E1 E2.
    assert (B1 : (r1<3)%nat) by (change (r1<length point_y_product_regs)%nat;apply nth_error_Some;congruence).
    assert (B2 : (r2<3)%nat) by (change (r2<length point_y_product_regs)%nat;apply nth_error_Some;congruence).
    destruct r1 as [|[|[|r1]]],r2 as [|[|[|r2]]];try lia;left;
      cbn [blk lay nth fst];congruence.
  - intros r reg HG;destruct r as [|[|[|r]]];cbn [point_y_product_regs nth_error] in HG;
      try (destruct r;discriminate);inversion HG;subst reg;assumption.
Qed.

Lemma point_y_product_fields a b m bp ba bb :
  rep (point_mul_valuation a b) [(bp,0);(ba,0);(bb,0)] point_y_product_out_regs m ->
  fe_at m bp 40 (words5 (point_mul_words a b)) /\
  fe_at m ba 0 (words5 a) /\ fe_at m bb 0 (words5 b) /\
  Mem.range_perm m bp 0 128 Cur Freeable /\
  Mem.range_perm m ba 0 40 Cur Freeable /\ Mem.range_perm m bb 0 40 Cur Freeable.
Proof.
  intro HR.
  pose proof (rep_region _ _ _ m 0 _ HR eq_refl) as H0.
  pose proof (rep_region _ _ _ m 1 _ HR eq_refl) as H1.
  pose proof (rep_region _ _ _ m 2 _ HR eq_refl) as H2.
  pose proof H0 as (_ & _ & _ & _ & _ & _ & HF0 & _).
  pose proof H1 as (_ & _ & _ & _ & _ & _ & HF1 & _).
  pose proof H2 as (_ & _ & _ & _ & _ & _ & HF2 & _).
  split.
  - eapply owned_region_field_slice with (exprs:=point_mul_out) (size:=128)
      (rho:=point_mul_valuation a b) (beta:=[(bp,0);(ba,0);(bb,0)]) (r:=0%nat);
      [exact H0|lia|exists 5;reflexivity|lia|
       change (128<=18446744073709551615);lia|reflexivity|reflexivity| |].
    + intros c HC;exact HC.
    + apply point_mul_output_den.
  - split.
    + eapply owned_region_field_slice with (exprs:=vars5 0) (size:=40)
        (rho:=point_mul_valuation a b) (beta:=[(bp,0);(ba,0);(bb,0)]) (r:=1%nat);
        [exact H1|lia|exists 0;reflexivity|lia|
         change (40<=18446744073709551615);lia|reflexivity|reflexivity| |].
      * intros c HC;exact HC.
      * reflexivity.
    + split.
      * eapply owned_region_field_slice with (exprs:=vars5 5) (size:=40)
          (rho:=point_mul_valuation a b) (beta:=[(bp,0);(ba,0);(bb,0)]) (r:=2%nat);
          [exact H2|lia|exists 0;reflexivity|lia|
           change (40<=18446744073709551615);lia|reflexivity|reflexivity| |].
        -- intros c HC;exact HC.
        -- reflexivity.
      * repeat split;assumption.
Qed.

Lemma point_y_product_foot bp ba bb b pos :
  foot [(bp,0);(ba,0);(bb,0)] (map rshape point_y_product_regs) b pos ->
  (b=bp /\ 40<=pos<80) \/ b=ba \/ b=bb.
Proof.
  intros (r & sh & d & ch & HN & HC & HB & HP);destruct r as [|[|[|r]]].
  - left;split;[exact HB|].
    cbn [point_y_product_regs map nth_error rshape rcells rw rfree] in HN;injection HN as <-.
    cbn [point_y_product_holes rshape rcells rw rfree fst map cshape cofs cchunk In] in HC.
    repeat match type of HC with _ \/ _ => destruct HC as [HC|HC] end;
      try contradiction;inversion HC;subst d ch;cbn [bas lay nth snd] in HP;
      change (size_chunk Mint64) with 8 in HP;lia.
  - right;left;exact HB.
  - right;right;exact HB.
  - destruct r;discriminate HN.
Qed.

Theorem eval_point_y_product a b m bp ba bb :
  square_input_bounds a -> square_input_bounds b -> bp<>ba -> bp<>bb -> ba<>bb ->
  Mem.range_perm m bp 0 128 Cur Freeable ->
  fe_at m ba 0 (words5 a) -> Mem.range_perm m ba 0 40 Cur Freeable ->
  fe_at m bb 0 (words5 b) -> Mem.range_perm m bb 0 40 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr bp (Ptrofs.repr 40);Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf Vundef /\
  fe_at mf bp 40 (words5 (point_mul_words a b)) /\
  fe_at mf ba 0 (words5 a) /\ fe_at mf bb 0 (words5 b) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\
  Mem.range_perm mf ba 0 40 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
  radix_value (point_mul_words a b) mod feP=(radix_value a*radix_value b) mod feP /\
  mul_small_input_bounds (point_mul_words a b) /\
  lframe (fun bx pos => bx<>ba /\ bx<>bb /\ (bx<>bp \/ pos<40 \/ 80<=pos)) m mf.
Proof.
  intros BA BB HPA HPB HAB HFP HA HFA HB HFB.
  destruct (eval_point_y_product_symbolic (point_mul_valuation a b) [(bp,0);(ba,0);(bb,0)] m
    (point_y_product_initial a b m bp ba bb HPA HPB HAB HFP HA HFA HB HFB)
    (fm_solves _ _ _ _ _ _ _ _ _ _)) as (mf & HC & HP & HL).
  destruct (point_y_product_fields a b mf bp ba bb HP) as (FO & FA & FB & FOF & FAF & FBF).
  destruct (curve_mul_value_bounds a b (field_operand_from_bounds a BA)
    (field_operand_from_bounds b BB)) as [HV HBounds].
  exists mf;split;[exact HC|];split;[exact FO|];split;[exact FA|];split;[exact FB|];
    split;[exact FOF|];split;[exact FAF|];split;[exact FBF|];split;[exact HV|];split;[exact HBounds|].
  eapply lframe_implies;[exact HL|]. intros bx pos (NA & NB & NO) HV' HFoot.
  destruct (point_y_product_foot bp ba bb bx pos HFoot) as [[HE HR]|[HE|HE]];try congruence.
  subst bx;destruct NO as [HN|[HN|HN]];[contradiction|lia|lia].
Qed.
