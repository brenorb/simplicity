(** Actual Z := Z*Y inside one owned 128-byte point.  The field operands are
    disjoint slices of the same allocation, not fictitious separate blocks. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_local_regions.
Require Import C.jet_secp_u128_word_oracle C.jet_secp_field_mul_word_model C.jet_secp_point_mul_run
  C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric C.jet_secp_curve_mul
  C.jet_secp_field_point_multiply C.jet_secp_owned_slice_fields.
Require Import C.jet_secp_field_add_initial C.jet_secp_multiply_normalize_bridge
  C.jet_secp_multiply_finish_product C.jet_secp_square_columns.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition point_zy_mul_regs :=
  [mkreg (u64_cells 40 (vars5 5)++u64_cells 80 (vars5 0)) true (Some 128)].
Definition point_zy_mul_args := [XP 0 80;XP 0 80;XP 0 40].
Definition point_zy_mul_run := xfun (genv_cenv secp_ge) [] point_mul_table 400
  f_secp256k1_fe_mul point_zy_mul_args point_zy_mul_regs [] 10.
Definition point_zy_mul_tree := Eval vm_compute in point_zy_mul_run.
Definition point_zy_mul_state := match point_zy_mul_tree with
  | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition point_zy_mul_out_regs :=
  [mkreg (u64_cells 40 (vars5 5)++u64_cells 80 point_mul_out) true (Some 128)].

Lemma point_zy_mul_run_eq : point_zy_mul_run=Some (RDone point_zy_mul_state ONormal).
Proof. reflexivity. Qed.
Lemma point_zy_mul_log_eq : slog point_zy_mul_state=fe_mul_log.
Proof. reflexivity. Qed.
Lemma point_zy_mul_out_eq : sregs point_zy_mul_state=point_zy_mul_out_regs.
Proof. reflexivity. Qed.
Lemma point_zy_mul_return : (stemps point_zy_mul_state)!1%positive=None.
Proof. reflexivity. Qed.

Local Opaque point_zy_mul_state.
Theorem eval_point_zy_mul_symbolic rho beta m :
  rep rho beta point_zy_mul_regs m -> Forall (u128_evok rho) fe_mul_log ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+80));
     Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+80));
     Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+40))] E0 mf Vundef /\
  rep rho beta point_zy_mul_out_regs mf /\
  lframe (fun b pos => ~foot beta (map rshape point_zy_mul_regs) b pos) m mf.
Proof.
  intros HR HSol.
  destruct (xfun_top_sound secp_ge [] point_mul_table u128_evok u128_inv u128_ext
    ltac:(intros;exact I) ltac:(intros;contradiction) point_mul_table_ok
    400 f_secp256k1_fe_mul point_zy_mul_args point_zy_mul_regs [] 10
    (RDone point_zy_mul_state ONormal) point_zy_mul_run_eq rho beta m HR)
    as (mf & vres & HC & HP & HV & HS & _ & HF).
  - split;intros;discriminate.
  - intros r _ HE;exact HE.
  - exact I.
  - cbn [rsel fst];rewrite point_zy_mul_log_eq;exact HSol.
  - cbn [rsel fst] in HP,HV,HS;rewrite point_zy_mul_return in HV;subst vres.
    rewrite point_zy_mul_out_eq in HP.
    exists mf;split;[exact HC|];split;[exact HP|].
    eapply lframe_implies;[exact HF|].
    intros b pos HOutside HValid;split;[exact HValid|];split;[exact HOutside|intros HE;exact HE].
Qed.

Lemma point_zy_mul_initial z y m b :
  fe_at m b 80 (words5 z) -> fe_at m b 40 (words5 y) ->
  Mem.range_perm m b 0 128 Cur Freeable ->
  rep (point_mul_valuation z y) [(b,0)] point_zy_mul_regs m.
Proof.
  intros HZ HY HF;apply (rep_add (point_mul_valuation z y) [] [] m b 0);
    [apply rep_nil|cbn;tauto|].
  apply owned_region_append.
  - apply owned_field_values_slice_region;[reflexivity|lia|lia| |exact HF].
    rewrite point_mul_valuation_second;exact HY.
  - apply owned_field_slice_region;[reflexivity|lia|lia| |exact HF].
    rewrite point_mul_valuation_first;exact HZ.
  - reflexivity.
Qed.

Lemma point_zy_mul_fields z y beta m :
  rep (point_mul_valuation z y) beta point_zy_mul_out_regs m ->
  fe_at m (blk beta 0) 80 (words5 (point_mul_words z y)) /\
  fe_at m (blk beta 0) 40 (words5 y) /\ Mem.range_perm m (blk beta 0) 0 128 Cur Freeable.
Proof.
  intro HR;pose proof (rep_region _ _ _ m 0 _ HR eq_refl) as H0.
  pose proof H0 as (_ & _ & _ & _ & _ & _ & HF & _).
  split.
  - eapply owned_region_field_slice with (exprs:=point_mul_out) (size:=128);
      [exact H0|lia|exists 10;reflexivity|lia|
       change (128<=18446744073709551615);lia|reflexivity|reflexivity| |].
    + intros c HC;apply in_or_app;right;exact HC.
    + apply point_mul_output_den.
  - split;[|exact HF].
    eapply owned_region_field_slice with (exprs:=vars5 5) (size:=128);
      [exact H0|lia|exists 5;reflexivity|lia|
       change (128<=18446744073709551615);lia|reflexivity|reflexivity| |].
    + intros c HC;apply in_or_app;left;exact HC.
    + reflexivity.
Qed.

Lemma point_zy_mul_foot b bx pos :
  foot [(b,0)] (map rshape point_zy_mul_regs) bx pos -> bx=b /\ 40<=pos<120.
Proof.
  intros (r & sh & d & ch & HN & HC & HB & HO).
  destruct r;[|destruct r;discriminate HN]. split;[exact HB|].
  cbn [point_zy_mul_regs map nth_error rshape rcells rw rfree] in HN;injection HN as <-.
  cbn [rshape rcells rw rfree fst map cshape cofs cchunk u64_cells vars5 app In] in HC.
  repeat match type of HC with _ \/ _ => destruct HC as [HC|HC] end;
    try contradiction;inversion HC;subst d ch;cbn [bas lay nth snd] in HO;
    change (size_chunk Mint64) with 8 in HO;lia.
Qed.

Theorem eval_point_zy_mul_owned z y m b :
  square_input_bounds z -> square_input_bounds y ->
  fe_at m b 80 (words5 z) -> fe_at m b 40 (words5 y) -> Mem.range_perm m b 0 128 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr b (Ptrofs.repr 80);Vptr b (Ptrofs.repr 80);Vptr b (Ptrofs.repr 40)] E0 mf Vundef /\
  fe_at mf b 80 (words5 (point_mul_words z y)) /\ fe_at mf b 40 (words5 y) /\
  Mem.range_perm mf b 0 128 Cur Freeable /\
  radix_value (point_mul_words z y) mod feP=(radix_value z*radix_value y) mod feP /\
  square_input_bounds (point_mul_words z y) /\
  (forall i, (i<5)%nat -> Int64.unsigned (point_mul_words z y i)<
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) /\
  lframe (fun bx pos => bx<>b \/ pos<40 \/ 120<=pos) m mf.
Proof.
  intros BZ BY HZ HY HF.
  destruct (eval_point_zy_mul_symbolic (point_mul_valuation z y) [(b,0)] m
    (point_zy_mul_initial z y m b HZ HY HF) (fm_solves _ _ _ _ _ _ _ _ _ _))
    as (mf & HC & HR & HL).
  destruct (point_zy_mul_fields z y [(b,0)] mf HR) as (FZ & FY & FF).
  destruct (curve_mul_value_bounds z y (field_operand_from_bounds z BZ)
    (field_operand_from_bounds y BY)) as [HV HB].
  exists mf;split;[exact HC|]. split;[exact FZ|]. split;[exact FY|]. split;[exact FF|].
  split;[exact HV|]. split;[exact (proj2 (point_mul_value_and_bounds z y BZ BY))|].
  split;[exact HB|]. eapply lframe_implies;[exact HL|].
  intros bx pos HOutside HValid HFoot;destruct (point_zy_mul_foot b bx pos HFoot) as [HE HP].
  destruct HOutside as [HOutside|[HOutside|HOutside]];[congruence|lia|lia].
Qed.
