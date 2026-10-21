(** Original in-place field multiplication from a 40-byte curve temporary and
    the X field of the actual 88-byte affine input. Reuses proved u128 oracles. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_local_regions.
Require Import C.jet_secp_u128_word_oracle C.jet_secp_field_mul_word_model C.jet_secp_point_mul_run.
Require Import C.jet_secp_fe_math C.jet_secp_field_add_initial C.jet_sx_revalue_cells.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_point_mul_storage.
Require Import C.jet_secp_b32_exec.
Require Import C.jet_secp_field_mul_word_math C.jet_secp_multiply_finish_product.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition curve_mul_regs : list region :=
  [free_region (fe_reg (vars5 0)) 40; free_region (fe_reg (vars5 5)) 88].
Definition curve_mul_args := [XP 0 0; XP 0 0; XP 1 0].
Definition curve_mul_run := xfun (genv_cenv secp_ge) [] point_mul_table 400
  f_secp256k1_fe_mul curve_mul_args curve_mul_regs [] 10.
Definition curve_mul_tree := Eval vm_compute in curve_mul_run.
Definition curve_mul_state := match curve_mul_tree with
  | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition curve_mul_out_regs :=
  [mkreg (u64_cells 0 point_mul_out) true (Some 40); free_region (fe_reg (vars5 5)) 88].

Lemma curve_mul_run_eq : curve_mul_run = Some (RDone curve_mul_state ONormal).
Proof. reflexivity. Qed.
Lemma curve_mul_log_eq : slog curve_mul_state = fe_mul_log.
Proof. reflexivity. Qed.
Lemma curve_mul_out_eq : sregs curve_mul_state = curve_mul_out_regs.
Proof. reflexivity. Qed.
Lemma curve_mul_return : (stemps curve_mul_state)!1%positive = None.
Proof. reflexivity. Qed.

Local Opaque curve_mul_state.
Theorem eval_curve_mul_symbolic rho beta m :
  rep rho beta curve_mul_regs m -> Forall (u128_evok rho) fe_mul_log -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
     Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
     Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))] E0 mf Vundef /\
  rep rho beta curve_mul_out_regs mf /\
  lframe (fun b ofs => ~ foot beta (map rshape curve_mul_regs) b ofs) m mf.
Proof.
  intros HR HSol.
  destruct (xfun_top_sound secp_ge [] point_mul_table u128_evok u128_inv u128_ext
    ltac:(intros; exact I) ltac:(intros; contradiction) point_mul_table_ok
    400 f_secp256k1_fe_mul curve_mul_args curve_mul_regs [] 10
    (RDone curve_mul_state ONormal) curve_mul_run_eq rho beta m HR)
    as (mf & vres & HC & HP & HV & HS & _ & HF).
  - split; intros; discriminate.
  - intros r _ HE; exact HE.
  - exact I.
  - cbn [rsel fst]; rewrite curve_mul_log_eq; exact HSol.
  - cbn [rsel fst] in HP, HV, HS; rewrite curve_mul_return in HV; subst vres.
    rewrite curve_mul_out_eq in HP.
    change (map (den rho (lay beta)) curve_mul_args) with
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0 + 0));
       Vptr (blk beta 0) (Ptrofs.repr (bas beta 0 + 0));
       Vptr (blk beta 1) (Ptrofs.repr (bas beta 1 + 0))] in HC.
    rewrite !Z.add_0_r in HC.
    exists mf; split; [exact HC|]. split; [exact HP|].
    eapply lframe_implies; [exact HF|].
    intros b ofs HOutside HValid; split; [exact HValid|]. split; [exact HOutside|intros HE; exact HE].
Qed.

Lemma curve_mul_initial a b m bout bin :
  bout <> bin -> fe_at m bout 0 (words5 a) -> Mem.range_perm m bout 0 40 Cur Freeable ->
  fe_at m bin 0 (words5 b) -> Mem.range_perm m bin 0 88 Cur Freeable ->
  rep (point_mul_valuation a b) [(bout,0);(bin,0)] curve_mul_regs m.
Proof.
  intros HNe HA HFA HB HFB.
  apply two_region_rep_separate; [reflexivity|exact HNe| |].
  - apply owned_field_slice_region; [reflexivity|lia|lia| |exact HFA].
    rewrite point_mul_valuation_first; exact HA.
  - apply region_with_freeable.
    + apply field_region_from_values; rewrite point_mul_valuation_second; exact HB.
    + reflexivity.
    + reflexivity.
    + exact HFB.
    + repeat constructor; cbn; lia.
Qed.

Lemma curve_mul_fields a b layout m :
  rep (point_mul_valuation a b) layout curve_mul_out_regs m ->
  fe_at m (blk layout 0) (bas layout 0) (words5 (point_mul_words a b)) /\
  Mem.range_perm m (blk layout 0) 0 40 Cur Freeable /\
  fe_at m (blk layout 1) (bas layout 1) (words5 b) /\
  Mem.range_perm m (blk layout 1) 0 88 Cur Freeable.
Proof.
  intro HR.
  pose proof (rep_region _ _ _ m 0 _ HR eq_refl) as H0.
  pose proof (rep_region _ _ _ m 1 _ HR eq_refl) as H1.
  pose proof H0 as (_ & _ & _ & _ & _ & _ & HF0 & _).
  pose proof H1 as (_ & _ & _ & _ & _ & _ & HF1 & _).
  split.
  - pose proof (region_ok_revalue_u64 _ _ _ _ point_mul_out true (Some 40) H0 eq_refl) as HV.
    rewrite (revalue_u64_machine_map _ _ _ _ (point_mul_output_den a b layout)) in HV.
    eapply u64_region_fe_at; exact HV.
  - split; [exact HF0|]. split; [|exact HF1].
    pose proof (region_ok_revalue_u64 _ _ _ _ (vars5 5) true (Some 88) H1 eq_refl) as HV.
    assert (HD : map (den (point_mul_valuation a b) (lay layout)) (vars5 5) = map Vlong (words5 b))
      by reflexivity.
    rewrite (revalue_u64_machine_map _ _ _ _ HD) in HV.
    eapply u64_region_fe_at; exact HV.
Qed.

Theorem eval_curve_mul_from_storage a b m bout bin :
  bout <> bin -> fe_at m bout 0 (words5 a) -> Mem.range_perm m bout 0 40 Cur Freeable ->
  fe_at m bin 0 (words5 b) -> Mem.range_perm m bin 0 88 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr bout Ptrofs.zero; Vptr bout Ptrofs.zero; Vptr bin Ptrofs.zero] E0 mf Vundef /\
  fe_at mf bout 0 (words5 (point_mul_words a b)) /\
  Mem.range_perm mf bout 0 40 Cur Freeable /\
  fe_at mf bin 0 (words5 b) /\ Mem.range_perm mf bin 0 88 Cur Freeable /\
  lframe (fun bx pos => ~ foot [(bout,0);(bin,0)] (map rshape curve_mul_regs) bx pos) m mf.
Proof.
  intros HNe HA HFA HB HFB.
  pose proof (curve_mul_initial a b m bout bin HNe HA HFA HB HFB) as HR.
  assert (HSol : Forall (u128_evok (point_mul_valuation a b)) fe_mul_log) by (apply fm_solves).
  destruct (eval_curve_mul_symbolic (point_mul_valuation a b) [(bout,0);(bin,0)] m HR HSol)
    as (mf & HC & HP & HF).
  destruct (curve_mul_fields a b [(bout,0);(bin,0)] mf HP) as (HO & HFO & HI & HFI).
  exists mf; split; [exact HC|]. split; [exact HO|]. split; [exact HFO|].
  split; [exact HI|]. split; assumption.
Qed.

Lemma curve_mul_value_bounds a b :
  field_mul_operand_ok (Int64.unsigned (a 0%nat)) (Int64.unsigned (a 1%nat))
    (Int64.unsigned (a 2%nat)) (Int64.unsigned (a 3%nat)) (Int64.unsigned (a 4%nat)) ->
  field_mul_operand_ok (Int64.unsigned (b 0%nat)) (Int64.unsigned (b 1%nat))
    (Int64.unsigned (b 2%nat)) (Int64.unsigned (b 3%nat)) (Int64.unsigned (b 4%nat)) ->
  radix_value (point_mul_words a b) mod feP = (radix_value a * radix_value b) mod feP /\
  (forall i, (i < 5)%nat -> Int64.unsigned (point_mul_words a b i) <
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496).
Proof.
  intros HA HB.
  destruct (fm_mul_values (a 0%nat) (a 1%nat) (a 2%nat) (a 3%nat) (a 4%nat)
    (b 0%nat) (b 1%nat) (b 2%nat) (b 3%nat) (b 4%nat) HA HB)
    as (B0 & B1 & B2 & B3 & B4 & HV).
  split.
  - rewrite !radix_value_matches_normalizer; exact HV.
  - intros i HI; destruct i as [|[|[|[|[|i]]]]]; try lia;
      cbn [point_mul_words nth Nat.eqb]; lia.
Qed.

Theorem eval_curve_mul_numeric a b m bout bin :
  field_mul_operand_ok (Int64.unsigned (a 0%nat)) (Int64.unsigned (a 1%nat))
    (Int64.unsigned (a 2%nat)) (Int64.unsigned (a 3%nat)) (Int64.unsigned (a 4%nat)) ->
  field_mul_operand_ok (Int64.unsigned (b 0%nat)) (Int64.unsigned (b 1%nat))
    (Int64.unsigned (b 2%nat)) (Int64.unsigned (b 3%nat)) (Int64.unsigned (b 4%nat)) ->
  bout <> bin -> fe_at m bout 0 (words5 a) -> Mem.range_perm m bout 0 40 Cur Freeable ->
  fe_at m bin 0 (words5 b) -> Mem.range_perm m bin 0 88 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr bout Ptrofs.zero; Vptr bout Ptrofs.zero; Vptr bin Ptrofs.zero] E0 mf Vundef /\
  fe_at mf bout 0 (words5 (point_mul_words a b)) /\
  Mem.range_perm mf bout 0 40 Cur Freeable /\
  fe_at mf bin 0 (words5 b) /\ Mem.range_perm mf bin 0 88 Cur Freeable /\
  radix_value (point_mul_words a b) mod feP = (radix_value a * radix_value b) mod feP /\
  (forall i, (i < 5)%nat -> Int64.unsigned (point_mul_words a b i) <
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) /\
  lframe (fun bx pos => ~ foot [(bout,0);(bin,0)] (map rshape curve_mul_regs) bx pos) m mf.
Proof.
  intros BA BB HNe HA HFA HB HFB.
  destruct (eval_curve_mul_from_storage a b m bout bin HNe HA HFA HB HFB)
    as (mf & HC & HO & HFO & HI & HFI & HF).
  destruct (curve_mul_value_bounds a b BA BB) as [HV HBounds].
  exists mf. split; [exact HC|]. split; [exact HO|]. split; [exact HFO|].
  split; [exact HI|]. split; [exact HFI|]. split; [exact HV|]. split; assumption.
Qed.
