(** Actual weak normalization on reader-produced limbs in an 88-byte affine object. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_b32_exec.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_local_regions C.jet_secp_write_fe_numeric.
Require Import C.jet_secp_write_fe_wide_values C.jet_secp_point_write_run C.jet_secp_point_write_preservation.
Require Import C.jet_secp_point_zero_owned C.jet_secp_point_weak_owned.
Require Import C.jet_secp_owned_field_slice C.jet_secp_affine_weak_exec C.jet_secp_affine_weak_loads.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma affine_coordinate_offset_bounds k : 0 <= affine_coordinate_offset k <= 40.
Proof. destruct k; split; discriminate. Qed.

Lemma affine_reader_initial_rep k value rc m b :
  fe_at m b (affine_coordinate_offset k) (map Int64.repr (fe_limbs_of value)) ->
  Mem.range_perm m b 0 88 Cur Freeable ->
  rep (write_fe_rho value rc) [(b,0)] (affine_initial_regs k) m.
Proof.
  intros HField HFree; rewrite <- point_canonical_write_rho.
  change (rep (wide_fe_rho (limb_rho value 0) (limb_rho value 1) (limb_rho value 2)
    (limb_rho value 3) (limb_rho value 4) rc) [(b,0)]
    (owned_field_slice (affine_coordinate_offset k) 88) m).
  apply owned_field_slice_initial_rep.
  - pose proof (affine_coordinate_offset_bounds k); lia.
  - exact HField.
  - exact HFree.
Qed.

Theorem eval_affine_weak_reader_owned k m b value :
  0 <= value < 2^256 ->
  fe_at m b (affine_coordinate_offset k) (map Int64.repr (fe_limbs_of value)) ->
  Mem.range_perm m b 0 88 Cur Freeable ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalize_weak)
      [Vptr b (Ptrofs.repr (affine_coordinate_offset k))] E0 mf Vundef /\
    fe_at mf b (affine_coordinate_offset k) (map Int64.repr (fe_limbs_of value)) /\
    Mem.range_perm mf b 0 88 Cur Freeable /\
    lframe (fun bx pos => ~ foot [(b,0)] (map rshape (affine_initial_regs k)) bx pos) m mf.
Proof.
  intros HV HField HFree.
  pose proof (affine_reader_initial_rep k value 0 m b HField HFree) as HInitial.
  destruct (eval_affine_weak_retains_freeable k m [(b,0)] (write_fe_rho value 0) HInitial)
    as (mf & HCall & HFinal & HFinalFree & HFrame).
  change (Mem.range_perm mf b 0 88 Cur Freeable) in HFinalFree.
  pose proof (affine_weak_rep_preserved_loads k mf [(b,0)] (write_fe_rho value 0)
    (point_weak_reader_bounds value HV) HFinal) as HLoads.
  exists mf; split; [exact HCall|]. split; [|split; assumption].
  destruct HField as (HB & HA & HM & HP & HL).
  split; [exact HB|]. split; [exact HA|]. split; [exact HM|]. split.
  - apply freeable_range_writable; intros pos HPos.
    apply HFinalFree; pose proof (affine_coordinate_offset_bounds k); lia.
  - intros i x HNth.
    assert (HIndex : (i < 5)%nat).
    { change (i < length (map Int64.repr (fe_limbs_of value)))%nat.
      apply (proj1 (nth_error_Some _ _)); rewrite HNth; discriminate. }
    specialize (HLoads i HIndex).
    change (Mem.load Mint64 mf b (affine_coordinate_offset k + 8*Z.of_nat i) =
      Some (Vlong (limb_rho value i))) in HLoads.
    rewrite nth_error_map in HNth.
    destruct (nth_error (fe_limbs_of value) i) as [z|] eqn:HZ; [|discriminate].
    inversion HNth; subst x.
    apply nth_error_nth with (d := 0) in HZ.
    unfold limb_rho in HLoads; rewrite HZ in HLoads; exact HLoads.
Qed.
Timeout 60 Print Assumptions eval_affine_weak_reader_owned.
