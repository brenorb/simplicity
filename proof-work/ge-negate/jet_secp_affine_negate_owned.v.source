(** Magnitude-one negation of actual reader limbs in the 88-byte affine object. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_local_regions.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_write_fe_numeric.
Require Import C.jet_secp_field_negate_values C.jet_secp_field_negate_storage.
Require Import C.jet_secp_affine_weak_exec C.jet_secp_affine_weak_owned C.jet_secp_affine_negate_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma affine_negate_cell_present k n : (n < 5)%nat ->
  In (mkcell (affine_coordinate_offset k + 8*Z.of_nat n) Mint64 (Some (negate_limb_expr n)))
    (rcells (hd (mkreg [] true None) (sregs (affine_negate_state k)))).
Proof.
  intro H; do 5 (destruct n as [|n]; [destruct k; cbn; tauto|]); lia.
Qed.

Lemma affine_negate_rep_loads k m layout rho :
  rep rho layout (sregs (affine_negate_state k)) m -> forall n, (n < 5)%nat ->
  Mem.load Mint64 m (blk layout 0) (bas layout 0 + (affine_coordinate_offset k + 8*Z.of_nat n)) =
    Some (Vlong (negate_value rho n)).
Proof.
  intros HRep n Hn.
  assert (HE : nth_error (sregs (affine_negate_state k)) 0 =
    Some (hd (mkreg [] true None) (sregs (affine_negate_state k)))).
  { destruct k; reflexivity. }
  pose proof (rep_region rho layout _ m 0 _ HRep HE) as HRegion.
  pose proof (region_load rho layout m 0 _ _ _ _ HRegion
    (affine_negate_cell_present k n Hn)) as HL.
  rewrite negate_expr_value in HL by exact Hn; exact HL.
Qed.

Theorem eval_affine_negate_reader_owned k m b value :
  fe_at m b (affine_coordinate_offset k) (map Int64.repr (fe_limbs_of value)) ->
  Mem.range_perm m b 0 88 Cur Freeable ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_negate)
      [Vptr b (Ptrofs.repr (affine_coordinate_offset k));
       Vptr b (Ptrofs.repr (affine_coordinate_offset k)); Vint Int.one] E0 mf Vundef /\
    fe_at mf b (affine_coordinate_offset k) (negate_values (write_fe_rho value 0)) /\
    Mem.range_perm mf b 0 88 Cur Freeable /\
    lframe (fun bx pos => ~ foot [(b,0)] (map rshape (affine_initial_regs k)) bx pos) m mf.
Proof.
  intros HField HFree.
  pose proof (affine_reader_initial_rep k value 0 m b HField HFree) as HInitial.
  destruct (eval_affine_negate_from_owned_region k m [(b,0)] (write_fe_rho value 0) HInitial)
    as (mf & HCall & HFinal & HFrame).
  assert (HI : (0 < length (sregs (affine_negate_state k)))%nat).
  { destruct k; change (0 < 1)%nat; lia. }
  pose proof (proj2 (rep_free_region _ _ _ _ 0 88 HFinal HI (affine_negate_owned_size k))) as HFinalFree.
  change (Mem.range_perm mf b 0 88 Cur Freeable) in HFinalFree.
  pose proof (affine_negate_rep_loads k mf [(b,0)] (write_fe_rho value 0) HFinal) as HLoads.
  exists mf; split; [exact HCall|]. split; [|split; assumption].
  destruct HField as (HB & HA & HM & HP & HL).
  split; [exact HB|]. split; [exact HA|]. split; [exact HM|]. split.
  - apply freeable_range_writable; intros pos HPos.
    apply HFinalFree; pose proof (affine_coordinate_offset_bounds k); lia.
  - intros i x HNth.
    assert (HIndex : (i < 5)%nat).
    { change (i < length (negate_values (write_fe_rho value 0)))%nat.
      apply (proj1 (nth_error_Some _ _)); rewrite HNth; discriminate. }
    specialize (HLoads i HIndex).
    assert (HX : x = negate_value (write_fe_rho value 0) i).
    { do 5 (destruct i as [|i]; [inversion HNth; reflexivity|]); lia. }
    rewrite HX; exact HLoads.
Qed.
Timeout 60 Print Assumptions eval_affine_negate_reader_owned.
