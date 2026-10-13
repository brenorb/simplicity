(** Original weak normalization on reader-produced limbs in an owned point.
    This discharges interval bounds internally; the public jet is still separate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_b32_exec.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_local_regions C.jet_secp_write_fe_numeric.
Require Import C.jet_secp_point_write_run C.jet_secp_point_write_preservation C.jet_secp_point_zero_owned.
Require Import C.jet_secp_point_weak_exec C.jet_secp_point_weak_values C.jet_secp_point_weak_loads.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma point_weak_reader_bounds value :
  0 <= value < 2^256 -> forall n,
  fst (point_weak_bounds n) <= Int64.unsigned (write_fe_rho value 0 n) <= snd (point_weak_bounds n).
Proof.
  intros HV [|n]; [split; discriminate|].
  change (0 <= Int64.unsigned (limb_rho value n) <=
    (if Nat.eqb (S n) 5 then 281474976710655 else 4503599627370495)).
  rewrite limb_rho_unsigned by exact HV.
  pose proof (proj1 (fe_limbs_of_ok value HV)) as HB.
  unfold fe_limbs_ok in HB.
  do 5 (destruct n as [|n]; [cbn [nth fe_limbs_of Nat.eqb]; lia|]).
  cbn [nth fe_limbs_of Nat.eqb]; destruct n; split; discriminate.
Qed.

Theorem eval_point_weak_reader_owned k m b value :
  0 <= value < 2^256 ->
  fe_at m b (point_coordinate_offset k) (map Int64.repr (fe_limbs_of value)) ->
  Mem.range_perm m b 0 128 Cur Freeable ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalize_weak)
      [Vptr b (Ptrofs.repr (point_coordinate_offset k))] E0 mf Vundef /\
    fe_at mf b (point_coordinate_offset k) (map Int64.repr (fe_limbs_of value)) /\
    Mem.range_perm mf b 0 128 Cur Freeable /\
    lframe (fun bx pos => ~ foot [(b,0)] (map rshape (point_write_initial_regs k)) bx pos) m mf.
Proof.
  intros HV HField HFree.
  pose proof (point_zero_initial_rep k value 0 m b HField HFree) as HInitial.
  destruct (eval_point_weak_from_owned_region k m [(b,0)] (write_fe_rho value 0) HInitial)
    as (mf & HCall & HFinal & HFrame).
  assert (HI : (0 < length (sregs (point_weak_state k)))%nat).
  { destruct k; change (0 < 1)%nat; lia. }
  assert (HF : rfree (nth 0 (sregs (point_weak_state k)) (mkreg [] true None)) = Some 128).
  { destruct k; reflexivity. }
  pose proof (proj2 (rep_free_region _ _ _ _ 0 128 HFinal HI HF)) as HFinalFree.
  change (Mem.range_perm mf b 0 128 Cur Freeable) in HFinalFree.
  pose proof (point_weak_rep_preserved_loads k mf [(b,0)] (write_fe_rho value 0)
    (point_weak_reader_bounds value HV) HFinal) as HLoads.
  exists mf; split; [exact HCall|]. split; [|split; assumption].
  destruct HField as (HB & HA & HM & HP & HL).
  split; [exact HB|]. split; [exact HA|]. split; [exact HM|]. split.
  - apply freeable_range_writable; intros pos HPos.
    apply HFinalFree; pose proof (point_coordinate_offset_bounds k); lia.
  - intros i x HNth.
    assert (HIndex : (i < 5)%nat).
    { change (i < length (map Int64.repr (fe_limbs_of value)))%nat.
      apply (proj1 (nth_error_Some _ _)); rewrite HNth; discriminate. }
    specialize (HLoads i HIndex).
    change (Mem.load Mint64 mf b (point_coordinate_offset k + 8*Z.of_nat i) =
      Some (Vlong (limb_rho value i))) in HLoads.
    rewrite nth_error_map in HNth.
    destruct (nth_error (fe_limbs_of value) i) as [z|] eqn:HZ; [|discriminate].
    inversion HNth; subst x.
    apply nth_error_nth with (d := 0) in HZ.
    unfold limb_rho in HLoads; rewrite HZ in HLoads.
    exact HLoads.
Qed.
Timeout 60 Print Assumptions eval_point_weak_reader_owned.
