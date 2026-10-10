(** Retain exact field storage through the original read-only zero helper. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Word.
Require Simplicity.Ty Simplicity.Alg Simplicity.Bit.
Require Import C.jet_toZ C.jet_word_repr C.jet_readBit_layout.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_local_regions C.jet_secp_write_fe_numeric C.jet_secp_b32_exec.
Require Import C.jet_secp_canonical_normalize C.jet_secp_canonical_zero C.jet_secp_zero_numeric.
Require Import C.jet_secp_point_write_run C.jet_secp_point_zero_exec C.jet_secp_point_zero_owned.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_normalize canonical_fe_is_zero.

Lemma point_initial_cell_present k n : (n < 5)%nat ->
  In (mkcell (point_coordinate_offset k+8*Z.of_nat n) Mint64 (Some (XLv (S n))))
    (rcells (hd (mkreg [] true None) (point_write_initial_regs k))).
Proof. intro H; do 5 (destruct n as [|n]; [destruct k; cbn; tauto|]); lia. Qed.

Lemma point_initial_rep_loads k m layout rho :
  rep rho layout (point_write_initial_regs k) m -> forall n, (n < 5)%nat ->
  Mem.load Mint64 m (blk layout 0) (bas layout 0+(point_coordinate_offset k+8*Z.of_nat n)) =
    Some (Vlong (rho (S n))).
Proof.
  intros HRep n Hn.
  pose proof (rep_region rho layout _ m 0 _ HRep eq_refl) as HR.
  exact (region_load rho layout m 0 _ _ _ _ HR (point_initial_cell_present k n Hn)).
Qed.

Theorem eval_point_zero_canonical_preserved k m b (value : Ty.tySem (Word 8)) :
  fe_at m b (point_coordinate_offset k) (map Int64.repr (fe_limbs_of
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)))) ->
  Mem.range_perm m b 0 128 Cur Freeable ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_is_zero)
      [Vptr b (Ptrofs.repr (point_coordinate_offset k))] E0 mf
      (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem value)))) /\
    fe_at mf b (point_coordinate_offset k) (map Int64.repr (fe_limbs_of
      (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)))) /\
    Mem.range_perm mf b 0 128 Cur Freeable /\
    lframe (fun bx pos => ~ foot [(b,0)] (map rshape (point_write_initial_regs k)) bx pos) m mf.
Proof.
  intros HField HFree.
  set (v := @toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)).
  pose proof (point_zero_initial_rep k v 0 m b HField HFree) as HRep.
  destruct (eval_point_zero_from_owned_region k m [(b,0)] (write_fe_rho v 0) HRep)
    as (mf & HCall & HFinal & HFrame).
  assert (HBounds : 0 <= v < 2^256) by (unfold v; apply word_toZ_range).
  rewrite (field_or_canonical_zero v 0 HBounds) in HCall.
  unfold v in HCall; rewrite canonical_fe_zero_after_normalize in HCall.
  pose proof (proj2 (rep_free_region _ _ _ _ 0 128 HFinal ltac:(cbn;lia) eq_refl)) as HFinalFree.
  change (Mem.range_perm mf b 0 128 Cur Freeable) in HFinalFree.
  pose proof (point_initial_rep_loads k mf [(b,0)] (write_fe_rho v 0) HFinal) as HLoads.
  exists mf; split; [exact HCall|]; split; [|split; assumption].
  destruct HField as (HB & HA & HM & HP & HL).
  split; [exact HB|]; split; [exact HA|]; split; [exact HM|]; split.
  - apply freeable_range_writable; intros pos HPos.
    apply HFinalFree; pose proof (point_coordinate_offset_bounds k); lia.
  - intros i x HNth.
    assert (HIndex : (i < 5)%nat).
    { change (i < length (map Int64.repr (fe_limbs_of v)))%nat.
      apply (proj1 (nth_error_Some _ _)); rewrite HNth; discriminate. }
    specialize (HLoads i HIndex).
    change (Mem.load Mint64 mf b (point_coordinate_offset k+8*Z.of_nat i) =
      Some (Vlong (limb_rho v i))) in HLoads.
    rewrite nth_error_map in HNth.
    destruct (nth_error (fe_limbs_of v) i) as [z|] eqn:HZ; [|discriminate].
    inversion HNth; subst x.
    apply nth_error_nth with (d := 0) in HZ.
    unfold limb_rho in HLoads; rewrite HZ in HLoads; exact HLoads.
Qed.
Timeout 60 Print Assumptions eval_point_zero_canonical_preserved.
