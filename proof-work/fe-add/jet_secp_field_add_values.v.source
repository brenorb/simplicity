(** Exact machine outputs of the original two-field C addition helper.
    No canonical jet equivalence is claimed by this intermediate result. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep.
Require Import C.jet_secp_field_add.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_local_regions.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition add_limb_expr (n : nat) : sx :=
  XLb Badd (XLv (S n)) (XLv ((6 + n)%nat)).
Definition add_value (rho : nat -> int64) (n : nat) : int64 :=
  Int64.add (rho (S n)) (rho ((6 + n)%nat)).

Lemma add_cell_present n : (n < 5)%nat ->
  In (mkcell (8 * Z.of_nat n) Mint64 (Some (add_limb_expr n)))
    (rcells (hd (mkreg [] true None) (sregs field_add_state))).
Proof.
  intro H.
  do 5 (destruct n as [|n]; [cbn; tauto|]). lia.
Qed.

Lemma add_expr_value rho beta n : (n < 5)%nat ->
  den rho beta (add_limb_expr n) = Vlong (add_value rho n).
Proof.
  intro H.
  do 5 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Theorem field_add_rep_loads m layout rho :
  rep rho layout (sregs field_add_state) m ->
  forall n, (n < 5)%nat ->
  Mem.load Mint64 m (blk layout 0) (bas layout 0 + 8 * Z.of_nat n) =
    Some (Vlong (add_value rho n)).
Proof.
  intros HRep n Hn.
  pose proof (rep_region rho layout _ m 0 _ HRep eq_refl) as HRegion.
  pose proof (region_load rho layout m 0 _ _ _ _ HRegion
    (add_cell_present n Hn)) as HLoad.
  rewrite (add_expr_value rho (lay layout) n Hn) in HLoad.
  exact HLoad.
Qed.
Print Assumptions field_add_rep_loads.

Theorem eval_field_add_with_values m layout rho :
  rep rho layout field_add_initial_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
       Vptr (blk layout 1) (Ptrofs.repr (bas layout 1))]
      E0 mf Vundef /\
    rep rho layout (sregs field_add_state) mf /\
    (forall n, (n < 5)%nat ->
      Mem.load Mint64 mf (blk layout 0) (bas layout 0 + 8 * Z.of_nat n) =
        Some (Vlong (add_value rho n))) /\
    map rshape (sregs field_add_state) = map rshape field_add_initial_regs /\
    lframe (fun b pos => ~ foot layout (map rshape field_add_initial_regs) b pos) m mf.
Proof.
  intro HRep.
  destruct (eval_field_add_from_owned_region m layout rho HRep)
    as (mf & HCall & HFinal & HShape & HFrame).
  exists mf. split; [exact HCall|]. split; [exact HFinal|].
  split; [apply field_add_rep_loads; exact HFinal|].
  split; assumption.
Qed.
Print Assumptions eval_field_add_with_values.

Lemma add_value_unsigned rho n :
  Int64.unsigned (rho (S n)) <= 2 ^ 52 - 1 ->
  Int64.unsigned (rho ((6 + n)%nat)) <= 2 ^ 52 - 1 ->
  Int64.unsigned (add_value rho n) =
    Int64.unsigned (rho (S n)) + Int64.unsigned (rho ((6 + n)%nat)).
Proof.
  intros HA HB. unfold add_value, Int64.add.
  rewrite Int64.unsigned_repr; [reflexivity|].
  pose proof (Int64.unsigned_range_2 (rho (S n))).
  pose proof (Int64.unsigned_range_2 (rho ((6 + n)%nat))).
  change Int64.max_unsigned with 18446744073709551615.
  change (2 ^ 52 - 1) with 4503599627370495 in HA, HB.
  lia.
Qed.

Lemma add_value_wide_bound rho n :
  Int64.unsigned (rho (S n)) <= 2 ^ 52 - 1 ->
  Int64.unsigned (rho ((6 + n)%nat)) <= 2 ^ 52 - 1 ->
  0 <= Int64.unsigned (add_value rho n) < 2 ^ 60.
Proof.
  intros HA HB. rewrite add_value_unsigned by assumption.
  pose proof (Int64.unsigned_range_2 (rho (S n))).
  pose proof (Int64.unsigned_range_2 (rho ((6 + n)%nat))).
  change (2 ^ 52 - 1) with 4503599627370495 in HA, HB.
  change (2 ^ 60) with 1152921504606846976. lia.
Qed.
Print Assumptions add_value_unsigned.
Print Assumptions add_value_wide_bound.
