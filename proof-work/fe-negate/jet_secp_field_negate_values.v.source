(** Exact machine outputs of the original magnitude-one C helper.
    No canonical jet equivalence is claimed by this intermediate result. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep.
Require Import C.jet_secp_field_negate.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_local_regions.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition negate_mask (n : nat) : Z :=
  match n with
  | O => 4503595332402223
  | S (S (S (S O))) => 281474976710655
  | _ => 4503599627370495
  end.
Definition negate_limb_expr (n : nat) : sx :=
  XLb Bsub
    (XLb Bmul
      (XLb Bmul (XLc (Int64.repr (negate_mask n)))
        (XI2L Signed (XIc (Int.repr 2))))
      (XI2L Signed (XIb Badd (XIc Int.one) (XIc Int.one))))
    (XLv (S n)).
Definition negate_value (rho : nat -> int64) (n : nat) : int64 :=
  Int64.sub (Int64.repr (4 * negate_mask n)) (rho (S n)).

Lemma negate_cell_present n : (n < 5)%nat ->
  In (mkcell (8 * Z.of_nat n) Mint64 (Some (negate_limb_expr n)))
    (rcells (hd (mkreg [] true None) (sregs field_negate_state))).
Proof.
  intro H.
  do 5 (destruct n as [|n]; [cbn; tauto|]). lia.
Qed.

Lemma negate_expr_value rho beta n : (n < 5)%nat ->
  den rho beta (negate_limb_expr n) = Vlong (negate_value rho n).
Proof.
  intro H.
  do 5 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Theorem field_negate_rep_loads m layout rho :
  rep rho layout (sregs field_negate_state) m ->
  forall n, (n < 5)%nat ->
  Mem.load Mint64 m (blk layout 0) (bas layout 0 + 8 * Z.of_nat n) =
    Some (Vlong (negate_value rho n)).
Proof.
  intros HRep n Hn.
  pose proof (rep_region rho layout _ m 0 _ HRep eq_refl) as HRegion.
  pose proof (region_load rho layout m 0 _ _ _ _ HRegion
    (negate_cell_present n Hn)) as HLoad.
  rewrite (negate_expr_value rho (lay layout) n Hn) in HLoad.
  exact HLoad.
Qed.
Print Assumptions field_negate_rep_loads.

Theorem eval_field_negate_with_values m layout rho :
  rep rho layout local_write_initial_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_negate)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
       Vptr (blk layout 0) (Ptrofs.repr (bas layout 0)); Vint Int.one]
      E0 mf Vundef /\
    rep rho layout (sregs field_negate_state) mf /\
    (forall n, (n < 5)%nat ->
      Mem.load Mint64 mf (blk layout 0) (bas layout 0 + 8 * Z.of_nat n) =
        Some (Vlong (negate_value rho n))) /\
    map rshape (sregs field_negate_state) = map rshape local_write_initial_regs /\
    lframe (fun b pos => ~ foot layout (map rshape local_write_initial_regs) b pos) m mf.
Proof.
  intro HRep.
  destruct (eval_field_negate_from_owned_region m layout rho HRep)
    as (mf & HCall & HFinal & HShape & HFrame).
  exists mf. split; [exact HCall|]. split; [exact HFinal|].
  split; [apply field_negate_rep_loads; exact HFinal|].
  split; assumption.
Qed.
Print Assumptions eval_field_negate_with_values.

Lemma unsigned_sub_constant c x :
  0 <= c <= Int64.max_unsigned -> Int64.unsigned x <= c ->
  Int64.unsigned (Int64.sub (Int64.repr c) x) = c - Int64.unsigned x.
Proof.
  intros Hc Hx. unfold Int64.sub.
  rewrite (Int64.unsigned_repr c) by exact Hc.
  rewrite Int64.unsigned_repr; [reflexivity|].
  pose proof (Int64.unsigned_range_2 x). lia.
Qed.

Lemma negate_mask_range n : (n < 5)%nat ->
  4503599627370495 <= 4 * negate_mask n <= Int64.max_unsigned \/
  n = 4%nat /\ 281474976710655 <= 4 * negate_mask n <= Int64.max_unsigned.
Proof.
  intro H. change Int64.max_unsigned with 18446744073709551615.
  do 5 (destruct n as [|n]; [cbn [negate_mask]; lia|]). lia.
Qed.

Lemma negate_value_unsigned rho n : (n < 5)%nat ->
  Int64.unsigned (rho (S n)) <=
    (if Nat.eqb n 4 then 281474976710655 else 4503599627370495) ->
  Int64.unsigned (negate_value rho n) =
    4 * negate_mask n - Int64.unsigned (rho (S n)).
Proof.
  intros Hn HInput. unfold negate_value. apply unsigned_sub_constant.
  - destruct (negate_mask_range n Hn) as [H|[_ H]]; lia.
  - destruct (negate_mask_range n Hn) as [H|[-> H]]; [|cbn in HInput; lia].
    destruct (Nat.eqb n 4); lia.
Qed.
Print Assumptions negate_value_unsigned.
