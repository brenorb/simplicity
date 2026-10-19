(** Numeric/machine interpretation of the original writer at general limb bounds. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_zval C.jet_sx_zrep.
Require Import C.jet_secp_write_fe_numeric C.jet_secp_write_fe_wide_checks.
Require Import C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_fe_b32 C.jet_secp_b32_exec.
Require Import C.jet_secp_symbolic_substitution.
Require Import C.jet_secp_frame.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wide_fe_rho t0 t1 t2 t3 t4 rc n : int64 :=
  match n with O => Int64.repr rc | S j => rho5 t0 t1 t2 t3 t4 j end.
Definition shifted_zrho (rho : nat -> int64) n := Int64.unsigned (rho (S n)).

Lemma wide_normalized_values rho state :
  map (zval (zrho rho))
    (map (fun c => sx_subst write_limb_shift (cell_sx c)) (cells0 state)) =
    zcells (shifted_zrho rho) (cells0 state).
Proof.
  rewrite map_map. unfold zcells. apply map_ext. intro c.
  destruct (cval c) as [x|] eqn:E.
  - unfold cell_sx. rewrite E, zval_sx_subst. reflexivity.
  - unfold cell_sx. rewrite E. reflexivity.
Qed.

Lemma wide_normalized_limbs_canonical t0 t1 t2 t3 t4 :
  Int64.unsigned t0 <= 2 ^ 60 -> Int64.unsigned t1 <= 2 ^ 60 ->
  Int64.unsigned t2 <= 2 ^ 60 -> Int64.unsigned t3 <= 2 ^ 60 ->
  Int64.unsigned t4 <= 2 ^ 60 ->
  nvz_list (Int64.unsigned t0) (Int64.unsigned t1) (Int64.unsigned t2)
    (Int64.unsigned t3) (Int64.unsigned t4) =
  fe_limbs_of (fe_val (Int64.unsigned t0) (Int64.unsigned t1)
    (Int64.unsigned t2) (Int64.unsigned t3) (Int64.unsigned t4) mod feP).
Proof.
  intros H0 H1 H2 H3 H4.
  pose proof (nvz_spec (Int64.unsigned t0) (Int64.unsigned t1)
    (Int64.unsigned t2) (Int64.unsigned t3) (Int64.unsigned t4)
    ltac:(pose proof (Int64.unsigned_range t0); lia)
    ltac:(pose proof (Int64.unsigned_range t1); lia)
    ltac:(pose proof (Int64.unsigned_range t2); lia)
    ltac:(pose proof (Int64.unsigned_range t3); lia)
    ltac:(pose proof (Int64.unsigned_range t4); lia)) as HSpec.
  unfold nvz_list.
  destruct (nvz (Int64.unsigned t0) (Int64.unsigned t1) (Int64.unsigned t2)
    (Int64.unsigned t3) (Int64.unsigned t4)) as [[[[r0 r1] r2] r3] r4].
  destruct HSpec as [HBounds HValue]. apply fe_limbs_unique; assumption.
Qed.

Lemma wide_normalized_variable rho state n :
  zval (zrho rho) (write_normalized_variables state n) =
  nth n (zcells (shifted_zrho rho) (cells0 state)) 0.
Proof.
  unfold write_normalized_variables.
  rewrite <- (map_nth (zval (zrho rho))
    (map (fun c => sx_subst write_limb_shift (cell_sx c)) (cells0 state)) (XLc Int64.zero) n).
  rewrite wide_normalized_values. reflexivity.
Qed.

Lemma wide_get_b32_substituted rho state :
  map (zval (zrho rho))
    (map (sx_subst (write_normalized_variables state)) (map cell_sx (cells0 gb_leaf))) =
  zcells (fun n => nth n (zcells (shifted_zrho rho) (cells0 state)) 0) (cells0 gb_leaf).
Proof.
  rewrite !map_map. unfold zcells at 2. apply map_ext. intro c.
  destruct (cval c) as [x|] eqn:E.
  - unfold cell_sx. rewrite E, zval_sx_subst.
    apply zval_ext. intro n. apply wide_normalized_variable.
  - unfold cell_sx. rewrite E. reflexivity.
Qed.

Lemma wide_fe_rho_bounds t0 t1 t2 t3 t4 rc :
  Int64.unsigned t0 <= 2 ^ 60 -> Int64.unsigned t1 <= 2 ^ 60 ->
  Int64.unsigned t2 <= 2 ^ 60 -> Int64.unsigned t3 <= 2 ^ 60 ->
  Int64.unsigned t4 <= 2 ^ 60 ->
  forall n, fst (wide_write_bounds n) <=
    Int64.unsigned (wide_fe_rho t0 t1 t2 t3 t4 rc n) <= snd (wide_write_bounds n).
Proof.
  intros H0 H1 H2 H3 H4 [|n].
  - apply Int64.unsigned_range_2.
  - change (0 <= Int64.unsigned (rho5 t0 t1 t2 t3 t4 n) <= 2 ^ 60).
    split; [apply Int64.unsigned_range|].
    unfold rho5. do 5 (destruct n as [|n]; [assumption|]).
    destruct n; change (0 <= 2 ^ 60); lia.
Qed.

Lemma shifted_wide_fe_rho t0 t1 t2 t3 t4 rc n :
  shifted_zrho (wide_fe_rho t0 t1 t2 t3 t4 rc) n =
  zrho5 (Int64.unsigned t0) (Int64.unsigned t1) (Int64.unsigned t2)
    (Int64.unsigned t3) (Int64.unsigned t4) n.
Proof.
  unfold shifted_zrho, wide_fe_rho, rho5, zrho5.
  do 5 (destruct n as [|n]; [reflexivity|]). destruct n; reflexivity.
Qed.

Lemma wide_write_condition rho bd base layout :
  (forall n, fst (wide_write_bounds n) <= Int64.unsigned (rho n) <= snd (wide_write_bounds n)) ->
  truth rho layout (write_fe_condition bd base) =
  negb (Z.eqb (zval (shifted_zrho rho) nv_c) 0).
Proof.
  intro HB.
  rewrite (truth_zval rho wide_write_bounds layout HB (write_fe_condition bd base) 0 1
    (proj1 (wide_write_condition_checked bd base)) (proj2 (wide_write_condition_checked bd base))).
  rewrite write_fe_condition_from_normalizer, zval_sx_subst. reflexivity.
Qed.

Lemma wide_write_selected_values rho bd base layout :
  (forall n, fst (wide_write_bounds n) <= Int64.unsigned (rho n) <= snd (wide_write_bounds n)) ->
  map (zval (zrho rho)) (write_fe_selected_bytes rho layout bd base) =
  zcells (fun n => nth n
    (if negb (Z.eqb (zval (shifted_zrho rho) nv_c) 0)
     then zcells (shifted_zrho rho) (cells0 nv_a)
     else zcells (shifted_zrho rho) (cells0 nv_b)) 0) (cells0 gb_leaf).
Proof.
  intro HB. unfold write_fe_selected_bytes. rewrite wide_write_condition by exact HB.
  destruct (negb (Z.eqb (zval (shifted_zrho rho) nv_c) 0)).
  - rewrite write_fe_true_bytes_from_get_b32. apply wide_get_b32_substituted.
  - rewrite write_fe_false_bytes_from_get_b32. apply wide_get_b32_substituted.
Qed.

Theorem wide_write_selected_bytes_numeric t0 t1 t2 t3 t4 rc bd base layout :
  Int64.unsigned t0 <= 2 ^ 60 -> Int64.unsigned t1 <= 2 ^ 60 ->
  Int64.unsigned t2 <= 2 ^ 60 -> Int64.unsigned t3 <= 2 ^ 60 ->
  Int64.unsigned t4 <= 2 ^ 60 ->
  map (zval (zrho (wide_fe_rho t0 t1 t2 t3 t4 rc)))
    (write_fe_selected_bytes (wide_fe_rho t0 t1 t2 t3 t4 rc) layout bd base) =
  be_bytes (fe_val (Int64.unsigned t0) (Int64.unsigned t1)
    (Int64.unsigned t2) (Int64.unsigned t3) (Int64.unsigned t4) mod feP).
Proof.
  intros H0 H1 H2 H3 H4.
  rewrite wide_write_selected_values by (apply wide_fe_rho_bounds; assumption).
  pose proof (shifted_wide_fe_rho t0 t1 t2 t3 t4 rc) as HShift.
  rewrite (zval_ext _ _ nv_c HShift),
    (zcells_ext _ _ (cells0 nv_a) HShift), (zcells_ext _ _ (cells0 nv_b) HShift).
  rewrite <- nv_bridge.
  rewrite wide_normalized_limbs_canonical by assumption.
  apply gb_math. apply field_mod_256_range.
Qed.

Theorem wide_write_selected_machine_bytes t0 t1 t2 t3 t4 rc bd base layout :
  Int64.unsigned t0 <= 2 ^ 60 -> Int64.unsigned t1 <= 2 ^ 60 ->
  Int64.unsigned t2 <= 2 ^ 60 -> Int64.unsigned t3 <= 2 ^ 60 ->
  Int64.unsigned t4 <= 2 ^ 60 ->
  map (fun x => ii (den (wide_fe_rho t0 t1 t2 t3 t4 rc) layout x))
    (write_fe_selected_bytes (wide_fe_rho t0 t1 t2 t3 t4 rc) layout bd base) =
  map Int.repr (be_bytes (fe_val (Int64.unsigned t0) (Int64.unsigned t1)
    (Int64.unsigned t2) (Int64.unsigned t3) (Int64.unsigned t4) mod feP)).
Proof.
  intros H0 H1 H2 H3 H4.
  rewrite <- (wide_write_selected_bytes_numeric t0 t1 t2 t3 t4 rc bd base layout
    H0 H1 H2 H3 H4), map_map.
  apply map_ext_in. intros x HX.
  assert (HC : Forall (fun x => zb wide_write_bounds x = Some (0,255) /\ isk KI x = true)
    (write_fe_selected_bytes (wide_fe_rho t0 t1 t2 t3 t4 rc) layout bd base)).
  { unfold write_fe_selected_bytes. destruct (truth _ _ _);
    [apply wide_write_true_bytes_checked|apply wide_write_false_bytes_checked]. }
  destruct (proj1 (Forall_forall _ _) HC x HX) as [HCheck HKind].
  rewrite (proj1 (den_zval_int (wide_fe_rho t0 t1 t2 t3 t4 rc) wide_write_bounds layout
    (wide_fe_rho_bounds t0 t1 t2 t3 t4 rc H0 H1 H2 H3 H4) x 0 255 HCheck HKind)).
  reflexivity.
Qed.
Print Assumptions wide_write_selected_machine_bytes.
