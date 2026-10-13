(** Internal bridge for the actual weak-normalizer output cells. Not a public
    jet equivalence: execution, owned loads, and the literal target are separate. *)
From Coq Require Import ZArith List Lia.
Require Import C.jet_sx_zrep C.jet_sx_zval C.jet_secp_fe_nv.
Require Import C.jet_secp_fe_math C.jet_secp_point_write_run C.jet_secp_point_weak_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition point_weak_bounds (n : nat) : Z * Z :=
  (0, if Nat.eqb n 5 then 281474976710655 else 4503599627370495).

Lemma point_weak_cells_checked k :
  zreg_okb point_weak_bounds (point_coordinate_offset k)
    (cells0 (point_weak_state k)) = true.
Proof. destruct k; reflexivity. Qed.

Definition point_weak_math t0 t1 t2 t3 t4 :=
  nv_pass (t0 + (t4 / 2^48)*feR) t1 t2 t3 (Z.land t4 281474976710655).

Definition point_weak_math_list t0 t1 t2 t3 t4 : list Z :=
  let '(a,b,c,d,e) := point_weak_math t0 t1 t2 t3 t4 in [a;b;c;d;e].

Lemma point_weak_cells_values k rho :
  zcells rho (cells0 (point_weak_state k)) =
  point_weak_math_list (rho 1%nat) (rho 2%nat) (rho 3%nat)
    (rho 4%nat) (rho 5%nat).
Proof. destruct k; reflexivity. Qed.

Lemma nv_pass_positioned_identity t0 t1 t2 t3 t4 :
  fe_limbs_ok t0 t1 t2 t3 t4 ->
  nv_pass t0 t1 t2 t3 t4 = (t0,t1,t2,t3,t4).
Proof.
  unfold fe_limbs_ok; intros (H0&H1&H2&H3&H4).
  assert (D0 : t0 / 2^52 = 0) by (apply Z.div_small; change (2^52) with 4503599627370496; lia).
  assert (D1 : t1 / 2^52 = 0) by (apply Z.div_small; change (2^52) with 4503599627370496; lia).
  assert (D2 : t2 / 2^52 = 0) by (apply Z.div_small; change (2^52) with 4503599627370496; lia).
  assert (D3 : t3 / 2^52 = 0) by (apply Z.div_small; change (2^52) with 4503599627370496; lia).
  unfold nv_pass; rewrite D0, Z.add_0_r, D1, Z.add_0_r, D2, Z.add_0_r, D3, Z.add_0_r.
  rewrite !land_M52, !Z.mod_small by (change (2^52) with 4503599627370496; lia).
  reflexivity.
Qed.

Lemma point_weak_math_positioned_identity t0 t1 t2 t3 t4 :
  fe_limbs_ok t0 t1 t2 t3 t4 ->
  point_weak_math t0 t1 t2 t3 t4 = (t0,t1,t2,t3,t4).
Proof.
  intro H; pose proof H as (_&_&_&_&H4).
  assert (D4 : t4 / 2^48 = 0) by (apply Z.div_small; change (2^48) with 281474976710656; lia).
  assert (M4 : Z.land t4 281474976710655 = t4).
  { rewrite land_M48; apply Z.mod_small; change (2^48) with 281474976710656; lia. }
  unfold point_weak_math; rewrite D4, M4, Z.mul_0_l, Z.add_0_r.
  apply nv_pass_positioned_identity; exact H.
Qed.

Lemma point_weak_cells_positioned_identity k rho :
  fe_limbs_ok (rho 1%nat) (rho 2%nat) (rho 3%nat) (rho 4%nat) (rho 5%nat) ->
  zcells rho (cells0 (point_weak_state k)) =
    [rho 1%nat;rho 2%nat;rho 3%nat;rho 4%nat;rho 5%nat].
Proof.
  intro H; rewrite point_weak_cells_values; unfold point_weak_math_list.
  rewrite point_weak_math_positioned_identity by exact H; reflexivity.
Qed.
Print Assumptions point_weak_cells_positioned_identity.
