(** Exact machine loads following actual weak normalization. Internal support. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory.
Require Import C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_zval C.jet_sx_zrep.
Require Import C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_point_write_run.
Require Import C.jet_secp_point_weak_exec C.jet_secp_point_weak_values.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma point_weak_bounds_positioned rho :
  (forall n, fst (point_weak_bounds n) <= Int64.unsigned (rho n) <= snd (point_weak_bounds n)) ->
  fe_limbs_ok (Int64.unsigned (rho 1%nat)) (Int64.unsigned (rho 2%nat))
    (Int64.unsigned (rho 3%nat)) (Int64.unsigned (rho 4%nat)) (Int64.unsigned (rho 5%nat)).
Proof.
  intro H; unfold fe_limbs_ok.
  split; [exact (H 1%nat)|]. split; [exact (H 2%nat)|].
  split; [exact (H 3%nat)|]. split; [exact (H 4%nat)|exact (H 5%nat)].
Qed.

Theorem point_weak_rep_preserved_loads k m layout rho :
  (forall n, fst (point_weak_bounds n) <= Int64.unsigned (rho n) <= snd (point_weak_bounds n)) ->
  rep rho layout (sregs (point_weak_state k)) m ->
  forall n, (n < 5)%nat ->
  Mem.load Mint64 m (blk layout 0) (bas layout 0 + (point_coordinate_offset k + 8 * Z.of_nat n)) =
    Some (Vlong (rho (S n))).
Proof.
  intros HB HRep n Hn.
  assert (HE : nth_error (sregs (point_weak_state k)) 0 =
    Some (hd (mkreg [] true None) (sregs (point_weak_state k)))).
  { destruct k; reflexivity. }
  pose proof (rep_region rho layout _ m 0 _ HRep HE) as HRegion.
  assert (HW : rw (hd (mkreg [] true None) (sregs (point_weak_state k))) = true).
  { destruct k; reflexivity. }
  destruct HRegion as (_ & _ & _ & HCells & _).
  rewrite HW in HCells.
  change (Forall (cell_ok rho layout m 0 true) (cells0 (point_weak_state k))) in HCells.
  destruct (zreg_load rho point_weak_bounds layout HB m 0 true
    (cells0 (point_weak_state k)) (point_coordinate_offset k)
    (point_weak_cells_checked k) HCells) as [HLoad _].
  rewrite point_weak_cells_positioned_identity in HLoad
    by (apply point_weak_bounds_positioned; exact HB).
  assert (HN : nth_error
    [Int64.unsigned (rho 1%nat);Int64.unsigned (rho 2%nat);Int64.unsigned (rho 3%nat);
     Int64.unsigned (rho 4%nat);Int64.unsigned (rho 5%nat)] n = Some (Int64.unsigned (rho (S n)))).
  { do 5 (destruct n as [|n]; [reflexivity|]); lia. }
  specialize (HLoad n _ HN).
  rewrite Int64.repr_unsigned in HLoad; exact HLoad.
Qed.
Print Assumptions point_weak_rep_preserved_loads.
