(** First column value of the actual scalar product execution.  The other
    seven columns and the public literal-program bridge remain open. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem C.jet_sx_eval.
Require Import C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_umul128_numeric C.jet_secp_scalar_mul512_run.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_mul512_low : sx := nth 0 scalar_mul512_limbs (XLc Int64.zero).
Lemma scalar_mul512_low_den rho beta : den rho beta scalar_mul512_low =
  Vlong (Int64.add Int64.zero (umul128_lo_machine (rho 0%nat) (rho 4%nat))).
Proof. Timeout 10 reflexivity. Qed.
Lemma scalar_mul512_low_carrier rho beta : den rho beta scalar_mul512_low =
  Vlong (Int64.repr ((Int64.unsigned (rho 0%nat) * Int64.unsigned (rho 4%nat)) mod Int64.modulus)).
Proof.
  rewrite scalar_mul512_low_den.
  rewrite Int64.add_zero_l. f_equal.
  rewrite <- (Int64.repr_unsigned (umul128_lo_machine (rho 0%nat) (rho 4%nat))).
  rewrite (proj2 (umul128_unsigned_outputs (rho 0%nat) (rho 4%nat))); reflexivity.
Qed.

Definition scalar_mul512_input_value (rho : nat -> int64) (start : nat) : Z :=
  Int64.unsigned (rho start) + Int64.modulus *
    (Int64.unsigned (rho (start + 1)%nat) + Int64.modulus *
      (Int64.unsigned (rho (start + 2)%nat) + Int64.modulus *
        Int64.unsigned (rho (start + 3)%nat))).
Lemma scalar_mul512_input_product_low rho :
  (scalar_mul512_input_value rho 0 * scalar_mul512_input_value rho 4) mod Int64.modulus =
  (Int64.unsigned (rho 0%nat) * Int64.unsigned (rho 4%nat)) mod Int64.modulus.
Proof.
  unfold scalar_mul512_input_value; cbn [Nat.add].
  set (a := Int64.unsigned (rho 0%nat)); set (b := Int64.unsigned (rho 4%nat)).
  set (ta := Int64.unsigned (rho 1%nat) + Int64.modulus *
    (Int64.unsigned (rho 2%nat) + Int64.modulus * Int64.unsigned (rho 3%nat))).
  set (tb := Int64.unsigned (rho 5%nat) + Int64.modulus *
    (Int64.unsigned (rho 6%nat) + Int64.modulus * Int64.unsigned (rho 7%nat))).
  change (((a + Int64.modulus * ta) * (b + Int64.modulus * tb)) mod Int64.modulus =
    (a*b) mod Int64.modulus).
  replace ((a + Int64.modulus * ta) * (b + Int64.modulus * tb)) with
    (a*b + (a*tb + b*ta + Int64.modulus*ta*tb) * Int64.modulus) by ring.
  apply Z.mod_add; discriminate.
Qed.
Lemma scalar_mul512_low_full_product rho beta : den rho beta scalar_mul512_low =
  Vlong (Int64.repr ((scalar_mul512_input_value rho 0 * scalar_mul512_input_value rho 4)
    mod Int64.modulus)).
Proof. rewrite scalar_mul512_input_product_low; apply scalar_mul512_low_carrier. Qed.
Lemma scalar_mul512_low_cell :
  In (mkcell 0 Mint64 (Some scalar_mul512_low)) (u64_cells 0 scalar_mul512_limbs).
Proof.
  pose proof scalar_mul512_limbs_length as Hlen.
  unfold scalar_mul512_low.
  destruct scalar_mul512_limbs as [|x xs]; [discriminate|].
  left; reflexivity.
Qed.
Theorem eval_scalar_mul512_owned_low_product rho beta m :
  rep rho beta scalar_mul512_initial_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_mul_512)
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
       Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));
       Vptr (blk beta 2) (Ptrofs.repr (bas beta 2))] E0 mf Vundef /\
    Mem.load Mint64 mf (blk beta 0) (bas beta 0) =
      Some (Vlong (Int64.repr ((scalar_mul512_input_value rho 0 * scalar_mul512_input_value rho 4)
        mod Int64.modulus))) /\
    rep rho beta (sregs scalar_mul512_state) mf /\
    lframe (fun b ofs => ~ foot beta (map rshape scalar_mul512_initial_regs) b ofs) m mf.
Proof.
  intro Hrep.
  destruct (eval_scalar_mul512_owned rho beta m Hrep) as (mf & Hcall & Hfinal & Hframe).
  pose proof (rep_region rho beta _ mf 0 _ Hfinal eq_refl) as Hregion.
  pose proof (region_load rho beta mf 0 _ 0 Mint64 scalar_mul512_low Hregion scalar_mul512_low_cell)
    as Hload.
  rewrite Z.add_0_r, scalar_mul512_low_full_product in Hload.
  rewrite <- scalar_mul512_output in Hfinal.
  exists mf; split; [exact Hcall|]. split; [exact Hload|]. split; [exact Hfinal|exact Hframe].
Qed.
