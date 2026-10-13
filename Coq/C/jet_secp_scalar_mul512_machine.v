(** Machine operations of the actual scalar_mul_512 macros, not a public spec. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values.
Require Import C.jet_sx_expr C.jet_secp_u64_carry.
Require Import C.jet_secp_umul128_numeric C.jet_secp_scalar_mul512_run.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Record mul_column := column { col_lo : int64; col_hi : int64; col_top : int }.
Definition column_value s := Int64.unsigned (col_lo s) + Int64.modulus *
  (Int64.unsigned (col_hi s) + Int64.modulus * Int.unsigned (col_top s)).
Definition column_zero := column Int64.zero Int64.zero Int.zero.
Definition column_carry64 x y := Int64.repr (Int.signed
  (if Int64.ltu (Int64.add x y) y then Int.one else Int.zero)).
Definition column_carry32 x y :=
  if Int64.ltu (Int64.add x y) y then Int.one else Int.zero.
Definition column_product_lo a b s := Int64.add (col_lo s) (umul128_lo_machine a b).
Definition column_product_hi_add a b s :=
  Int64.add (umul128_hi_machine a b) (column_carry64 (col_lo s) (umul128_lo_machine a b)).
Definition column_muladd a b s := column
  (column_product_lo a b s)
  (Int64.add (col_hi s) (column_product_hi_add a b s))
  (Int.add (col_top s) (column_carry32 (col_hi s) (column_product_hi_add a b s))).
Definition column_muladd_fast a b s := column
  (column_product_lo a b s)
  (Int64.add (col_hi s) (column_product_hi_add a b s)) (col_top s).
Definition column_extract s := column (col_hi s)
  (Int64.repr (Int.unsigned (col_top s))) Int.zero.
Definition column_extract_fast s := column (col_hi s) Int64.zero (col_top s).

Definition scalar_mul512_machine_outputs (rho : nat -> int64) : list int64 :=
  let c0 := column_muladd_fast (rho 0%nat) (rho 4%nat) column_zero in
  let c1 := column_muladd (rho 1%nat) (rho 4%nat)
    (column_muladd (rho 0%nat) (rho 5%nat) (column_extract_fast c0)) in
  let c2 := column_muladd (rho 2%nat) (rho 4%nat)
    (column_muladd (rho 1%nat) (rho 5%nat)
      (column_muladd (rho 0%nat) (rho 6%nat) (column_extract c1))) in
  let c3 := column_muladd (rho 3%nat) (rho 4%nat)
    (column_muladd (rho 2%nat) (rho 5%nat)
      (column_muladd (rho 1%nat) (rho 6%nat)
        (column_muladd (rho 0%nat) (rho 7%nat) (column_extract c2)))) in
  let c4 := column_muladd (rho 3%nat) (rho 5%nat)
    (column_muladd (rho 2%nat) (rho 6%nat)
      (column_muladd (rho 1%nat) (rho 7%nat) (column_extract c3))) in
  let c5 := column_muladd (rho 3%nat) (rho 6%nat)
    (column_muladd (rho 2%nat) (rho 7%nat) (column_extract c4)) in
  let c6 := column_muladd_fast (rho 3%nat) (rho 7%nat) (column_extract c5) in
  [col_lo c0; col_lo c1; col_lo c2; col_lo c3; col_lo c4; col_lo c5; col_lo c6; col_hi c6].

Lemma column_carry64_value x y : Int64.unsigned (column_carry64 x y) =
  (Int64.unsigned x + Int64.unsigned y) / Int64.modulus.
Proof. apply u64_add_carry_bit_right. Qed.
Lemma column_carry64_bound x y : 0 <= Int64.unsigned (column_carry64 x y) <= 1.
Proof.
  unfold column_carry64; destruct (Int64.ltu (Int64.add x y) y);
    [change (0 <= 1 <= 1)|change (0 <= 0 <= 1)]; lia.
Qed.
Lemma column_carry32_value x y : Int.unsigned (column_carry32 x y) =
  (Int64.unsigned x + Int64.unsigned y) / Int64.modulus.
Proof.
  rewrite <- column_carry64_value; unfold column_carry32,column_carry64.
  destruct (Int64.ltu (Int64.add x y) y); reflexivity.
Qed.
Lemma column_carry32_bound x y : 0 <= Int.unsigned (column_carry32 x y) <= 1.
Proof.
  unfold column_carry32; destruct (Int64.ltu (Int64.add x y) y);
    [change (0 <= 1 <= 1)|change (0 <= 0 <= 1)]; lia.
Qed.
Lemma column_product_hi_bound a b : Int64.unsigned (umul128_hi_machine a b) < Int64.modulus - 1.
Proof.
  rewrite (proj1 (umul128_unsigned_outputs a b)).
  apply Z.div_lt_upper_bound; [pose proof Int64.modulus_pos; lia|].
  pose proof (Int64.unsigned_range a); pose proof (Int64.unsigned_range b).
  assert (2 <= Int64.modulus) by (change (2 <= 18446744073709551616); lia).
  nia.
Qed.
Lemma column_product_hi_add_value a b s : Int64.unsigned (column_product_hi_add a b s) =
  (Int64.unsigned a * Int64.unsigned b) / Int64.modulus +
    (Int64.unsigned (col_lo s) + (Int64.unsigned a * Int64.unsigned b) mod Int64.modulus)
      / Int64.modulus.
Proof.
  unfold column_product_hi_add. rewrite Int64.add_unsigned, Int64.unsigned_repr.
  - rewrite column_carry64_value.
    destruct (umul128_unsigned_outputs a b) as [HH HL]; rewrite HH,HL; reflexivity.
  - pose proof (column_product_hi_bound a b).
    pose proof (Int64.unsigned_range (umul128_hi_machine a b)).
    pose proof (column_carry64_bound (col_lo s) (umul128_lo_machine a b)).
    unfold Int64.max_unsigned; lia.
Qed.
