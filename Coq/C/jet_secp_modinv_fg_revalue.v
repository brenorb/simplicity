(** Reuse the checked body at successive indices without assuming stores. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clightdefs Clight Maps Memory Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_u64_transport.
Require Import C.jet_secp_modinv_fg_prefix C.jet_secp_modinv_fg_iteration_prefix.
Require Import C.jet_secp_modinv_fg_iteration C.jet_secp_modinv_fg_iteration_numeric.
Require Import C.jet_secp_i128_shift62_rep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition fg_output_limbs (high : bool) k := map (fun j=>
 if Nat.eqb j (k-1) then XLb Band (fst (fg_iter_pair_sx high k)) fg_iter_mask
 else XLv (if high then (5+j)%nat else j)) (seq 0 5).
Definition fg_output_carry (high : bool) k :=
 [i128_shift62_lo_sx (fst (fg_iter_pair_sx high k)) (snd (fg_iter_pair_sx high k));
  i128_shift62_hi_sx (snd (fg_iter_pair_sx high k))].
Definition fg_output_regs k :=
 [mkreg (u64_cells 0 (fg_output_limbs false k)) true (Some 40);
  mkreg (u64_cells 0 (fg_output_limbs true k)) true (Some 40);
  mkreg (u64_cells 0 [XLv 10;XLv 11;XLv 12;XLv 13]) false None;
  mkreg (u64_cells 0 (fg_output_carry false k)) true (Some 16);
  mkreg (u64_cells 0 (fg_output_carry true k)) true (Some 16)].
Lemma fg_output_regs_eq k : (0<k<5)%nat -> sregs (fg_iter_final_state k)=fg_output_regs k.
Proof. destruct k as [|[|[|[|[|k]]]]];intro K;try lia;vm_compute;reflexivity. Qed.

Definition fg_next_rho (rho : nat->int64) k n :=
 if (n <? 10)%nat then
  if Nat.eqb (n mod 5) (k-1) then fg_iter_limb rho (5 <=? n)%nat k else rho n
 else match n with
 | 15%nat=>fst (fg_iter_carry rho false k) | 16%nat=>snd (fg_iter_carry rho false k)
 | 17%nat=>fst (fg_iter_carry rho true k) | 18%nat=>snd (fg_iter_carry rho true k)
 | _=>rho n end.

Lemma fg_next_limb_den rho beta (high : bool) k : (0<k<5)%nat ->
 map (den (fg_next_rho rho k) beta) (map XLv (seq (if high then 5 else 0) 5))=
 map (den rho beta) (fg_output_limbs high k).
Proof.
 destruct high;destruct k as [|[|[|[|[|k]]]]];intro K;try lia;
 cbn [fg_output_limbs map seq Nat.add Nat.eqb Nat.sub];
 rewrite fg_iter_limb_den;reflexivity.
Qed.
Lemma fg_next_carry_den rho beta (high : bool) k :
 map (den (fg_next_rho rho k) beta) (if high then [XLv 17;XLv 18] else [XLv 15;XLv 16])=
 map (den rho beta) (fg_output_carry high k).
Proof.
 destruct high;cbn [fg_output_carry map];rewrite fg_iter_carry_low_den,fg_iter_carry_high_den;reflexivity.
Qed.

Lemma fg_iteration_revalue rho beta k m : (0<k<5)%nat ->
 rep rho beta (sregs (fg_iter_final_state k)) m -> rep (fg_next_rho rho k) beta fg_iter_regs m.
Proof.
 intros K Rep;rewrite fg_output_regs_eq in Rep by exact K.
 destruct Rep as (Len & Sep & Regions).
 split;[exact Len|];split.
 - eapply rsep_shape with (regs:=fg_output_regs k);[|exact Sep].
   destruct k as [|[|[|[|[|k]]]]];try lia;vm_compute;reflexivity.
 - intros r reg Entry.
   assert (R : (r<length fg_iter_regs)%nat) by (apply nth_error_Some;congruence).
   change (r<5)%nat in R.
   destruct r as [|[|[|[|[|r]]]]];try lia.
   all: cbn [fg_iter_regs fg_regs app nth_error] in Entry.
   all: injection Entry as <-.
   + eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=0%nat) (xs:=fg_output_limbs false k)
      (ys:=[XLv 0;XLv 1;XLv 2;XLv 3;XLv 4]).
     * reflexivity.
     * reflexivity.
     * exact (fg_next_limb_den rho (lay beta) false k K).
     * reflexivity.
     * exact (Regions 0%nat _ eq_refl).
   + eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=1%nat) (xs:=fg_output_limbs true k)
      (ys:=[XLv 5;XLv 6;XLv 7;XLv 8;XLv 9]).
     * reflexivity.
     * reflexivity.
     * exact (fg_next_limb_den rho (lay beta) true k K).
     * reflexivity.
     * exact (Regions 1%nat _ eq_refl).
   + eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=2%nat) (xs:=[XLv 10;XLv 11;XLv 12;XLv 13])
      (ys:=[XLv 10;XLv 11;XLv 12;XLv 13]);
      try reflexivity;exact (Regions 2%nat _ eq_refl).
   + eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=3%nat) (xs:=fg_output_carry false k)
      (ys:=[XLv 15;XLv 16]).
     * reflexivity.
     * reflexivity.
     * exact (fg_next_carry_den rho (lay beta) false k).
     * reflexivity.
     * exact (Regions 3%nat _ eq_refl).
   + eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=4%nat) (xs:=fg_output_carry true k)
      (ys:=[XLv 17;XLv 18]).
     * reflexivity.
     * reflexivity.
     * exact (fg_next_carry_den rho (lay beta) true k).
     * reflexivity.
     * exact (Regions 4%nat _ eq_refl).
Qed.
