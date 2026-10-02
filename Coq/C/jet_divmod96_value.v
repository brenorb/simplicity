(** Scalar CompCert observations needed for div_mod_96_64. The final
    multiply/add/subtract is modular; the guard's comparison is exact only
    in the short-circuit branch that evaluates it. Not public jet coverage. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import C.jet_divmod96_arith.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition divmod96_radix : Z := 4294967296.
Definition divmod96_high b := Int64.shru b (Int64.repr 32).
Definition divmod96_low b := Int64.and b (Int64.repr 4294967295).

Lemma divmod96_high_unsigned b :
  Int64.unsigned (divmod96_high b) = Int64.unsigned b / divmod96_radix.
Proof.
  unfold divmod96_high. rewrite Int64.shru_div_two_p.
  rewrite (Int64.unsigned_repr 32 ltac:(change (0 <= 32 <= 18446744073709551615); lia)).
  change (Int64.unsigned (Int64.repr (Int64.unsigned b / divmod96_radix)) =
    Int64.unsigned b / divmod96_radix).
  apply Int64.unsigned_repr.
  pose proof (Int64.unsigned_range_2 b) as HB.
  split; [apply Z.div_pos; unfold divmod96_radix; lia|].
  transitivity (Int64.unsigned b); [apply Z.div_le_upper_bound; unfold divmod96_radix; nia|lia].
Qed.

Lemma divmod96_low_unsigned b :
  Int64.unsigned (divmod96_low b) = Int64.unsigned b mod divmod96_radix.
Proof.
  unfold divmod96_low.
  change (Int64.unsigned (Int64.and b (Int64.repr (two_p 32 - 1))) =
    Int64.unsigned b mod divmod96_radix).
  rewrite <- Int64.zero_ext_and by lia.
  rewrite Int64.zero_ext_mod by (change (0 <= 32 < 64); lia). reflexivity.
Qed.

Lemma divmod96_sum_modular B rh al :
  Int64.add (Int64.mul (Int64.repr B) rh) al =
  Int64.repr (B * Int64.unsigned rh + Int64.unsigned al).
Proof.
  unfold Int64.add, Int64.mul. apply Int64.eqm_samerepr. apply Int64.eqm_add.
  - apply Int64.eqm_unsigned_repr_l. apply Int64.eqm_mult.
    + apply Int64.eqm_unsigned_repr_l. apply Int64.eqm_refl.
    + apply Int64.eqm_refl.
  - apply Int64.eqm_refl.
Qed.

Lemma divmod96_final_modular B rh al d :
  Int64.sub (Int64.add (Int64.mul (Int64.repr B) rh) al) d =
  Int64.repr (B * Int64.unsigned rh + Int64.unsigned al - Int64.unsigned d).
Proof.
  rewrite divmod96_sum_modular. unfold Int64.sub. apply Int64.eqm_samerepr.
  apply Int64.eqm_sub; [apply Int64.eqm_unsigned_repr_l|]; apply Int64.eqm_refl.
Qed.

Lemma divmod96_final_unsigned rh al d :
  0 <= divmod96_radix * Int64.unsigned rh + Int64.unsigned al - Int64.unsigned d < Int64.modulus ->
  Int64.unsigned (Int64.sub (Int64.add (Int64.mul (Int64.repr divmod96_radix) rh) al) d) =
  divmod96_radix * Int64.unsigned rh + Int64.unsigned al - Int64.unsigned d.
Proof. intros Hrange. rewrite divmod96_final_modular. apply Int64.unsigned_repr. unfold Int64.max_unsigned; lia. Qed.

Definition divmod96_guard rh al d :=
  if negb (Int64.ltu (Int64.repr (divmod96_radix - 1)) rh)
  then Int64.ltu (Int64.add (Int64.mul (Int64.repr divmod96_radix) rh) al) d
  else Datatypes.false.

Lemma divmod96_guard_negative rh al d :
  Int64.unsigned al < divmod96_radix -> Int64.unsigned d < divmod96_radix * divmod96_radix ->
  divmod96_guard rh al d = Datatypes.true <->
  divmod96_radix * Int64.unsigned rh + Int64.unsigned al - Int64.unsigned d < 0.
Proof.
  intros HAL HD.
  pose proof (Int64.unsigned_range rh) as HR.
  pose proof (Int64.unsigned_range al) as HA.
  pose proof (Int64.unsigned_range d) as Hd.
  unfold divmod96_guard, Int64.ltu.
  rewrite Int64.unsigned_repr by (unfold divmod96_radix; change Int64.max_unsigned with 18446744073709551615; lia).
  destruct (zlt (divmod96_radix - 1) (Int64.unsigned rh)) as [Hlarge|Hsmall]; cbn [negb].
  - split; [discriminate|]. intros Hneg.
    destruct (proj2 (divmod96_guard_exact divmod96_radix (Int64.unsigned rh)
      (Int64.unsigned al) (Int64.unsigned d) ltac:(unfold divmod96_radix; lia)
      ltac:(lia) ltac:(lia) ltac:(lia)) Hneg) as [Hfirst _]. lia.
  - rewrite divmod96_sum_modular.
    rewrite Int64.unsigned_repr.
    + destruct (zlt (divmod96_radix * Int64.unsigned rh + Int64.unsigned al) (Int64.unsigned d));
        split; intros; try reflexivity; try discriminate; lia.
    + pose proof (divmod96_compare_no_wrap divmod96_radix (Int64.unsigned rh) (Int64.unsigned al)
        ltac:(unfold divmod96_radix; lia) ltac:(lia) ltac:(lia)) as Hsum.
      unfold divmod96_radix in Hsum |- *. change Int64.max_unsigned with 18446744073709551615. lia.
Qed.
