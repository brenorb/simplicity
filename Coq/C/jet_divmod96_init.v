(** Connect the helper's actual shifted/masked divisor and clipped CompCert
    quotient to the correction invariant. Not a whole-function contract. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import C.jet_divmod96_arith C.jet_divmod96_value.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma divmod96_denominator_parts b : Int64.modulus <= 2 * Int64.unsigned b ->
  0 < Int64.unsigned (divmod96_high b) < divmod96_radix /\
  0 <= Int64.unsigned (divmod96_low b) < divmod96_radix /\
  Int64.unsigned b = Int64.unsigned (divmod96_high b) * divmod96_radix +
    Int64.unsigned (divmod96_low b).
Proof.
  intros Hnorm. rewrite divmod96_high_unsigned, divmod96_low_unsigned.
  pose proof (Int64.unsigned_range b) as HB.
  pose proof (Z.mod_pos_bound (Int64.unsigned b) divmod96_radix ltac:(unfold divmod96_radix; lia)) as Hlow.
  pose proof (Z.div_mod (Int64.unsigned b) divmod96_radix ltac:(unfold divmod96_radix; lia)) as Hdiv.
  assert (Hhigh0 : 0 <= Int64.unsigned b / divmod96_radix).
  { apply Z.div_pos; unfold divmod96_radix; lia. }
  assert (Hhigh : Int64.unsigned b / divmod96_radix < divmod96_radix).
  { apply Z.div_lt_upper_bound; [unfold divmod96_radix; lia|].
    unfold divmod96_radix. change Int64.modulus with 18446744073709551616 in HB. lia. }
  split.
  - split; [|exact Hhigh].
    unfold divmod96_radix in Hlow, Hdiv, Hhigh0 |- *.
    change Int64.modulus with 18446744073709551616 in Hnorm. lia.
  - split; [exact Hlow|]. nia.
Qed.

Lemma divmod96_divu_unsigned ah bh : 0 < Int64.unsigned bh ->
  Int64.unsigned (Int64.divu ah bh) = Int64.unsigned ah / Int64.unsigned bh.
Proof.
  intros HP. unfold Int64.divu. apply Int64.unsigned_repr.
  pose proof (Int64.unsigned_range_2 ah) as HA.
  split; [apply Z.div_pos; lia|]. transitivity (Int64.unsigned ah); [|lia].
  apply Z.div_le_upper_bound; nia.
Qed.

Definition divmod96_clamp ah bh :=
  let est := Int64.divu ah bh in
  if negb (Int64.ltu (Int64.repr (divmod96_radix - 1)) est)
  then est else Int64.repr (divmod96_radix - 1).

Lemma divmod96_clamp_unsigned ah bh : 0 < Int64.unsigned bh ->
  Int64.unsigned (divmod96_clamp ah bh) =
  divmod96_estimate divmod96_radix (Int64.unsigned ah) (Int64.unsigned bh).
Proof.
  intros HP. unfold divmod96_clamp, Int64.ltu, divmod96_estimate.
  rewrite divmod96_divu_unsigned by exact HP.
  rewrite (Int64.unsigned_repr (divmod96_radix - 1)
    ltac:(unfold divmod96_radix; change Int64.max_unsigned with 18446744073709551615; lia)).
  destruct (zlt (divmod96_radix - 1) (Int64.unsigned ah / Int64.unsigned bh)) as [Hlarge|Hsmall]; cbn [negb].
  - rewrite Int64.unsigned_repr by (unfold divmod96_radix; change Int64.max_unsigned with 18446744073709551615; lia).
    symmetry. apply Z.min_r; lia.
  - rewrite divmod96_divu_unsigned by exact HP. symmetry. apply Z.min_l; lia.
Qed.

Lemma divmod96_machine_initial_bounds ah al b :
  Int64.modulus <= 2 * Int64.unsigned b -> Int64.unsigned ah < Int64.unsigned b ->
  Int64.unsigned al < divmod96_radix ->
  let bh := divmod96_high b in let bl := divmod96_low b in
  let q := Int64.unsigned (divmod96_clamp ah bh) in
  0 <= q < divmod96_radix /\
  0 <= Int64.unsigned ah - q * Int64.unsigned bh <= Int64.unsigned ah /\
  0 <= q * Int64.unsigned bl < Int64.modulus /\
  -2 * Int64.unsigned b <=
    Int64.unsigned ah * divmod96_radix + Int64.unsigned al - q * Int64.unsigned b < Int64.unsigned b.
Proof.
  intros Hnorm Hah Hal. cbn zeta.
  destruct (divmod96_denominator_parts b Hnorm) as [Hbh [Hbl Hb]].
  rewrite divmod96_clamp_unsigned by exact (proj1 Hbh).
  replace Int64.modulus with (divmod96_radix * divmod96_radix) in * by reflexivity.
  apply divmod96_initial_bounds; try assumption.
  - unfold divmod96_radix; lia.
  - pose proof (Int64.unsigned_range ah); lia.
  - pose proof (Int64.unsigned_range al); lia.
Qed.
