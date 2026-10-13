(** Exact uint64-top macro operations used by the original reduce512 body.
    Arithmetic observations are internal bridges, not public Simplicity specs. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import C.jet_secp_u64_carry.
Require Import C.jet_secp_umul128_numeric C.jet_secp_scalar_mul512_machine
  C.jet_secp_scalar_mul512_columns.
Local Open Scope Z_scope.
Set Default Timeout 10.

Record wide_column := wcolumn { wlo : int64; whi : int64; wtop : int64 }.
Definition wide_value s := Int64.unsigned (wlo s) + Int64.modulus *
  (Int64.unsigned (whi s) + Int64.modulus * Int64.unsigned (wtop s)).
Definition wide_lower s := column (wlo s) (whi s) Int.zero.
Definition wide_from_word x := wcolumn x Int64.zero Int64.zero.
Definition wide_muladd a b s := wcolumn
  (column_product_lo a b (wide_lower s))
  (Int64.add (whi s) (column_product_hi_add a b (wide_lower s)))
  (Int64.add (wtop s) (column_carry64 (whi s) (column_product_hi_add a b (wide_lower s)))).
Definition wide_muladd_fast a b s := wcolumn
  (column_product_lo a b (wide_lower s))
  (Int64.add (whi s) (column_product_hi_add a b (wide_lower s))) (wtop s).
Definition wide_sumadd x s := wcolumn (Int64.add (wlo s) x)
  (Int64.add (whi s) (column_carry64 (wlo s) x))
  (Int64.add (wtop s) (column_carry64 (whi s) (column_carry64 (wlo s) x))).
Definition wide_sumadd_fast x s := wcolumn (Int64.add (wlo s) x)
  (Int64.add (whi s) (column_carry64 (wlo s) x)) (wtop s).
Definition wide_extract s := wcolumn (whi s) (wtop s) Int64.zero.
Definition wide_extract_fast s := wcolumn (whi s) Int64.zero (wtop s).

Lemma wide_value_nonnegative s : 0 <= wide_value s.
Proof.
  unfold wide_value; pose proof (Int64.unsigned_range (wlo s));
    pose proof (Int64.unsigned_range (whi s)); pose proof (Int64.unsigned_range (wtop s)).
  pose proof Int64.modulus_pos; nia.
Qed.
Lemma wide_from_word_value x : wide_value (wide_from_word x) = Int64.unsigned x.
Proof. unfold wide_value; cbn [wide_from_word wlo whi wtop]; rewrite Int64.unsigned_zero; ring. Qed.
Lemma wide_top_small s : wide_value s < 5 * (Int64.modulus * Int64.modulus) ->
  Int64.unsigned (wtop s) < Int64.max_unsigned.
Proof.
  intro H; unfold wide_value in H.
  pose proof (Int64.unsigned_range (wlo s)); pose proof (Int64.unsigned_range (whi s)).
  pose proof (Int64.unsigned_range (wtop s)); pose proof Int64.modulus_pos.
  assert (Int64.unsigned (wtop s) < 5) by nia.
  change (Int64.unsigned (wtop s) < 18446744073709551615); lia.
Qed.
Lemma wide_add_top_value t x y : Int64.unsigned t < Int64.max_unsigned ->
  Int64.unsigned (Int64.add t (column_carry64 x y)) = Int64.unsigned t +
    (Int64.unsigned x + Int64.unsigned y) / Int64.modulus.
Proof.
  intro H; rewrite Int64.add_unsigned,Int64.unsigned_repr.
  - rewrite column_carry64_value; reflexivity.
  - pose proof (Int64.unsigned_range t); pose proof (column_carry64_bound x y); lia.
Qed.
Lemma wide_muladd_value a b s : Int64.unsigned (wtop s) < Int64.max_unsigned ->
  wide_value (wide_muladd a b s) = wide_value s + Int64.unsigned a * Int64.unsigned b.
Proof.
  intro HT.
  pose proof (column_product_hi_add_value a b (wide_lower s)) as Hth.
  pose proof (proj1 (u64_add_with_carry (wlo s) (umul128_lo_machine a b))) as Hlo.
  rewrite (proj2 (umul128_unsigned_outputs a b)) in Hlo.
  pose proof (proj1 (u64_add_with_carry (whi s) (column_product_hi_add a b (wide_lower s)))) as Hhi.
  pose proof (wide_add_top_value (wtop s) (whi s) (column_product_hi_add a b (wide_lower s)) HT) as Htop.
  unfold wide_value; cbn [wide_muladd wlo whi wtop].
  unfold column_product_lo; cbn [wide_lower col_lo] in *.
  rewrite Hlo,Hhi,Htop,Hth.
  set (P := Int64.unsigned a * Int64.unsigned b).
  set (L := Int64.unsigned (wlo s)); set (H := Int64.unsigned (whi s)).
  pose proof (Z.div_mod P Int64.modulus ltac:(discriminate)) as HP.
  pose proof (Z.div_mod (L + P mod Int64.modulus) Int64.modulus ltac:(discriminate)) as HL.
  pose proof (Z.div_mod (H + (P / Int64.modulus + (L + P mod Int64.modulus) / Int64.modulus))
    Int64.modulus ltac:(discriminate)) as HH.
  change Int64.modulus with 18446744073709551616 in *; lia.
Qed.
Lemma wide_sumadd_value x s : Int64.unsigned (wtop s) < Int64.max_unsigned ->
  wide_value (wide_sumadd x s) = wide_value s + Int64.unsigned x.
Proof.
  intro HT.
  pose proof (proj1 (u64_add_with_carry (wlo s) x)) as Hlo.
  pose proof (proj1 (u64_add_with_carry (whi s) (column_carry64 (wlo s) x))) as Hhi.
  pose proof (wide_add_top_value (wtop s) (whi s) (column_carry64 (wlo s) x) HT) as Htop.
  unfold wide_value; cbn [wide_sumadd wlo whi wtop].
  rewrite Hlo,Hhi,Htop,column_carry64_value.
  set (L := Int64.unsigned (wlo s) + Int64.unsigned x).
  set (H := Int64.unsigned (whi s)).
  pose proof (Z.div_mod L Int64.modulus ltac:(discriminate)) as HL.
  pose proof (Z.div_mod (H + L / Int64.modulus) Int64.modulus ltac:(discriminate)) as HH.
  unfold L in *; change Int64.modulus with 18446744073709551616 in *; lia.
Qed.
Lemma wide_lower_value s : wtop s = Int64.zero -> column_value (wide_lower s) = wide_value s.
Proof.
  intro HT; unfold column_value,wide_value; cbn [wide_lower col_lo col_hi col_top].
  rewrite HT,Int64.unsigned_zero,Int.unsigned_zero; reflexivity.
Qed.
Lemma wide_muladd_fast_value a b s : wtop s = Int64.zero ->
  wide_value s + Int64.unsigned a * Int64.unsigned b < Int64.modulus * Int64.modulus ->
  wide_value (wide_muladd_fast a b s) = wide_value s + Int64.unsigned a * Int64.unsigned b.
Proof.
  intros HT HB.
  pose proof (column_fast_value a b (wide_lower s) eq_refl) as H.
  rewrite (wide_lower_value s HT) in H; specialize (H HB).
  unfold column_value in H; cbn [column_muladd_fast wide_lower col_lo col_hi col_top] in H.
  unfold wide_value; cbn [wide_muladd_fast wlo whi wtop].
  rewrite HT,Int64.unsigned_zero; rewrite Int.unsigned_zero in H.
  unfold wide_value in H; rewrite HT,Int64.unsigned_zero in H; exact H.
Qed.
Lemma wide_sumadd_fast_value x s : wtop s = Int64.zero ->
  wide_value s + Int64.unsigned x < Int64.modulus * Int64.modulus ->
  wide_value (wide_sumadd_fast x s) = wide_value s + Int64.unsigned x.
Proof.
  intros HT HB.
  assert (Hguard : Int64.unsigned (wtop s) < Int64.max_unsigned) by
    (rewrite HT,Int64.unsigned_zero; change (0 < 18446744073709551615); lia).
  pose proof (wide_sumadd_value x s Hguard) as H.
  assert (Hz : Int64.unsigned (wtop (wide_sumadd x s)) = 0).
  { pose proof (Int64.unsigned_range (wlo (wide_sumadd x s))).
    pose proof (Int64.unsigned_range (whi (wide_sumadd x s))).
    pose proof (Int64.unsigned_range (wtop (wide_sumadd x s))).
    unfold wide_value in H,HB; pose proof Int64.modulus_pos; nia. }
  unfold wide_value in H |- *; cbn [wide_sumadd_fast wlo whi wtop].
  rewrite HT,Int64.unsigned_zero.
  rewrite Hz,HT,Int64.unsigned_zero in H; exact H.
Qed.
Lemma wide_extract_decomposition s :
  wide_value s = Int64.unsigned (wlo s) + Int64.modulus * wide_value (wide_extract s).
Proof. unfold wide_value; cbn [wide_extract wlo whi wtop]; rewrite Int64.unsigned_zero; ring. Qed.
Lemma wide_extract_value s : wide_value (wide_extract s) = wide_value s / Int64.modulus.
Proof.
  rewrite (wide_extract_decomposition s).
  replace (Int64.modulus * wide_value (wide_extract s)) with
    (wide_value (wide_extract s) * Int64.modulus) by ring.
  rewrite Z.div_add by discriminate.
  rewrite Z.div_small by apply Int64.unsigned_range; lia.
Qed.
Lemma wide_extract_fast_decomposition s : wtop s = Int64.zero ->
  wide_value s = Int64.unsigned (wlo s) + Int64.modulus * wide_value (wide_extract_fast s).
Proof.
  intro HT; unfold wide_value; cbn [wide_extract_fast wlo whi wtop].
  rewrite HT,Int64.unsigned_zero; ring.
Qed.
