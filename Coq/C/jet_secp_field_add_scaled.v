(** Original fe_add for a tight field plus seven times a tight field.
    The projective curve checker keeps this loose sum for the equality call. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_field_add_owned C.jet_secp_field_add_storage C.jet_secp_field_add_values
  C.jet_secp_field_add C.jet_secp_curve_tail_values C.jet_secp_curve_frame.
Require Import C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition field_sum_words (a b : nat -> int64) (i : nat) := Int64.add (a i) (b i).

Lemma field_sum_output a b : add_values (curve_equal_rho a b)=words5 (field_sum_words a b).
Proof. reflexivity. Qed.

Lemma field_sum_unsigned a b i :
  Int64.unsigned (a i)+Int64.unsigned (b i)<=Int64.max_unsigned ->
  Int64.unsigned (field_sum_words a b i)=Int64.unsigned (a i)+Int64.unsigned (b i).
Proof.
  intro HB;unfold field_sum_words,Int64.add.
  rewrite Int64.unsigned_repr;[reflexivity|].
  pose proof (Int64.unsigned_range_2 (a i));pose proof (Int64.unsigned_range_2 (b i));lia.
Qed.

Lemma field_sum_scaled_nowrap a b :
  (forall i, (i<5)%nat -> Int64.unsigned (a i)<
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) ->
  (forall i, (i<5)%nat -> Int64.unsigned (b i)<
    if Nat.eqb i 4 then 3940649673949184 else 31525197391593472) ->
  forall i, (i<5)%nat -> Int64.unsigned (a i)+Int64.unsigned (b i)<=Int64.max_unsigned.
Proof.
  intros HA HB i HI;pose proof (HA i HI);pose proof (HB i HI).
  change Int64.max_unsigned with 18446744073709551615;destruct (Nat.eqb i 4);lia.
Qed.

Lemma field_sum_scaled_value a b :
  (forall i, (i<5)%nat -> Int64.unsigned (a i)<
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) ->
  (forall i, (i<5)%nat -> Int64.unsigned (b i)<
    if Nat.eqb i 4 then 3940649673949184 else 31525197391593472) ->
  radix_value (field_sum_words a b)=radix_value a+radix_value b /\ square_input_bounds (field_sum_words a b).
Proof.
  intros HA HB;pose proof (field_sum_scaled_nowrap a b HA HB) as HN.
  split.
  - rewrite !radix_value_matches_normalizer;unfold fe_val.
    rewrite (field_sum_unsigned a b 0%nat (HN 0%nat ltac:(lia))),
      (field_sum_unsigned a b 1%nat (HN 1%nat ltac:(lia))),
      (field_sum_unsigned a b 2%nat (HN 2%nat ltac:(lia))),
      (field_sum_unsigned a b 3%nat (HN 3%nat ltac:(lia))),
      (field_sum_unsigned a b 4%nat (HN 4%nat ltac:(lia)));ring.
  - intros i HI;rewrite field_sum_unsigned by (apply HN;exact HI).
    pose proof (HA i HI);pose proof (HB i HI);destruct (Nat.eqb i 4);lia.
Qed.

Theorem eval_field_add_scaled a b m ba bb :
  (forall i, (i<5)%nat -> Int64.unsigned (a i)<
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) ->
  (forall i, (i<5)%nat -> Int64.unsigned (b i)<
    if Nat.eqb i 4 then 3940649673949184 else 31525197391593472) ->
  ba<>bb -> fe_at m ba 0 (words5 a) -> fe_at m bb 0 (words5 b) ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bb 0 40 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add)
    [Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf Vundef /\
  fe_at mf ba 0 (words5 (field_sum_words a b)) /\
  Mem.range_perm mf ba 0 40 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
  radix_value (field_sum_words a b)=radix_value a+radix_value b /\ square_input_bounds (field_sum_words a b) /\
  lframe (fun bx _ => bx<>ba /\ bx<>bb) m mf.
Proof.
  intros BA BB HNe HA HB HFA HFB.
  destruct (eval_field_add_owned m ba bb (curve_equal_rho a b) HNe HA HB HFA HFB)
    as (mf & HC & FO & FFA & FFB & HL).
  rewrite field_sum_output in FO.
  destruct (field_sum_scaled_value a b BA BB) as [HV HBounds].
  exists mf;split;[exact HC|]. split;[exact FO|]. split;[exact FFA|]. split;[exact FFB|].
  split;[exact HV|]. split;[exact HBounds|].
  exact (curve_frame_two field_add_initial_regs ba bb m mf eq_refl HL).
Qed.
