(** Sticky overflow composition, including a crossing at an intermediate add. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import C.jet_elements_support_sha_uchars_exec C.jet_elements_support_sha_uchars_loop C.jet_elements_support_sha_ctx8_bridge.
Require Import C.jet_read_sha256_counter C.jet_elements_support_sha_ctx_abs.
Require Import C.jet_amount_exec_common C.jet_amount_exec_compose.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma sha_chain_overflow c m n :
  Int64.unsigned c < 2305843009213693952 -> 0 <= m <= 4096 -> 0 <= n <= 4096 ->
  uc_overflow (uc_overflow false c (Int64.repr m)) (Int64.add c (Int64.repr m)) (Int64.repr n) =
    uc_overflow false c (Int64.repr (m + n)).
Proof.
  intros HC HM HN. pose proof (Int64.unsigned_range c) as HR.
  assert (HS : Int64.unsigned (Int64.add c (Int64.repr m)) = Int64.unsigned c + m).
  { unfold Int64.add. rewrite (Int64.unsigned_repr m) by
      (change Int64.max_unsigned with 18446744073709551615; lia).
    apply Int64.unsigned_repr. change Int64.max_unsigned with 18446744073709551615; lia. }
  unfold uc_overflow. cbn [orb]. rewrite !cmpu_le_bool.
  rewrite (long_sub_unsigned sha_max_counter c) by
    (change (Int64.unsigned sha_max_counter) with 2305843009213693952; lia).
  change (Int64.unsigned sha_max_counter) with 2305843009213693952.
  rewrite (Int64.unsigned_repr m), (Int64.unsigned_repr n), (Int64.unsigned_repr (m + n)) by
    (change Int64.max_unsigned with 18446744073709551615; lia).
  destruct (Z.leb_spec (2305843009213693952 - Int64.unsigned c) m) as [HY|HY].
  - cbn [orb]. symmetry. apply Z.leb_le. lia.
  - cbn [orb]. rewrite long_sub_unsigned by
      (change (Int64.unsigned sha_max_counter) with 2305843009213693952; rewrite HS; lia).
    change (Int64.unsigned sha_max_counter) with 2305843009213693952. rewrite HS.
    destruct (Z.leb_spec (2305843009213693952 - (Int64.unsigned c + m)) n);
      destruct (Z.leb_spec (2305843009213693952 - Int64.unsigned c) (m + n));
      try reflexivity; lia.
Qed.

Lemma asset_amount_counter c a :
  Int64.add (Int64.add c (Int64.repr 33)) (Int64.repr (amount_count a)) =
    Int64.add c (Int64.repr (33 + amount_count a)).
Proof. rewrite Int64.add_assoc. destruct a; reflexivity. Qed.

Lemma asset_amount_overflow c a :
  Int64.unsigned c < 2305843009213693952 ->
  amount_overflow (asset_overflow false c) (Int64.add c (Int64.repr 33)) a =
    uc_overflow false c (Int64.repr (33 + amount_count a)).
Proof.
  intro HC. unfold amount_overflow, asset_overflow.
  rewrite (sha_chain_overflow c 1 32 HC ltac:(lia) ltac:(lia)).
  change (Int64.repr (1 + 32)) with (Int64.repr 33).
  rewrite (sha_chain_overflow c 33 1 HC ltac:(lia) ltac:(lia)).
  change (Int64.repr (33 + 1)) with (Int64.repr 34).
  rewrite Int64.add_assoc.
  change (Int64.add (Int64.repr 33) (Int64.repr 1)) with (Int64.repr 34).
  destruct a as [p|v]; cbn [amount_payload_count amount_count].
  - exact (sha_chain_overflow c 34 32 HC ltac:(lia) ltac:(lia)).
  - exact (sha_chain_overflow c 34 8 HC ltac:(lia) ltac:(lia)).
Qed.
