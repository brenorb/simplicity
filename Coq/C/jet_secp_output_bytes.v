(** Exact big-endian byte encoding of canonical Simplicity Word256 values. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jet_encoding C.jet_input_layout C.jet_spec C.jet_write8_sequence C.jet_secp_fe_b32.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma msb_bits_mod N value : msb_bits N (value mod 2 ^ Z.of_nat N) = msb_bits N value.
Proof.
  unfold msb_bits; apply map_ext_in; intros i HIn; apply in_seq in HIn.
  rewrite Z.mod_pow2_bits_low by lia; reflexivity.
Qed.
Fixpoint be_chunks count value : list Z :=
  match count with O => [] | S n =>
    (value / 2 ^ (8 * Z.of_nat n)) mod 256 :: be_chunks n value end.
Lemma be_chunks_bits count value :
  concat (map (msb_bits 8) (be_chunks count value)) = msb_bits (8 * count) value.
Proof.
  induction count as [|count IH]; [reflexivity|].
  cbn [be_chunks map concat]; rewrite IH.
  change (msb_bits 8 ((value / 2 ^ (8 * Z.of_nat count)) mod 2 ^ Z.of_nat 8) ++
    msb_bits (8 * count) value = msb_bits (8 * S count) value).
  rewrite msb_bits_mod; symmetry.
  replace (8 * S count)%nat with (8 + 8 * count)%nat by lia.
  replace (8 * Z.of_nat count) with (Z.of_nat (8 * count)) by lia.
  assert (HDecomp : value = (value / 2 ^ Z.of_nat (8 * count)) * 2 ^ Z.of_nat (8 * count) +
    value mod 2 ^ Z.of_nat (8 * count)).
  { pose proof (Z.div_mod value (2 ^ Z.of_nat (8 * count)) ltac:(apply Z.pow_nonzero; lia)); lia. }
  rewrite HDecomp at 1.
  rewrite msb_bits_app by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  rewrite msb_bits_mod; reflexivity.
Qed.
Lemma be_chunks_32 value : be_chunks 32 value = be_bytes value.
Proof. reflexivity. Qed.
Lemma be_chunks_byte_bounds count value : Forall (fun byte => 0 <= byte < 256) (be_chunks count value).
Proof.
  induction count; cbn [be_chunks]; constructor; [apply Z.mod_pos_bound; lia|exact IHcount].
Qed.
Lemma machine_byte_encoding byte :
  0 <= byte < 256 ->
  encode (decode_word8 (Int64.repr (Int.unsigned (Int.repr byte)))) = map Some (msb_bits 8 byte).
Proof.
  intro HByte; rewrite encode_word, frame_input_word_bits_msb.
  unfold decode_word8; rewrite to_fromZ.
  rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
  rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
  change (map Some (msb_bits 8 (byte mod 256)) = map Some (msb_bits 8 byte)).
  rewrite Z.mod_small by exact HByte; reflexivity.
Qed.
Theorem be_bytes_canonical_encoding (value : Ty.tySem (Word 8)) :
  byte_sequence_cells (map Int.repr (be_bytes (@toZ (WordToZ 8) value))) = encode value.
Proof.
  rewrite <- be_chunks_32; unfold byte_sequence_cells; rewrite map_map.
  replace (map (fun byte => encode (decode_word8 (Int64.repr (Int.unsigned (Int.repr byte)))))
    (be_chunks 32 (@toZ (WordToZ 8) value))) with
    (map (fun byte => map Some (msb_bits 8 byte)) (be_chunks 32 (@toZ (WordToZ 8) value))).
  - rewrite <- map_map, <- concat_map.
    rewrite be_chunks_bits, encode_word, frame_input_word_bits_msb; reflexivity.
  - apply map_ext_in; intros byte HIn; symmetry; apply machine_byte_encoding.
    exact (proj1 (Forall_forall _ _) (be_chunks_byte_bounds 32 (@toZ (WordToZ 8) value)) byte HIn).
Qed.
