(** Shared equality between the field serializer's bytes and word encoding. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_word_repr C.jet_read8s_layout C.jet_buffer_input C.jet_sha_word_bytes
 C.jet_secp_fe_math C.jet_secp_fe_b32 C.jet_secp_b32_exec C.jet_secp_input_bytes
 C.jet_secp_output_bytes C.jet_secp_generator_codec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma be_val_bytes_unique xs ys:
 length xs=length ys ->Forall (fun b=>0<=b<=255) xs ->Forall (fun b=>0<=b<=255) ys ->
 be_val xs=be_val ys ->xs=ys.
Proof.
 revert ys;induction xs as [|a xs IH];intros [|b ys] Length BX BY Value;try discriminate;[reflexivity|].
 inversion BX as [|a' xs' AX AXS];subst.
 inversion BY as [|b' ys' AY AYS];subst.
 injection Length as Length.
 pose proof (fold_be_bytes_bound xs AXS 0 ltac:(lia)) as RX.
 pose proof (fold_be_bytes_bound ys AYS 0 ltac:(lia)) as RY.
 rewrite Z.mul_0_l,Z.add_0_l,Z.mul_1_l in RX,RY.
 change (0<=be_val xs<256^Z.of_nat (length xs)) in RX.
 change (0<=be_val ys<256^Z.of_nat (length ys)) in RY.
 rewrite be_val_cons,be_val_cons,<-Length in Value.
 rewrite <-Length in RY.
 assert (Positive:0<256^Z.of_nat (length xs)) by (apply Z.pow_pos_nonneg;lia).
 assert (Same:a=b) by nia;subst b.
 f_equal;apply IH;[exact Length|exact AXS|exact AYS|nia].
Qed.
Lemma word256_unsigned_bytes_bounds (w:Ty.tySem (Word 8)):
 Forall (fun b=>0<=b<=255) (map Int.unsigned (map word8_array_value (vector_values (Word 3) 5 w))).
Proof.
 rewrite map_map;apply Forall_forall;intros b Member.
 apply in_map_iff in Member as (x & <- & Member).
 unfold word8_array_value;rewrite Int.unsigned_repr.
 - pose proof (word_toZ_range 3 x);change (0<=@toZ (WordToZ 3) x<256) in H;lia.
 - pose proof (word_toZ_range 3 x);change (0<=@toZ (WordToZ 3) x<256) in H;
   change Int.max_unsigned with 4294967295;lia.
Qed.
Theorem word256_serializer_bytes (w:Ty.tySem (Word 8)):
 map Int.repr (C.jet_secp_fe_b32.be_bytes (@toZ (WordToZ 8) w))=map word8_array_value (vector_values (Word 3) 5 w).
Proof.
 assert (Unsigned:C.jet_secp_fe_b32.be_bytes (@toZ (WordToZ 8) w)=
   map Int.unsigned (map word8_array_value (vector_values (Word 3) 5 w))).
 { apply be_val_bytes_unique.
   - unfold C.jet_secp_fe_b32.be_bytes;rewrite map_length,seq_length,!map_length,vector_values_length;reflexivity.
   - rewrite <-be_chunks_32;eapply Forall_impl;[|apply be_chunks_byte_bounds];intros b Bound;change (0<=b<256) in Bound;lia.
   - apply word256_unsigned_bytes_bounds.
   - rewrite generator_be_bytes_value by apply word_toZ_range.
     symmetry;apply word256_bytes_integer. }
 rewrite Unsigned,map_map.
 change (map (fun x=>Int.repr (Int.unsigned x)) (map word8_array_value (vector_values (Word 3) 5 w))=map word8_array_value (vector_values (Word 3) 5 w)).
 transitivity (map (fun x:int=>x) (map word8_array_value (vector_values (Word 3) 5 w))).
 - apply map_ext;intro x;apply Int.repr_unsigned.
 - apply map_id.
Qed.
