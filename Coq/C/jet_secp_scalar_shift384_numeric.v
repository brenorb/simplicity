(** Exact quotient and round bit of all eight product limbs. The rounded
    value is allowed to equal 2^128; no low-128 truncation is introduced. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import C.jet_secp_scalar_mul512_accumulate C.jet_secp_scalar_shift384_round
 C.jet_secp_scalar_shift384_stores C.jet_secp_scalar_get_b32_numeric
 C.jet_secp_scalar_limb_bridge C.jet_secp_scalar_split128_literal.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition shift384_product_value (w:nat->int64) := column_words_value (map w (seq 0 8)).
Definition shift384_quotient (w:nat->int64) := Int64.unsigned (w 6%nat)+2^64*Int64.unsigned (w 7%nat).
Definition shift384_low w := column_words_value (map w (seq 0 6)).
Definition shift384_low5 w := column_words_value (map w (seq 0 5)).

Lemma shift384_product_decomposition w :
 shift384_product_value w=shift384_low w+2^384*shift384_quotient w /\
 shift384_low w=shift384_low5 w+2^320*Int64.unsigned (w 5%nat).
Proof.
 assert (P:map w (seq 0 8)=map w (seq 0 6)++[w 6%nat;w 7%nat]) by reflexivity.
 assert (L:map w (seq 0 6)=map w (seq 0 5)++[w 5%nat]) by reflexivity.
 split.
 - unfold shift384_product_value;rewrite P,column_words_append.
   change (column_words_value (map w (seq 0 6))+2^384*column_words_value [w 6%nat;w 7%nat]=
    shift384_low w+2^384*shift384_quotient w).
   unfold shift384_low,shift384_quotient;cbn [column_words_value];change Int64.modulus with (2^64);ring.
 - unfold shift384_low;rewrite L,column_words_append.
   change (column_words_value (map w (seq 0 5))+2^320*column_words_value [w 5%nat]=
    shift384_low5 w+2^320*Int64.unsigned (w 5%nat)).
   unfold shift384_low5;cbn [column_words_value];ring.
Qed.

Lemma shift384_low_bounds w : 0<=shift384_low w<2^384 /\ 0<=shift384_low5 w<2^320.
Proof.
 pose proof (column_words_bound (map w (seq 0 6))) as Low.
 pose proof (column_words_bound (map w (seq 0 5))) as Low5.
 split;[exact Low|exact Low5].
Qed.
Lemma shift384_quotient_bounds w : 0<=shift384_quotient w<2^128.
Proof.
 unfold shift384_quotient;pose proof (Int64.unsigned_range (w 6%nat));pose proof (Int64.unsigned_range (w 7%nat)).
 change Int64.modulus with (2^64) in *;lia.
Qed.
Lemma shift384_quotient_value w : shift384_product_value w/2^384=shift384_quotient w.
Proof.
 destruct (shift384_product_decomposition w) as [P _].
 destruct (shift384_low_bounds w) as [Low _].
 rewrite P;replace (2^384*shift384_quotient w) with (shift384_quotient w*2^384) by ring.
 rewrite Z.div_add by lia;rewrite Z.div_small by exact Low;lia.
Qed.
Lemma shift384_quotient_limbs w :
 map Int64.repr (scalar_limbs_of (shift384_quotient w))=shift384_words w.
Proof. apply scalar_split128_two_word_limbs. Qed.

Theorem shift384_rounded_value w :
 shift384_quotient w+(if shift384_round_flag (w 5%nat) then 1 else 0)=
 (shift384_product_value w+2^383)/2^384.
Proof.
 destruct (shift384_product_decomposition w) as [Product Low].
 destruct (shift384_low_bounds w) as [LowBound Low5Bound].
 pose proof (proj2 (shift384_round_value (w 5%nat))) as Round.
 pose proof (Z.div_mod (Int64.unsigned (w 5%nat)) (2^63) ltac:(lia)) as Divide.
 pose proof (Z.mod_pos_bound (Int64.unsigned (w 5%nat)) (2^63) ltac:(lia)) as Remainder.
 destruct (shift384_round_flag (w 5%nat)).
 - apply Z.div_unique with (r:=shift384_low w-2^383);[lia|].
   rewrite Product;ring.
 - apply Z.div_unique with (r:=shift384_low w+2^383);[lia|].
   rewrite Product;ring.
Qed.

Corollary shift384_rounded_bounds w :
 0<=(shift384_product_value w+2^383)/2^384<=2^128.
Proof. rewrite <-shift384_rounded_value;pose proof (shift384_quotient_bounds w);destruct (shift384_round_flag (w 5%nat));lia. Qed.
