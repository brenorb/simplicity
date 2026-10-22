(** Shared bit-window arithmetic for the actual 52/62-bit repacking functions. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers.
Require Import C.jet_secp_signed62_repack C.jet_secp_fe_math C.jet_secp_fe_b32
 C.jet_secp_u128_word_shift C.jet_secp_multiply_finish_product C.jet_secp_multiply_checkpoint_columns
 C.jet_secp_multiply_normalize_bridge.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma repack_mask_unsigned x k : 0<=k<64 ->
 Int64.unsigned (Int64.and x (Int64.repr (2^k-1)))=Int64.unsigned x mod 2^k.
Proof.
 intro HK;rewrite <-two_p_equiv.
 rewrite <-Int64.zero_ext_and by lia.
 apply Int64.zero_ext_mod;exact HK.
Qed.

Lemma repack_join_mod lo hi shift width :
 0<=shift<=width -> 0<=lo<2^shift ->
 (lo+hi*2^shift) mod 2^width=lo+(hi mod 2^(width-shift))*2^shift.
Proof.
 intros HW HL.
 assert (E : 2^width=2^(width-shift)*2^shift).
 { rewrite <-Z.pow_add_r by lia;f_equal;lia. }
 assert (HP : 0<2^(width-shift)) by (apply Z.pow_pos_nonneg;lia).
 assert (HS : 0<2^shift) by (apply Z.pow_pos_nonneg;lia).
 pose proof (Z.mod_pos_bound hi _ HP) as R.
 pose proof (Z.div_mod hi (2^(width-shift)) ltac:(lia)) as D.
 symmetry;apply Z.mod_unique with (hi/2^(width-shift));[left;rewrite E;nia|rewrite E;nia].
Qed.

Lemma repack_masked_join_unsigned lo hi shift width :
 0<=shift<64 -> 0<=width<64 -> Int64.unsigned lo<2^shift ->
 Int64.unsigned (Int64.and (Int64.or lo (Int64.shl hi (Int64.repr shift)))
   (Int64.repr (2^width-1)))=
 (Int64.unsigned lo+Int64.unsigned hi*2^shift) mod 2^width.
Proof.
 intros HS HW HL;rewrite repack_mask_unsigned by exact HW.
 rewrite Int64.or_commut,Int64.shifted_or_is_add by
   (try exact HS;rewrite two_p_equiv;exact HL).
 rewrite two_p_equiv,Int64.unsigned_repr_eq.
 change Int64.modulus with (2^64).
 rewrite mod_mod_pow by lia;f_equal;ring.
Qed.

Lemma repack_shifted_join_unsigned a hi drop shift width :
 0<=drop<64 -> 0<=shift<64 -> 0<=width<64 ->
 Int64.unsigned a<2^(drop+shift) ->
 Int64.unsigned (Int64.and
   (Int64.or (Int64.shru a (Int64.repr drop)) (Int64.shl hi (Int64.repr shift)))
   (Int64.repr (2^width-1)))=
 (Int64.unsigned a/2^drop+Int64.unsigned hi*2^shift) mod 2^width.
Proof.
 intros HD HS HW HA.
 assert (HL : Int64.unsigned (Int64.shru a (Int64.repr drop))<2^shift).
 { rewrite uns_shru by exact HD.
   apply Z.div_lt_upper_bound;[apply Z.pow_pos_nonneg;lia|].
   rewrite Z.pow_add_r in HA by lia;nia. }
 rewrite (repack_masked_join_unsigned _ _ _ _ HS HW HL).
 rewrite uns_shru by exact HD;reflexivity.
Qed.

Definition fe_to62_value (w : nat -> Int64.int) i :=
 if Nat.eqb i 4 then Int64.unsigned (w 4%nat)/2^40
 else (Int64.unsigned (w i)/2^(10*Z.of_nat i)+
       Int64.unsigned (w (S i))*2^(52-10*Z.of_nat i)) mod 2^62.

Lemma fe_to62_words_numeric w :
 fe_limbs_ok (Int64.unsigned (w 0%nat)) (Int64.unsigned (w 1%nat))
  (Int64.unsigned (w 2%nat)) (Int64.unsigned (w 3%nat)) (Int64.unsigned (w 4%nat)) ->
 forall i,(i<5)%nat -> Int64.unsigned (fe_repack_words true w i)=fe_to62_value w i.
Proof.
 intros (B0 & B1 & B2 & B3 & B4) i HI.
 destruct i as [|[|[|[|[|i]]]]];try lia;
   cbn [fe_repack_words fe_to62_value nth Nat.eqb Z.of_nat].
 - rewrite repack_masked_join_unsigned by lia.
   change ((Int64.unsigned (w 0%nat)+Int64.unsigned (w 1%nat)*2^52) mod 2^62=
     (Int64.unsigned (w 0%nat)/1+Int64.unsigned (w 1%nat)*2^52) mod 2^62).
   rewrite Z.div_1_r;reflexivity.
 - apply repack_shifted_join_unsigned;lia.
 - apply repack_shifted_join_unsigned;lia.
 - apply repack_shifted_join_unsigned;lia.
 - apply uns_shru;lia.
Qed.

Definition signed62_unsigned_value (w : nat -> Int64.int) :=
 Int64.unsigned (w 0%nat)+2^62*Int64.unsigned (w 1%nat)+
 2^124*Int64.unsigned (w 2%nat)+2^186*Int64.unsigned (w 3%nat)+
 2^248*Int64.unsigned (w 4%nat).

Theorem fe_to62_preserves_value w :
 fe_limbs_ok (Int64.unsigned (w 0%nat)) (Int64.unsigned (w 1%nat))
  (Int64.unsigned (w 2%nat)) (Int64.unsigned (w 3%nat)) (Int64.unsigned (w 4%nat)) ->
 signed62_unsigned_value (fe_repack_words true w)=radix_value w.
Proof.
 intro Bound;unfold signed62_unsigned_value.
 rewrite !fe_to62_words_numeric by (exact Bound || lia).
 unfold fe_to62_value.
 set (a0:=Int64.unsigned (w 0%nat)) in *.
 set (a1:=Int64.unsigned (w 1%nat)) in *.
 set (a2:=Int64.unsigned (w 2%nat)) in *.
 set (a3:=Int64.unsigned (w 3%nat)) in *.
 set (a4:=Int64.unsigned (w 4%nat)) in *.
 destruct Bound as (B0 & B1 & B2 & B3 & B4).
 change ((a0/1+a1*2^52) mod 2^62+
   2^62*((a1/2^10+a2*2^42) mod 2^62)+
   2^124*((a2/2^20+a3*2^32) mod 2^62)+
   2^186*((a3/2^30+a4*2^22) mod 2^62)+2^248*(a4/2^40)=
   radix_value w).
 rewrite Z.div_1_r.
 rewrite (repack_join_mod a0 a1 52 62 ltac:(lia) ltac:(lia)).
 rewrite (repack_join_mod (a1/2^10) a2 42 62 ltac:(lia)
   ltac:(split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia])).
 rewrite (repack_join_mod (a2/2^20) a3 32 62 ltac:(lia)
   ltac:(split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia])).
 rewrite (repack_join_mod (a3/2^30) a4 22 62 ltac:(lia)
   ltac:(split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia])).
 pose proof (Z.div_mod a1 (2^10) ltac:(lia)) as E1.
 pose proof (Z.div_mod a2 (2^20) ltac:(lia)) as E2.
 pose proof (Z.div_mod a3 (2^30) ltac:(lia)) as E3.
 pose proof (Z.div_mod a4 (2^40) ltac:(lia)) as E4.
 change (radix_value w) with (a0+2^52*a1+2^104*a2+2^156*a3+2^208*a4).
 change (62-52) with 10;change (62-42) with 20;
   change (62-32) with 30;change (62-22) with 40.
 lia.
Qed.

Definition signed62_normalized (w : nat -> Int64.int) :=
 forall i,(i<5)%nat ->
 0<=Int64.unsigned (w i)<if Nat.eqb i 4 then 2^8 else 2^62.

Lemma fe_to62_normalized w :
 fe_limbs_ok (Int64.unsigned (w 0%nat)) (Int64.unsigned (w 1%nat))
  (Int64.unsigned (w 2%nat)) (Int64.unsigned (w 3%nat)) (Int64.unsigned (w 4%nat)) ->
 signed62_normalized (fe_repack_words true w).
Proof.
 intros Bound i HI;rewrite fe_to62_words_numeric by assumption.
 unfold fe_to62_value;destruct (Nat.eqb i 4) eqn:E.
 - destruct Bound as (B0 & B1 & B2 & B3 & B4).
   split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia].
 - apply Z.mod_pos_bound;lia.
Qed.

Lemma repack_join_unsigned lo hi shift :
 0<=shift<64 -> Int64.unsigned lo<2^shift ->
 Int64.unsigned lo+Int64.unsigned hi*2^shift<2^64 ->
 Int64.unsigned (Int64.or lo (Int64.shl hi (Int64.repr shift)))=
 Int64.unsigned lo+Int64.unsigned hi*2^shift.
Proof.
 intros HS HL HB.
 rewrite Int64.or_commut,Int64.shifted_or_is_add by
   (try exact HS;rewrite two_p_equiv;exact HL).
 rewrite two_p_equiv,Z.add_comm,Z.mul_comm.
 apply Int64.unsigned_repr.
 split;[pose proof (Int64.unsigned_range_2 lo);pose proof (Int64.unsigned_range_2 hi);
   pose proof (Z.pow_pos_nonneg 2 shift ltac:(lia) ltac:(lia));nia|].
 change Int64.max_unsigned with (2^64-1);lia.
Qed.

Definition fe_from62_value (w : nat -> Int64.int) i :=
 match i with
 | O => Int64.unsigned (w 0%nat) mod 2^52
 | S O => (Int64.unsigned (w 0%nat)/2^52+Int64.unsigned (w 1%nat)*2^10) mod 2^52
 | S (S O) => (Int64.unsigned (w 1%nat)/2^42+Int64.unsigned (w 2%nat)*2^20) mod 2^52
 | S (S (S O)) => (Int64.unsigned (w 2%nat)/2^32+Int64.unsigned (w 3%nat)*2^30) mod 2^52
 | _ => Int64.unsigned (w 3%nat)/2^22+Int64.unsigned (w 4%nat)*2^40
 end.

Lemma fe_from62_words_numeric w : signed62_normalized w ->
 forall i,(i<5)%nat -> Int64.unsigned (fe_repack_words false w i)=fe_from62_value w i.
Proof.
 intros Bound i HI.
 pose proof (Bound 0%nat ltac:(lia)) as B0.
 pose proof (Bound 1%nat ltac:(lia)) as B1.
 pose proof (Bound 2%nat ltac:(lia)) as B2.
 pose proof (Bound 3%nat ltac:(lia)) as B3.
 pose proof (Bound 4%nat ltac:(lia)) as B4.
 cbn [Nat.eqb] in B0,B1,B2,B3,B4.
 destruct i as [|[|[|[|[|i]]]]];try lia;
   cbn [fe_repack_words fe_from62_value nth].
 - apply repack_mask_unsigned;lia.
 - apply repack_shifted_join_unsigned;lia.
 - apply repack_shifted_join_unsigned;lia.
 - apply repack_shifted_join_unsigned;lia.
 - rewrite repack_join_unsigned.
   + rewrite uns_shru by lia;reflexivity.
   + lia.
   + rewrite uns_shru by lia;apply Z.div_lt_upper_bound;lia.
   + rewrite uns_shru by lia.
     assert (Int64.unsigned (w 3%nat)/2^22<2^40) by (apply Z.div_lt_upper_bound;lia).
     lia.
Qed.

Theorem fe_from62_preserves_value w : signed62_normalized w ->
 radix_value (fe_repack_words false w)=signed62_unsigned_value w.
Proof.
 intro Bound;unfold radix_value.
 rewrite !fe_from62_words_numeric by (exact Bound || lia).
 unfold fe_from62_value,signed62_unsigned_value.
 pose proof (Bound 0%nat ltac:(lia)) as B0.
 pose proof (Bound 1%nat ltac:(lia)) as B1.
 pose proof (Bound 2%nat ltac:(lia)) as B2.
 cbn [Nat.eqb] in B0,B1,B2.
 set (a0:=Int64.unsigned (w 0%nat)) in *.
 set (a1:=Int64.unsigned (w 1%nat)) in *.
 set (a2:=Int64.unsigned (w 2%nat)) in *.
 set (a3:=Int64.unsigned (w 3%nat)) in *.
 set (a4:=Int64.unsigned (w 4%nat)) in *.
 change (a0 mod 2^52+
   2^52*((a0/2^52+a1*2^10) mod 2^52)+
   2^104*((a1/2^42+a2*2^20) mod 2^52)+
   2^156*((a2/2^32+a3*2^30) mod 2^52)+
   2^208*(a3/2^22+a4*2^40)=
   a0+2^62*a1+2^124*a2+2^186*a3+2^248*a4).
 rewrite (repack_join_mod (a0/2^52) a1 10 52 ltac:(lia)
   ltac:(split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia])).
 rewrite (repack_join_mod (a1/2^42) a2 20 52 ltac:(lia)
   ltac:(split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia])).
 rewrite (repack_join_mod (a2/2^32) a3 30 52 ltac:(lia)
   ltac:(split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia])).
 change (52-10) with 42;change (52-20) with 32;change (52-30) with 22.
 pose proof (Z.div_mod a0 (2^52) ltac:(lia)) as E0.
 pose proof (Z.div_mod a1 (2^42) ltac:(lia)) as E1.
 pose proof (Z.div_mod a2 (2^32) ltac:(lia)) as E2.
 pose proof (Z.div_mod a3 (2^22) ltac:(lia)) as E3.
 lia.
Qed.

Theorem fe_from62_positioned w : signed62_normalized w ->
 fe_limbs_ok (Int64.unsigned (fe_repack_words false w 0%nat))
  (Int64.unsigned (fe_repack_words false w 1%nat))
  (Int64.unsigned (fe_repack_words false w 2%nat))
  (Int64.unsigned (fe_repack_words false w 3%nat))
  (Int64.unsigned (fe_repack_words false w 4%nat)).
Proof.
 intro Bound.
 assert (Low : forall i,(i<4)%nat -> 0<=Int64.unsigned (fe_repack_words false w i)<2^52).
 { intros i HI;rewrite fe_from62_words_numeric by (exact Bound || lia).
   destruct i as [|[|[|[|i]]]];try lia;cbn [fe_from62_value];apply Z.mod_pos_bound;lia. }
 pose proof (Low 0%nat ltac:(lia)) as B0.
 pose proof (Low 1%nat ltac:(lia)) as B1.
 pose proof (Low 2%nat ltac:(lia)) as B2.
 pose proof (Low 3%nat ltac:(lia)) as B3.
 assert (Top : 0<=Int64.unsigned (fe_repack_words false w 4%nat)<2^48).
 { rewrite fe_from62_words_numeric by (exact Bound || lia).
   cbn [fe_from62_value].
   pose proof (Bound 3%nat ltac:(lia)) as BHi.
   pose proof (Bound 4%nat ltac:(lia)) as BTop.
   cbn [Nat.eqb] in BHi,BTop.
   assert (D : 0<=Int64.unsigned (w 3%nat)/2^22<2^40)
    by (split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia]).
   lia. }
 unfold fe_limbs_ok;lia.
Qed.

Theorem fe_signed62_roundtrip w :
 fe_limbs_ok (Int64.unsigned (w 0%nat)) (Int64.unsigned (w 1%nat))
  (Int64.unsigned (w 2%nat)) (Int64.unsigned (w 3%nat)) (Int64.unsigned (w 4%nat)) ->
 words5 (fe_repack_words false (fe_repack_words true w))=words5 w.
Proof.
 intro Bound;set (out:=fe_repack_words false (fe_repack_words true w)).
 assert (OB : fe_limbs_ok (Int64.unsigned (out 0%nat)) (Int64.unsigned (out 1%nat))
   (Int64.unsigned (out 2%nat)) (Int64.unsigned (out 3%nat)) (Int64.unsigned (out 4%nat))).
 { apply fe_from62_positioned,fe_to62_normalized;exact Bound. }
 assert (Value : radix_value out=radix_value w).
 { unfold out;rewrite fe_from62_preserves_value by (apply fe_to62_normalized;exact Bound).
   apply fe_to62_preserves_value;exact Bound. }
 pose proof (fe_limbs_unique _ _ _ _ _ (radix_value w) Bound
   (eq_sym (radix_value_matches_normalizer w))) as Input.
 pose proof (fe_limbs_unique _ _ _ _ _ (radix_value w) OB
   (eq_trans (eq_sym (radix_value_matches_normalizer out)) Value)) as Output.
 rewrite <-Input in Output.
 pose proof (f_equal (map Int64.repr) Output) as Words.
 cbn [map] in Words;rewrite !Int64.repr_unsigned in Words;exact Words.
Qed.
