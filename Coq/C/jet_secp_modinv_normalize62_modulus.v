(** Shared signed62 numeric interpretation of the original normalize_62
    machine operations. Modulus-specific loads are discharged by callers;
    these internal bounds must still be established by the inverse loop. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers.
Require Import C.jet_secp_modinv_normalize62_words C.jet_secp_modinv_normalize62_exec
 C.jet_secp_signed62_numeric.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition modnorm62_limb_bounds w :=
 forall i, (i<5)%nat -> -(2^62-1)<=Int64.signed (w i)<=2^62-1.

Section Modulus.
Variables (mu : nat -> int64) (M : Z).
Hypothesis ModBounds : modnorm62_limb_bounds mu.
Hypothesis ModValue : norm62_value_z 4 (fun i=>Int64.signed (mu i))=M.
Hypothesis ModSize : 2^248<=M<=2^256.

Definition modnorm62_first w sign := norm62_neg_words (norm62_add_words w mu) sign.

Lemma modnorm62_first_signed w sign i : modnorm62_limb_bounds w -> (i<5)%nat ->
 Int64.signed (modnorm62_first w sign i)=
 (if Int64.lt sign Int64.zero then -1 else 1) *
 (Int64.signed (w i)+
  if Int64.lt (w 4%nat) Int64.zero then Int64.signed (mu i) else 0).
Proof.
 intros Bound I.
 pose proof (Bound i I) as B;pose proof (ModBounds i I) as MB.
 assert (Add : Int64.signed (norm62_add_words w mu i)=
   Int64.signed (w i)+
   if Int64.lt (w 4%nat) Int64.zero then Int64.signed (mu i) else 0).
 { rewrite norm62_add_word_cases. destruct (Int64.lt (w 4%nat) Int64.zero).
   - apply norm62_signed_add;change Int64.min_signed with (-9223372036854775808);
      change Int64.max_signed with 9223372036854775807;lia.
   - lia. }
 unfold modnorm62_first;rewrite norm62_neg_word_cases.
 destruct (Int64.lt sign Int64.zero).
 - rewrite norm62_signed_neg.
   + rewrite Add;ring.
   + rewrite Add;destruct (Int64.lt (w 4%nat) Int64.zero);
      change Int64.min_signed with (-9223372036854775808);
      change Int64.max_signed with 9223372036854775807;lia.
 - rewrite Add;ring.
Qed.

Lemma modnorm62_first_bound w sign : modnorm62_limb_bounds w ->
 forall i, (i<5)%nat ->
 Int64.min_signed+2<=Int64.signed (modnorm62_first w sign i)<=Int64.max_signed-1.
Proof.
 intros Bound i I;rewrite modnorm62_first_signed by assumption.
 pose proof (Bound i I);pose proof (ModBounds i I).
 destruct (Int64.lt sign Int64.zero);destruct (Int64.lt (w 4%nat) Int64.zero);
 change Int64.min_signed with (-9223372036854775808);
 change Int64.max_signed with 9223372036854775807;lia.
Qed.

Lemma modnorm62_first_value w sign : modnorm62_limb_bounds w ->
 norm62_value_z 4 (fun i=>Int64.signed (modnorm62_first w sign i))=
 (if Int64.lt sign Int64.zero then -1 else 1) *
 (norm62_value_z 4 (fun i=>Int64.signed (w i))+
  if Int64.lt (w 4%nat) Int64.zero then M else 0).
Proof.
 intro Bound;pose proof ModValue as MV;cbn [norm62_value_z] in MV|-*.
 rewrite !modnorm62_first_signed by (exact Bound||lia).
 destruct (Int64.lt sign Int64.zero);destruct (Int64.lt (w 4%nat) Int64.zero);lia.
Qed.

Lemma modnorm62_first_range w sign : modnorm62_limb_bounds w ->
 -2*M<norm62_value_z 4 (fun i=>Int64.signed (w i))<M ->
 -M<norm62_value_z 4 (fun i=>Int64.signed (modnorm62_first w sign i))<M.
Proof.
 intros Bound Value;rewrite modnorm62_first_value by exact Bound.
 pose proof (Bound 0%nat ltac:(lia)) as B0.
 pose proof (Bound 1%nat ltac:(lia)) as B1.
 pose proof (Bound 2%nat ltac:(lia)) as B2.
 pose proof (Bound 3%nat ltac:(lia)) as B3.
 pose proof (Bound 4%nat ltac:(lia)) as B4.
 unfold Int64.lt;rewrite Int64.signed_zero.
 destruct (zlt (Int64.signed sign) 0);
 destruct (zlt (Int64.signed (w 4%nat)) 0);
 cbn [norm62_value_z] in Value|-*;pose proof ModSize;lia.
Qed.

Lemma modnorm62_unsigned_nonnegative a : 0<=Int64.signed a ->
 Int64.unsigned a=Int64.signed a.
Proof.
 intro Nonneg;rewrite <-(Int64.repr_signed a) at 1.
 apply Int64.unsigned_repr;pose proof (Int64.signed_range a).
 change Int64.max_signed with 9223372036854775807 in *.
 change Int64.max_unsigned with 18446744073709551615;lia.
Qed.

Lemma modnorm62_canonical_from_value w :
 (forall i,(i<4)%nat -> 0<=Int64.signed (w i)<2^62) ->
 0<=norm62_value_z 4 (fun i=>Int64.signed (w i))<M ->
 signed62_normalized w /\
 signed62_unsigned_value w=norm62_value_z 4 (fun i=>Int64.signed (w i)).
Proof.
 intros Low Value.
 pose proof (Low 0%nat ltac:(lia)) as L0;pose proof (Low 1%nat ltac:(lia)) as L1;
 pose proof (Low 2%nat ltac:(lia)) as L2;pose proof (Low 3%nat ltac:(lia)) as L3.
 assert (Top : 0<=Int64.signed (w 4%nat)<256).
 { cbn [norm62_value_z] in Value;pose proof ModSize;lia. }
 assert (Nonneg : forall i,(i<5)%nat -> 0<=Int64.signed (w i)).
 { intros i I;destruct (Nat.eq_dec i 4) as [->|NE];[lia|pose proof (Low i ltac:(lia));lia]. }
 split.
 - intros i I;rewrite modnorm62_unsigned_nonnegative by (apply Nonneg;exact I).
   destruct (Nat.eqb i 4) eqn:E.
   + apply Nat.eqb_eq in E;subst i;exact Top.
   + apply Nat.eqb_neq in E;apply Low;lia.
 - unfold signed62_unsigned_value;rewrite !modnorm62_unsigned_nonnegative by (apply Nonneg;lia).
   cbn [norm62_value_z];ring.
Qed.

Lemma modnorm62_top_range w :
 (forall i,(i<4)%nat -> 0<=Int64.signed (w i)<2^62) ->
 -M<norm62_value_z 4 (fun i=>Int64.signed (w i))<M ->
 -256<=Int64.signed (w 4%nat)<=255.
Proof.
 intros Low Value.
 pose proof (Low 0%nat ltac:(lia));pose proof (Low 1%nat ltac:(lia));
 pose proof (Low 2%nat ltac:(lia));pose proof (Low 3%nat ltac:(lia)).
 cbn [norm62_value_z] in Value;pose proof ModSize;lia.
Qed.

Definition modnorm62_carried w :=
 (forall i,(i<4)%nat -> 0<=Int64.signed (w i)<2^62) /\
 -256<=Int64.signed (w 4%nat)<=255.

Lemma modnorm62_first_carried w sign : modnorm62_limb_bounds w ->
 -2*M<norm62_value_z 4 (fun i=>Int64.signed (w i))<M ->
 modnorm62_carried (norm62_carry_words (modnorm62_first w sign)) /\
 -M<norm62_value_z 4 (fun i=>Int64.signed (norm62_carry_words (modnorm62_first w sign) i))<M.
Proof.
 intros Bounds Value.
 pose proof (modnorm62_first_bound w sign Bounds) as B.
 pose proof (norm62_carry_words_low _ B) as Low.
 pose proof (modnorm62_first_range w sign Bounds Value) as V.
 rewrite <-norm62_carry_words_value in V by exact B.
 split;[split;[exact Low|apply modnorm62_top_range;assumption]|exact V].
Qed.

Lemma modnorm62_second_signed w : modnorm62_carried w -> forall i,(i<5)%nat ->
 Int64.signed (norm62_add_words w mu i)=
 Int64.signed (w i)+
 if Int64.lt (w 4%nat) Int64.zero then Int64.signed (mu i) else 0.
Proof.
 intros (Low & Top) i I;rewrite norm62_add_word_cases.
 destruct (Int64.lt (w 4%nat) Int64.zero);[|lia].
 apply norm62_signed_add;pose proof (ModBounds i I).
 destruct (Nat.eq_dec i 4) as [->|NE];[|pose proof (Low i ltac:(lia))];
 change Int64.min_signed with (-9223372036854775808);
 change Int64.max_signed with 9223372036854775807;lia.
Qed.

Lemma modnorm62_second_bound w : modnorm62_carried w -> forall i,(i<5)%nat ->
 Int64.min_signed+2<=Int64.signed (norm62_add_words w mu i)<=Int64.max_signed-1.
Proof.
 intros Carried i I;rewrite modnorm62_second_signed by assumption.
 destruct Carried as (Low & Top);pose proof (ModBounds i I).
 destruct (Nat.eq_dec i 4) as [->|NE];[|pose proof (Low i ltac:(lia))];
 destruct (Int64.lt (w 4%nat) Int64.zero);
 change Int64.min_signed with (-9223372036854775808);
 change Int64.max_signed with 9223372036854775807;lia.
Qed.

Lemma modnorm62_second_value w : modnorm62_carried w ->
 norm62_value_z 4 (fun i=>Int64.signed (norm62_add_words w mu i))=
 norm62_value_z 4 (fun i=>Int64.signed (w i))+
 if Int64.lt (w 4%nat) Int64.zero then M else 0.
Proof.
 intro Carried;pose proof ModValue as MV;cbn [norm62_value_z] in MV|-*.
 rewrite !modnorm62_second_signed by (exact Carried||lia).
 destruct (Int64.lt (w 4%nat) Int64.zero);lia.
Qed.

Lemma modnorm62_second_range w : modnorm62_carried w ->
 -M<norm62_value_z 4 (fun i=>Int64.signed (w i))<M ->
 0<=norm62_value_z 4 (fun i=>Int64.signed (norm62_add_words w mu i))<M.
Proof.
 intros Carried Value;rewrite modnorm62_second_value by exact Carried.
 destruct Carried as (Low & Top).
 pose proof (Low 0%nat ltac:(lia));pose proof (Low 1%nat ltac:(lia));
 pose proof (Low 2%nat ltac:(lia));pose proof (Low 3%nat ltac:(lia)).
 unfold Int64.lt;rewrite Int64.signed_zero.
 destruct (zlt (Int64.signed (w 4%nat)) 0);
 cbn [norm62_value_z] in Value|-*;pose proof ModSize;lia.
Qed.

Theorem modnorm62_machine_numeric w sign : modnorm62_limb_bounds w ->
 -2*M<norm62_value_z 4 (fun i=>Int64.signed (w i))<M ->
 signed62_normalized (norm62_machine w mu sign) /\
 signed62_unsigned_value (norm62_machine w mu sign)=
 ((if Int64.lt sign Int64.zero then -1 else 1)*
   norm62_value_z 4 (fun i=>Int64.signed (w i))) mod M.
Proof.
 intros Bounds Value.
 set (first := norm62_carry_words (modnorm62_first w sign)).
 destruct (modnorm62_first_carried w sign Bounds Value) as (Carried & FirstRange).
 change (modnorm62_carried first) in Carried.
 change (-M<norm62_value_z 4 (fun i=>Int64.signed (first i))<M) in FirstRange.
 pose proof (modnorm62_second_bound first Carried) as Bound2.
 pose proof (modnorm62_second_range first Carried FirstRange) as Range2.
 rewrite <-norm62_carry_words_value in Range2 by exact Bound2.
 change (0<=norm62_value_z 4 (fun i=>Int64.signed (norm62_machine w mu sign i))<M) in Range2.
 pose proof (norm62_carry_words_low _ Bound2) as Low2.
 change (forall i,(i<4)%nat -> 0<=Int64.signed (norm62_machine w mu sign i)<2^62) in Low2.
 destruct (modnorm62_canonical_from_value _ Low2 Range2) as (Norm & U).
 split;[exact Norm|rewrite U].
 set (v := norm62_value_z 4 (fun i=>Int64.signed (w i))).
 set (sgn := if Int64.lt sign Int64.zero then -1 else 1).
 set (a := if Int64.lt (w 4%nat) Int64.zero then 1 else 0).
 set (b := if Int64.lt (first 4%nat) Int64.zero then 1 else 0).
 assert (Exact : norm62_value_z 4 (fun i=>Int64.signed (norm62_machine w mu sign i))=
   sgn*v+(sgn*a+b)*M).
 { change (norm62_value_z 4 (fun i=>Int64.signed (norm62_carry_words (norm62_add_words first mu) i))=
     sgn*v+(sgn*a+b)*M).
   rewrite norm62_carry_words_value by exact Bound2.
   rewrite modnorm62_second_value by exact Carried.
   unfold first at 1;rewrite norm62_carry_words_value by (apply modnorm62_first_bound;exact Bounds).
   rewrite modnorm62_first_value by exact Bounds.
   unfold sgn,a,b,v.
   destruct (Int64.lt sign Int64.zero);destruct (Int64.lt (w 4%nat) Int64.zero);
   destruct (Int64.lt (first 4%nat) Int64.zero);ring. }
 assert (Mod : norm62_value_z 4 (fun i=>Int64.signed (norm62_machine w mu sign i)) mod M=
   (sgn*v) mod M).
 { rewrite Exact;apply Z_mod_plus_full. }
 rewrite Z.mod_small in Mod by exact Range2;exact Mod.
Qed.

End Modulus.

