(** Numeric interpretation of the original field normalize_62 helper.
    Uses the actual sparse modulus and proves the precise final value and
    canonical limbs. The variable-inverse loop must still establish the
    internal bounds before this can complete the public inversion proof. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers.
Require Import C.jet_secp_modinv_normalize62_words C.jet_secp_modinv_normalize62_exec
 C.jet_secp_modinfo_fe_copy C.jet_secp_fe_math C.jet_secp_signed62_numeric.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma norm62_modulus_signed i : (i<5)%nat ->
 Int64.signed (modinfo_fe_limb i)=
 match i with O => -4294968273 | 4%nat => 256 | _ => 0 end.
Proof. intro I;destruct i as [|[|[|[|[|i]]]]];try lia;reflexivity. Qed.

Lemma norm62_modulus_bound i : (i<5)%nat ->
 - (2^62-1)<=Int64.signed (modinfo_fe_limb i)<=2^62-1.
Proof.
 intro I;rewrite norm62_modulus_signed by exact I.
 destruct i as [|[|[|[|[|i]]]]];lia.
Qed.

Definition norm62_limb_bounds w :=
 forall i, (i<5)%nat -> -(2^62-1)<=Int64.signed (w i)<=2^62-1.

Definition norm62_first w sign := norm62_neg_words (norm62_add_words w modinfo_fe_limb) sign.

Lemma norm62_first_signed w sign i : norm62_limb_bounds w -> (i<5)%nat ->
 Int64.signed (norm62_first w sign i)=
 (if Int64.lt sign Int64.zero then -1 else 1) *
 (Int64.signed (w i)+
  if Int64.lt (w 4%nat) Int64.zero then Int64.signed (modinfo_fe_limb i) else 0).
Proof.
 intros Bound I.
 pose proof (Bound i I) as B;pose proof (norm62_modulus_bound i I) as M.
 assert (Add : Int64.signed (norm62_add_words w modinfo_fe_limb i)=
   Int64.signed (w i)+
   if Int64.lt (w 4%nat) Int64.zero then Int64.signed (modinfo_fe_limb i) else 0).
 { rewrite norm62_add_word_cases. destruct (Int64.lt (w 4%nat) Int64.zero).
   - apply norm62_signed_add;change Int64.min_signed with (-9223372036854775808);
      change Int64.max_signed with 9223372036854775807;lia.
   - lia. }
 unfold norm62_first;rewrite norm62_neg_word_cases.
 destruct (Int64.lt sign Int64.zero).
 - rewrite norm62_signed_neg.
   + rewrite Add;ring.
   + rewrite Add;destruct (Int64.lt (w 4%nat) Int64.zero);
      change Int64.min_signed with (-9223372036854775808);
      change Int64.max_signed with 9223372036854775807;lia.
 - rewrite Add;ring.
Qed.

Lemma norm62_first_bound w sign : norm62_limb_bounds w ->
 forall i, (i<5)%nat ->
 Int64.min_signed+2<=Int64.signed (norm62_first w sign i)<=Int64.max_signed-1.
Proof.
 intros Bound i I;rewrite norm62_first_signed by assumption.
 pose proof (Bound i I);pose proof (norm62_modulus_bound i I).
 destruct (Int64.lt sign Int64.zero);destruct (Int64.lt (w 4%nat) Int64.zero);
 change Int64.min_signed with (-9223372036854775808);
 change Int64.max_signed with 9223372036854775807;lia.
Qed.

Lemma norm62_first_value w sign : norm62_limb_bounds w ->
 norm62_value_z 4 (fun i=>Int64.signed (norm62_first w sign i))=
 (if Int64.lt sign Int64.zero then -1 else 1) *
 (norm62_value_z 4 (fun i=>Int64.signed (w i))+
  if Int64.lt (w 4%nat) Int64.zero then feP else 0).
Proof.
 intro Bound;cbn [norm62_value_z].
 rewrite !norm62_first_signed by (exact Bound||lia).
 rewrite !norm62_modulus_signed by lia.
 destruct (Int64.lt sign Int64.zero);destruct (Int64.lt (w 4%nat) Int64.zero);
 unfold feP,feR;ring.
Qed.

Lemma norm62_first_range w sign : norm62_limb_bounds w ->
 -2*feP<norm62_value_z 4 (fun i=>Int64.signed (w i))<feP ->
 -feP<norm62_value_z 4 (fun i=>Int64.signed (norm62_first w sign i))<feP.
Proof.
 intros Bound Value;rewrite norm62_first_value by exact Bound.
 pose proof (Bound 0%nat ltac:(lia)) as B0.
 pose proof (Bound 1%nat ltac:(lia)) as B1.
 pose proof (Bound 2%nat ltac:(lia)) as B2.
 pose proof (Bound 3%nat ltac:(lia)) as B3.
 pose proof (Bound 4%nat ltac:(lia)) as B4.
 unfold Int64.lt;rewrite Int64.signed_zero.
 destruct (zlt (Int64.signed sign) 0);
 destruct (zlt (Int64.signed (w 4%nat)) 0);
 cbn [norm62_value_z] in Value|-*;unfold feP,feR in *;lia.
Qed.

Lemma norm62_unsigned_nonnegative a : 0<=Int64.signed a ->
 Int64.unsigned a=Int64.signed a.
Proof.
 intro Nonneg;rewrite <-(Int64.repr_signed a) at 1.
 apply Int64.unsigned_repr;pose proof (Int64.signed_range a).
 change Int64.max_signed with 9223372036854775807 in *.
 change Int64.max_unsigned with 18446744073709551615;lia.
Qed.

Lemma norm62_canonical_from_value w :
 (forall i,(i<4)%nat -> 0<=Int64.signed (w i)<2^62) ->
 0<=norm62_value_z 4 (fun i=>Int64.signed (w i))<feP ->
 signed62_normalized w /\
 signed62_unsigned_value w=norm62_value_z 4 (fun i=>Int64.signed (w i)).
Proof.
 intros Low Value.
 pose proof (Low 0%nat ltac:(lia)) as L0;pose proof (Low 1%nat ltac:(lia)) as L1;
 pose proof (Low 2%nat ltac:(lia)) as L2;pose proof (Low 3%nat ltac:(lia)) as L3.
 assert (Top : 0<=Int64.signed (w 4%nat)<256).
 { cbn [norm62_value_z] in Value;unfold feP,feR in Value;lia. }
 assert (Nonneg : forall i,(i<5)%nat -> 0<=Int64.signed (w i)).
 { intros i I;destruct (Nat.eq_dec i 4) as [->|NE];[lia|pose proof (Low i ltac:(lia));lia]. }
 split.
 - intros i I;rewrite norm62_unsigned_nonnegative by (apply Nonneg;exact I).
   destruct (Nat.eqb i 4) eqn:E.
   + apply Nat.eqb_eq in E;subst i;exact Top.
   + apply Nat.eqb_neq in E;apply Low;lia.
 - unfold signed62_unsigned_value;rewrite !norm62_unsigned_nonnegative by (apply Nonneg;lia).
   cbn [norm62_value_z];ring.
Qed.

Lemma norm62_top_range w :
 (forall i,(i<4)%nat -> 0<=Int64.signed (w i)<2^62) ->
 -feP<norm62_value_z 4 (fun i=>Int64.signed (w i))<feP ->
 -256<=Int64.signed (w 4%nat)<=255.
Proof.
 intros Low Value.
 pose proof (Low 0%nat ltac:(lia));pose proof (Low 1%nat ltac:(lia));
 pose proof (Low 2%nat ltac:(lia));pose proof (Low 3%nat ltac:(lia)).
 cbn [norm62_value_z] in Value;unfold feP,feR in Value;lia.
Qed.

Definition norm62_carried w :=
 (forall i,(i<4)%nat -> 0<=Int64.signed (w i)<2^62) /\
 -256<=Int64.signed (w 4%nat)<=255.

Lemma norm62_first_carried w sign : norm62_limb_bounds w ->
 -2*feP<norm62_value_z 4 (fun i=>Int64.signed (w i))<feP ->
 norm62_carried (norm62_carry_words (norm62_first w sign)) /\
 -feP<norm62_value_z 4 (fun i=>Int64.signed (norm62_carry_words (norm62_first w sign) i))<feP.
Proof.
 intros Bounds Value.
 pose proof (norm62_first_bound w sign Bounds) as B.
 pose proof (norm62_carry_words_low _ B) as Low.
 pose proof (norm62_first_range w sign Bounds Value) as V.
 rewrite <-norm62_carry_words_value in V by exact B.
 split;[split;[exact Low|apply norm62_top_range;assumption]|exact V].
Qed.

Lemma norm62_second_signed w : norm62_carried w -> forall i,(i<5)%nat ->
 Int64.signed (norm62_add_words w modinfo_fe_limb i)=
 Int64.signed (w i)+
 if Int64.lt (w 4%nat) Int64.zero then Int64.signed (modinfo_fe_limb i) else 0.
Proof.
 intros (Low & Top) i I;rewrite norm62_add_word_cases.
 destruct (Int64.lt (w 4%nat) Int64.zero);[|lia].
 apply norm62_signed_add.
 rewrite norm62_modulus_signed by exact I.
 destruct i as [|[|[|[|[|i]]]]];try lia;
 try (pose proof (Low 0%nat ltac:(lia)));
 try (pose proof (Low 1%nat ltac:(lia)));
 try (pose proof (Low 2%nat ltac:(lia)));
 try (pose proof (Low 3%nat ltac:(lia)));
 change Int64.min_signed with (-9223372036854775808);
 change Int64.max_signed with 9223372036854775807;lia.
Qed.

Lemma norm62_second_bound w : norm62_carried w -> forall i,(i<5)%nat ->
 Int64.min_signed+2<=Int64.signed (norm62_add_words w modinfo_fe_limb i)<=Int64.max_signed-1.
Proof.
 intros Carried i I;rewrite norm62_second_signed by assumption.
 destruct Carried as (Low & Top);rewrite norm62_modulus_signed by exact I.
 destruct (Int64.lt (w 4%nat) Int64.zero);
 destruct i as [|[|[|[|[|i]]]]];try lia;
 try (pose proof (Low 0%nat ltac:(lia)));
 try (pose proof (Low 1%nat ltac:(lia)));
 try (pose proof (Low 2%nat ltac:(lia)));
 try (pose proof (Low 3%nat ltac:(lia)));
 change Int64.min_signed with (-9223372036854775808);
 change Int64.max_signed with 9223372036854775807;lia.
Qed.

Lemma norm62_second_value w : norm62_carried w ->
 norm62_value_z 4 (fun i=>Int64.signed (norm62_add_words w modinfo_fe_limb i))=
 norm62_value_z 4 (fun i=>Int64.signed (w i))+
 if Int64.lt (w 4%nat) Int64.zero then feP else 0.
Proof.
 intro Carried;cbn [norm62_value_z].
 rewrite !norm62_second_signed by (exact Carried||lia).
 rewrite !norm62_modulus_signed by lia.
 destruct (Int64.lt (w 4%nat) Int64.zero);unfold feP,feR;ring.
Qed.

Lemma norm62_second_range w : norm62_carried w ->
 -feP<norm62_value_z 4 (fun i=>Int64.signed (w i))<feP ->
 0<=norm62_value_z 4 (fun i=>Int64.signed (norm62_add_words w modinfo_fe_limb i))<feP.
Proof.
 intros Carried Value;rewrite norm62_second_value by exact Carried.
 destruct Carried as (Low & Top).
 pose proof (Low 0%nat ltac:(lia));pose proof (Low 1%nat ltac:(lia));
 pose proof (Low 2%nat ltac:(lia));pose proof (Low 3%nat ltac:(lia)).
 unfold Int64.lt;rewrite Int64.signed_zero.
 destruct (zlt (Int64.signed (w 4%nat)) 0);
 cbn [norm62_value_z] in Value|-*;unfold feP,feR in *;lia.
Qed.

Theorem norm62_field_machine_numeric w sign : norm62_limb_bounds w ->
 -2*feP<norm62_value_z 4 (fun i=>Int64.signed (w i))<feP ->
 signed62_normalized (norm62_machine w modinfo_fe_limb sign) /\
 signed62_unsigned_value (norm62_machine w modinfo_fe_limb sign)=
 ((if Int64.lt sign Int64.zero then -1 else 1)*
   norm62_value_z 4 (fun i=>Int64.signed (w i))) mod feP.
Proof.
 intros Bounds Value.
 set (first := norm62_carry_words (norm62_first w sign)).
 destruct (norm62_first_carried w sign Bounds Value) as (Carried & FirstRange).
 change (norm62_carried first) in Carried.
 change (-feP<norm62_value_z 4 (fun i=>Int64.signed (first i))<feP) in FirstRange.
 pose proof (norm62_second_bound first Carried) as Bound2.
 pose proof (norm62_second_range first Carried FirstRange) as Range2.
 rewrite <-norm62_carry_words_value in Range2 by exact Bound2.
 change (0<=norm62_value_z 4 (fun i=>Int64.signed (norm62_machine w modinfo_fe_limb sign i))<feP) in Range2.
 pose proof (norm62_carry_words_low _ Bound2) as Low2.
 change (forall i,(i<4)%nat -> 0<=Int64.signed (norm62_machine w modinfo_fe_limb sign i)<2^62) in Low2.
 destruct (norm62_canonical_from_value _ Low2 Range2) as (Norm & U).
 split;[exact Norm|rewrite U].
 set (v := norm62_value_z 4 (fun i=>Int64.signed (w i))).
 set (sgn := if Int64.lt sign Int64.zero then -1 else 1).
 set (a := if Int64.lt (w 4%nat) Int64.zero then 1 else 0).
 set (b := if Int64.lt (first 4%nat) Int64.zero then 1 else 0).
 assert (Exact : norm62_value_z 4 (fun i=>Int64.signed (norm62_machine w modinfo_fe_limb sign i))=
   sgn*v+(sgn*a+b)*feP).
 { change (norm62_value_z 4 (fun i=>Int64.signed (norm62_carry_words (norm62_add_words first modinfo_fe_limb) i))=
     sgn*v+(sgn*a+b)*feP).
   rewrite norm62_carry_words_value by exact Bound2.
   rewrite norm62_second_value by exact Carried.
   unfold first at 1;rewrite norm62_carry_words_value by (apply norm62_first_bound;exact Bounds).
   rewrite norm62_first_value by exact Bounds.
   unfold sgn,a,b,v.
   destruct (Int64.lt sign Int64.zero);destruct (Int64.lt (w 4%nat) Int64.zero);
   destruct (Int64.lt (first 4%nat) Int64.zero);ring. }
 assert (Mod : norm62_value_z 4 (fun i=>Int64.signed (norm62_machine w modinfo_fe_limb sign i)) mod feP=
   (sgn*v) mod feP).
 { rewrite Exact;apply Z_mod_plus_full. }
 rewrite Z.mod_small in Mod by exact Range2;exact Mod.
Qed.

From compcert Require Import AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_secp_modinv_normalize62_global C.jet_secp_modinfo_fe_global
 C.jet_secp_linkage C.jets_secp C.jet_sx_mem C.jet_secp_fe_nv
 C.jet_secp_multiply_normalize_bridge.
Import ListNotations.
Local Opaque secp_ge modinfo_fe_block.

(** This is an internal C-helper contract. The inverse loop must discharge
    Bounds and Value; neither is assumed of arbitrary public jet inputs. *)
Theorem eval_field_norm62_numeric w sign m br :
 norm62_limb_bounds w ->
 -2*feP<norm62_value_z 4 (fun i=>Int64.signed (w i))<feP ->
 br<>modinfo_fe_block -> fe_at m br 0 (words5 w) ->
 Mem.range_perm m br 0 40 Cur Freeable -> modinfo_fe_global_rep m -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_normalize_62)
  [Vptr br Ptrofs.zero;Vlong sign;Vptr modinfo_fe_block Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br 0 (words5 (norm62_machine w modinfo_fe_limb sign)) /\
 signed62_normalized (norm62_machine w modinfo_fe_limb sign) /\
 signed62_unsigned_value (norm62_machine w modinfo_fe_limb sign)=
  ((if Int64.lt sign Int64.zero then -1 else 1)*
    norm62_value_z 4 (fun i=>Int64.signed (w i))) mod feP /\
 Mem.range_perm mf br 0 40 Cur Freeable /\ modinfo_fe_global_rep mf /\
 lframe (norm62_outside br modinfo_fe_block) m mf.
Proof.
 intros Bounds Value NE Field Free Global.
 destruct (eval_field_norm62_with_global w sign m br NE Field Free Global)
  as (mf & Call & FieldF & FreeF & GlobalF & Frame).
 destruct (norm62_field_machine_numeric w sign Bounds Value) as (Norm & Numeric).
 exists mf;exact (conj Call (conj FieldF (conj Norm (conj Numeric
  (conj FreeF (conj GlobalF Frame)))))).
Qed.
