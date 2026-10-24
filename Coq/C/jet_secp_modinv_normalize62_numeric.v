(** Numeric interpretation of the original field normalize_62 helper.
    Uses the actual sparse modulus and proves the precise final value and
    canonical limbs. The variable-inverse loop must still establish the
    internal bounds before this can complete the public inversion proof. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers.
Require Import C.jet_secp_modinv_normalize62_words C.jet_secp_modinv_normalize62_exec
 C.jet_secp_modinfo_fe_copy C.jet_secp_fe_math C.jet_secp_signed62_numeric.
Require Import C.jet_secp_modinv_normalize62_modulus.
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

Lemma norm62_modulus_value :
 norm62_value_z 4 (fun i=>Int64.signed (modinfo_fe_limb i))=feP.
Proof. vm_compute;reflexivity. Qed.
Lemma norm62_modulus_range : 2^248<=feP<=2^256.
Proof. unfold feP,feR;lia. Qed.

Definition norm62_limb_bounds w :=
 forall i, (i<5)%nat -> -(2^62-1)<=Int64.signed (w i)<=2^62-1.

Definition norm62_first w sign := norm62_neg_words (norm62_add_words w modinfo_fe_limb) sign.

Lemma norm62_first_signed w sign i : norm62_limb_bounds w -> (i<5)%nat ->
 Int64.signed (norm62_first w sign i)=
 (if Int64.lt sign Int64.zero then -1 else 1) *
 (Int64.signed (w i)+
  if Int64.lt (w 4%nat) Int64.zero then Int64.signed (modinfo_fe_limb i) else 0).
Proof.
 exact (modnorm62_first_signed modinfo_fe_limb norm62_modulus_bound w sign i).
Qed.

Lemma norm62_first_bound w sign : norm62_limb_bounds w ->
 forall i, (i<5)%nat ->
 Int64.min_signed+2<=Int64.signed (norm62_first w sign i)<=Int64.max_signed-1.
Proof.
 exact (modnorm62_first_bound modinfo_fe_limb norm62_modulus_bound w sign).
Qed.

Lemma norm62_first_value w sign : norm62_limb_bounds w ->
 norm62_value_z 4 (fun i=>Int64.signed (norm62_first w sign i))=
 (if Int64.lt sign Int64.zero then -1 else 1) *
 (norm62_value_z 4 (fun i=>Int64.signed (w i))+
  if Int64.lt (w 4%nat) Int64.zero then feP else 0).
Proof.
 exact (modnorm62_first_value modinfo_fe_limb feP norm62_modulus_bound norm62_modulus_value w sign).
Qed.

Lemma norm62_first_range w sign : norm62_limb_bounds w ->
 -2*feP<norm62_value_z 4 (fun i=>Int64.signed (w i))<feP ->
 -feP<norm62_value_z 4 (fun i=>Int64.signed (norm62_first w sign i))<feP.
Proof.
 exact (modnorm62_first_range modinfo_fe_limb feP norm62_modulus_bound norm62_modulus_value norm62_modulus_range w sign).
Qed.

Lemma norm62_unsigned_nonnegative a : 0<=Int64.signed a ->
 Int64.unsigned a=Int64.signed a.
Proof.
 exact (modnorm62_unsigned_nonnegative a).
Qed.

Lemma norm62_canonical_from_value w :
 (forall i,(i<4)%nat -> 0<=Int64.signed (w i)<2^62) ->
 0<=norm62_value_z 4 (fun i=>Int64.signed (w i))<feP ->
 signed62_normalized w /\
 signed62_unsigned_value w=norm62_value_z 4 (fun i=>Int64.signed (w i)).
Proof.
 exact (modnorm62_canonical_from_value feP norm62_modulus_range w).
Qed.

Lemma norm62_top_range w :
 (forall i,(i<4)%nat -> 0<=Int64.signed (w i)<2^62) ->
 -feP<norm62_value_z 4 (fun i=>Int64.signed (w i))<feP ->
 -256<=Int64.signed (w 4%nat)<=255.
Proof.
 exact (modnorm62_top_range feP norm62_modulus_range w).
Qed.

Definition norm62_carried w :=
 (forall i,(i<4)%nat -> 0<=Int64.signed (w i)<2^62) /\
 -256<=Int64.signed (w 4%nat)<=255.

Lemma norm62_first_carried w sign : norm62_limb_bounds w ->
 -2*feP<norm62_value_z 4 (fun i=>Int64.signed (w i))<feP ->
 norm62_carried (norm62_carry_words (norm62_first w sign)) /\
 -feP<norm62_value_z 4 (fun i=>Int64.signed (norm62_carry_words (norm62_first w sign) i))<feP.
Proof.
 exact (modnorm62_first_carried modinfo_fe_limb feP norm62_modulus_bound norm62_modulus_value norm62_modulus_range w sign).
Qed.

Lemma norm62_second_signed w : norm62_carried w -> forall i,(i<5)%nat ->
 Int64.signed (norm62_add_words w modinfo_fe_limb i)=
 Int64.signed (w i)+
 if Int64.lt (w 4%nat) Int64.zero then Int64.signed (modinfo_fe_limb i) else 0.
Proof.
 exact (modnorm62_second_signed modinfo_fe_limb norm62_modulus_bound w).
Qed.

Lemma norm62_second_bound w : norm62_carried w -> forall i,(i<5)%nat ->
 Int64.min_signed+2<=Int64.signed (norm62_add_words w modinfo_fe_limb i)<=Int64.max_signed-1.
Proof.
 exact (modnorm62_second_bound modinfo_fe_limb norm62_modulus_bound w).
Qed.

Lemma norm62_second_value w : norm62_carried w ->
 norm62_value_z 4 (fun i=>Int64.signed (norm62_add_words w modinfo_fe_limb i))=
 norm62_value_z 4 (fun i=>Int64.signed (w i))+
 if Int64.lt (w 4%nat) Int64.zero then feP else 0.
Proof.
 exact (modnorm62_second_value modinfo_fe_limb feP norm62_modulus_bound norm62_modulus_value w).
Qed.

Lemma norm62_second_range w : norm62_carried w ->
 -feP<norm62_value_z 4 (fun i=>Int64.signed (w i))<feP ->
 0<=norm62_value_z 4 (fun i=>Int64.signed (norm62_add_words w modinfo_fe_limb i))<feP.
Proof.
 exact (modnorm62_second_range modinfo_fe_limb feP norm62_modulus_bound norm62_modulus_value norm62_modulus_range w).
Qed.

Theorem norm62_field_machine_numeric w sign : norm62_limb_bounds w ->
 -2*feP<norm62_value_z 4 (fun i=>Int64.signed (w i))<feP ->
 signed62_normalized (norm62_machine w modinfo_fe_limb sign) /\
 signed62_unsigned_value (norm62_machine w modinfo_fe_limb sign)=
 ((if Int64.lt sign Int64.zero then -1 else 1)*
   norm62_value_z 4 (fun i=>Int64.signed (w i))) mod feP.
Proof.
 exact (modnorm62_machine_numeric modinfo_fe_limb feP norm62_modulus_bound norm62_modulus_value norm62_modulus_range w sign).
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
