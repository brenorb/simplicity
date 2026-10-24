(** The original normalize_62 C helper at the actual scalar-order global.
    Reuses the field/scalar numeric derivation and the original symbolic C
    execution. The inverse loop must establish the internal input bounds. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_secp_modinv_normalize62_exec C.jet_secp_modinv_normalize62_words
 C.jet_secp_modinv_normalize62_modulus C.jet_secp_modinfo_scalar_global
 C.jet_secp_scalar_inverse_caller C.jet_secp_canonical_scalar C.jet_secp_signed62_numeric
 C.jet_secp_linkage C.jets_secp C.jet_sx_mem C.jet_secp_fe_nv
 C.jet_secp_multiply_normalize_bridge.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge scalar_inv_modinfo_block.

Definition modinfo_scalar_limb i := nth i modinfo_scalar_words Int64.zero.

Lemma scalar_norm62_modulus_bound : modnorm62_limb_bounds modinfo_scalar_limb.
Proof.
 intros i I;destruct i as [|[|[|[|[|i]]]]];try lia;
 vm_compute;split;discriminate.
Qed.
Lemma scalar_norm62_modulus_value :
 norm62_value_z 4 (fun i=>Int64.signed (modinfo_scalar_limb i))=canonical_group_order.
Proof. vm_compute;reflexivity. Qed.
Lemma scalar_norm62_modulus_range : 2^248<=canonical_group_order<=2^256.
Proof. unfold canonical_group_order;lia. Qed.

Theorem scalar_norm62_machine_numeric w sign : modnorm62_limb_bounds w ->
 -2*canonical_group_order<norm62_value_z 4 (fun i=>Int64.signed (w i))<canonical_group_order ->
 signed62_normalized (norm62_machine w modinfo_scalar_limb sign) /\
 signed62_unsigned_value (norm62_machine w modinfo_scalar_limb sign)=
 ((if Int64.lt sign Int64.zero then -1 else 1)*
   norm62_value_z 4 (fun i=>Int64.signed (w i))) mod canonical_group_order.
Proof.
 exact (modnorm62_machine_numeric modinfo_scalar_limb canonical_group_order
  scalar_norm62_modulus_bound scalar_norm62_modulus_value scalar_norm62_modulus_range w sign).
Qed.

Definition scalar_norm62_rho (w : nat -> int64) (sign : int64) n :=
 if Nat.ltb n 5 then w n else
 if Nat.ltb n 10 then modinfo_scalar_limb (n-5)%nat else sign.

Lemma scalar_norm62_input_words w sign : words5 (scalar_norm62_rho w sign)=words5 w.
Proof. reflexivity. Qed.
Lemma scalar_norm62_output_words w sign :
 words5 (norm62_machine (scalar_norm62_rho w sign)
   (fun i=>scalar_norm62_rho w sign (5+i)%nat) (scalar_norm62_rho w sign 10%nat))=
 words5 (norm62_machine w modinfo_scalar_limb sign).
Proof. reflexivity. Qed.
Lemma scalar_norm62_initial_modulus w sign m : modinfo_scalar_global_rep m ->
 norm62_modulus_at m scalar_inv_modinfo_block (fun i=>scalar_norm62_rho w sign (5+i)%nat).
Proof.
 intros (Valid & Read & Loads);split.
 - intros pos Range;apply Read;lia.
 - intros i I;destruct i as [|[|[|[|[|i]]]]];try lia;apply Loads;reflexivity.
Qed.

(** This derives the actual C call and canonical numeric result from storage,
    rather than assuming either. No CTZ or external-library model is used. *)
Theorem eval_scalar_norm62_numeric w sign m br :
 modnorm62_limb_bounds w ->
 -2*canonical_group_order<norm62_value_z 4 (fun i=>Int64.signed (w i))<canonical_group_order ->
 br<>scalar_inv_modinfo_block -> fe_at m br 0 (words5 w) ->
 Mem.range_perm m br 0 40 Cur Freeable -> modinfo_scalar_global_rep m -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_normalize_62)
  [Vptr br Ptrofs.zero;Vlong sign;Vptr scalar_inv_modinfo_block Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br 0 (words5 (norm62_machine w modinfo_scalar_limb sign)) /\
 signed62_normalized (norm62_machine w modinfo_scalar_limb sign) /\
 signed62_unsigned_value (norm62_machine w modinfo_scalar_limb sign)=
  ((if Int64.lt sign Int64.zero then -1 else 1)*
    norm62_value_z 4 (fun i=>Int64.signed (w i))) mod canonical_group_order /\
 Mem.range_perm mf br 0 40 Cur Freeable /\ modinfo_scalar_global_rep mf /\
 lframe (norm62_outside br scalar_inv_modinfo_block) m mf.
Proof.
 intros Bounds Value NE Field Free Global.
 destruct (eval_norm62_from_storage (scalar_norm62_rho w sign) m br scalar_inv_modinfo_block NE
   ltac:(rewrite scalar_norm62_input_words;exact Field) Free
   (scalar_norm62_initial_modulus w sign m Global)) as (mf & Call & FieldF & FreeF & ModulusF & Frame).
 rewrite scalar_norm62_output_words in FieldF.
 destruct Global as (Valid & Read & Loads);destruct ModulusF as (ReadF & WordsF).
 assert (Outside : forall pos,40<=pos -> norm62_outside br scalar_inv_modinfo_block scalar_inv_modinfo_block pos).
 { intros pos P;split;[left;congruence|right;right;exact P]. }
 assert (Metadata : modinfo_scalar_global_rep mf).
 { split;[exact ((proj2 (proj2 Frame)) _ Valid)|];split.
   - intros pos Range;destruct (Z_lt_dec pos 40).
     + apply ReadF;lia.
     + eapply (proj1 (proj2 Frame));[exact Valid|apply Outside;lia|apply Read;exact Range].
   - intros i v At;destruct i as [|[|[|[|[|[|i]]]]]];
       try (destruct i;discriminate At).
     + injection At as <-;exact (WordsF 0%nat ltac:(lia)).
     + injection At as <-;exact (WordsF 1%nat ltac:(lia)).
     + injection At as <-;exact (WordsF 2%nat ltac:(lia)).
     + injection At as <-;exact (WordsF 3%nat ltac:(lia)).
     + injection At as <-;exact (WordsF 4%nat ltac:(lia)).
     + change (Mem.load Mint64 mf scalar_inv_modinfo_block 40=Some(Vlong v)).
       rewrite (proj1 Frame Mint64 scalar_inv_modinfo_block 40 Valid).
       * exact (Loads 5%nat v At).
       * intros pos Range;apply Outside;change (size_chunk Mint64) with 8 in Range;lia. }
 destruct (scalar_norm62_machine_numeric w sign Bounds Value) as (Norm & Numeric).
 exists mf;exact (conj Call (conj FieldF (conj Norm (conj Numeric
   (conj FreeF (conj Metadata Frame)))))).
Qed.
