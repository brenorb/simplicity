(** Linked field normalization with the exact sparse metadata and numeric result. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_secp_modinv_normalize62_exec C.jet_secp_modinv_normalize62_global
 C.jet_secp_modinv_normalize62_numeric C.jet_secp_modinv_normalize62_words C.jet_secp_signed62_numeric C.jet_secp_fe_math
 C.jet_secp_modinfo_fe_global C.jet_secp_modinfo_fe_copy C.jet_secp_linkage C.jets_secp
 C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_multiply_normalize_bridge
 C.jet_elements_taptweak_pure C.jet_elements_taptweak_modinfo C.jet_elements_taptweak_curve_transport.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma elements_taptweak_has_normalize62:
 In(_secp256k1_modinv64_normalize_62,f_secp256k1_modinv64_normalize_62)elements_taptweak_curve_helpers.
Proof.
 assert(Found:find(fun it=>Pos.eqb(fst it)_secp256k1_modinv64_normalize_62)elements_taptweak_curve_helpers=
 Some(_secp256k1_modinv64_normalize_62,f_secp256k1_modinv64_normalize_62))by(vm_compute;reflexivity).
 apply find_some in Found;exact(proj1 Found).
Qed.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_modinfo_fe_block elements_taptweak_curve_helpers.
Lemma elements_taptweak_norm62_initial_modulus w sign m : elements_taptweak_modinfo_fe_global_rep m ->
 norm62_modulus_at m elements_taptweak_modinfo_fe_block (fun i => field_norm62_rho w sign (5+i)%nat).
Proof.
 intros (Valid & Read & Loads). split.
 - intros pos Range; apply Read;lia.
 - intros i I. destruct i as [|[|[|[|[|i]]]]]; try lia; apply Loads; reflexivity.
Qed.

Theorem eval_elements_taptweak_norm62_with_global w sign m br : br <> elements_taptweak_modinfo_fe_block ->
 fe_at m br 0 (words5 w) -> Mem.range_perm m br 0 40 Cur Freeable ->
 elements_taptweak_modinfo_fe_global_rep m -> exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_modinv64_normalize_62)
   [Vptr br Ptrofs.zero; Vlong sign; Vptr elements_taptweak_modinfo_fe_block Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br 0 (words5 (norm62_machine w modinfo_fe_limb sign)) /\
 Mem.range_perm mf br 0 40 Cur Freeable /\ elements_taptweak_modinfo_fe_global_rep mf /\
 lframe (norm62_outside br elements_taptweak_modinfo_fe_block) m mf.
Proof.
 intros NE Field Free Global.
 destruct (eval_norm62_from_storage (field_norm62_rho w sign) m br elements_taptweak_modinfo_fe_block NE
   ltac:(rewrite field_norm62_input_words; exact Field) Free
   (elements_taptweak_norm62_initial_modulus w sign m Global)) as (mf & Call & FieldF & FreeF & ModulusF & Frame).
 rewrite field_norm62_output_words in FieldF.
 destruct Global as (Valid & Read & Loads).
 destruct ModulusF as (ReadF & WordsF).
 assert (Outside : forall pos, 40 <= pos -> norm62_outside br elements_taptweak_modinfo_fe_block elements_taptweak_modinfo_fe_block pos).
 { intros pos P. split; [left;congruence|right;right;exact P]. }
 assert (Metadata : elements_taptweak_modinfo_fe_global_rep mf).
 { split; [exact ((proj2 (proj2 Frame)) _ Valid)|]. split.
   - intros pos Range. destruct (Z_lt_dec pos 40).
     + apply ReadF;lia.
     + eapply (proj1 (proj2 Frame)); [exact Valid|apply Outside;lia|apply Read;exact Range].
   - intros i v At. destruct i as [|[|[|[|[|[|i]]]]]];
       try (destruct i; discriminate At).
     + injection At as <-. exact (WordsF 0%nat ltac:(lia)).
     + injection At as <-. exact (WordsF 1%nat ltac:(lia)).
     + injection At as <-. exact (WordsF 2%nat ltac:(lia)).
     + injection At as <-. exact (WordsF 3%nat ltac:(lia)).
     + injection At as <-. exact (WordsF 4%nat ltac:(lia)).
     + change (Mem.load Mint64 mf elements_taptweak_modinfo_fe_block 40 = Some (Vlong v)).
       rewrite (proj1 Frame Mint64 elements_taptweak_modinfo_fe_block 40 Valid).
       * exact (Loads 5%nat v At).
       * intros pos Range;apply Outside. change (size_chunk Mint64) with 8 in Range;lia. }
 pose proof(elements_taptweak_curve_transport _ _ m _ E0 mf _ elements_taptweak_has_normalize62 Call)as CallT.
 exists mf. exact (conj CallT (conj FieldF (conj FreeF (conj Metadata Frame)))).
Qed.

Theorem eval_elements_taptweak_norm62_numeric w sign m br :
 norm62_limb_bounds w ->
 -2*feP<norm62_value_z 4 (fun i=>Int64.signed (w i))<feP ->
 br<>elements_taptweak_modinfo_fe_block -> fe_at m br 0 (words5 w) ->
 Mem.range_perm m br 0 40 Cur Freeable -> elements_taptweak_modinfo_fe_global_rep m -> exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_modinv64_normalize_62)
  [Vptr br Ptrofs.zero;Vlong sign;Vptr elements_taptweak_modinfo_fe_block Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br 0 (words5 (norm62_machine w modinfo_fe_limb sign)) /\
 signed62_normalized (norm62_machine w modinfo_fe_limb sign) /\
 signed62_unsigned_value (norm62_machine w modinfo_fe_limb sign)=
  ((if Int64.lt sign Int64.zero then -1 else 1)*
    norm62_value_z 4 (fun i=>Int64.signed (w i))) mod feP /\
 Mem.range_perm mf br 0 40 Cur Freeable /\ elements_taptweak_modinfo_fe_global_rep mf /\
 lframe (norm62_outside br elements_taptweak_modinfo_fe_block) m mf.
Proof.
 intros Bounds Value NE Field Free Global.
 destruct (eval_elements_taptweak_norm62_with_global w sign m br NE Field Free Global)
  as (mf & Call & FieldF & FreeF & GlobalF & Frame).
 destruct (norm62_field_machine_numeric w sign Bounds Value) as (Norm & Numeric).
 exists mf;exact (conj Call (conj FieldF (conj Norm (conj Numeric
  (conj FreeF (conj GlobalF Frame)))))).
Qed.
