(** Decode the selected table entry and execute the original negative-digit
    field negation, retaining X, infinity, ownership and table framing. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_state C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_storage_unpack C.jet_secp_storage_numeric
 C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge
 C.jet_secp_affine_storage C.jet_secp_affine_storage_frame
 C.jet_secp_affine_weak_exec C.jet_secp_affine_negate_owned
 C.jet_secp_field_negate_storage C.jet_secp_write_fe_numeric
 C.jet_secp_owned_field_slice C.jet_secp_owned_field_transport
 C.jet_clight_forward C.jet_clight_readonly_frame.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma storage_unpack_machine_limbs w :
 words5 (storage_unpack_words w)=map Int64.repr (fe_limbs_of (field_storage_value w)).
Proof.
 rewrite <-storage_unpack_exact_limbs,map_map.
 transitivity (map (fun x : int64 => x) (words5 (storage_unpack_words w))).
 - symmetry;apply map_id.
 - apply map_ext;intro x;symmetry;apply Int64.repr_unsigned.
Qed.

Lemma field_storage_value_bounds w : 0<=field_storage_value w<2^256.
Proof.
 rewrite <-storage_unpack_preserves_value,radix_value_matches_normalizer.
 apply fe_val_bound;apply storage_unpack_limb_bounds.
Qed.

Definition table_negative_y (w : nat->int64) :=
 negate_values (write_fe_rho (field_storage_value (fun i => w (4+i)%nat)) 0).
Definition table_signed_coordinate w (neg k : bool) :=
 if k then (if neg then table_negative_y w else words5 (affine_storage_coord w true))
 else words5 (affine_storage_coord w false).

Lemma affine_storage_readable_lframe w m mf bin sbase P :
 affine_storage_readable m bin sbase w -> lframe P m mf ->
 (forall pos,P bin pos) -> affine_storage_readable mf bin sbase w.
Proof.
 intros (HB & HA & HM & HP & HL) HF HOutside.
 assert (HV : Mem.valid_block m bin).
 { eapply Mem.perm_valid_block;apply (HP sbase);lia. }
 split;[exact HB|];split;[exact HA|];split;[exact HM|];split.
 - intros pos HPos;apply (proj1 (proj2 HF));[exact HV|apply HOutside|apply HP;exact HPos].
 - intros i HI;rewrite (proj1 HF Mint64 bin (sbase+8*Z.of_nat i) HV);
     [apply HL;exact HI|intros;apply HOutside].
Qed.

Theorem eval_table_decode_signed (neg : bool) w m bout bin sbase lo hi :
 bout<>bin -> Mem.range_perm m bout 0 88 Cur Freeable ->
 affine_storage_readable m bin sbase w -> readonly_region_bounds m bin lo hi ->
 exists md mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_from_storage)
   [Vptr bout Ptrofs.zero;Vptr bin (Ptrofs.repr sbase)] E0 md Vundef /\
 (if neg then Clight2.eval_funcall secp_ge md (Internal f_secp256k1_fe_negate)
   [Vptr bout (Ptrofs.repr 40);Vptr bout (Ptrofs.repr 40);Vint Int.one] E0 mf Vundef else mf=md) /\
 Mem.range_perm mf bout 0 88 Cur Freeable /\
 (forall k : bool,fe_at mf bout (if k then 40 else 0) (table_signed_coordinate w neg k)) /\
 Mem.load Mint32 mf bout 80=Some (Vint Int.zero) /\
 affine_storage_readable mf bin sbase w /\ readonly_region_bounds mf bin lo hi /\
 lframe (fun b pos => b<>bout \/ pos<0 \/ 84<=pos) m mf.
Proof.
 intros Sep Free Input Bounds.
 destruct (eval_ge_from_storage_table w m bout bin sbase lo hi Sep Free Input Bounds)
   as (md & Decode & Owned & Fields & Infinity & Source & RO & Frame).
 destruct neg.
 - assert (Y : fe_at md bout (affine_coordinate_offset AffineY)
     (map Int64.repr (fe_limbs_of (field_storage_value (fun i => w (4+i)%nat))))).
   { rewrite <-storage_unpack_machine_limbs;exact (Fields true). }
   destruct (eval_affine_negate_reader_owned AffineY md bout _ Y Owned)
     as (mf & Negate & YF & OF & NF).
   assert (VD : Mem.valid_block md bout).
   { eapply Mem.perm_valid_block;apply (Owned 0);lia. }
   assert (XF : fe_at mf bout 0 (words5 (affine_storage_coord w false))).
   { eapply owned_field_load_transport with (size:=88);[lia|reflexivity|exact (Fields false)|exact OF|].
     intros i HI;apply (proj1 NF Mint64 bout (0+8*Z.of_nat i) VD).
     intros pos HP HF.
     change (foot [(bout,0)] (map rshape (owned_field_slice 40 88)) bout pos) in HF.
     destruct (owned_field_slice_foot_bounds 40 88 bout bout pos HF) as [_ HR].
     change (size_chunk Mint64) with 8 in HP;lia. }
   assert (IF : Mem.load Mint32 mf bout 80=Some (Vint Int.zero)).
   { rewrite (proj1 NF Mint32 bout 80 VD);[exact Infinity|].
     intros pos HP HF.
     change (foot [(bout,0)] (map rshape (owned_field_slice 40 88)) bout pos) in HF.
     destruct (owned_field_slice_foot_bounds 40 88 bout bout pos HF) as [_ HR].
     change (size_chunk Mint32) with 4 in HP;lia. }
   assert (FF : lframe (fun b pos => b<>bout \/ pos<0 \/ 84<=pos) md mf).
   { eapply lframe_implies;[exact NF|].
     intros b pos HOutside HV HF.
     change (foot [(bout,0)] (map rshape (owned_field_slice 40 88)) b pos) in HF.
     destruct (owned_field_slice_foot_bounds 40 88 bout b pos HF) as [HE HR].
     destruct HOutside as [HN|[HN|HN]];[congruence|lia|lia]. }
   pose proof (affine_storage_readable_lframe w md mf bin sbase _ Source FF
     ltac:(intro pos;left;congruence)) as SF.
   assert (VB : Mem.valid_block md bin).
   { destruct Source as (_ & _ & _ & HP & _).
     eapply Mem.perm_valid_block;apply (HP sbase);lia. }
   assert (RP : Mem.range_perm mf bin lo hi Cur Readable).
   { intros pos HPos;apply (proj1 (proj2 FF));[exact VB|left;congruence|].
     apply (proj2 (RO pos Cur Readable));split;[exact HPos|constructor]. }
   pose proof (readonly_bounds_transport md mf bin lo hi VB RO
     (proj2 (clight_exec_forward secp_ge) md _ _ _ mf _ Negate) RP) as RF.
   exists md,mf;split;[exact Decode|];split;[exact Negate|];split;[exact OF|];split.
   + intro k;destruct k;[exact YF|exact XF].
   + split;[exact IF|];split;[exact SF|];split;[exact RF|].
     eapply lframe_trans;[exact Frame|exact FF].
 - exists md,md;split;[exact Decode|];split;[reflexivity|];split;[exact Owned|];split.
   + intro k;destruct k;[exact (Fields true)|exact (Fields false)].
   + split;[exact Infinity|];split;[exact Source|];split;assumption.
Qed.
