(** Original signed table lookup using only its checked internal call graph.
    Readonly framing does not require properties of arbitrary external calls. *)
(** Restore full framing of a genuinely readonly generator-table block after
    the original affine decoder. Reuses general Clight readonly readback. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory Values Clight ClightBigstep Events Ctypes.
Require Import C.jet_sx_state C.jet_sx_rep C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_secp_fe_nv C.jet_secp_multiply_normalize_bridge
 C.jet_secp_affine_storage C.jet_clight_forward C.jet_clight_readonly_frame.
Import ListNotations Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

From compcert Require Import Maps Clightdefs.
Require Import C.jet_secp_fe_math C.jet_secp_curve_statements C.jet_secp_table_index C.jet_secp_fns C.jet_clight_internal_frame C.jet_secp_affine_fields C.jet_secp_affine_storage_frame C.jet_secp_table_decode C.jet_secp_table_call
 C.jet_secp_affine_negate_owned C.jet_secp_field_negate_storage C.jet_secp_write_fe_numeric
 C.jet_secp_owned_field_slice C.jet_secp_owned_field_transport C.jet_secp_storage_unpack
 C.jet_secp_storage_numeric C.jet_secp_multiply_finish_product C.jet_secp_affine_weak_exec
 C.jet_secp_closed_helpers C.jet_clight_internal_preserve.
Lemma table_storage_internal_closed:
 closed_stmtb secp_closed_helpers(fn_body f_secp256k1_ge_from_storage)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma table_negate_internal_closed:
 closed_stmtb secp_closed_helpers(fn_body f_secp256k1_fe_negate)=true.
Proof. vm_compute;reflexivity. Qed.
Theorem affine_storage_internal_readonly_frame w m mf bout bin sbase lo hi :
 bout<>bin -> affine_storage_readable m bin sbase w ->
 readonly_region_bounds m bin lo hi ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_from_storage)
   [Vptr bout Ptrofs.zero;Vptr bin (Ptrofs.repr sbase)] E0 mf Vundef ->
 affine_storage_readable mf bin sbase w ->
 lframe (fun b pos => ~foot [(bout,0);(bin,sbase)] (map rshape affine_storage_regs) b pos) m mf ->
 readonly_region_bounds mf bin lo hi /\
 lframe (fun b pos => b<>bout \/ pos<0 \/ 84<=pos) m mf.
Proof.
 intros Sep Input Bounds Exec Output Frame.
 destruct Input as (IB & IA & IM & IP & IL).
 destruct Output as (OB & OA & OM & OP & OL).
 assert (Valid : Mem.valid_block m bin).
 { eapply Mem.perm_valid_block;apply (IP sbase);lia. }
 assert (Readable : Mem.range_perm mf bin lo hi Cur Readable).
 { intros pos HP.
   destruct (Z_le_dec sbase pos);[destruct (Z_lt_dec pos (sbase+64))|].
   - apply OP;lia.
   - apply (proj1 (proj2 Frame));[exact Valid| |].
     + intro HF;destruct (affine_storage_foot_bounds bout bin sbase bin pos HF)
         as [[HE _]|[_ HR]];[congruence|lia].
     + apply (proj2 (Bounds pos Cur Readable));split;[exact HP|constructor].
   - apply (proj1 (proj2 Frame));[exact Valid| |].
     + intro HF;destruct (affine_storage_foot_bounds bout bin sbase bin pos HF)
         as [[HE _]|[_ HR]];[congruence|lia].
     + apply (proj2 (Bounds pos Cur Readable));split;[exact HP|constructor]. }
 assert(Preserved:readonly_preserved m mf).
 { eapply(secp_closed_function_preserved f_secp256k1_ge_from_storage);
   [exact table_storage_internal_closed|reflexivity|exact Exec]. }
 assert(SourceFrame:lframe(fun b _=>b=bin)m mf).
 { apply lframe_unchanged;eapply Mem.unchanged_on_implies;[exact(proj2 Preserved)|].
   intros b pos Eq Valid';subst b;split;[exact Valid|].
   eapply readonly_bounds_not_writable;exact Bounds. }
 split.
 - apply (readonly_bounds_transport m mf bin lo hi Valid Bounds
     (proj1 Preserved) Readable).
 - eapply lframe_add_block;[exact Frame|exact SourceFrame|].
   intros b pos NotSource Outside HF.
   destruct (affine_storage_foot_bounds bout bin sbase b pos HF)
     as [[HE HR]|[HE HR]];[destruct Outside as [HN|[HN|HN]];[congruence|lia|lia]|congruence].
Qed.

Theorem eval_ge_from_storage_internal_table w m bout bin sbase lo hi :
 bout<>bin -> Mem.range_perm m bout 0 88 Cur Freeable ->
 affine_storage_readable m bin sbase w -> readonly_region_bounds m bin lo hi ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_from_storage)
   [Vptr bout Ptrofs.zero;Vptr bin (Ptrofs.repr sbase)] E0 mf Vundef /\
 Mem.range_perm mf bout 0 88 Cur Freeable /\
 (forall k : bool,fe_at mf bout (if k then 40 else 0) (words5 (affine_storage_coord w k))) /\
 Mem.load Mint32 mf bout 80=Some (Vint Int.zero) /\
 affine_storage_readable mf bin sbase w /\ readonly_region_bounds mf bin lo hi /\
 lframe (fun b pos => b<>bout \/ pos<0 \/ 84<=pos) m mf.
Proof.
 intros Sep Free Input Bounds.
 destruct (eval_ge_from_storage_readonly w m bout bin sbase Sep Free Input)
   as (mf & Exec & Owned & Fields & Infinity & Source & Frame).
 destruct (affine_storage_internal_readonly_frame w m mf bout bin sbase lo hi
   Sep Input Bounds Exec Source Frame) as (FinalBounds & FullFrame).
 exists mf;split;[exact Exec|];split;[exact Owned|];split;[exact Fields|];
   split;[exact Infinity|];split;[exact Source|];split;assumption.
Qed.
Theorem eval_table_decode_signed_internal (neg : bool) w m bout bin sbase lo hi :
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
 destruct (eval_ge_from_storage_internal_table w m bout bin sbase lo hi Sep Free Input Bounds)
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
   assert(Preserved:readonly_preserved md mf).
   { eapply(secp_closed_function_preserved f_secp256k1_fe_negate);
     [exact table_negate_internal_closed|reflexivity|exact Negate]. }
   pose proof(readonly_bounds_transport md mf bin lo hi VB RO(proj1 Preserved)RP)as RF.
   exists md,mf;split;[exact Decode|];split;[exact Negate|];split;[exact OF|];split.
   + intro k;destruct k;[exact YF|exact XF].
   + split;[exact IF|];split;[exact SF|];split;[exact RF|].
     eapply lframe_trans;[exact Frame|exact FF].
 - exists md,md;split;[exact Decode|];split;[reflexivity|];split;[exact Owned|];split.
   + intro k;destruct k;[exact (Fields true)|exact (Fields false)].
   + split;[exact Infinity|];split;[exact Source|];split;assumption.
Qed.
Theorem eval_ecmult_table_get_ge_storage_internal n w m bout bin base lo hi :
 0<Z.abs n<16384 -> 0<=base -> bout<>bin -> Mem.range_perm m bout 0 88 Cur Freeable ->
 affine_storage_readable m bin (base+64*table_storage_index n) w ->
 readonly_region_bounds m bin lo hi ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_table_get_ge_storage)
 [Vptr bout Ptrofs.zero;Vptr bin (Ptrofs.repr base);Vint (Int.repr n);Vint (Int.repr 15)] E0 mf Vundef /\
 Mem.range_perm mf bout 0 88 Cur Freeable /\
 (forall k : bool,fe_at mf bout (if k then 40 else 0) (table_signed_coordinate w (negb (0<?n)) k)) /\
 Mem.load Mint32 mf bout 80=Some (Vint Int.zero) /\
 affine_storage_readable mf bin (base+64*table_storage_index n) w /\
 readonly_region_bounds mf bin lo hi /\
 lframe (fun b pos => b<>bout \/ pos<0 \/ 84<=pos) m mf.
Proof.
 intros Bound Base Sep Free Source Readonly.
 destruct (eval_table_decode_signed_internal (negb (0<?n)) w m bout bin
   (base+64*table_storage_index n) lo hi Sep Free Source Readonly)
   as (md & mf & Decode & Tail & Owned & Fields & Infinity & Input & RO & Frame).
 assert (Max : base+64*table_storage_index n+64<=Ptrofs.max_unsigned)
   by exact (proj1 (proj2 (proj2 Source))).
 assert (HR : (table_lookup_temps n bout bin base)!_r=Some (Vptr bout Ptrofs.zero)).
 { unfold table_lookup_temps;rewrite !PTree.gso by discriminate;apply PTree.gss. }
 assert (HP : (table_lookup_temps n bout bin base)!_pre=Some (Vptr bin (Ptrofs.repr base))).
 { unfold table_lookup_temps;rewrite !PTree.gso by discriminate;apply PTree.gss. }
 assert (HN : (table_lookup_temps n bout bin base)!_n=Some (Vint (Int.repr n))).
 { unfold table_lookup_temps;rewrite PTree.gso by discriminate;apply PTree.gss. }
 exists mf;split.
 - eapply eval_funcall_internal with (e:=empty_env) (le1:=table_lookup_temps n bout bin base)
     (le2:=table_lookup_temps n bout bin base) (m1:=m) (m2:=mf) (out:=Out_normal).
   + apply table_lookup_entry.
   + rewrite table_lookup_body_source;eapply exec_table_lookup_body;eassumption.
   + reflexivity.
   + reflexivity.
 - split;[exact Owned|];split;[exact Fields|];split;[exact Infinity|];
     split;[exact Input|];split;assumption.
Qed.
