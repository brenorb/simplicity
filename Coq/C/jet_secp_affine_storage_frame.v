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

Lemma affine_storage_foot_bounds bout bin sbase b pos :
 foot [(bout,0);(bin,sbase)] (map rshape affine_storage_regs) b pos ->
 (b=bout /\ 0<=pos<84) \/ (b=bin /\ sbase<=pos<sbase+64).
Proof.
 intros (r & sh & d & ch & HN & HC & HB & HO).
 destruct r as [|[|r]].
 - left;split;[exact HB|].
   cbn [affine_storage_regs map nth_error rshape affine_storage_undef rcells rw rfree] in HN;
     injection HN as <-.
   cbn [fst map cshape cofs cchunk] in HC.
   destruct HC as [HC|[HC|[HC|[HC|[HC|[HC|[HC|[HC|[HC|[HC|[HC|HC]]]]]]]]]]];
     try contradiction;inversion HC;subst d ch;
     cbv beta iota zeta delta [bas lay nth snd] in HO;
     cbn [size_chunk] in HO;lia.
 - right;split;[exact HB|].
   cbn [affine_storage_regs map nth_error rshape rcells rw rfree] in HN;
     injection HN as <-.
   cbn [affine_storage_input seq u64_cells fst map cshape cofs cchunk] in HC.
   destruct HC as [HC|[HC|[HC|[HC|[HC|[HC|[HC|[HC|HC]]]]]]]];
     try contradiction;inversion HC;subst d ch;
     cbv beta iota zeta delta [bas lay nth snd] in HO;
     change (size_chunk Mint64) with 8 in HO;lia.
 - destruct r;discriminate HN.
Qed.

Theorem affine_storage_readonly_frame w m mf bout bin sbase lo hi :
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
 pose proof (clight_funcall_readonly_lframe secp_ge m _ _ _ mf _ bin lo hi
   Exec Valid Bounds Readable) as SourceFrame.
 split.
 - apply (readonly_bounds_transport m mf bin lo hi Valid Bounds
     (proj2 (clight_exec_forward secp_ge) m _ _ _ mf _ Exec) Readable).
 - eapply lframe_add_block;[exact Frame|exact SourceFrame|].
   intros b pos NotSource Outside HF.
   destruct (affine_storage_foot_bounds bout bin sbase b pos HF)
     as [[HE HR]|[HE HR]];[destruct Outside as [HN|[HN|HN]];[congruence|lia|lia]|congruence].
Qed.

Theorem eval_ge_from_storage_table w m bout bin sbase lo hi :
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
 destruct (affine_storage_readonly_frame w m mf bout bin sbase lo hi
   Sep Input Bounds Exec Source Frame) as (FinalBounds & FullFrame).
 exists mf;split;[exact Exec|];split;[exact Owned|];split;[exact Fields|];
   split;[exact Infinity|];split;[exact Source|];split;assumption.
Qed.
