(** Public hash_to_curve's actual frame copy and raw-byte reader. The input
    is the full Word256 domain: there is no reduction modulo the field. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jet_exec C.jet_encoding C.jet_frame_layout C.jet_frame_copy_layout C.jet_frame_inv
 C.jet_input_layout C.jet_buffer_input C.jet_read8s_layout C.jet_sx_mem C.jet_sx_state C.jet_sx_exec
 C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_secp_local_regions C.jet_secp_hash_public_entry
 C.jet_clight_internal_preserve C.jet_secp_modinfo_fe_caller.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge Translate.encode.

Definition hash_public_copy := Sassign (Evar _src (Tstruct _frameItem noattr))
 (Etempvar _src (Tstruct _frameItem noattr)).
Definition hash_public_read := Scall None
 (Evar _read8s (Tfunction (Tcons (tptr tuchar)
   (Tcons tulong (Tcons (tptr (Tstruct _frameItem noattr)) Tnil))) tvoid cc_default))
 [Evar _key (tarray tuchar 32);Econst_int (Int.repr 32) tint;
  Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr))].
Definition hash_public_prefix := Ssequence hash_public_copy hash_public_read.
Definition hash_public_tail := match fn_body f_simplicity_hash_to_curve with
 | Ssequence _ (Ssequence _ rest)=>rest | _=>Sskip end.
Lemma hash_public_source : fn_body f_simplicity_hash_to_curve=
 Ssequence hash_public_copy (Ssequence hash_public_read hash_public_tail).
Proof. reflexivity. Qed.

Lemma hash_raw_reader_preserved m args t mf result :
 Clight2.eval_funcall secp_ge m (Internal C.jets.f_read8s) args t mf result -> readonly_preserved m mf.
Proof.
 intro Run;apply (proj2(internal_exec_preserved _ _ gej_reader_internal_table_correct)
   m _ args t mf result Run).
 exists _read8s,f_read8s;split;reflexivity.
Qed.

Lemma exec_hash_public_read le m mf bl bk bg bp :
 Clight2.eval_funcall secp_ge m (Internal C.jets.f_read8s)
   [Vptr bk Ptrofs.zero;Vlong (Int64.repr 32);Vptr bl Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge (hash_public_env bl bk bg bp) le m hash_public_read E0 le mf Out_normal.
Proof.
 intro Read.
 assert (Member:In (C.jets._read8s,C.jets.f_read8s) secp_core_helpers).
 { unfold secp_core_helpers;do 19 right;left;reflexivity. }
 destruct (secp_core_helpers_entries _ _ Member) as (b0 & bf & HS0 & HF0 & HS & HF).
 unfold hash_public_read;eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
   (vargs:=[Vptr bk Ptrofs.zero;Vlong (Int64.repr 32);Vptr bl Ptrofs.zero])
   (f:=Internal C.jets.f_read8s) (vres:=Vundef).
 - reflexivity.
 - eapply eval_Elvalue.
   + eapply eval_Evar_global;[reflexivity|exact HS].
   + apply deref_loc_reference;reflexivity.
 - eapply eval_Econs.
   + eapply eval_Elvalue;[apply eval_Evar_local;reflexivity|apply deref_loc_reference;reflexivity].
   + reflexivity.
   + eapply eval_Econs;[constructor|reflexivity|].
     eapply eval_Econs;[eapply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
 - exact HF.
 - reflexivity.
 - exact Read.
Qed.

Theorem hash_public_prepare key le m0 mi bl bk bg bp bs sbase bi edge rc :
 NoDup (hash_public_locals bl bk bg bp) ->
 (forall b,Mem.valid_block m0 b ->~In b (hash_public_locals bl bk bg bp)) ->
 (forall b hi,In (b,hi) (hash_public_storage bl bk bg bp) ->
   Mem.range_perm mi b 0 hi Cur Freeable) ->
 lframe (fun _ _=>True) m0 mi ->readonly_preserved m0 mi ->
 le!_src=Some (Vptr bs (Ptrofs.repr sbase)) ->
 frame_base_valid sbase ->(8|sbase) ->frame_fields_at m0 bs sbase bi edge rc ->
 frame_input_cells_at m0 bi edge rc (Translate.encode (key:Ty.tySem (Word 8))) ->
 0<=rc ->rc+256<=Int64.max_unsigned ->exists mf,
 Clight2.exec_stmt secp_ge (hash_public_env bl bk bg bp) le mi hash_public_prefix E0 le mf Out_normal /\
 (forall i,(i<32)%nat ->Mem.load Mint8unsigned mf bk (Z.of_nat i)=
   Some (Vint (nth i (map word8_array_value (vector_values (Word 3) 5 key)) Int.zero))) /\
 frame_fields_at mf bl 0 bi edge (rc+256) /\
 (forall b hi,In (b,hi) (hash_public_storage bl bk bg bp) ->
   Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun _ _=>True) m0 mf /\readonly_preserved m0 mf.
Proof.
 intros Distinct Old Free Alloc RO Temp Base Align Source Input RC Max.
 assert (Length:length (vector_values (Word 3) 5 key)=32%nat) by apply vector_values_length.
 assert (InputBytes:forall i x,nth_error (vector_values (Word 3) 5 key) i=Some x ->
   frame_input_word_at m0 bi edge (rc+8*Z.of_nat i) x).
 { apply frame_input_byte_list;rewrite <-(encode_vector_values (Word 3) 5 key);exact Input. }
 assert (ValidI:Mem.valid_block m0 bi).
 { destruct (vector_values (Word 3) 5 key) as [|x xs] eqn:Bytes;[discriminate|].
   pose proof (InputBytes 0%nat x eq_refl) as Bits.
   specialize (Bits 0%nat (Z.testbit (@toZ (WordToZ 3) x) 7) eq_refl).
   destruct Bits as (_ & _ & w & Load & _);eapply load_valid;exact Load. }
 assert (Apart:bl<>bk /\ bl<>bi /\ bk<>bi).
 { split.
   - clear -Distinct;unfold hash_public_locals in Distinct;repeat rewrite NoDup_cons_iff in Distinct;
     cbn [In] in Distinct;intuition congruence.
   - split;intro Same;subst;apply (Old bi ValidI);unfold hash_public_locals;cbn;tauto. }
 destruct Apart as (LK & LI & KI).
 assert (FL:Mem.range_perm mi bl 0 16 Cur Freeable).
 { apply Free;clear;cbn [hash_public_storage In];tauto. }
 assert (SourceI:frame_fields_at mi bs sbase bi edge rc).
 { destruct Source as [Edge Cursor];pose proof (load_valid _ _ _ _ _ Edge) as V.
   split;rewrite (proj1 Alloc) by auto;assumption. }
 destruct SourceI as [EdgeI CursorI].
 destruct (frame_loadbytes_at mi bs sbase _ _ EdgeI CursorI) as (bytes & LoadBytes).
 pose proof (Mem.loadbytes_length _ _ _ _ _ LoadBytes) as BytesLength.
 assert (CopyWritable:Mem.range_perm mi bl 0 (0+Z.of_nat (length bytes)) Cur Writable).
 { rewrite BytesLength;apply freeable_range_writable;exact FL. }
 destruct (Mem.range_perm_storebytes mi bl 0 bytes CopyWritable) as (md & Store).
 assert (FrameD:lframe (fun b _=>Mem.valid_block m0 b) m0 md).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact Alloc|];intros;exact I.
   - apply lframe_unchanged;eapply Mem.storebytes_unchanged_on;[exact Store|].
     intros pos Range Valid;apply (Old bl Valid);unfold hash_public_locals;cbn;tauto. }
 assert (Copy:Clight2.exec_stmt secp_ge (hash_public_env bl bk bg bp) le mi hash_public_copy E0 le md Out_normal).
 { assert (Unsigned:Ptrofs.unsigned (Ptrofs.repr sbase)=sbase).
   { apply Ptrofs.unsigned_repr;unfold frame_base_valid in Base;lia. }
   unfold hash_public_copy;eapply exec_Sassign_copy.
   - apply eval_Evar_local;reflexivity.
   - apply eval_Etempvar;exact Temp.
   - reflexivity.
   - eapply assign_loc_copy with (b':=bs) (ofs':=Ptrofs.repr sbase) (bytes:=bytes).
     + reflexivity.
     + intros _;change (8|Ptrofs.unsigned (Ptrofs.repr sbase));rewrite Unsigned;exact Align.
     + intros _;change (8|0);exists 0;reflexivity.
     + left;intro Same;subst bs;apply (Old bl (load_valid _ _ _ _ _ (proj1 Source)));
       unfold hash_public_locals;cbn;tauto.
     + change (Mem.loadbytes mi bs (Ptrofs.unsigned (Ptrofs.repr sbase)) 16=Some bytes).
       rewrite Unsigned;exact LoadBytes.
     + exact Store. }
 assert (FreeD:forall b hi,In (b,hi) (hash_public_storage bl bk bg bp) ->
   Mem.range_perm md b 0 hi Cur Freeable).
 { intros b hi Slot pos Range;eapply Mem.perm_storebytes_1;[exact Store|exact (Free b hi Slot pos Range)]. }
 assert (InputD:forall i x,nth_error (vector_values (Word 3) 5 key) i=Some x ->
   frame_input_word_at md bi edge (rc+8*Z.of_nat i) x).
 { intros i x At;eapply frame_input_bits_at_preserved;[|exact (InputBytes i x At)].
   intros ofs w Load;rewrite (proj1 FrameD) by auto;exact Load. }
 assert (KeyWritable:Mem.range_perm md bk 0 (0+Z.of_nat (length (vector_values (Word 3) 5 key))) Cur Writable).
 { rewrite Length;apply freeable_range_writable;apply FreeD;clear;cbn [hash_public_storage In];tauto. }
 assert (CursorWritable:Mem.valid_access md Mint64 bl (0+8) Writable).
 { split;[|change (8|8);exists 1;reflexivity].
   intros pos Range;eapply Mem.perm_implies;[apply (FreeD bl 16);[clear;cbn [hash_public_storage In];tauto|cbn in Range;lia]|constructor]. }
 destruct (secp_read8s_layout md bk 0 bl 0 bi edge rc (vector_values (Word 3) 5 key)
   ltac:(clear;lia) ltac:(rewrite Length;clear;change (32<=18446744073709551615);lia)
   KeyWritable LK LI KI ltac:(unfold frame_base_valid;change (0<=0 /\ 0+16<=18446744073709551615);lia)
   RC ltac:(rewrite Length;exact Max) (frame_copy_fields_at _ _ _ _ _ _ _ _ LoadBytes Store EdgeI CursorI)
   CursorWritable InputD) as (mf & Read & Key & Fields & Loads & Perms & Valid).
 assert (FrameR:lframe (fun b _=>Mem.valid_block m0 b) md mf).
 { split.
   - intros chunk b ofs VB Range;apply Loads.
     + left;intro Same;subst b;apply (Old bl (Range ofs ltac:(pose proof (size_chunk_pos chunk);lia)));
       unfold hash_public_locals;cbn;tauto.
     + left;intro Same;subst b;apply (Old bk (Range ofs ltac:(pose proof (size_chunk_pos chunk);lia)));
       unfold hash_public_locals;cbn;tauto.
   - split;[intros;apply Perms;assumption|exact Valid]. }
 exists mf;split.
 - unfold hash_public_prefix;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=md) (le1:=le);
   [exact Copy|apply exec_hash_public_read;rewrite Length in Read;exact Read].
 - split.
   + intros i Bound;replace (Z.of_nat i) with (0+Z.of_nat i) by lia;apply Key.
     apply nth_error_nth';rewrite map_length,Length;exact Bound.
   + split;[rewrite Length in Fields;exact Fields|];split.
     * intros b hi Slot pos Range;apply Perms;exact (FreeD b hi Slot pos Range).
     * split.
       -- eapply lframe_implies;[eapply lframe_trans;[exact FrameD|exact FrameR]|];auto.
       -- eapply preserved_trans;[exact RO|];eapply preserved_trans.
          ++ eapply storebytes_preserved;exact Store.
          ++ eapply hash_raw_reader_preserved;exact Read.
Qed.
