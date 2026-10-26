(** Whole original NULL-blinding generator call, with its eleven allocations
    and frees. Retain exact return, stored bytes, point-sum correspondence
    and both affine branches. Deferred memcpy/CTZ premises remain explicit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.extraMath C.jet_memcpy_model C.jet_sx_exec C.jet_sx_mem C.jet_readBit_layout
 C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_field_cmov C.jet_secp_field_pair_multiply C.jet_secp_square_columns
 C.jet_secp_square_numeric C.jet_secp_point_mul_storage C.jet_secp_multiply_normalize_bridge
 C.jet_secp_multiply_finish_product C.jet_secp_invert_literal C.jet_secp_fe_inv_prefix
 C.jet_secp_rescale_literal C.jet_secp_swu_literal C.jet_secp_swu_startup C.jet_secp_curve_frame
 C.jet_clight_internal_preserve C.jet_buffer_input C.jet_read8s_layout C.jet_secp_sha_startup
 C.jet_secp_generator_sha_start C.jet_secp_generator_sha_absorb C.jet_secp_generator_hash_literal
 C.jet_secp_generator_hash_map C.jet_secp_generator_points_prefix C.jet_secp_generator_generate_body
 C.jet_secp_generator_codec C.jet_secp_generator_affine_roundtrip C.jet_secp_hashgen_entry
 C.jet_secp_add_literal C.jet_secp_literal_add_program C.jet_secp_canonical_zero.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_swu rescale_field_output literal_generator_hash literal_gej_ge_add generator_saved_bytes.

Definition hashgen_result key m bg sx sy sz sumflag ox oy : Prop :=
 square_input_bounds sx /\square_input_bounds sy /\square_input_bounds sz /\
 sumflag=bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output sz))) /\
 (generator_hash_accepted false key=true ->generator_hash_accepted true key=true ->
   ((rescale_field_output sx,rescale_field_output sy),rescale_field_output sz)=
   @literal_gej_ge_add Alg.CoreFunSem
     ((@literal_swu Alg.CoreFunSem (@literal_generator_hash false Alg.CoreFunSem key),
        @literal_fe_one256 Alg.CoreFunSem tt),
       @literal_swu Alg.CoreFunSem (@literal_generator_hash true Alg.CoreFunSem key))) /\
 (forall (second:bool) i,(i<32)%nat ->
   Mem.load Mint8unsigned m bg ((if second then 32 else 0)+Z.of_nat i)=
     Some (Vint (nth i (map Int.repr (generator_saved_bytes (field_pair_valuation ox oy)
       (if second then 5 else 0))) Int.zero))) /\
 square_input_bounds ox /\square_input_bounds oy /\
 (sumflag=Int.zero ->exists zi,radix_value zi=literal_invert_numeric (fe_inv_value sz) /\
   ox=point_mul_words sx (square_words zi) /\oy=point_mul_words sy (point_mul_words zi (square_words zi))) /\
 (sumflag<>Int.zero ->ox=generator_infinite_words /\oy=generator_infinite_words).

Lemma hashgen_result_lframe key m mf bg sx sy sz sumflag ox oy P :
 hashgen_result key m bg sx sy sz sumflag ox oy ->lframe P m mf ->
 (forall pos,P bg pos) ->hashgen_result key mf bg sx sy sz sumflag ox oy.
Proof.
 intros (BX & BY & BZ & Flag & Point & Bytes & BO & BP & Finite & Infinite) Frame Outside.
 assert (Valid:Mem.valid_block m bg).
 { pose proof (Bytes false 0%nat ltac:(clear;lia)) as Load;apply Mem.load_valid_access in Load.
   eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact Load|constructor]. }
 split;[exact BX|];split;[exact BY|];split;[exact BZ|];split;[exact Flag|];split;[exact Point|];split.
 - intros second i Index;rewrite (proj1 Frame);[apply Bytes;exact Index|exact Valid|intros;apply Outside].
 - split;[exact BO|];split;[exact BP|];split;assumption.
Qed.

Local Ltac stored_owned Free := apply Free;clear;cbn [hashgen_storage In];tauto.
Local Ltac local_geometry Sep Old :=
 clear -Sep Old;unfold hashgen_locals in *;
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence.

Theorem eval_hashgen_internal (Hmodel:memcpy_model) (key:Ty.tySem (Word 8)) m bg ba oa :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
     E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
 ba<>bg ->Ptrofs.unsigned oa+32<=Ptrofs.max_unsigned ->
 secp_sha_startup m ->swu_startup m ->(forall prefix,generator_sha_prefix_state prefix m) ->
 Mem.range_perm m bg 0 64 Cur Freeable ->
 (forall i,(i<32)%nat ->Mem.load Mint8unsigned m ba (Ptrofs.unsigned oa+Z.of_nat i)=
   Some (Vint (nth i (map word8_array_value (vector_values (Word 3) 5 key)) Int.zero))) ->
 exists mf sx sy sz sumflag ox oy,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_generator_generate_internal)
   [Vptr bg Ptrofs.zero;Vptr ba oa;Vlong Int64.zero] E0 mf
   (Vint (cmov_int (generator_hash_accepted false key && generator_hash_accepted true key))) /\
 hashgen_result key mf bg sx sy sz sumflag ox oy /\Mem.range_perm mf bg 0 64 Cur Freeable /\
 (forall i,(i<32)%nat ->Mem.load Mint8unsigned mf ba (Ptrofs.unsigned oa+Z.of_nat i)=
   Some (Vint (nth i (map word8_array_value (vector_values (Word 3) 5 key)) Int.zero))) /\
 lframe (fun b _=>b<>bg) m mf /\readonly_preserved m mf /\
 secp_sha_startup mf /\swu_startup mf /\(forall prefix,generator_sha_prefix_state prefix mf).
Proof.
 intros Count AG Hi SHA SWU Prefixes FG Input.
 assert (VG:Mem.valid_block m bg) by (eapply Mem.perm_valid_block;apply (FG 0);clear;lia).
 assert (VA:Mem.valid_block m ba).
 { pose proof (Input 0%nat ltac:(clear;lia)) as Load;apply Mem.load_valid_access in Load.
   eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact Load|constructor]. }
 destruct (hashgen_entry m bg ba oa)
   as (mi & bt & bp & bx & bo & bs & bb & bl & bc0 & bc1 & br1 & br0 & Entry & Sep & Old & Free & AllocFrame & AllocRead).
 pose proof (Old bg VG) as OldG;pose proof (Old ba VA) as OldA.
 assert (BodySep:NoDup [ba;br0;bc0;br1;bc1;bs;bb;bt;bp;bx;bg]).
 { clear -Sep OldG OldA AG;unfold hashgen_locals in *;
   repeat rewrite NoDup_cons_iff in Sep;cbn [In] in OldG,OldA,Sep;
   repeat rewrite NoDup_cons_iff;cbn [In];intuition congruence. }
 assert (FGI:Mem.range_perm mi bg 0 64 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FG|exact AllocFrame|intros;exact I]. }
 assert (SHAI:secp_sha_startup mi).
 { eapply secp_sha_startup_preserved;[exact SHA|exact AllocRead|exact AllocFrame|intros;exact I]. }
 assert (SWUI:swu_startup mi) by (eapply swu_startup_preserved;[exact SWU|exact AllocRead]).
 assert (PrefixI:forall prefix,generator_sha_prefix_state prefix mi).
 { intro prefix;eapply generator_sha_prefix_preserved;[apply Prefixes|exact AllocRead]. }
 assert (InputI:forall i,(i<32)%nat ->Mem.load Mint8unsigned mi ba (Ptrofs.unsigned oa+Z.of_nat i)=
   Some (Vint (nth i (map word8_array_value (vector_values (Word 3) 5 key)) Int.zero))).
 { intros i Index;rewrite (proj1 AllocFrame);[apply Input;exact Index|exact VA|intros;exact I]. }
 destruct (exec_generator_generate_body Hmodel key
   (hashgen_env bt bp bx bo bs bb bl bc0 bc1 br1 br0) (hashgen_entry_temps bg ba oa) mi
   br0 bc0 br1 bc1 bs bb bt bp bx ba oa bg Count
   eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
   eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
   ltac:(intros [];reflexivity) eq_refl eq_refl eq_refl BodySep Hi SHAI SWUI PrefixI
   ltac:(stored_owned Free) ltac:(stored_owned Free) ltac:(stored_owned Free) ltac:(stored_owned Free)
   ltac:(stored_owned Free) ltac:(stored_owned Free) ltac:(stored_owned Free) ltac:(stored_owned Free)
   ltac:(stored_owned Free) FGI InputI)
   as (mo & sx & sy & sz & sumflag & ox & oy & Body & BX & BY & BZ & Flag & Point & Bytes & BO & BP & Finite & Infinite &
     FR0 & FC0 & FR1 & FC1 & FS & FB & FT & FP & FX & FGO & KeyO & BodyFrame & BodyRead & SHAO & SWUO & PrefixO).
 assert (Value:hashgen_result key mo bg sx sy sz sumflag ox oy).
 { split;[exact BX|];split;[exact BY|];split;[exact BZ|];split;[exact Flag|];split;[exact Point|];
   split;[exact Bytes|];split;[exact BO|];split;[exact BP|];split;assumption. }
 assert (FO:Mem.range_perm mo bo 0 4 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|stored_owned Free|exact BodyFrame|];intro pos;local_geometry Sep OldG. }
 assert (FL:Mem.range_perm mo bl 0 32 Cur Freeable).
 { eapply curve_keep_free.
   - clear;lia.
   - stored_owned Free.
   - exact BodyFrame.
   - intro pos;local_geometry Sep OldG. }
 destruct (free_list_exists [(bo,0,4);(bc1,0,88);(bc0,0,88);(bs,0,32);(bx,0,128);(bp,0,88);
   (br0,0,88);(br1,0,88);(bt,0,40);(bl,0,32);(bb,0,32)] mo) as (mf & FreeAll & Unchanged).
 - clear -Sep;unfold hashgen_locals in Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
   cbn;repeat constructor;cbn;intuition congruence.
 - intros b lo hi Slot;cbn [In] in Slot;
   repeat match goal with S:_ \/ _ |- _=>destruct S as [S|S] end;try contradiction;
   match goal with S:(_,_,_) = (_,_,_) |- _=>inversion S;subst b lo hi end;assumption.
 - assert (FreeFrame:lframe (fun b _=>~In b (hashgen_locals bt bp bx bo bs bb bl bc0 bc1 br1 br0)) mo mf).
   { eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
     intros b pos Outside Valid;clear -Outside;unfold hashgen_locals in Outside;cbn in *;intuition congruence. }
   assert (FGF:Mem.range_perm mf bg 0 64 Cur Freeable).
   { eapply curve_keep_free;[clear;lia|exact FGO|exact FreeFrame|intros;exact OldG]. }
   assert (ValueF:hashgen_result key mf bg sx sy sz sumflag ox oy)
     by (eapply hashgen_result_lframe;[exact Value|exact FreeFrame|intros;exact OldG]).
   assert (FrameOld:lframe (fun b _=>Mem.valid_block m b /\b<>bg) m mf).
   { eapply lframe_trans.
     - eapply lframe_implies;[exact AllocFrame|intros;exact I].
     - eapply lframe_trans.
       + eapply lframe_implies;[exact BodyFrame|];intros b pos [Valid Other] _.
         pose proof (Old b Valid) as Outside;clear -Outside Other;unfold hashgen_locals in Outside;cbn [In] in Outside;
           repeat split;intuition congruence.
       + eapply lframe_implies;[exact FreeFrame|];intros b pos [Valid Other] _;exact (Old b Valid). }
   assert (Frame:lframe (fun b _=>b<>bg) m mf).
   { eapply lframe_implies;[exact FrameOld|];intros b pos Other Valid;split;assumption. }
   assert (Read:readonly_preserved m mf).
   { eapply preserved_trans;[exact AllocRead|];eapply preserved_trans;[exact BodyRead|].
     eapply freelist_preserved;exact FreeAll. }
   exists mf,sx,sy,sz,sumflag,ox,oy;split.
   + eapply eval_funcall_internal with
       (e:=hashgen_env bt bp bx bo bs bb bl bc0 bc1 br1 br0)
       (le1:=hashgen_entry_temps bg ba oa) (le2:=generator_points_temps key (hashgen_entry_temps bg ba oa))
       (m1:=mi) (m2:=mo)
       (out:=Out_return (Some (Vint (cmov_int (generator_hash_accepted false key && generator_hash_accepted true key)),tint))).
     * exact Entry.
     * exact Body.
     * split;[discriminate|reflexivity].
     * rewrite hashgen_blocks;exact FreeAll.
   + split;[exact ValueF|];split;[exact FGF|];split.
     * intros i Index;rewrite (proj1 Frame);[apply Input;exact Index|exact VA|intros;exact AG].
     * split;[exact Frame|];split;[exact Read|];split.
       -- eapply secp_sha_startup_preserved;[exact SHA|exact Read|exact Frame|].
          pose proof (proj1 (secp_sha_startup_separate m bg 64 SHA ltac:(clear;lia) FG));intros;congruence.
       -- split;[eapply swu_startup_preserved;[exact SWU|exact Read]|].
          intro prefix;eapply generator_sha_prefix_preserved;[apply Prefixes|exact Read].
Qed.
