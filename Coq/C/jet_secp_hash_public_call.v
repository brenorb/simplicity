(** Whole original public hash_to_curve execution, including both return
    branches and all four frees. This characterizes the C result; the final
    canonical assertion/infinity boundary is not assumed away. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit Simplicity.Translate.
Require Import C.extraMath C.jet_memcpy_model C.jet_encoding C.jet_frame_layout C.jet_input_layout
 C.jet_output_layout C.jet_frame_inv C.jet_sx_mem C.jet_sx_exec C.jet_readBit_layout
 C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_secp_fe_math C.jet_secp_field_cmov
 C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_point_mul_storage
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_invert_literal
 C.jet_secp_fe_inv_prefix C.jet_secp_rescale_literal C.jet_secp_swu_literal
 C.jet_secp_add_literal C.jet_secp_literal_add_program C.jet_secp_canonical_zero
 C.jet_secp_generator_hash_literal C.jet_secp_generator_hash_map C.jet_secp_generator_affine_roundtrip
 C.jet_secp_sha_startup C.jet_secp_swu_startup C.jet_secp_generator_sha_absorb
 C.jet_secp_hashgen_function C.jet_clight_internal_preserve
 C.jet_secp_hash_public_entry C.jet_secp_hash_public_read C.jet_secp_hash_public_generate
 C.jet_secp_hash_public_finish.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge Simplicity.Translate.encode literal_swu literal_generator_hash
 literal_gej_ge_add rescale_field_output.

(** Pure part of the computed generator result, retained after its storage is
    freed. No new semantic target or memory/execution premise is introduced. *)
Definition hash_public_value key sx sy sz sumflag ox oy : Prop :=
 square_input_bounds sx /\square_input_bounds sy /\square_input_bounds sz /\
 sumflag=bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output sz))) /\
 (generator_hash_accepted false key=true ->generator_hash_accepted true key=true ->
   ((rescale_field_output sx,rescale_field_output sy),rescale_field_output sz)=
   @literal_gej_ge_add Alg.CoreFunSem
     ((@literal_swu Alg.CoreFunSem (@literal_generator_hash false Alg.CoreFunSem key),
        @literal_fe_one256 Alg.CoreFunSem tt),
       @literal_swu Alg.CoreFunSem (@literal_generator_hash true Alg.CoreFunSem key))) /\
 square_input_bounds ox /\square_input_bounds oy /\
 (sumflag=Int.zero ->exists zi,radix_value zi=literal_invert_numeric (fe_inv_value sz) /\
   ox=point_mul_words sx (square_words zi) /\oy=point_mul_words sy (point_mul_words zi (square_words zi)) /\
   radix_value ox mod feP=(radix_value sx*(radix_value zi*radix_value zi)) mod feP /\
   radix_value oy mod feP=(radix_value sy*(radix_value zi*(radix_value zi*radix_value zi))) mod feP) /\
 (sumflag<>Int.zero ->ox=generator_infinite_words /\oy=generator_infinite_words).
Lemma hash_public_value_of_result key m bg sx sy sz sumflag ox oy :
 hashgen_result key m bg sx sy sz sumflag ox oy ->hash_public_value key sx sy sz sumflag ox oy.
Proof.
 intros (BX & BY & BZ & Flag & Point & Bytes & BO & BP & Finite & Infinite).
 split;[exact BX|];split;[exact BY|];split;[exact BZ|];split;[exact Flag|];split;[exact Point|];
 split;[exact BO|];split;[exact BP|];split;assumption.
Qed.

Local Ltac empty_traces := repeat match goal with
 | H : Eapp ?a ?b = nil |- _ => apply app_eq_nil in H;destruct H;subst
 | H : Eapp ?a ?b = E0 |- _ => apply app_eq_nil in H;destruct H;subst
 end.
Lemma hash_public_body_splice e le leg mi mg mf out :
 Clight2.exec_stmt secp_ge e le mi (Ssequence hash_public_prefix hash_public_generate) E0 leg mg Out_normal ->
 Clight2.exec_stmt secp_ge e leg mg (Ssequence hash_public_decision hash_public_finish) E0 leg mf out ->
 Clight2.exec_stmt secp_ge e le mi (fn_body f_simplicity_hash_to_curve) E0 leg mf out.
Proof.
 intros Begin Rest;unfold hash_public_prefix in Begin.
 inversion Begin;subst;try contradiction;empty_traces.
 match goal with H:exec_stmt function_entry2 _ _ _ _ (Ssequence hash_public_copy hash_public_read) _ _ _ _ |- _ =>
   inversion H;subst;try contradiction end;empty_traces.
 rewrite hash_public_source,hash_public_tail_source.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[eassumption|].
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[eassumption|].
 inversion Rest;subst;empty_traces.
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[|eassumption].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);eassumption.
 - eapply exec_Sseq_2;[|eassumption].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);eassumption.
Qed.

Theorem eval_hash_public_original (Hmodel:memcpy_model) key v_env m0 bd base bs sbase bw outedge cursor N bi edge rc :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
     E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
 secp_sha_startup m0 ->swu_startup m0 ->(forall prefix,generator_sha_prefix_state prefix m0) ->
 write_frame_at m0 bd base bw outedge cursor N ->512<=N ->
 frame_base_valid sbase ->(8|sbase) ->frame_fields_at m0 bs sbase bi edge rc ->
 frame_input_cells_at m0 bi edge rc (Simplicity.Translate.encode (key:Ty.tySem (Word 8))) ->
 0<=rc ->rc+256<=Int64.max_unsigned ->exists mf sx sy sz sumflag ox oy,
 Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_hash_to_curve)
   [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] E0 mf
   (Vint (cmov_int (generator_hash_accepted false key && generator_hash_accepted true key))) /\
 hash_public_value key sx sy sz sumflag ox oy /\
 finv m0 bd base bw outedge cursor N bi mf
   (generator_hash_accepted false key && generator_hash_accepted true key)
   (if generator_hash_accepted false key && generator_hash_accepted true key
    then @Simplicity.Translate.encode (Ty.Prod (Word 8) (Word 8))
      (rescale_field_output ox,rescale_field_output oy) else []) /\
 lframe (fun b _=>~extA m0 bd bw bi b) m0 mf /\readonly_preserved m0 mf.
Proof.
 intros Count SHA SWU Prefixes Output Cap Base Align Source Input RC Max.
 destruct (hash_public_begin Hmodel key v_env m0 bd base bs sbase bi edge rc
   Count SHA SWU Prefixes Base Align Source Input RC Max)
   as (mi & bl & bk & bg & bp & mg & sx & sy & sz & sumflag & ox & oy & Entry & Begin & Result &
     Distinct & Old & Free & FrameG & ROG & SHAG & SWUG & PrefixG).
 set (accepted:=generator_hash_accepted false key && generator_hash_accepted true key) in *.
 set (le:=hash_public_temps v_env bd base bs sbase) in *.
 set (leg:=PTree.set _t'1 (Vint (cmov_int accepted)) le) in *.
 assert (InvG:finv m0 bd base bw outedge cursor N bi mg false []).
 { eapply finv_stable;[exact Output|apply finv_init;exact Output|].
   eapply lframe_implies;[exact FrameG|];intros;exact I. }
 assert (Dst:leg!_dst=Some (Vptr bd (Ptrofs.repr base))).
 { unfold leg,le,hash_public_temps;rewrite !PTree.gso by discriminate;apply PTree.gss. }
 assert (Flag:leg!_t'1=Some (Vint (cmov_int accepted))) by (unfold leg;apply PTree.gss).
 pose proof (hash_public_value_of_result _ _ _ _ _ _ _ _ _ Result) as Value.
 destruct Result as (BX & BY & BZ & SumFlag & Point & Bytes & BO & BP & Finite & Infinite).
 destruct (exec_hash_public_rest leg m0 bd base bw outedge cursor N bi rc mg bl bk bg bp accepted ox oy
   Dst Flag Output Cap InvG Distinct Old Free Bytes)
   as (mw & Rest & Final & FreeW & FrameW & ROW).
 destruct (hash_public_free mw bl bk bg bp Distinct FreeW) as (mf & Freed & FrameF & ROF).
 assert (ExtF:eqext m0 bd bw bi mw mf).
 { eapply lframe_implies;[exact FrameF|];intros b pos [_ Valid] _;exact (Old b Valid). }
 assert (ROFinal:readonly_preserved m0 mf) by
   (eapply preserved_trans;[exact ROG|];eapply preserved_trans;[exact ROW|exact ROF]).
 exists mf,sx,sy,sz,sumflag,ox,oy;split.
 - eapply eval_funcall_internal with (e:=hash_public_env bl bk bg bp) (le1:=le) (le2:=leg)
     (m1:=mi) (m2:=mw) (out:=Out_return (Some (Vint (cmov_int accepted),tint))).
   + exact Entry.
   + eapply hash_public_body_splice;[exact Begin|exact Rest].
   + split;[discriminate|destruct accepted;reflexivity].
   + exact Freed.
 - split;[exact Value|];split;[eapply finv_stable;[exact Output|exact Final|exact ExtF]|];split;[|exact ROFinal].
   assert (Frame:lframe (fun b _=>Mem.valid_block m0 b /\ ~extA m0 bd bw bi b) m0 mf).
   { eapply lframe_trans.
     - eapply lframe_implies;[exact FrameG|];intros;exact I.
     - eapply lframe_trans.
       + eapply lframe_implies;[exact FrameW|].
         intros b pos [Valid Outside] _;split;[|split;[|exact Outside]];
         intro Same;subst b;apply (Old _ Valid);clear;unfold hash_public_locals;cbn;tauto.
       + eapply lframe_implies;[exact FrameF|];intros b pos [Valid Outside] _;exact (Old b Valid). }
   eapply lframe_implies;[exact Frame|];intros b pos Outside Valid;split;assumption.
Qed.
