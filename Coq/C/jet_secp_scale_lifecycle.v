(** Full original off_curve_scale execution on general valid frames/cursors.
    Derive every helper call, literal output, framing, startup preservation
    and the actual private-object lifecycle. Memset remains explicit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Integers Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jets_secp C.jet_secp_linkage C.jet_clight_internal_preserve C.jet_secp_strauss_zero_generator C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem
 C.jet_frame_layout C.jet_frame_copy_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv C.jet_encoding
 C.jet_secp_frame C.jet_secp_scale_startup C.jet_secp_strauss_complete_program.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Require Import C.jet_secp_scale_public_support.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit Simplicity.Translate.
Require Import C.jet_memset_model C.jet_readBit_layout C.jet_secp_curve_frame C.jet_secp_ecmult_scale C.jet_secp_scale_public_reads C.jet_secp_rescale_public_reads
 C.jet_secp_point_output_literal C.jet_secp_rescale_literal C.jet_secp_square_spec_bridge
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_odd_table_literal_walk C.jet_secp_literal_gej_predicate C.jet_secp_strauss_complete_program
 C.jet_secp_scalar_io_preserve C.jet_secp_generate_body C.jet_secp_canonical_scalar
 C.jet_secp_fe_nv C.jet_secp_canonical_zero C.jet_encoding C.jet_secp_wrapper_run.
Local Opaque literal_off_curve_scale Simplicity.Translate.encode.
Lemma scale_reader_literal (value:Ty.tySem (Word 8)) :
 table_word_literal (square_reader_rho value) value.
Proof.
 unfold table_word_literal;rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue.
Qed.

Theorem eval_off_curve_scale_initialized (Model:memset_model) v_env m0 bd base bs sbase bw edge cursor N bi inedge rc
 (raw ax ay az:Ty.tySem (Word 8)) :
 scale_startup m0 -> write_frame_at m0 bd base bw edge cursor N -> 768<=N ->
 frame_base_valid sbase -> (8|sbase) -> frame_fields_at m0 bs sbase bi inedge rc ->
 frame_input_cells_at m0 bi inedge rc (map Some (frame_input_word_bits raw)) ->
 frame_input_cells_at m0 bi inedge (rc+256) (map Some (frame_input_word_bits ax)) ->
 frame_input_cells_at m0 bi inedge (rc+512) (map Some (frame_input_word_bits ay)) ->
 frame_input_cells_at m0 bi inedge (rc+768) (map Some (frame_input_word_bits az)) ->
 0<=rc -> rc+1024<=Int64.max_unsigned ->
 exists mf,
 Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_off_curve_scale)
  [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] E0 mf (Vint Int.one) /\
 finv m0 bd base bw edge cursor N bi mf true
  (Simplicity.Translate.encode (@literal_off_curve_scale Alg.CoreFunSem (raw,((ax,ay),az)))) /\
 lframe (fun b _=>~extA m0 bd bw bi b) m0 mf /\ scale_startup mf.
Proof.
 intros Ready Output Cap Base Align Source Raw AX AY AZ RC Max.
 destruct (scale_public_prepare v_env m0 bd base bs sbase bw edge cursor N bi inedge rc
  Ready Output Base Align Source)
  as (mi & md & bl & br & ba & bk & Entry & Copy & OwnedD & SourceD & Separate & Old & Sep & FinD & ReadyD & PrepFrame).
 pose (le:=scale_public_temps v_env bd base bs sbase).
 assert (Distinct:br<>bk /\ br<>ba /\ br<>bl /\ bk<>bl /\ ba<>bl /\ bk<>ba).
 { clear -Separate;unfold scale_public_locals in Separate;repeat rewrite NoDup_cons_iff in Separate;
   cbn [In] in Separate;intuition congruence. }
 destruct Distinct as (RK & RA & RL & KL & AL & KA).
 assert (FRD:Mem.range_perm md br 0 128 Cur Freeable) by (apply OwnedD;clear;cbn [scale_public_storage In];tauto).
 assert (FKD:Mem.range_perm md bk 0 32 Cur Freeable) by (apply OwnedD;clear;cbn [scale_public_storage In];tauto).
 assert (FAD:Mem.range_perm md ba 0 128 Cur Freeable) by (apply OwnedD;clear;cbn [scale_public_storage In];tauto).
 assert (FLD:Mem.range_perm md bl 0 16 Cur Freeable) by (apply OwnedD;clear;cbn [scale_public_storage In];tauto).
 assert (SepRead:xsep (extA m0 bd bw bi) [(bk,0);(ba,0);(bl,0)]).
 { intros [|[|[|r]]] Index;[exact (Sep 2%nat ltac:(cbn;lia))|exact (Sep 1%nat ltac:(cbn;lia))|
   exact (Sep 3%nat ltac:(cbn;lia))|cbn in Index;lia]. }
 destruct (eval_scale_public_reads m0 bd base bw edge cursor N bi inedge rc raw ax ay az md bk ba bl
  Output Cap Raw AX AY AZ RC Max FKD FAD FLD SourceD KL AL KA SepRead FinD)
  as (mr & mp & Scalar & Point & Input & X & Y & Z & Flag & FKP & FAP & FLP & SourceP & FinP & ReadFrame).
 assert (FRP:Mem.range_perm mp br 0 128 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FRD|exact ReadFrame|].
   intros pos;repeat split;try assumption;exact (Sep 0%nat ltac:(cbn;lia)). }
 assert (ReadyP:scale_startup mp).
 { eapply scale_startup_readonly;[exact ReadyD|].
   eapply preserved_trans;[eapply scalar_reader_preserved;exact Scalar|eapply scale_point_reader_preserved;exact Point]. }
 assert (OwnedP:forall b hi,In (b,hi) [(br,128);(bk,32);(ba,128)] -> Mem.range_perm mp b 0 hi Cur Freeable).
 { intros b hi [Same|[Same|[Same|[]]]];injection Same;intros;subst;assumption. }
 assert (MultSeparate:NoDup [br;bk;ba]).
 { clear -RK RA KA;repeat constructor;cbn [In];intuition congruence. }
 rewrite !rescale_reader_limbs in X,Y,Z.
 change (Mem.load Mint32 mp ba 120=Some (Vint (bit_int (Bit.toBool
  (@literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)))))) in Flag.
 destruct (eval_ecmult_scale Model raw ax ay az
  (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az) mp br bk ba
  (proj1 ReadyP) (proj1 (proj2 ReadyP)) (proj2 (proj2 ReadyP)) MultSeparate OwnedP Input
  (square_reader_bounds ax) (square_reader_bounds ay) (square_reader_bounds az) X Y Z Flag
  (scale_reader_literal ax) (scale_reader_literal ay) (scale_reader_literal az))
  as (mn & ox & oy & oz & Mult & XO & YO & ZO & BXO & BYO & BZO & Literal & OwnedN & GlobalN & MultFrame).
 assert (ReadyN:scale_startup mn).
 { eapply scale_startup_ecmult_call;[exact ReadyP|exact OwnedP|exact Mult|exact MultFrame]. }
 assert (FLN:Mem.range_perm mn bl 0 16 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FLP|exact MultFrame|].
   intros pos;clear -RL KL AL;cbn [In];intuition congruence. }
 assert (ExtN:eqext m0 bd bw bi mp mn).
 { eapply lframe_implies;[exact MultFrame|].
   intros b pos [Ext V] _;intros [Same|[Same|[Same|[]]]];subst b;
    first [exact (Sep 0%nat ltac:(cbn;lia) (conj Ext V))|
     exact (Sep 2%nat ltac:(cbn;lia) (conj Ext V))|
     exact (Sep 1%nat ltac:(cbn;lia) (conj Ext V))]. }
 assert (FinN:finv m0 bd base bw edge cursor N bi mn false []) by
  (eapply finv_stable;[exact Output|exact FinP|exact ExtN]).
 assert (FRN:Mem.range_perm mn br 0 128 Cur Freeable) by
  (apply OwnedN;clear;cbn [In];tauto).
 assert (FKN:Mem.range_perm mn bk 0 32 Cur Freeable) by
  (apply OwnedN;clear;cbn [In];tauto).
 assert (FAN:Mem.range_perm mn ba 0 128 Cur Freeable) by
  (apply OwnedN;clear;cbn [In];tauto).
 assert (SepWrite:xsep (extA m0 bd bw bi) [(br,0)]).
 { intros [|r] Index;[exact (Sep 0%nat ltac:(cbn;lia))|cbn in Index;lia]. }
 destruct (eval_write_gej_literal_output m0 bd base bw edge cursor N bi rc mn br ox oy oz
  (@literal_off_curve_scale Alg.CoreFunSem (raw,((ax,ay),az)))
  Output Cap FinN BXO BYO BZO XO YO ZO FRN SepWrite Literal)
  as (mw & Write & FinW & FRW & WriteFrame).
 assert (FKW:Mem.range_perm mw bk 0 32 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FKN|exact WriteFrame|].
   intros pos;split;[congruence|exact (Sep 2%nat ltac:(cbn;lia))]. }
 assert (FAW:Mem.range_perm mw ba 0 128 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FAN|exact WriteFrame|].
   intros pos;split;[congruence|exact (Sep 1%nat ltac:(cbn;lia))]. }
 assert (FLW:Mem.range_perm mw bl 0 16 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FLN|exact WriteFrame|].
   intros pos;split;[congruence|exact (Sep 3%nat ltac:(cbn;lia))]. }
 assert (ReadyW:scale_startup mw).
 { eapply scale_startup_readonly;[exact ReadyN|eapply generate_writer_preserved;exact Write]. }
 assert (OwnedW:forall b hi,In (b,hi) (scale_public_storage bl br ba bk) ->
  Mem.range_perm mw b 0 hi Cur Freeable).
 { intros b hi Slot;cbn [scale_public_storage In] in Slot;
   repeat match type of Slot with _\/_=>destruct Slot as [Slot|Slot] end;try contradiction;
    inversion Slot;subst b hi;assumption. }
 destruct (scale_public_free mw bl br ba bk Separate OwnedW) as (mf & Free & FreeFrame & FreeRead).
 assert (FreeExt:eqext m0 bd bw bi mw mf).
 { eapply lframe_implies;[exact FreeFrame|].
   intros b pos [_ V] _;apply Old;exact V. }
 assert (ReadyF:scale_startup mf) by (eapply scale_startup_readonly;[exact ReadyW|exact FreeRead]).
 exists mf;split.
 - eapply eval_funcall_internal with (e:=scale_public_env bl br ba bk) (le1:=le) (le2:=le)
   (m1:=mi) (m2:=mw) (out:=Out_return (Some (Vint Int.one,tint))).
   + exact Entry.
   + rewrite scale_public_body_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=md) (le1:=le);
      [exact Copy|].
     eapply exec_scale_public_rest;[unfold le,scale_public_temps;rewrite !PTree.gso by discriminate;apply PTree.gss|
      exact Scalar|exact Point|exact Mult|exact Write].
   + cbn;split;[discriminate|reflexivity].
   + exact Free.
 - split;[eapply finv_stable;[exact Output|exact FinW|exact FreeExt]|];split;[|exact ReadyF].
   assert (Whole:lframe (fun b _=>Mem.valid_block m0 b /\ ~extA m0 bd bw bi b) m0 mf).
   { eapply lframe_trans;[eapply lframe_implies;[exact PrepFrame|intros b pos [V Outside] _;apply Old;exact V]|].
     eapply lframe_trans.
     - eapply lframe_implies;[exact ReadFrame|].
       intros b pos [V Outside] _;pose proof (Old b V) as Private;
        unfold scale_public_locals in Private;cbn [In] in Private;intuition congruence.
     - eapply lframe_trans.
       + eapply lframe_implies;[exact MultFrame|].
         intros b pos [V Outside] _;pose proof (Old b V) as Private;
          unfold scale_public_locals in Private;cbn [In] in Private|-*;intuition congruence.
       + eapply lframe_trans.
         * eapply lframe_implies;[exact WriteFrame|].
           intros b pos [V Outside] _;split;[intro Same;subst b;apply (Old br V);unfold scale_public_locals;cbn [In];tauto|exact Outside].
         * eapply lframe_implies;[exact FreeFrame|intros b pos [V Outside] _;apply Old;exact V]. }
   eapply lframe_implies;[exact Whole|intros b pos Outside V;split;assumption].
Qed.
