(** Reusable actual scalar-plus-affine reader sequence for linear_verify_1.
    The output capacity may be zero because neither reader writes output. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_state C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_secp_curve_frame C.jet_secp_fe_nv C.jet_secp_frame C.jet_secp_public_body C.jet_secp_wrapper_run
 C.jet_secp_read_ge_fields C.jet_secp_scalar_add_reader_support C.jet_secp_scalar_public_rest
 C.jet_secp_scalar_get_b32_storage C.jet_toZ C.jet_secp_scalar_reader_set C.jet_secp_scalar_get_b32_numeric C.jet_secp_canonical_scalar
 C.jet_frame_layout C.jet_frame_inv C.jet_input_layout C.jet_output_layout C.jet_encoding
 C.jet_secp_point_three_reads C.jet_secp_local_regions.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge canonical_scalar_normalize.

Theorem eval_linear_verify_read_pair m0 bd base bw edge cursor N bi inedge rc
 (raw ax ay:Ty.tySem (Word 8)) m bk ba bl :
 write_frame_at m0 bd base bw edge cursor N ->
 frame_input_cells_at m0 bi inedge rc (map Some (frame_input_word_bits raw)) ->
 frame_input_cells_at m0 bi inedge (rc+256) (map Some (frame_input_word_bits ax)) ->
 frame_input_cells_at m0 bi inedge (rc+512) (map Some (frame_input_word_bits ay)) ->
 0<=rc -> rc+768<=Int64.max_unsigned ->
 Mem.range_perm m bk 0 32 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
 Mem.range_perm m bl 0 16 Cur Freeable -> frame_fields_at m bl 0 bi inedge rc ->
 bk<>bl -> ba<>bl -> bk<>ba -> xsep (extA m0 bd bw bi) [(bk,0);(ba,0);(bl,0)] ->
 finv m0 bd base bw edge cursor N bi m false [] ->
 exists mr mf,
 Clight2.eval_funcall secp_ge m (Internal f_read_scalar)
  [Vptr bk Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef /\
 Clight2.eval_funcall secp_ge mr (Internal f_read_ge)
  [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mf Vundef /\
 scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) /\
 fe_at mf ba 0 (point_canonical_limbs ax) /\
 fe_at mf ba 40 (point_canonical_limbs ay) /\
 Mem.load Mint32 mf ba 80=Some (Vint Int.zero) /\
 Mem.range_perm mf bk 0 32 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 Mem.range_perm mf bl 0 16 Cur Freeable /\ frame_fields_at mf bl 0 bi inedge (rc+768) /\
 finv m0 bd base bw edge cursor N bi mf false [] /\
 lframe (fun b _=>b<>bk /\ b<>ba /\ b<>bl /\ ~extA m0 bd bw bi b) m mf.
Proof.
 intros Output Raw AX AY RC Max FK FA FL Source KL AL KA Sep Fin.
 assert (Cap:0<=N) by (destruct Output as (_ & _ & _ & Bound & _);lia).
 assert (SepK:xsep (extA m0 bd bw bi) [(bk,0);(bl,0)]).
 { intros [|[|r]] Index;[exact (Sep 0%nat ltac:(cbn;lia))|
   exact (Sep 2%nat ltac:(cbn;lia))|cbn in Index;lia]. }
 assert (SepA:xsep (extA m0 bd bw bi) [(ba,0);(bl,0)]).
 { intros [|[|r]] Index;[exact (Sep 1%nat ltac:(cbn;lia))|
   exact (Sep 2%nat ltac:(cbn;lia))|cbn in Index;lia]. }
 assert (Inv:invA m0 bd base bw edge cursor N bi rc false [] 0
  (read_fe_rho (frame_input_word_bits raw) rc) [] m).
 { split;[reflexivity|];split;[exact Fin|];split;[exact Cap|cbn;lia]. }
 destruct (eval_read_scalar_canonical_with_source m0 bd base bw edge cursor N 0 bi inedge rc raw
  m bk bl Output Raw RC ltac:(lia) FK FL Source KL SepK Inv)
  as (mr & Scalar & Input & SourceR & FKR & FLR & InvR & FrameK).
 assert (VKA:Mem.valid_block m ba) by (eapply Mem.perm_valid_block;apply (FA 0);clear;lia).
 assert (SameA:lframe (fun b _=>b=ba) m mr).
 { eapply lframe_implies;[exact FrameK|].
   intros b pos Same Valid;subst b;unfold frame;split;[exact Valid|];split.
   - apply scalar_locals_not_foot;congruence.
   - exact (Sep 1%nat ltac:(cbn;lia)). }
 assert (FAR:Mem.range_perm mr ba 0 88 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FA|exact SameA|intros;reflexivity]. }
 assert (InvA:invA m0 bd base bw edge cursor N bi (rc+256) false [] 0
  (read_fe_rho (frame_input_word_bits ax) (rc+256)) [] mr).
 { exact (scalar_reader_final_inv_to_next_initial m0 bd base bw edge cursor N bi
   inedge rc (rc+256) 0 raw ax mr InvR). }
 assert (InputY:frame_input_cells_at m0 bi inedge (rc+256+256) (map Some (frame_input_word_bits ay))).
 { replace (rc+256+256) with (rc+512) by lia;exact AY. }
 destruct (eval_read_ge_canonical_fields m0 bd base bw edge cursor N 0 bi inedge (rc+256)
  ax ay mr ba bl Output AX InputY ltac:(lia) ltac:(lia) FAR FLR SourceR AL SepA InvA)
  as (mf & Point & X & Y & Flag & SourceF & FAF & FLF & InvF & FrameA).
 assert (SameK:lframe (fun b _=>b=bk) mr mf).
 { eapply lframe_implies;[exact FrameA|].
   intros b pos Same Valid;subst b;unfold secp_locals_outside;repeat split;try congruence.
   exact (Sep 0%nat ltac:(cbn;lia)). }
 assert (InputF:scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw))))).
 { eapply scalar_at_lframe;[exact Input|exact SameK|intros;reflexivity]. }
 assert (FKF:Mem.range_perm mf bk 0 32 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FKR|exact SameK|intros;reflexivity]. }
 replace (rc+256+512) with (rc+768) in SourceF by lia.
 exists mr,mf;split;[exact Scalar|];split;[exact Point|];split;[exact InputF|];
 split;[exact X|];split;[exact Y|];split;[exact Flag|];
 split;[exact FKF|];split;[exact FAF|];split;[exact FLF|];split;[exact SourceF|];split.
 - exact (proj1 (proj2 InvF)).
 - eapply lframe_trans.
   + eapply lframe_implies;[exact FrameK|].
     intros b pos (K & A & L & Other) V;unfold frame;split;[exact V|];split;
      [apply scalar_locals_not_foot;assumption|exact Other].
   + eapply lframe_implies;[exact FrameA|].
     intros b pos (K & A & L & Other) V;unfold secp_locals_outside;repeat split;assumption.
Qed.
