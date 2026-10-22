(** Actual tag, affine payload and padding calls for the decompression result.
    Arbitrary valid output cursors and unrelated output contents are retained. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jet_sx_mem C.jet_sx_exec C.jet_frame_inv C.jet_output_layout C.jet_encoding
 C.jet_secp_frame C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp C.jet_secp_curve_frame
 C.jet_secp_point_write_field C.jet_secp_bit_writer C.jet_secp_affine_write_prefix
 C.jet_secp_affine_skip.
Require C.jets.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge Simplicity.Translate.encode point_field_output.

Lemma decompress_encode_result (bit : bool) (x y : Ty.tySem (Word 8)) :
 @encode (Ty.Sum Ty.Unit (Ty.Prod (Word 8) (Word 8))) (if bit then inr (x,y) else inl tt)=
 [Some bit]++(if bit then encode x++encode y else repeat None 512).
Proof. destruct bit;reflexivity. Qed.

Theorem eval_decompress_result_writes m0 bd base bw edge cursor N bi (rc : Z) m br fx fy (bit : bool) :
 write_frame_at m0 bd base bw edge cursor N -> 513<=N ->
 finv m0 bd base bw edge cursor N bi m false [] ->
 point_field_bounds fx -> point_field_bounds fy ->
 fe_at m br 0 (point_field_limbs fx) -> fe_at m br 40 (point_field_limbs fy) ->
 Mem.range_perm m br 0 88 Cur Freeable -> ~extA m0 bd bw bi br -> exists mt mf,
 Clight2.eval_funcall secp_ge m (Internal C.jets.f_writeBit)
   [Vptr bd (Ptrofs.repr base);Vint (if bit then Int.one else Int.zero)] E0 mt
   (Vint (if bit then Int.one else Int.zero)) /\
 Clight2.eval_funcall secp_ge mt (Internal (if bit then f_write_ge else f_skip_ge))
   (if bit then [Vptr bd (Ptrofs.repr base);Vptr br Ptrofs.zero] else [Vptr bd (Ptrofs.repr base)]) E0 mf Vundef /\
 finv m0 bd base bw edge cursor N bi mf true
   (@encode (Ty.Sum Ty.Unit (Ty.Prod (Word 8) (Word 8)))
     (if bit then inr (point_field_output fx,point_field_output fy) else inl tt)) /\
 Mem.range_perm mf br 0 88 Cur Freeable /\
 lframe (fun b _=>b<>br /\ ~extA m0 bd bw bi b) m mf.
Proof.
 intros Output Cap Inv BoundX BoundY FieldX FieldY Free Outside.
 assert (VBd : extA m0 bd bw bi bd)
   by (apply fext_bd with (dbase:=base) (outedge:=edge) (cursor:=cursor) (N:=N);exact Output).
 assert (VBw : extA m0 bd bw bi bw).
 { split;[right;left;reflexivity|];eapply bw_valid;[exact Output|lia]. }
 assert (RD : br<>bd) by (intro HE;subst br;contradiction).
 assert (RW : br<>bw) by (intro HE;subst br;contradiction).
 destruct (eval_secp_writeBit_from_invariant m0 bd base bw edge cursor N bi m bit Output ltac:(lia) Inv)
   as (mt & Tag & InvT & FrameT & PermsT).
 assert (FieldXT : fe_at mt br 0 (point_field_limbs fx)).
 { eapply curve_keep_field_range;[reflexivity|exact FieldX|exact FrameT|];intros;split;assumption. }
 assert (FieldYT : fe_at mt br 40 (point_field_limbs fy)).
 { eapply curve_keep_field_range;[reflexivity|exact FieldY|exact FrameT|];intros;split;assumption. }
 assert (FreeT : Mem.range_perm mt br 0 88 Cur Freeable).
 { eapply curve_keep_free;[lia|exact Free|exact FrameT|];intros;split;assumption. }
 assert (TagFrame : lframe (fun b _=>b<>br /\ ~extA m0 bd bw bi b) m mt).
 { eapply lframe_implies;[exact FrameT|];intros b pos [NR NE] _;split;intro HE;subst b;contradiction. }
 destruct bit.
 - assert (Sep : xsep (extA m0 bd bw bi) [(br,0)]).
   { intros [|r] HI;[exact Outside|cbn in HI;lia]. }
   destruct (eval_write_ge_from_prefix m0 bd base bw edge cursor N bi rc true [Some true]
     mt br fx fy Output ltac:(cbn;lia) InvT BoundX BoundY FieldXT FieldYT FreeT Sep)
     as (mf & Payload & Final & FreeF & FrameP).
   exists mt,mf;split;[exact Tag|];split;[exact Payload|];split.
   + rewrite (decompress_encode_result true (point_field_output fx) (point_field_output fy));exact Final.
   + split;[exact FreeF|];eapply lframe_trans;eassumption.
 - destruct (eval_secp_skip_ge_from_prefix m0 bd base bw edge cursor N bi true [Some false] mt
     Output ltac:(cbn;lia) InvT) as (mf & Payload & Final & FrameP).
   assert (FreeF : Mem.range_perm mf br 0 88 Cur Freeable).
   { eapply curve_keep_free;[lia|exact FreeT|exact FrameP|];intros;exact RD. }
   exists mt,mf;split;[exact Tag|];split;[exact Payload|];split.
   + rewrite (decompress_encode_result false (point_field_output fx) (point_field_output fy));exact Final.
   + split;[exact FreeF|];eapply lframe_trans;[exact TagFrame|].
     eapply lframe_implies;[exact FrameP|];intros b pos [NR NE] _;intro HE;subst b;contradiction.
Qed.
