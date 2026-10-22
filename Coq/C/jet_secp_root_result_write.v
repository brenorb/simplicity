(** Actual tag and conditional field/padding writes, composing their general
    frame contracts. This does not yet execute the public jet wrapper. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jet_sx_mem C.jet_frame_inv C.jet_output_layout C.jet_encoding C.jet_secp_frame
 C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp C.jet_secp_curve_frame
 C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns C.jet_secp_rescale_literal
 C.jet_secp_bit_writer C.jet_secp_owned_field_write C.jet_secp_field_skip.
Require C.jets.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge Simplicity.Translate.encode rescale_field_output.

Lemma root_encode_result (bit : bool) (y : Ty.tySem (Word 8)) :
 @encode (Ty.Sum Ty.Unit (Word 8)) (if bit then inr y else inl tt)=
 [Some bit]++(if bit then encode y else repeat None 256).
Proof. destruct bit;reflexivity. Qed.

Theorem eval_root_result_writes m0 bd base bw edge cursor N bi m br w (bit : bool) :
 write_frame_at m0 bd base bw edge cursor N -> 257<=N ->
 finv m0 bd base bw edge cursor N bi m false [] ->
 square_input_bounds w -> fe_at m br 0 (words5 w) -> Mem.range_perm m br 0 40 Cur Freeable ->
 ~extA m0 bd bw bi br -> exists mt mf,
 Clight2.eval_funcall secp_ge m (Internal C.jets.f_writeBit)
   [Vptr bd (Ptrofs.repr base);Vint (if bit then Int.one else Int.zero)] E0 mt
   (Vint (if bit then Int.one else Int.zero)) /\
 Clight2.eval_funcall secp_ge mt (Internal (if bit then f_write_fe else f_skip_fe))
   (if bit then [Vptr bd (Ptrofs.repr base);Vptr br Ptrofs.zero] else [Vptr bd (Ptrofs.repr base)]) E0 mf Vundef /\
 finv m0 bd base bw edge cursor N bi mf true
   (@encode (Ty.Sum Ty.Unit (Word 8)) (if bit then inr (rescale_field_output w) else inl tt)) /\
 Mem.range_perm mf br 0 40 Cur Freeable /\
 lframe (fun b _=>b<>br /\ ~extA m0 bd bw bi b) m mf.
Proof.
 intros Output Cap Inv Bound Field Free Outside.
 assert (VBd : extA m0 bd bw bi bd) by (apply fext_bd with (dbase:=base) (outedge:=edge) (cursor:=cursor) (N:=N);exact Output).
 assert (VBw : extA m0 bd bw bi bw).
 { split;[right;left;reflexivity|];eapply bw_valid;[exact Output|lia]. }
 assert (RD : br<>bd) by (intro HE;subst br;contradiction).
 assert (RW : br<>bw) by (intro HE;subst br;contradiction).
 destruct (eval_secp_writeBit_from_invariant m0 bd base bw edge cursor N bi m bit Output ltac:(lia) Inv)
   as (mt & Tag & InvT & FrameT & PermsT).
 assert (FieldT : fe_at mt br 0 (words5 w)).
 { eapply curve_keep_field_range;[reflexivity|exact Field|exact FrameT|];intros;split;assumption. }
 assert (FreeT : Mem.range_perm mt br 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact Free|exact FrameT|];intros;split;assumption. }
 assert (TagFrame : lframe (fun b _=>b<>br /\ ~extA m0 bd bw bi b) m mt).
 { eapply lframe_implies;[exact FrameT|];intros b pos [NR NE] _;split;intro HE;subst b;contradiction. }
 destruct bit.
 - destruct (eval_owned_field_write m0 bd base bw edge cursor N bi true [Some true] mt br w
     Output ltac:(cbn;lia) Bound FieldT FreeT Outside InvT) as (mf & Payload & Final & FreeF & FrameP).
   exists mt,mf;split;[exact Tag|];split;[exact Payload|];split.
   + rewrite (root_encode_result true (rescale_field_output w));exact Final.
   + split;[exact FreeF|];eapply lframe_trans;eassumption.
 - destruct (eval_secp_skip_fe_from_prefix m0 bd base bw edge cursor N bi true [Some false] mt
     Output ltac:(cbn;lia) InvT) as (mf & Payload & Final & FrameP).
   assert (FreeF : Mem.range_perm mf br 0 40 Cur Freeable).
   { eapply curve_keep_free;[lia|exact FreeT|exact FrameP|];intros;exact RD. }
   exists mt,mf;split;[exact Tag|];split;[exact Payload|];split.
   + rewrite (root_encode_result false (rescale_field_output w));exact Final.
   + split;[exact FreeF|];eapply lframe_trans;[exact TagFrame|].
     eapply lframe_implies;[exact FrameP|];intros b pos [NR NE] _;intro HE;subst b;contradiction.
Qed.
