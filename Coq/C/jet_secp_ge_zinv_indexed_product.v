(** Reuse the checked arbitrary-slice multiplication for X/Y of an indexed
    affine result, retaining the actual table allocation and point owners. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_ge_zinv_statements C.jet_secp_field_slice_product C.jet_secp_slice_permissions
 C.jet_clight_internal_permissions C.jet_secp_curve_statements C.jet_secp_curve_square
 C.jet_secp_square_columns C.jet_secp_point_mul_storage C.jet_secp_multiply_normalize_bridge
 C.jet_secp_multiply_finish_product C.jet_secp_fe_math C.jet_secp_local_regions.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma eval_ge_zinv_indexed_field e le m br base fid delta ty :
 In (fid,delta) [(_x,0);(_y,40);(_infinity,80)] ->
 0<=base -> base+88<=Ptrofs.max_unsigned -> le!_r=Some (Vptr br (Ptrofs.repr base)) ->
 eval_lvalue secp_ge e le m (ge_zinv_result_field fid ty) br (Ptrofs.repr (base+delta)) Full.
Proof.
 intros Field Base Max R;destruct (curve_affine_layout fid delta Field) as (co & Lookup & Offset).
 assert (Bound:0<=delta<=80) by
   (destruct Field as [Same|[Same|[Same|Same]]];try contradiction;inversion Same;lia).
 replace (Ptrofs.repr (base+delta)) with (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr delta)).
 - eapply eval_Efield_struct with (co:=co) (delta:=delta).
   + eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact R|apply deref_loc_copy;reflexivity].
   + reflexivity.
   + exact Lookup.
   + exact Offset.
 - unfold Ptrofs.add;rewrite !Ptrofs.unsigned_repr by lia;reflexivity.
Qed.

Lemma eval_ge_zinv_indexed_address e le m br base (y:bool) :
 0<=base -> base+88<=Ptrofs.max_unsigned -> le!_r=Some (Vptr br (Ptrofs.repr base)) ->
 eval_expr secp_ge e le m (ge_zinv_result_address (if y then _y else _x))
  (Vptr br (Ptrofs.repr (base+curve_square_offset y))).
Proof.
 intros Base Max R;apply eval_Eaddrof;apply eval_ge_zinv_indexed_field;
  [destruct y;cbn [curve_square_offset In];tauto|exact Base|exact Max|exact R].
Qed.

Theorem eval_ge_zinv_indexed_product y base size a b m br ba bf :
 0<=base -> (8|base) -> base+88<=size -> size<=Ptrofs.max_unsigned ->
 square_input_bounds a -> square_input_bounds b -> br<>ba -> br<>bf -> ba<>bf ->
 Mem.range_perm m br 0 size Cur Freeable ->
 fe_at m ba (curve_square_offset y) (words5 a) -> Mem.range_perm m ba 0 128 Cur Freeable ->
 fe_at m bf 0 (words5 b) -> Mem.range_perm m bf 0 40 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
  [Vptr br (Ptrofs.repr (base+curve_square_offset y));
   Vptr ba (Ptrofs.repr (curve_square_offset y));Vptr bf Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br (base+curve_square_offset y) (words5 (point_mul_words a b)) /\
 fe_at mf ba (curve_square_offset y) (words5 a) /\ fe_at mf bf 0 (words5 b) /\
 Mem.range_perm mf br 0 size Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
 Mem.range_perm mf bf 0 40 Cur Freeable /\
 radix_value (point_mul_words a b) mod feP=(radix_value a*radix_value b) mod feP /\
 square_input_bounds (point_mul_words a b) /\ keeps_permissions m mf /\
 lframe (fun bx pos=>bx<>bf /\
  (bx<>br \/ pos<base+curve_square_offset y \/ base+curve_square_offset y+40<=pos) /\
  (bx<>ba \/ pos<curve_square_offset y \/ curve_square_offset y+40<=pos)) m mf.
Proof.
 intros Base Align Fit Max BA BB RA RF AF FreeR A FreeA B FreeF.
 assert (Offset:0<=curve_square_offset y<=40) by (destruct y;cbn [curve_square_offset];lia).
 assert (Aligned:(8|base+curve_square_offset y)).
 { destruct Align as [k Eq];destruct y;cbn [curve_square_offset];[exists (k+5)|exists k];lia. }
 destruct (eval_field_slice_product a b m br (base+curve_square_offset y) ba (curve_square_offset y) bf 0
   BA BB ltac:(left;exact RA) ltac:(left;exact RF) ltac:(left;exact AF)
   ltac:(lia) Aligned ltac:(lia)
   ltac:(intros pos Range;apply (freeable_range_writable m br 0 size FreeR);lia) A B)
  as (mf & Call & Out & AP & BF & Value & Bounds & Keep & Frame).
 exists mf;split;[exact Call|];split;[exact Out|];split;[exact AP|];split;[exact BF|];split.
 - exact (keeps_range_permissions m mf br 0 size Cur Freeable Keep FreeR).
 - split;[exact (keeps_range_permissions m mf ba 0 128 Cur Freeable Keep FreeA)|];
   split;[exact (keeps_range_permissions m mf bf 0 40 Cur Freeable Keep FreeF)|];
   split;[exact Value|];split;[exact Bounds|];split;[exact Keep|].
   eapply lframe_implies;[exact Frame|].
   intros bx pos (NF & NR & NA) Valid;repeat split;try assumption;left;exact NF.
Qed.
