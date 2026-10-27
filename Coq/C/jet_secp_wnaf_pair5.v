(** The two original window-5 calls fit in one Strauss point-state object.
    The second call retains the first array, both scalars and the two fields
    following the buffers; no digit output or memory preservation is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_memset_model
 C.jet_secp_wnaf_slice_frame C.jet_secp_wnaf_function5 C.jet_secp_wnaf_loop
 C.jet_secp_wnaf5_input C.jet_secp_wnaf5_literal C.jet_secp_wnaf5_signed_array
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric
 C.jet_secp_scalar_add_reader_support C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma wnaf_array_slice_lframe m mf b base len w sign bit last digits P :
 wnaf_array_state m b base len w sign bit last digits ->
 lframe P m mf -> (forall pos,base<=pos<base+4*len -> P b pos) ->
 wnaf_array_state mf b base len w sign bit last digits.
Proof.
 intros [Access Load Suffix Digits Last] Frame Cover;constructor;try assumption.
 - intros i Range;destruct (Access i Range) as [Cells Align];split;[|exact Align].
   intros pos Cell;apply (proj1 (proj2 Frame)).
   + eapply Mem.perm_valid_block;apply Cells;exact Cell.
   + apply Cover;change (base+4*i<=pos<base+4*i+4) in Cell;lia.
   + apply Cells;exact Cell.
 - intros i Range;rewrite (proj1 Frame).
   + apply Load;exact Range.
   + eapply Mem.perm_valid_block;apply (proj1 (Access i Range) (base+4*i)).
     change (base+4*i<=base+4*i<base+4*i+4);lia.
   + intros pos Cell;apply Cover;change (base+4*i<=pos<base+4*i+4) in Cell;lia.
Qed.

Theorem eval_wnaf_literal5_pair (Model:memset_model) sb1 sb2
 (word1 word2:Ty.tySem (Word 7)) m ba1 abase1 ba2 abase2 b :
 scalar_at m ba1 abase1 (map Int64.repr (scalar_limbs_of (wnaf5_input_scalar sb1 word1))) ->
 scalar_at m ba2 abase2 (map Int64.repr (scalar_limbs_of (wnaf5_input_scalar sb2 word2))) ->
 ba1<>b -> ba2<>b -> Mem.range_perm m b 0 1040 Cur Freeable ->
 exists m1 mf last1 last2 digits1 digits2,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_wnaf)
  [Vptr b Ptrofs.zero;Vint (Int.repr 129);Vptr ba1 (Ptrofs.repr abase1);Vint (Int.repr 5)]
  E0 m1 (Vint (Int.repr (last1+1))) /\
 Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_ecmult_wnaf)
  [Vptr b (Ptrofs.repr 516);Vint (Int.repr 129);Vptr ba2 (Ptrofs.repr abase2);Vint (Int.repr 5)]
  E0 mf (Vint (Int.repr (last2+1))) /\
 wnaf_array_state mf b 0 129 5 (wnaf5_input_sign sb1) 129 last1 digits1 /\
 wnaf_array_state mf b 516 129 5 (wnaf5_input_sign sb2) 129 last2 digits2 /\
 0<=last1+1<=129 /\ 0<=last2+1<=129 /\
 scalar_at mf ba1 abase1 (map Int64.repr (scalar_limbs_of (wnaf5_input_scalar sb1 word1))) /\
 scalar_at mf ba2 abase2 (map Int64.repr (scalar_limbs_of (wnaf5_input_scalar sb2 word2))) /\
 Mem.range_perm mf b 0 1040 Cur Freeable /\ lframe (wnaf_slice_outside b 0 258) m mf /\
 keeps_permissions m mf /\ readonly_preserved m mf /\
 map wnaf5_literal_value (literal_wnaf5_digits (sb1,word1))=
  rev (map (fun i=>wnaf5_input_sign sb1*digits1 (Z.of_nat i)) (seq 0 129)) /\
 map wnaf5_literal_value (literal_wnaf5_digits (sb2,word2))=
  rev (map (fun i=>wnaf5_input_sign sb2*digits2 (Z.of_nat i)) (seq 0 129)).
Proof.
 intros Input1 Input2 Separate1 Separate2 Owned.
 assert (Owned1:Mem.range_perm m b 0 (0+516) Cur Freeable).
 { intros pos Range;apply Owned;lia. }
 destruct (eval_wnaf_literal5_slice Model sb1 word1 m ba1 abase1 b 0 Input1 Separate1
  ltac:(lia) (Z.divide_0_r 4) ltac:(change (516<=18446744073709551615);lia) Owned1)
  as (m1 & last1 & digits1 & Call1 & Array1 & Bound1 & Free1 & Frame1 & Source1 & Keep1 & Readonly1 & Literal1).
 assert (Input2I:scalar_at m1 ba2 abase2
  (map Int64.repr (scalar_limbs_of (wnaf5_input_scalar sb2 word2)))).
 { eapply scalar_at_lframe;[exact Input2|exact Frame1|intros;left;exact Separate2]. }
 assert (Owned2:Mem.range_perm m1 b 516 (516+516) Cur Freeable).
 { intros pos Range;apply Keep1,Owned;lia. }
 destruct (eval_wnaf_literal5_slice Model sb2 word2 m1 ba2 abase2 b 516 Input2I Separate2
  ltac:(lia) ltac:(exists 129;reflexivity)
  ltac:(change (1032<=18446744073709551615);lia) Owned2)
  as (mf & last2 & digits2 & Call2 & Array2 & Bound2 & Free2 & Frame2 & Source2 & Keep2 & Readonly2 & Literal2).
 assert (Array1F:wnaf_array_state mf b 0 129 5 (wnaf5_input_sign sb1) 129 last1 digits1).
 { eapply wnaf_array_slice_lframe;[exact Array1|exact Frame2|].
   intros pos Range;right;left;lia. }
 assert (Frame:lframe (wnaf_slice_outside b 0 258) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact Frame1|].
     unfold wnaf_slice_outside;intros old pos Outside _;intuition lia.
   - eapply lframe_implies;[exact Frame2|].
     unfold wnaf_slice_outside;intros old pos Outside _;intuition lia. }
 assert (Source1F:scalar_at mf ba1 abase1
  (map Int64.repr (scalar_limbs_of (wnaf5_input_scalar sb1 word1)))).
 { eapply scalar_at_lframe;[exact Input1|exact Frame|intros;left;exact Separate1]. }
 assert (Keep:keeps_permissions m mf) by (eapply keeps_permissions_trans;eassumption).
 assert (OwnedF:Mem.range_perm mf b 0 1040 Cur Freeable).
 { intros pos Range;apply Keep,Owned;exact Range. }
 exists m1,mf,last1,last2,digits1,digits2;
 split;[exact Call1|];split;[exact Call2|];split;[exact Array1F|];split;[exact Array2|];
 split;[exact Bound1|];split;[exact Bound2|];split;[exact Source1F|];split;[exact Source2|];
 split;[exact OwnedF|];split;[exact Frame|];split;[exact Keep|];split.
 - eapply preserved_trans;eassumption.
 - split;assumption.
Qed.
