(** Exact original window-5 preprocessing statements for the one-point Strauss caller. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events Errors.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_sx_eval
 C.jet_secp_curve_statements C.jet_secp_ecmult_state C.jet_secp_generator_preprocess
 C.jet_secp_generator_globalz_call C.jet_secp_wnaf_function5 C.jet_secp_wnaf_slice_frame
 C.jet_secp_wnaf_loop C.jet_secp_wnaf5_input C.jet_secp_wnaf5_literal C.jet_secp_wnaf5_signed_array
 C.jet_memset_model C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric
 C.jet_secp_wnaf_pair5 C.jet_secp_scalar_add_reader_support
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Local Opaque secp_ge.
Set Default Timeout 10.
Require Import C.jet_secp_strauss_wnaf_calls C.jet_elements_taptweak_pure C.jet_transport.
Require Import C.jet_elements_taptweak_wnaf5 C.jet_elements_taptweak_wnaf_call.
Lemma elements_taptweak_strauss_ps_checked:
 expr_okb secp_ge elements_taptweak_ge strauss_ps_pointer=Datatypes.true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_strauss_point_field_checked tmp field delta ty:
 In(field,delta)[(_wnaf_na_1,0);(_wnaf_na_lam,516);(_bits_na_1,1032);(_bits_na_lam,1036)] ->
 expr_okb secp_ge elements_taptweak_ge(Efield(strauss_point_from_temp tmp)field ty)=Datatypes.true.
Proof.
 intros[Same|[Same|[Same|[Same|[]]]]];injection Same as <- <-;vm_compute;reflexivity.
Qed.
Local Opaque elements_taptweak_ge.
Lemma eval_elements_taptweak_strauss_ps_pointer e le m bs bp:
 le!_state=Some(Vptr bs Ptrofs.zero) ->Mem.load Mptr m bs 16=Some(Vptr bp Ptrofs.zero) ->
 eval_expr elements_taptweak_ge e le m strauss_ps_pointer(Vptr bp Ptrofs.zero).
Proof.
 intros State Load;apply(proj1(eval_expr_transport secp_ge elements_taptweak_ge e le m));
 [apply(eval_strauss_ps_pointer e le m bs bp State Load)|exact elements_taptweak_strauss_ps_checked].
Qed.
Lemma eval_elements_taptweak_strauss_point_field e le m bp tmp field delta ty:
 In(field,delta)[(_wnaf_na_1,0);(_wnaf_na_lam,516);(_bits_na_1,1032);(_bits_na_lam,1036)] ->
 le!tmp=Some(Vptr bp Ptrofs.zero) ->le!_no=Some(Vlong Int64.zero) ->
 eval_lvalue elements_taptweak_ge e le m(Efield(strauss_point_from_temp tmp)field ty)bp(Ptrofs.repr delta)Full.
Proof.
 intros Field Pointer No;apply(proj2(eval_expr_transport secp_ge elements_taptweak_ge e le m));
 [apply(eval_strauss_point_field e le m bp tmp field delta ty Field Pointer No)|
 apply(elements_taptweak_strauss_point_field_checked tmp field delta ty);exact Field].
Qed.
Lemma exec_elements_taptweak_strauss_wnaf_half_from_call (high:bool) e le m mr mf bs bp ba bits :
 e!(if high then _na_lam else _na_1)=Some (ba,Tstruct __5826 noattr) ->
 e!_secp256k1_ecmult_wnaf=None -> le!_state=Some (Vptr bs Ptrofs.zero) ->
 le!_no=Some (Vlong Int64.zero) ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mptr mr bs 16=Some (Vptr bp Ptrofs.zero) ->
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_ecmult_wnaf)
  [Vptr bp (Ptrofs.repr (strauss_wnaf_base high));Vint (Int.repr 129);
   Vptr ba Ptrofs.zero;Vint (Int.repr 5)] E0 mr (Vint (Int.repr bits)) ->
 Mem.store Mint32 mr bp (strauss_wnaf_count_offset high) (Vint (Int.repr bits))=Some mf ->
 Clight2.exec_stmt elements_taptweak_ge e le m (strauss_wnaf_half high) E0
  (strauss_wnaf_half_temps high le bp bits) mf Out_normal.
Proof.
 intros Local Symbol State No Pointer PointerR Call Store.
 pose (l0:=PTree.set (if high then _t'45 else _t'47) (Vptr bp Ptrofs.zero) le).
 pose (l1:=PTree.set (if high then _t'5 else _t'4) (Vint (Int.repr bits)) l0).
 pose (l2:=strauss_wnaf_half_temps high le bp bits).
 assert (State1:l1!_state=Some (Vptr bs Ptrofs.zero)).
 { unfold l1,l0;destruct high;rewrite !PTree.gso by discriminate;exact State. }
 assert (No0:l0!_no=Some (Vlong Int64.zero)).
 { unfold l0;destruct high;rewrite PTree.gso by discriminate;exact No. }
 assert (No2:l2!_no=Some (Vlong Int64.zero)).
 { unfold l2,strauss_wnaf_half_temps;destruct high;rewrite !PTree.gso by discriminate;exact No. }
 assert (CountRange:0<=strauss_wnaf_count_offset high<=1036).
 { destruct high;cbn [strauss_wnaf_count_offset];lia. }
 unfold strauss_wnaf_half;cbv zeta.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=l1).
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=l0).
   + apply exec_Sset;apply eval_elements_taptweak_strauss_ps_pointer with (bs:=bs);assumption.
   + eapply exec_elements_taptweak_wnaf_call with
     (vargs:=[Vptr bp (Ptrofs.repr (strauss_wnaf_base high));Vint (Int.repr 129);
      Vptr ba Ptrofs.zero;Vint (Int.repr 5)]) (v:=Vint (Int.repr bits)).
     * exact Symbol.
     * eapply eval_Econs with (v1:=Vptr bp (Ptrofs.repr (strauss_wnaf_base high))).
       -- eapply eval_Elvalue;[apply eval_elements_taptweak_strauss_point_field|apply deref_loc_reference;reflexivity].
          ++ destruct high;cbn [strauss_wnaf_base In];tauto.
          ++ unfold l0;apply PTree.gss.
          ++ exact No0.
       -- reflexivity.
       -- eapply eval_Econs;[constructor|reflexivity|].
          eapply eval_Econs with (v1:=Vptr ba Ptrofs.zero).
          ++ apply eval_Eaddrof;apply eval_Evar_local;exact Local.
          ++ reflexivity.
          ++ eapply eval_Econs;[constructor|reflexivity|constructor].
     * exact Call.
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=l2).
   + apply exec_Sset;apply eval_elements_taptweak_strauss_ps_pointer with (bs:=bs);assumption.
   + eapply exec_Sassign with (loc:=bp) (ofs:=Ptrofs.repr (strauss_wnaf_count_offset high))
      (bf:=Full) (v2:=Vint (Int.repr bits)) (v:=Vint (Int.repr bits)).
     * apply eval_elements_taptweak_strauss_point_field.
       -- destruct high;cbn [strauss_wnaf_count_offset In];tauto.
       -- unfold l2,strauss_wnaf_half_temps;apply PTree.gss.
       -- exact No2.
     * apply eval_Etempvar;unfold l2,strauss_wnaf_half_temps.
       destruct high;rewrite PTree.gso by discriminate;apply PTree.gss.
     * reflexivity.
     * eapply assign_loc_value with (chunk:=Mint32);[reflexivity|].
       change (Mem.store Mint32 mr bp (Ptrofs.unsigned (Ptrofs.repr (strauss_wnaf_count_offset high)))
        (Vint (Int.repr bits))=Some mf).
       rewrite Ptrofs.unsigned_repr;[exact Store|change Ptrofs.max_unsigned with 18446744073709551615;lia].
Qed.

Theorem exec_elements_taptweak_strauss_wnaf_half (Model:memset_model) (high:bool) e le m bs bp ba sb
 (word:Ty.tySem (Word 7)) :
 e!(if high then _na_lam else _na_1)=Some (ba,Tstruct __5826 noattr) ->
 e!_secp256k1_ecmult_wnaf=None -> le!_state=Some (Vptr bs Ptrofs.zero) ->
 le!_no=Some (Vlong Int64.zero) -> Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 bs<>bp -> ba<>bp -> Mem.range_perm m bp 0 1040 Cur Freeable ->
 scalar_at m ba 0 (map Int64.repr (scalar_limbs_of (wnaf5_input_scalar sb word))) ->
 exists mf last digits,
 Clight2.exec_stmt elements_taptweak_ge e le m (strauss_wnaf_half high) E0
  (strauss_wnaf_half_temps high le bp (last+1)) mf Out_normal /\
 wnaf_array_state mf bp (strauss_wnaf_base high) 129 5 (wnaf5_input_sign sb) 129 last digits /\
 0<=last+1<=129 /\
 Mem.load Mint32 mf bp (strauss_wnaf_count_offset high)=Some (Vint (Int.repr (last+1))) /\
 Mem.load Mptr mf bs 16=Some (Vptr bp Ptrofs.zero) /\
 scalar_at mf ba 0 (map Int64.repr (scalar_limbs_of (wnaf5_input_scalar sb word))) /\
 Mem.range_perm mf bp 0 1040 Cur Freeable /\
 lframe (strauss_wnaf_half_outside high bp) m mf /\
 keeps_permissions m mf /\ readonly_preserved m mf /\
 map wnaf5_literal_value (literal_wnaf5_digits (sb,word))=
  rev (map (fun i=>wnaf5_input_sign sb*digits (Z.of_nat i)) (seq 0 129)).
Proof.
 intros Local Symbol State No Pointer StateSeparate ScalarSeparate Owned Input.
 destruct (strauss_wnaf_half_geometry high) as (Base & End & Fits & Align & CountAlign).
 assert (Max:strauss_wnaf_base high+516<=Ptrofs.max_unsigned).
 { change Ptrofs.max_unsigned with 18446744073709551615;lia. }
 assert (Part:Mem.range_perm m bp (strauss_wnaf_base high) (strauss_wnaf_base high+516) Cur Freeable).
 { intros pos Range;apply Owned;lia. }
 destruct (eval_elements_taptweak_wnaf5_slice Model sb word m ba 0 bp (strauss_wnaf_base high)
  Input ScalarSeparate Base Align Max Part)
  as (mr & last & digits & Call & Array & Bound & PartR & FrameR & SourceR & KeepR & ReadonlyR & Literal).
 assert (StateValid:Mem.valid_block m bs).
 { eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
   [eapply Mem.load_valid_access;exact Pointer|apply perm_any_N]. }
 assert (PointerR:Mem.load Mptr mr bs 16=Some (Vptr bp Ptrofs.zero)).
 { rewrite (proj1 FrameR Mptr bs 16 StateValid ltac:(intros;left;exact StateSeparate));exact Pointer. }
 assert (OwnedR:Mem.range_perm mr bp 0 1040 Cur Freeable).
 { intros pos Range;apply KeepR,Owned;exact Range. }
 assert (Access:Mem.valid_access mr Mint32 bp (strauss_wnaf_count_offset high) Writable).
 { split.
   - intros pos Range;change (strauss_wnaf_count_offset high<=pos<strauss_wnaf_count_offset high+4) in Range.
     eapply Mem.perm_implies;[apply OwnedR;lia|constructor].
   - exact CountAlign. }
 destruct (Mem.valid_access_store mr Mint32 bp (strauss_wnaf_count_offset high)
  (Vint (Int.repr (last+1))) Access) as (mf & Store).
 assert (StoreFrame:lframe (wnaf_slice_outside bp (strauss_wnaf_count_offset high) 1) mr mf).
 { eapply wnaf_slice_store_frame with (bit:=0);[lia|].
   rewrite Z.mul_0_r,Z.add_0_r;exact Store. }
 assert (Frame:lframe (strauss_wnaf_half_outside high bp) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FrameR|intros old pos [ArrayPart CountPart] _;exact ArrayPart].
   - eapply lframe_implies;[exact StoreFrame|intros old pos [ArrayPart CountPart] _;exact CountPart]. }
 assert (ArrayF:wnaf_array_state mf bp (strauss_wnaf_base high) 129 5 (wnaf5_input_sign sb) 129 last digits).
 { eapply wnaf_array_slice_lframe;[exact Array|exact StoreFrame|].
   intros pos Range;right;left;lia. }
 assert (PointerF:Mem.load Mptr mf bs 16=Some (Vptr bp Ptrofs.zero)).
 { rewrite (proj1 Frame Mptr bs 16 StateValid ltac:(intros;split;left;exact StateSeparate));exact Pointer. }
 assert (SourceF:scalar_at mf ba 0 (map Int64.repr (scalar_limbs_of (wnaf5_input_scalar sb word)))).
 { eapply scalar_at_lframe;[exact SourceR|exact StoreFrame|intros;left;exact ScalarSeparate]. }
 assert (Keep:keeps_permissions m mf).
 { intros old pos k p Perm;eapply Mem.perm_store_1;[exact Store|apply KeepR;exact Perm]. }
 assert (OwnedF:Mem.range_perm mf bp 0 1040 Cur Freeable).
 { intros pos Range;apply Keep,Owned;exact Range. }
 exists mf,last,digits;split.
 - eapply exec_elements_taptweak_strauss_wnaf_half_from_call;
   [exact Local|exact Symbol|exact State|exact No|exact Pointer|exact PointerR|exact Call|exact Store].
 - split;[exact ArrayF|];split;[exact Bound|];split.
   + exact (Mem.load_store_same _ _ _ _ _ _ Store).
   + split;[exact PointerF|];split;[exact SourceF|];split;[exact OwnedF|];split;[exact Frame|];split;[exact Keep|];split.
     * eapply preserved_trans;[exact ReadonlyR|eapply store_preserved;exact Store].
     * exact Literal.
Qed.

Theorem exec_elements_taptweak_strauss_wnaf_prepare (Model:memset_model) e le m bs bp ba1 ba2 sb1 sb2
 (word1 word2:Ty.tySem (Word 7)) :
 e!_na_1=Some (ba1,Tstruct __5826 noattr) -> e!_na_lam=Some (ba2,Tstruct __5826 noattr) ->
 e!_secp256k1_ecmult_wnaf=None -> le!_state=Some (Vptr bs Ptrofs.zero) ->
 le!_no=Some (Vlong Int64.zero) -> Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 bs<>bp -> ba1<>bp -> ba2<>bp -> Mem.range_perm m bp 0 1040 Cur Freeable ->
 scalar_at m ba1 0 (map Int64.repr (scalar_limbs_of (wnaf5_input_scalar sb1 word1))) ->
 scalar_at m ba2 0 (map Int64.repr (scalar_limbs_of (wnaf5_input_scalar sb2 word2))) ->
 exists mf last1 last2 digits1 digits2,
 Clight2.exec_stmt elements_taptweak_ge e le m strauss_wnaf_prepare E0
  (strauss_wnaf_prepare_temps le bp (last1+1) (last2+1)) mf Out_normal /\
 wnaf_array_state mf bp 0 129 5 (wnaf5_input_sign sb1) 129 last1 digits1 /\
 wnaf_array_state mf bp 516 129 5 (wnaf5_input_sign sb2) 129 last2 digits2 /\
 0<=last1+1<=129 /\ 0<=last2+1<=129 /\
 Mem.load Mint32 mf bp 1032=Some (Vint (Int.repr (last1+1))) /\
 Mem.load Mint32 mf bp 1036=Some (Vint (Int.repr (last2+1))) /\
 Mem.load Mptr mf bs 16=Some (Vptr bp Ptrofs.zero) /\
 scalar_at mf ba1 0 (map Int64.repr (scalar_limbs_of (wnaf5_input_scalar sb1 word1))) /\
 scalar_at mf ba2 0 (map Int64.repr (scalar_limbs_of (wnaf5_input_scalar sb2 word2))) /\
 Mem.range_perm mf bp 0 1040 Cur Freeable /\ lframe (wnaf_slice_outside bp 0 260) m mf /\
 keeps_permissions m mf /\ readonly_preserved m mf /\
 map wnaf5_literal_value (literal_wnaf5_digits (sb1,word1))=
  rev (map (fun i=>wnaf5_input_sign sb1*digits1 (Z.of_nat i)) (seq 0 129)) /\
 map wnaf5_literal_value (literal_wnaf5_digits (sb2,word2))=
  rev (map (fun i=>wnaf5_input_sign sb2*digits2 (Z.of_nat i)) (seq 0 129)).
Proof.
 intros LowLocal HighLocal Symbol State No Pointer StateSeparate LowSeparate HighSeparate Owned Input1 Input2.
 destruct (exec_elements_taptweak_strauss_wnaf_half Model Datatypes.false e le m bs bp ba1 sb1 word1
  LowLocal Symbol State No Pointer StateSeparate LowSeparate Owned Input1)
  as (m1 & last1 & digits1 & First & Array1 & Bound1 & Count1 & Pointer1 & Source1 & Owned1 & Frame1
    & Keep1 & Readonly1 & Literal1).
 pose (l1:=strauss_wnaf_half_temps Datatypes.false le bp (last1+1)).
 assert (State1:l1!_state=Some (Vptr bs Ptrofs.zero)).
 { unfold l1,strauss_wnaf_half_temps;rewrite !PTree.gso by discriminate;exact State. }
 assert (No1:l1!_no=Some (Vlong Int64.zero)).
 { unfold l1,strauss_wnaf_half_temps;rewrite !PTree.gso by discriminate;exact No. }
 assert (Input2I:scalar_at m1 ba2 0 (map Int64.repr (scalar_limbs_of (wnaf5_input_scalar sb2 word2)))).
 { eapply scalar_at_lframe;[exact Input2|exact Frame1|intros;split;left;exact HighSeparate]. }
 destruct (exec_elements_taptweak_strauss_wnaf_half Model Datatypes.true e l1 m1 bs bp ba2 sb2 word2
  HighLocal Symbol State1 No1 Pointer1 StateSeparate HighSeparate Owned1 Input2I)
  as (mf & last2 & digits2 & Second & Array2 & Bound2 & Count2 & Pointer2 & Source2 & Owned2 & Frame2
    & Keep2 & Readonly2 & Literal2).
 assert (Array1F:wnaf_array_state mf bp 0 129 5 (wnaf5_input_sign sb1) 129 last1 digits1).
 { eapply wnaf_array_slice_lframe;[exact Array1|exact Frame2|].
   intros pos Range;unfold strauss_wnaf_half_outside,wnaf_slice_outside;
   cbn [strauss_wnaf_base strauss_wnaf_count_offset];split;right;left;lia. }
 assert (PointValid:Mem.valid_block m1 bp).
 { eapply Mem.perm_valid_block;apply (Owned1 0);lia. }
 assert (Count1F:Mem.load Mint32 mf bp 1032=Some (Vint (Int.repr (last1+1)))).
 { rewrite (proj1 Frame2 Mint32 bp 1032 PointValid);[exact Count1|].
   intros pos Range;change (1032<=pos<1032+4) in Range.
   unfold strauss_wnaf_half_outside,wnaf_slice_outside;
   cbn [strauss_wnaf_base strauss_wnaf_count_offset];split;[right;right|right;left];lia. }
 assert (Source1F:scalar_at mf ba1 0 (map Int64.repr (scalar_limbs_of (wnaf5_input_scalar sb1 word1)))).
 { eapply scalar_at_lframe;[exact Source1|exact Frame2|intros;split;left;exact LowSeparate]. }
 assert (Frame:lframe (wnaf_slice_outside bp 0 260) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact Frame1|].
     unfold strauss_wnaf_half_outside,wnaf_slice_outside;
     cbn [strauss_wnaf_base strauss_wnaf_count_offset];intros old pos Outside _;clear -Outside;intuition lia.
   - eapply lframe_implies;[exact Frame2|].
     unfold strauss_wnaf_half_outside,wnaf_slice_outside;
     cbn [strauss_wnaf_base strauss_wnaf_count_offset];intros old pos Outside _;clear -Outside;intuition lia. }
 exists mf,last1,last2,digits1,digits2;split.
 - unfold strauss_wnaf_prepare,strauss_wnaf_prepare_temps.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact First|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Second|constructor].
 - split;[exact Array1F|];split;[exact Array2|];split;[exact Bound1|];split;[exact Bound2|];
   split;[exact Count1F|];split;[exact Count2|];split;[exact Pointer2|];
   split;[exact Source1F|];split;[exact Source2|];split;[exact Owned2|];split;[exact Frame|];split.
   + eapply keeps_permissions_trans;eassumption.
   + split;[eapply preserved_trans;eassumption|];split;assumption.
Qed.
