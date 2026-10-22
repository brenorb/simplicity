(** Original decompression caller prefix, from real caller-owned storage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_local_regions
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_copy_owned
 C.jet_secp_multiply_normalize_bridge C.jet_secp_decompress_statements
 C.jet_secp_square_execution C.jet_secp_square_columns C.jet_secp_square_numeric
 C.jet_secp_square_separate_numeric C.jet_secp_square_separate_caller
 C.jet_secp_field_product_owned C.jet_secp_point_mul_storage C.jet_secp_field_add7
 C.jet_secp_field_mul_small C.jet_secp_decompress_numeric C.jet_secp_statement_prefix C.jet_secp_fns.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem exec_decompress_copy_owned e le m bx br w :
 le!_x=Some (Vptr bx Ptrofs.zero) -> le!_r=Some (Vptr br Ptrofs.zero) -> bx<>br ->
 fe_at m bx 0 (words5 w) -> Mem.range_perm m br 0 88 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m decompress_copy_stmt E0 le mf Out_normal /\
 fe_at mf br 0 (words5 w) /\ Mem.range_perm mf br 0 88 Cur Freeable /\
 (forall b pos k p, Mem.perm mf b pos k p <-> Mem.perm m b pos k p) /\
 lframe (fun b pos=>b<>br \/ pos<0 \/ 40<=pos) m mf.
Proof.
 intros X R Ne Field Free.
 destruct (exec_field_copy_owned e le m (Ederef decompress_source curve_fe_type)
  (decompress_point_field _x curve_fe_type) bx 0 br 0 w eq_refl eq_refl)
  as (mf & Copy & Out & Perms & Frame).
 - eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact X|apply deref_loc_copy;reflexivity].
 - apply eval_decompress_field;[left;reflexivity|exact R].
 - exact Ne.
 - exact Field.
 - lia.
 - exists 0;reflexivity.
 - change (40<=18446744073709551615);lia.
 - intros pos Range;apply Free;lia.
 - exists mf;split;[exact Copy|];split;[exact Out|];split.
   + intros pos Range;apply Perms;apply Free;exact Range.
   + split;assumption.
Qed.

Theorem exec_decompress_finite_owned e le m br :
 le!_r=Some (Vptr br Ptrofs.zero) -> Mem.range_perm m br 0 88 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m decompress_finite_stmt E0 le mf Out_normal /\
 Mem.load Mint32 mf br 80=Some (Vint Int.zero) /\ Mem.range_perm mf br 0 88 Cur Freeable /\
 lframe (fun b pos=>b<>br \/ pos<80 \/ 84<=pos) m mf.
Proof.
 intros R Free.
 assert (WritePerm : Mem.range_perm m br 0 88 Cur Writable) by (apply freeable_range_writable;exact Free).
 assert (Access : Mem.valid_access m Mint32 br 80 Writable).
 { split;[intros pos Range;apply WritePerm;change (80<=pos<84) in Range;lia|exists 20;reflexivity]. }
 destruct (Mem.valid_access_store m Mint32 br 80 (Vint Int.zero) Access) as (mf & Store).
 exists mf;split.
 - unfold decompress_finite_stmt;eapply exec_Sassign with (loc:=br) (ofs:=Ptrofs.repr 80) (bf:=Full)
    (v2:=Vint Int.zero) (v:=Vint Int.zero).
   + apply eval_decompress_field;[right;right;left;reflexivity|exact R].
   + constructor.
   + reflexivity.
   + eapply assign_loc_value with (chunk:=Mint32);[reflexivity|].
     change (Mem.store Mint32 m br 80 (Vint Int.zero)=Some mf);exact Store.
 - split;[exact (Mem.load_store_same _ _ _ _ _ _ Store)|];split.
   + intros pos Range;eapply Mem.perm_store_1;[exact Store|apply Free;exact Range].
   + apply lframe_unchanged;eapply Mem.store_unchanged_on;[exact Store|].
     intros pos Range;change (80<=pos<84) in Range.
     intros [Other|[Before|After]];[contradiction|lia|lia].
Qed.

Definition decompress_prefix_frame (bx br b2 b3 b : block) (_ : Z) :=
 b<>bx /\ b<>br /\ b<>b2 /\ b<>b3.
Local Ltac prefix_keep_field H F :=
 eapply curve_keep_field_range;[reflexivity|exact H|exact F|];intros;repeat split;
 first [congruence|left;congruence|right;left;lia].
Local Ltac prefix_keep_free H F :=
 eapply curve_keep_free;[lia|exact H|exact F|];intros;repeat split;
 first [congruence|left;congruence].

Theorem exec_decompress_prefix_owned e le m bx br b2 b3 w :
 le!_x=Some (Vptr bx Ptrofs.zero) -> le!_r=Some (Vptr br Ptrofs.zero) ->
 e!_x2=Some (b2,curve_fe_type) -> e!_x3=Some (b3,curve_fe_type) ->
 e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_add_int=None ->
 NoDup [bx;br;b2;b3] -> square_input_bounds w -> fe_at m bx 0 (words5 w) ->
 Mem.range_perm m bx 0 40 Cur Freeable -> Mem.range_perm m br 0 88 Cur Freeable ->
 Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m (statement_sequence decompress_prefix Sskip) E0 le mf Out_normal /\
 fe_at mf bx 0 (words5 w) /\ fe_at mf br 0 (words5 w) /\
 fe_at mf b3 0 (words5 (decompress_root_words w)) /\ Mem.load Mint32 mf br 80=Some (Vint Int.zero) /\
 Mem.range_perm mf bx 0 40 Cur Freeable /\ Mem.range_perm mf br 0 88 Cur Freeable /\
 Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\
 lframe (decompress_prefix_frame bx br b2 b3) m mf.
Proof.
 intros X R E2 E3 EQ EM EA Sep Bounds Input XF RF F2 F3.
 assert (Pairs : bx<>br /\ bx<>b2 /\ bx<>b3 /\ br<>b2 /\ br<>b3 /\ b2<>b3).
 { repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence. }
 destruct Pairs as (XR & X2 & X3 & R2 & R3 & N23).
 destruct (exec_decompress_copy_owned e le m bx br w X R XR Input RF)
  as (mc & Copy & RX0 & RF0 & Perms & Frame0).
 assert (IX0 : fe_at mc bx 0 (words5 w)) by (prefix_keep_field Input Frame0).
 assert (XF0 : Mem.range_perm mc bx 0 40 Cur Freeable) by (prefix_keep_free XF Frame0).
 assert (F20 : Mem.range_perm mc b2 0 40 Cur Freeable) by (prefix_keep_free F2 Frame0).
 assert (F30 : Mem.range_perm mc b3 0 40 Cur Freeable) by (prefix_keep_free F3 Frame0).
 destruct (eval_square_separate_from_storage w mc b2 bx Bounds F20 IX0 XF0 ltac:(congruence))
  as (ms & Square & SQ & F2S & IX1 & XF1 & SqVal & SqBounds & Frame1).
 assert (RX1 : fe_at ms br 0 (words5 w)) by (prefix_keep_field RX0 Frame1).
 assert (RF1 : Mem.range_perm ms br 0 88 Cur Freeable) by (prefix_keep_free RF0 Frame1).
 assert (F31 : Mem.range_perm ms b3 0 40 Cur Freeable) by (prefix_keep_free F30 Frame1).
 destruct (eval_field_product_owned w (square_words w) ms b3 bx b2 Bounds SqBounds
  ltac:(congruence) ltac:(congruence) X2 F31 IX1 XF1 SQ F2S)
  as (mm & Multiply & Cubic & IX2 & SQ2 & F32 & XF2 & F22 & CubeVal & CubeBounds & Frame2).
 assert (RX2 : fe_at mm br 0 (words5 w)) by (prefix_keep_field RX1 Frame2).
 assert (RF2 : Mem.range_perm mm br 0 88 Cur Freeable) by (prefix_keep_free RF1 Frame2).
 destruct (exec_decompress_finite_owned e le mm br R RF2) as (mi & Finite & Flag & RF3 & Frame3).
 assert (RX3 : fe_at mi br 0 (words5 w)) by (prefix_keep_field RX2 Frame3).
 assert (IX3 : fe_at mi bx 0 (words5 w)) by (prefix_keep_field IX2 Frame3).
 assert (Cubic3 : fe_at mi b3 0 (words5 (point_mul_words w (square_words w)))) by (prefix_keep_field Cubic Frame3).
 assert (XF3 : Mem.range_perm mi bx 0 40 Cur Freeable) by (prefix_keep_free XF2 Frame3).
 assert (F23 : Mem.range_perm mi b2 0 40 Cur Freeable) by (prefix_keep_free F22 Frame3).
 assert (F33 : Mem.range_perm mi b3 0 40 Cur Freeable) by (prefix_keep_free F32 Frame3).
 destruct (eval_field_add7_small (point_mul_words w (square_words w)) mi b3 Cubic3 F33 CubeBounds)
  as (mf & Add & Root & RootVal & RootBound & F34 & RawFrame4).
 pose proof (curve_frame_one add7_regs b3 mi mf eq_refl RawFrame4) as Frame4.
 assert (RX4 : fe_at mf br 0 (words5 w)) by (prefix_keep_field RX3 Frame4).
 assert (IX4 : fe_at mf bx 0 (words5 w)) by (prefix_keep_field IX3 Frame4).
 assert (XF4 : Mem.range_perm mf bx 0 40 Cur Freeable) by (prefix_keep_free XF3 Frame4).
 assert (RF4 : Mem.range_perm mf br 0 88 Cur Freeable) by (prefix_keep_free RF3 Frame4).
 assert (F24 : Mem.range_perm mf b2 0 40 Cur Freeable) by (prefix_keep_free F23 Frame4).
 assert (FlagF : Mem.load Mint32 mf br 80=Some (Vint Int.zero)).
 { rewrite (proj1 Frame4 Mint32 br 80 ltac:(eapply Mem.perm_valid_block;apply (RF3 0);lia)
   ltac:(intros;exact R3));exact Flag. }
 assert (C2 : Clight2.exec_stmt secp_ge e le mc decompress_square_stmt E0 le ms Out_normal).
 { unfold decompress_square_stmt;eapply exec_curve_call with
    (vargs:=[Vptr b2 Ptrofs.zero;Vptr bx Ptrofs.zero]) (v:=Vundef).
   - unfold secp_pure;repeat (first [left;reflexivity|right]).
   - exact EQ.
   - eapply eval_Econs;[apply eval_curve_local;exact E2|reflexivity|].
     eapply eval_Econs;[apply eval_Etempvar;exact X|reflexivity|constructor].
   - exact Square. }
 assert (C3 : Clight2.exec_stmt secp_ge e le ms decompress_cube_stmt E0 le mm Out_normal).
 { unfold decompress_cube_stmt;eapply exec_curve_call with
    (vargs:=[Vptr b3 Ptrofs.zero;Vptr bx Ptrofs.zero;Vptr b2 Ptrofs.zero]) (v:=Vundef).
   - unfold secp_pure;repeat (first [left;reflexivity|right]).
   - exact EM.
   - eapply eval_Econs;[apply eval_curve_local;exact E3|reflexivity|].
     eapply eval_Econs;[apply eval_Etempvar;exact X|reflexivity|].
     eapply eval_Econs;[apply eval_curve_local;exact E2|reflexivity|constructor].
   - exact Multiply. }
 assert (C5 : Clight2.exec_stmt secp_ge e le mi decompress_add_stmt E0 le mf Out_normal).
 { unfold decompress_add_stmt;eapply exec_curve_call with
    (vargs:=[Vptr b3 Ptrofs.zero;Vint (Int.repr 7)]) (v:=Vundef).
   - unfold secp_pure;repeat (first [left;reflexivity|right]).
   - exact EA.
   - eapply eval_Econs;[apply eval_curve_local;exact E3|reflexivity|].
     eapply eval_Econs;[constructor|reflexivity|constructor].
   - exact Add. }
 assert (Frame : lframe (decompress_prefix_frame bx br b2 b3) m mf).
 { eapply lframe_trans;[eapply lframe_implies;[exact Frame0|];intros b pos [NX [NR [N2 N3]]] _;left;exact NR|].
   eapply lframe_trans;[eapply lframe_implies;[exact Frame1|];intros b pos [NX [NR [N2 N3]]] _;split;assumption|].
   eapply lframe_trans;[eapply lframe_implies;[exact Frame2|];intros b pos [NX [NR [N2 N3]]] _;repeat split;assumption|].
   eapply lframe_trans;[eapply lframe_implies;[exact Frame3|];intros b pos [NX [NR [N2 N3]]] _;left;exact NR|].
   eapply lframe_implies;[exact Frame4|];intros b pos [NX [NR [N2 N3]]] _;exact N3. }
 exists mf;split.
 - unfold decompress_prefix;cbn [statement_sequence].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Copy|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact C2|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact C3|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Finite|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact C5|apply exec_Sskip].
 - split;[exact IX4|];split;[exact RX4|];split;[exact Root|];split;[exact FlagF|].
   split;[exact XF4|];split;[exact RF4|];split;[exact F24|];split;assumption.
Qed.
