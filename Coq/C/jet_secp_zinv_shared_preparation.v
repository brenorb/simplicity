(** Both actual loose-coordinate preparation triples and their shared source. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_curve_statements C.jet_secp_curve_square C.jet_secp_multiply_normalize_bridge
 C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage C.jet_secp_square_columns
 C.jet_secp_field_mul_small C.jet_secp_field_weak_loose C.jet_secp_curve_frame
 C.jet_secp_field_read_preservation C.jet_secp_statement_prefix C.jet_secp_zinv_initial_products
 C.jet_secp_zinv_coordinate.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words weak_loose_words.
Fixpoint zinv_statement_drop n s := match n,s with
 | O,_=>s | S n,Ssequence _ tail=>zinv_statement_drop n tail | _,_=>Sskip end.
Definition zinv_shared_preparation := zinv_coordinate_statements false++zinv_coordinate_statements true.
Definition zinv_after_shared_preparation := zinv_statement_drop 6 zinv_after_z12.
Lemma zinv_shared_preparation_source : zinv_after_z12=
 statement_sequence zinv_shared_preparation zinv_after_shared_preparation.
Proof. reflexivity. Qed.
Definition zinv_shared_frame (bu bv bs bt bz ba bx : block) pos :=
 bx<>bu /\ bx<>bv /\ bx<>bs /\ bx<>bt /\ bx<>bz /\ (bx<>ba \/ pos<0 \/ 80<=pos).

Theorem exec_zinv_shared_preparation x y u v t e le m bp ba bu bv bs bt bz :
 le!_a=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) ->
 e!_u1=Some (bu,curve_fe_type) -> e!_u2=Some (bv,curve_fe_type) ->
 e!_s1=Some (bs,curve_fe_type) -> e!_s2=Some (bt,curve_fe_type) -> e!_z12=Some (bz,curve_fe_type) ->
 e!_secp256k1_fe_normalize_weak=None -> e!_secp256k1_fe_mul=None ->
 NoDup [bp;ba;bu;bv;bs;bt;bz] ->
 (forall i,(i<5)%nat -> Int64.unsigned (x i)<=2^60) ->
 (forall i,(i<5)%nat -> Int64.unsigned (y i)<=2^60) ->
 square_input_bounds u -> square_input_bounds v -> square_input_bounds t ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) ->
 fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) -> fe_at m bz 0 (words5 t) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
 Mem.range_perm m bu 0 40 Cur Freeable -> Mem.range_perm m bv 0 40 Cur Freeable ->
 Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m bz 0 40 Cur Freeable ->
 exists mf,
 Clight2.exec_stmt secp_ge e le m (statement_sequence zinv_shared_preparation Sskip) E0 le mf Out_normal /\
 fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\
 fe_at mf ba 0 (words5 u) /\ fe_at mf ba 40 (words5 v) /\ fe_at mf bz 0 (words5 t) /\
 fe_at mf bu 0 (words5 (weak_loose_words x)) /\ fe_at mf bv 0 (words5 (point_mul_words u t)) /\
 fe_at mf bs 0 (words5 (weak_loose_words y)) /\ fe_at mf bt 0 (words5 (point_mul_words v t)) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 Mem.range_perm mf bu 0 40 Cur Freeable /\ Mem.range_perm mf bv 0 40 Cur Freeable /\
 Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bz 0 40 Cur Freeable /\
 mul_small_input_bounds (weak_loose_words x) /\ mul_small_input_bounds (weak_loose_words y) /\
 square_input_bounds (point_mul_words u t) /\ square_input_bounds (point_mul_words v t) /\
 lframe (zinv_shared_frame bu bv bs bt bz ba) m mf.
Proof.
 intros HA HB EU EV ES ET EZ EW EM Sep BX BY BU BV BT X Y U V T PF AF UF VF SF TF ZF.
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep.
 assert (SepX : NoDup [bp;ba;bu;bv;bz]) by
   (repeat rewrite NoDup_cons_iff;cbn [In];intuition congruence).
 assert (SepY : NoDup [bp;ba;bs;bt;bz]) by
   (repeat rewrite NoDup_cons_iff;cbn [In];intuition congruence).
 destruct (exec_zinv_coordinate false x u t e le m bp ba bu bv bz HA HB EU EV EZ EW EM
   SepX BX BU BT X U T PF AF UF VF ZF)
   as (mi & CX & XI & UI & TI & U1I & U2I & PFI & AFI & UFI & VFI & ZFI & VX & TX & VU & TU & FX).
 assert (OutP : forall pos,zinv_coordinate_frame false bu bv ba bz bp pos).
 { intro pos;unfold zinv_coordinate_frame;repeat split;try (left;intuition congruence);intuition congruence. }
 pose proof (field_at_lframe _ _ _ _ _ _ Y FX OutP) as YI.
 assert (VI : fe_at mi ba 40 (words5 v)).
 { eapply curve_keep_field_range;[reflexivity|exact V|exact FX|].
   intros pos Range;unfold zinv_coordinate_frame,curve_square_offset;repeat split;
     try (intuition congruence);right;right;lia. }
 assert (SFI : Mem.range_perm mi bs 0 40 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact SF|exact FX|].
   intro pos;unfold zinv_coordinate_frame;repeat split;
     first [solve [left;clear -Sep;intuition congruence]|solve [clear -Sep;intuition congruence]]. }
 assert (TFI : Mem.range_perm mi bt 0 40 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact TF|exact FX|].
   intro pos;unfold zinv_coordinate_frame;repeat split;
     first [solve [left;clear -Sep;intuition congruence]|solve [clear -Sep;intuition congruence]]. }
 destruct (exec_zinv_coordinate true y v t e le mi bp ba bs bt bz HA HB ES ET EZ EW EM
   SepY BY BV BT YI VI TI PFI AFI SFI TFI ZFI)
   as (mf & CY & YF & VFinal & TOut & S1F & S2F & PFF & AFF & SFF & TFF & ZFF & VY & TY & VV & TV & FY).
 assert (OutPF : forall pos,zinv_coordinate_frame true bs bt ba bz bp pos).
 { intro pos;unfold zinv_coordinate_frame;repeat split;try (left;intuition congruence);intuition congruence. }
 pose proof (field_at_lframe _ _ _ _ _ _ XI FY OutPF) as XF.
 assert (UFinal : fe_at mf ba 0 (words5 u)).
 { eapply curve_keep_field_range;[reflexivity|exact UI|exact FY|].
   intros pos Range;unfold zinv_coordinate_frame,curve_square_offset;repeat split;
     try (intuition congruence);right;left;lia. }
 assert (OutU1 : forall pos,zinv_coordinate_frame true bs bt ba bz bu pos).
 { intro pos;unfold zinv_coordinate_frame;repeat split;try (left;intuition congruence);intuition congruence. }
 assert (OutU2 : forall pos,zinv_coordinate_frame true bs bt ba bz bv pos).
 { intro pos;unfold zinv_coordinate_frame;repeat split;try (left;intuition congruence);intuition congruence. }
 pose proof (field_at_lframe _ _ _ _ _ _ U1I FY OutU1) as U1F.
 pose proof (field_at_lframe _ _ _ _ _ _ U2I FY OutU2) as U2F.
 pose proof (curve_keep_free _ _ _ _ 40 ltac:(clear;lia) UFI FY OutU1) as UFF.
 pose proof (curve_keep_free _ _ _ _ 40 ltac:(clear;lia) VFI FY OutU2) as VFF.
 exists mf;split.
 - unfold zinv_shared_preparation.
   change (Clight2.exec_stmt secp_ge e le m (statement_sequence (zinv_coordinate_statements false)
     (statement_sequence (zinv_coordinate_statements true) Sskip)) E0 le mf Out_normal).
   eapply exec_statement_prefix_then_last;[exact CX|exact CY].
 - split;[exact XF|];split;[exact YF|];split;[exact UFinal|];split;[exact VFinal|];split;[exact TOut|];
   split;[exact U1F|];split;[exact U2F|];split;[exact S1F|];split;[exact S2F|];
   split;[exact PFF|];split;[exact AFF|];split;[exact UFF|];split;[exact VFF|];
   split;[exact SFF|];split;[exact TFF|];split;[exact ZFF|];
   split;[exact TX|];split;[exact TY|];split;[exact TU|];split;[exact TV|].
   eapply lframe_trans.
   + eapply lframe_implies;[exact FX|].
     intros bx pos (NU & NV & NS & NT & NZ & NA) Valid.
     unfold zinv_coordinate_frame,curve_square_offset;split;[exact NU|];split;[exact NV|];split;[exact NZ|].
     destruct NA as [NE|[Lo|Hi]];[left;exact NE|right;left;exact Lo|right;right;clear - Hi;lia].
   + eapply lframe_implies;[exact FY|].
     intros bx pos (NU & NV & NS & NT & NZ & NA) Valid.
     unfold zinv_coordinate_frame,curve_square_offset;split;[exact NS|];split;[exact NT|];split;[exact NZ|].
     destruct NA as [NE|[Lo|Hi]];[left;exact NE|right;left;clear - Lo;lia|right;right;exact Hi].
Qed.
