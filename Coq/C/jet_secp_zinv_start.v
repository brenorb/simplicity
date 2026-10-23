(** Nine original finite-path preparation statements from caller inputs only. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_curve_statements C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_point_mul_storage C.jet_secp_square_columns C.jet_secp_square_numeric
 C.jet_secp_field_mul_small C.jet_secp_field_weak_loose C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_statement_prefix C.jet_secp_zinv_initial_products C.jet_secp_zinv_product_prefix
 C.jet_secp_zinv_preparation C.jet_secp_zinv_s2.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words weak_loose_words square_words.
Definition zinv_az_words z inv := point_mul_words z inv.
Definition zinv_z12_words z inv := square_words (zinv_az_words z inv).
Definition zinv_start_statements := [zinv_az_statement;zinv_z12_statement]++zinv_preparation_statements.
Lemma zinv_start_source : zinv_finite_suffix=statement_sequence zinv_start_statements zinv_after_s2_az.
Proof. rewrite zinv_az_source,zinv_z12_source,zinv_preparation_source;reflexivity. Qed.
Definition zinv_start_fields m bp ba bb baz bz bu bv bs bt x y z u v inv :=
 fe_at m bp 0 (words5 x) /\ fe_at m bp 40 (words5 y) /\ fe_at m bp 80 (words5 z) /\
 fe_at m ba 0 (words5 u) /\ fe_at m ba 40 (words5 v) /\ fe_at m bb 0 (words5 inv) /\
 fe_at m baz 0 (words5 (zinv_az_words z inv)) /\ fe_at m bz 0 (words5 (zinv_z12_words z inv)) /\
 fe_at m bu 0 (words5 (weak_loose_words x)) /\ fe_at m bv 0 (words5 (point_mul_words u (zinv_z12_words z inv))) /\
 fe_at m bs 0 (words5 (weak_loose_words y)) /\ fe_at m bt 0 (words5 (zinv_s2_words v (zinv_z12_words z inv) (zinv_az_words z inv))).
Definition zinv_start_owned m bp ba bb baz bz bu bv bs bt :=
 Mem.range_perm m bp 0 128 Cur Freeable /\ Mem.range_perm m ba 0 88 Cur Freeable /\
 Mem.range_perm m bb 0 40 Cur Freeable /\ Mem.range_perm m baz 0 40 Cur Freeable /\
 Mem.range_perm m bz 0 40 Cur Freeable /\ Mem.range_perm m bu 0 40 Cur Freeable /\
 Mem.range_perm m bv 0 40 Cur Freeable /\ Mem.range_perm m bs 0 40 Cur Freeable /\ Mem.range_perm m bt 0 40 Cur Freeable.
Definition zinv_start_tight x y z u v inv :=
 mul_small_input_bounds (weak_loose_words x) /\ mul_small_input_bounds (weak_loose_words y) /\
 mul_small_input_bounds (zinv_az_words z inv) /\ mul_small_input_bounds (zinv_z12_words z inv) /\
 mul_small_input_bounds (point_mul_words u (zinv_z12_words z inv)) /\
 mul_small_input_bounds (zinv_s2_words v (zinv_z12_words z inv) (zinv_az_words z inv)).
Definition zinv_start_frame (bu bv bs bt bz baz bp ba bb bx : block) pos :=
 bx<>bu /\ bx<>bv /\ bx<>bs /\ bx<>bt /\ bx<>bz /\ bx<>baz /\
 (bx<>bp \/ pos<80 \/ 120<=pos) /\ (bx<>ba \/ pos<0 \/ 80<=pos) /\ bx<>bb.
Local Ltac separate_blocks HSep :=
 repeat rewrite NoDup_cons_iff in HSep;cbn [In] in HSep;
 repeat match goal with HC : _ /\ _ |- _ => destruct HC end;
 repeat match goal with HC : ~(?P \/ ?Q) |- _ =>
   let HP:=fresh "Sep" in let HQ:=fresh "Sep" in
   assert (HP:~P) by (intro;apply HC;left;assumption);
   assert (HQ:~Q) by (intro;apply HC;right;assumption);clear HC end.

Theorem exec_zinv_start x y z u v inv e le m bp ba bb baz bz bu bv bs bt :
 le!_a=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) -> le!_bzinv=Some (Vptr bb Ptrofs.zero) ->
 e!_u1=Some (bu,curve_fe_type) -> e!_u2=Some (bv,curve_fe_type) ->
 e!_s1=Some (bs,curve_fe_type) -> e!_s2=Some (bt,curve_fe_type) ->
 e!_z12=Some (bz,curve_fe_type) -> e!_az=Some (baz,curve_fe_type) ->
 e!_secp256k1_fe_normalize_weak=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None ->
 NoDup [bp;ba;bb;baz;bz;bu;bv;bs;bt] ->
 (forall i,(i<5)%nat -> Int64.unsigned (x i)<=2^60) ->
 (forall i,(i<5)%nat -> Int64.unsigned (y i)<=2^60) ->
 square_input_bounds z -> square_input_bounds inv -> square_input_bounds u -> square_input_bounds v ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) -> fe_at m bb 0 (words5 inv) ->
 zinv_start_owned m bp ba bb baz bz bu bv bs bt -> exists mf,
 Clight2.exec_stmt secp_ge e le m (statement_sequence zinv_start_statements Sskip) E0 le mf Out_normal /\
 zinv_start_fields mf bp ba bb baz bz bu bv bs bt x y z u v inv /\
 zinv_start_owned mf bp ba bb baz bz bu bv bs bt /\ zinv_start_tight x y z u v inv /\
 lframe (zinv_start_frame bu bv bs bt bz baz bp ba bb) m mf.
Proof.
 intros HA HB HI EU EV ES ET EZ EA EW EM EQ Sep BX BY BZ BI BU BV X Y Z U V I Owned.
 destruct Owned as (PF & AF & IF & AZF & ZF & UF & VF & SF & TF).
 separate_blocks Sep.
 assert (SepProd : NoDup [baz;bz;bp;bb]) by
   (repeat rewrite NoDup_cons_iff;cbn [In];intuition congruence).
 assert (SepPrep : NoDup [bp;ba;baz;bu;bv;bs;bt;bz]) by
   (repeat rewrite NoDup_cons_iff;cbn [In];intuition congruence).
 destruct (exec_zinv_first_products z inv e le m baz bz bp bb HA HI EA EZ EM EQ SepProd BZ BI AZF ZF Z PF I IF)
   as (mi & Products & AZI & TI & ZI & II & AZFI & ZFI & PFI & IFI & VA & VT & BA & BT & FI).
 assert (OutA : forall pos,zinv_product_frame baz bz bp bb ba pos).
 { intro pos;unfold zinv_product_frame;repeat split;try (left;congruence);congruence. }
 assert (XI : fe_at mi bp 0 (words5 x)).
 { eapply curve_keep_field_range;[reflexivity|exact X|exact FI|].
   intros pos Range;unfold zinv_product_frame;split;[congruence|];split;[congruence|];split;[right;left;clear - Range;lia|congruence]. }
 assert (YI : fe_at mi bp 40 (words5 y)).
 { eapply curve_keep_field_range;[reflexivity|exact Y|exact FI|].
   intros pos Range;unfold zinv_product_frame;split;[congruence|];split;[congruence|];split;[right;left;clear - Range;lia|congruence]. }
 pose proof (field_at_lframe _ _ _ _ _ _ U FI OutA) as UI.
 pose proof (field_at_lframe _ _ _ _ _ _ V FI OutA) as VI.
 pose proof (curve_keep_free _ _ _ _ 88 ltac:(lia) AF FI OutA) as AFI.
 assert (UFI : Mem.range_perm mi bu 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact UF|exact FI|];intro pos;unfold zinv_product_frame;repeat split;try (left;congruence);congruence. }
 assert (VFI : Mem.range_perm mi bv 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact VF|exact FI|];intro pos;unfold zinv_product_frame;repeat split;try (left;congruence);congruence. }
 assert (SFI : Mem.range_perm mi bs 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact SF|exact FI|];intro pos;unfold zinv_product_frame;repeat split;try (left;congruence);congruence. }
 assert (TFI : Mem.range_perm mi bt 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact TF|exact FI|];intro pos;unfold zinv_product_frame;repeat split;try (left;congruence);congruence. }
 destruct (exec_zinv_preparation x y u v (zinv_z12_words z inv) (zinv_az_words z inv) e le mi bp ba baz bu bv bs bt bz
   HA HB EU EV ES ET EZ EA EW EM SepPrep BX BY BU BV (zinv_tight_square _ BT) (zinv_tight_square _ BA)
   XI YI UI VI TI AZI PFI AFI AZFI UFI VFI SFI TFI ZFI)
   as (mf & Prep & XF & YF & UFinal & VFinal & TFinal & AZFinal & U1F & U2F & S1F & S2F &
     PFF & AFF & AZFF & UFF & VFF & SFF & TFF & ZFF & TX & TY & TU & TS & SValue & FP).
 assert (OutP : forall pos,zinv_preparation_frame bu bv bs bt bz baz ba bp pos).
 { intro pos;unfold zinv_preparation_frame;repeat split;try (left;congruence);congruence. }
 assert (OutI : forall pos,zinv_preparation_frame bu bv bs bt bz baz ba bb pos).
 { intro pos;unfold zinv_preparation_frame;repeat split;try (left;congruence);congruence. }
 pose proof (field_at_lframe _ _ _ _ _ _ ZI FP OutP) as ZFinal.
 pose proof (field_at_lframe _ _ _ _ _ _ II FP OutI) as IFinal.
 pose proof (curve_keep_free _ _ _ _ 40 ltac:(lia) IFI FP OutI) as IFF.
 exists mf;split.
 - unfold zinv_start_statements.
   change (Clight2.exec_stmt secp_ge e le m (statement_sequence [zinv_az_statement;zinv_z12_statement]
     (statement_sequence zinv_preparation_statements Sskip)) E0 le mf Out_normal).
   eapply exec_statement_prefix_then_last;[exact Products|exact Prep].
 - split.
   + unfold zinv_start_fields;repeat first [assumption|split].
   + split.
     * unfold zinv_start_owned;repeat first [assumption|split].
     * split.
       -- unfold zinv_start_tight;repeat first [assumption|split].
       -- eapply lframe_trans.
          ++ eapply lframe_implies;[exact FI|].
             intros bx pos (NU & NV & NS & NT & NZ & NAZ & NP & NA & NI) Valid.
             unfold zinv_product_frame;split;[exact NAZ|];split;[exact NZ|];split;assumption.
          ++ eapply lframe_implies;[exact FP|].
             intros bx pos (NU & NV & NS & NT & NZ & NAZ & NP & NA & NI) Valid.
             unfold zinv_preparation_frame;split;[exact NU|];split;[exact NV|];split;[exact NS|];
               split;[exact NT|];split;[exact NZ|];split;assumption.
Qed.
